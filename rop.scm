(load-option 'sos)

(define (instance-copy r)
  (let* ((class (instance-class r))
         (slots (map slot-name (class-slots class))))
    (define constr
      (instance-constructor class slots 'no-init))
    (apply constr (map (lambda (slot) (slot-value r slot)) slots))))
(define (slot-subst r f e)
  (let ((r (instance-copy r)))
    (set-slot-value! r f e)
    r))

(define-class <reflective> ())
(define-class <simple-reflective> (<reflective>))
(define-class <value-reflective> (<simple-reflective>) base-value)
(define-class <control-reflective> (<reflective>) (objs initial-value '()))

(define-generic atomic (v outer))
(define-generic compound-initial (outer))
(define-generic compound-rest (outer inner))

(define-generic atomic-control (outer atom))
(define-generic compound-control (outer initial rest))

(define-method atomic (v (outer <simple-reflective>)) outer)
(define-method compound-initial ((outer <simple-reflective>)) outer)
(define-method compound-rest ((outer <simple-reflective>) (inner <simple-reflective>)) inner)

(define-method atomic (v (outer <value-reflective>)) (slot-subst outer 'base-value v))

(define-method atomic-control ((outer <control-reflective>) atom) (atom outer))
(define-method compound-control ((outer <control-reflective>) initial rest) (append-map rest (initial outer)))

(define (value-objs c)
  (filter (lambda (x) (instance-of? x <value-reflective>)) (slot-value c 'objs)))

(define (alpha v)
  (lambda (c)
    (atomic-control c (lambda (c1) (list (slot-subst c1 'objs (map (lambda (s) (atomic v s)) (slot-value c1 'objs))))))))
(define (gamma i r)
  (lambda (c)
    (compound-control c
                      (lambda (c1) (i (slot-subst c1 'objs (map compound-initial (slot-value c1 'objs)))))
                      (lambda (c2)
                        (let ((c3 (slot-subst c2 'objs (map compound-rest (slot-value c 'objs) (slot-value c2 'objs)))))
                          (append-map (lambda (v) ((r (slot-value v 'base-value)) c3)) (value-objs c3)))))))

(define make-value-reflective (instance-constructor <value-reflective> '() 'no-init))
(define make-control-reflective (instance-constructor <control-reflective> '(objs) 'no-init))

(define (reflective-ref c r)
  (if (instance-of? c <control-reflective>)
      (if (instance-of? c r)
          c
          (reflective-ref (slot-value c 'objs) r))
      (if (instance-of? (car c) r)
          (car c)
          (reflective-ref (cdr c) r))))
(define (reflective-subst o r c)
  (if (instance-of? c <control-reflective>)
      (if (instance-of? c r)
          (slot-subst o 'objs (slot-value c 'objs))
          (slot-subst c 'objs (reflective-subst o r (slot-value c 'objs))))
      (if (instance-of? (car c) r)
          (cons o (cdr c))
          (cons (car c) (reflective-subst o r (cdr c))))))

(define (constant? e)
  (not (or (symbol? e) (pair? e))))

(define (trans e)
  (cond
    ((constant? e) `(_alpha ,e))
    ((symbol? e) `(_alpha ,e))
    ((eq? (car e) 'lambda)
     `(_alpha (lambda ,(cadr e) ,(trans (caddr e)))))
    ((eq? (car e) 'let)
     (trans `((lambda ,(map car (cadr e)) . ,(cddr e)) . ,(map cadr (cadr e)))))
    ((eq? (car e) 'if)
     `(_bind (_t ,(trans (cadr e)))
             (if _t ,(trans (caddr e)) ,(trans (cadddr e)))))
    ((eq? (car e) 'slot-subst)
     `(_bind (_e0 ,(trans (cadr e)))
             (_bind (_e1 ,(trans (cadddr e)))
                    (_alpha (slot-subst _e0 ,(caddr e) _e1)))))
    ((eq? (car e) 'slot-value)
     `(_bind (_e ,(trans (cadr e)))
             (_alpha (slot-value _e ,(caddr e)))))
    ((eq? (car e) 'reify)
     `(_bind (_r ,(trans (cadr e)))
             (lambda (_c) ((_alpha (_reflective-ref _c _r)) _c))))
    ((eq? (car e) 'reflect)
     `(_bind (_r ,(trans (cadr e)))
             (_bind (_o ,(trans (caddr e)))
                    (lambda (_c) (,(trans (cadddr e)) (_reflective-subst _o _r _c))))))
    (else
     (let ((names (list '_e0 '_e1 '_e2 '_e3 '_e4)))
       (fold-left (lambda (x y) `(_bind ,y ,x))
                  (map (lambda (n v) n) names e)
                  (reverse
                   (map (lambda (n v) (list n (trans v))) names e)))))))

(define (ev e env)
  (cond
    ((constant? e) e)
    ((symbol? e) (env e))
    ((eq? (car e) '_alpha)
     (alpha (ev (cadr e) env)))
    ((eq? (car e) '_bind)
     (gamma (ev (cadr (cadr e)) env) (lambda (x)
       (ev (caddr e) (lambda (y) (if (eq? y (car (cadr e))) x (env y)))))))
    ((eq? (car e) '_reflective-ref)
     (reflective-ref (ev (cadr e) env) (ev (caddr e) env)))
    ((eq? (car e) '_reflective-subst)
     (reflective-subst (ev (cadr e) env) (ev (caddr e) env) (ev (cadddr e) env)))
    ((eq? (car e) 'lambda)
     (lambda (x) (ev (caddr e) (lambda (y) (if (eq? y (car (cadr e))) x (env y))))))
    ((eq? (car e) 'if)
     (if (ev (cadr e) env) (ev (caddr e) env) (ev (cadddr e) env)))
    ((eq? (car e) 'slot-subst)
     (slot-subst (ev (cadr e) env) (cadr (caddr e)) (ev (cadddr e) env)))
    ((eq? (car e) 'slot-value)
     (slot-value (ev (cadr e) env) (cadr (caddr e))))
    (else
     (let ((rs (map (lambda (x) (ev x env)) e)))
       (apply (car rs) (cdr rs))))))

(load-option 'format)

(define-syntax eg
  (syntax-rules ()
    ((_ tested-expression expected-result)
     (begin
       (format #t "Testing ~a\n" 'tested-expression)
       (let* ((expected expected-result)
              (produced tested-expression))
         (or (equal? expected produced)
             (errorf 'test-check
               "Failed: ~a~%Expected: ~a~%Computed: ~a~%"
               'tested-expression expected produced)))))))

(define (vanilla-ev e)
  (let ((f (ev (trans e) (lambda (y) (error 'env (list 'unbound 'variable y)))))
        (c (make-control-reflective (list (make-value-reflective)))))
    (slot-value (car (slot-value (car (f c)) 'objs)) 'base-value)))

(eg (vanilla-ev 1) 1)
(eg (vanilla-ev '((lambda (x) x) 1)) 1)

(define-class <runtime> (<simple-reflective>) (ticks initial-value 0))
(define make-runtime (instance-constructor <runtime> '() 'no-init))
(define-method atomic (v (outer <runtime>))
  (slot-subst outer 'ticks (1+ (slot-value outer 'ticks))))
(define-method compound-initial ((outer <runtime>))
  (slot-subst outer 'ticks (1+ (slot-value outer 'ticks))))

(define (instr-ev e)
  (let ((f (ev (trans e) (lambda (y)
                           (if (eq? y '<runtime>) <runtime>
                               (error 'env (list 'unbound 'variable y))))))
        (c (make-control-reflective (list (make-value-reflective) (make-runtime)))))
    (list
     (slot-value (car (slot-value (car (f c)) 'objs)) 'base-value)
     (slot-value (cadr (slot-value (car (f c)) 'objs)) 'ticks))
    ))

(eg (instr-ev 1) '(1 1))
(eg (instr-ev '((lambda (x) x) 1)) '(1 5))

(eg
 (instr-ev '(let ((r (reify <runtime>)))
              (let ((result ((lambda (x) x) 1)))
                (reflect <runtime> r result))))

 (instr-ev '(let ((r (reify <runtime>)))
              (let ((result ((lambda (x) x) ((lambda (x) x) 1))))
                (reflect <runtime> r result)))))

(eg
 (instr-ev '(let ((r (reify <runtime>)))
              (let ((result 1))
                (let ((t (slot-value (reify <runtime>) 'ticks)))
                  (reflect <runtime> r t)))))
 '(16 6))
