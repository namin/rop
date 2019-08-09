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

(define-syntax bind
  (syntax-rules (gamma)
    ((_ (v ev) e)
     (gamma ev (lambda (v) e)))))

(define (constant? e)
  (not (or (symbol? e) (pair? e))))

(define (trans e)
  (cond
    ((constant? e) `(_alpha ,e))
    ((symbol? e) `(_alpha ,e))
    ((eq? (car e) 'lambda)
     `(_alpha (lambda ,(cadr e) ,(trans (caddr e)))))
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
    ((eq? (car e) 'lambda)
     (lambda (x) (ev (caddr e) (lambda (y) (if (eq? y (cadr e)) x (env y))))))
    ((eq? (car e) 'if)
     (if (ev (cadr e) env) (ev (caddr e) env) (ev (cadddr e) env)))
    ((eq? (car e) 'slot-subst)
     (slot-subst (ev (cadr e) env) (caddr e) (ev (cadddr e) env)))
    ((eq? (car e) 'slot-value)
     (slot-value (ev (cadr e) env) (caddr e)))
    (else
     (let ((rs (map (lambda (x) (ev x env)) e)))
       (apply (car rs) (cdr rs))))))

;;; examples

(define (vanilla-ev e)
  (let ((f (ev (trans e) (lambda (y) (error 'env (list 'unbound 'variable y)))))
        (c (make-control-reflective (list (make-value-reflective)))))
    (slot-value (car (slot-value (car (f c)) 'objs)) 'base-value)))

(define-class <runtime> (<simple-reflective>) (ticks initial-value 0))
(define make-runtime (instance-constructor <runtime> '() 'no-init))
(define-method atomic (v (outer <runtime>))
  (slot-subst outer 'ticks (1+ (slot-value outer 'ticks))))
(define-method compound-initial ((outer <runtime>))
  (slot-subst outer 'ticks (1+ (slot-value outer 'ticks))))

(define (instr-ev e)
  (let ((f (ev (trans e) (lambda (y) (error 'env (list 'unbound 'variable y)))))
        (c (make-control-reflective (list (make-value-reflective) (make-runtime)))))
    (list
     (slot-value (car (slot-value (car (f c)) 'objs)) 'base-value)
     (slot-value (cadr (slot-value (car (f c)) 'objs)) 'ticks))
    ))
