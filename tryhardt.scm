(import (srfi 48))
(define (gensym s)
  (if (symbol? s) s (string->symbol s)))
(define db
  ;; Maps predicates to rules with the given predicate as their head.
  (make-hashtable equal-hash equal?))
(define fail #f)
(define no-bindings '())

(define (variable? x)
  (and (symbol? x) (char-upper-case? (string-ref (symbol->string x) 0))))

(define (get-binding var bindings)
  (assq var bindings))

(define (binding-val binding)
  (cdr binding))

;(define (extend-bindings var val bindings)
;  (cons (cons var val)
;        (if (eq? bindings no-bindings)
;            '()
;            bindings)))

(define (extend-bindings var val bindings)
  (cons (cons var val) bindings))

(define *occurs-check* (make-parameter #t))

(define (unify x y bindings)
  (cond
    [(eq? bindings fail) fail]
    [(eq? x y) bindings]
    [(variable? x) (unify-variable x y bindings)]
    [(variable? y) (unify-variable y x bindings)]
    [(and (pair? x) (pair? y))
     (unify (cdr x)
            (cdr y)
            (unify (car x) (car y) bindings))]
    [(equal? x y) bindings]
    [else fail]))

(define (unify-variable var x bindings)
  (cond
    [(get-binding var bindings)
     => (lambda (binding) (unify (binding-val binding) x bindings))]
    [(variable? x)
     (cond
       [(get-binding x bindings)
        => (lambda (binding) (unify var (binding-val binding) bindings))]
       [else (extend-bindings var x bindings)])]
    [(and (*occurs-check*) (occurs-check var x bindings))
     fail]
    [else
     (extend-bindings var x bindings)]))

(define (occurs-check var x bindings)
  (cond
    [(eq? var x) #t]
    [(and (variable? x) (get-binding x bindings))
     => (lambda (binding) (occurs-check var (binding-val binding) bindings))]
    [(pair? x)
     (or (occurs-check var (car x) bindings)
         (occurs-check var (cdr x) bindings))]
    [else #f]))

(define (reuse-cons a d p)
  (if (and (eq? a (car p)) (eq? d (cdr p)))
      p
      (cons a d)))

(define (subst-bindings bindings x)
  (cond
    [(eq? bindings fail) fail]
    [(eq? bindings no-bindings) x]
    [(and (variable? x) (get-binding x bindings))
     => (lambda (binding) (subst-bindings bindings (binding-val binding)))]
    [(pair? x)
     (reuse-cons (subst-bindings bindings (car x))
                 (subst-bindings bindings (cdr x))
                 x)]
    [else x]))

(define (clause-head clause)
  (car clause))

(define (clause-body clause)
  (cdr clause))

(define (get-clauses pred)
  (display "Getting clauses\n")
  (display pred)
  (hashtable-ref db pred '()))

(define (predicate relation)
  (car relation))

(define *db-predicates* '())

(define (add-clause clause)
  (let ([pred (predicate (clause-head clause))])
    (unless (and (symbol? pred) (not (variable? pred)))
      (error '<- "invalid predicate name (symbol required), given ~a" pred))
    (unless (memq pred *db-predicates*)
      (set! *db-predicates* (cons pred *db-predicates*)))
    (hashtable-update! db pred
             (lambda (clauses) (append (get-clauses pred) (list clause))) '())
    pred))

(define (replace-?-variables exp)
  (cond
    [(eq? exp '?) (gensym '?)]
    [(pair? exp)
     (reuse-cons (replace-?-variables (car exp))
                 (replace-?-variables (cdr exp))
                 exp)]
    [else exp]))

; (define-syntax <-
;   (syntax-rules ()
;     [(_ . clause)
;      (add-clause (replace-?-variables 'clause))]))
(define-syntax <-
  ;; Macro for rule definitions. Pass a head clause and 0+ body clauses.
  (syntax-rules ()
    ((_ head . body)
     (hashtable-update!
       db (predicate `head)
      (lambda (clauses) (append clauses (list (cons `head `body)))) '()))))


(define (unique-find-anywhere-if predicate tree found-so-far)
  (if (pair? tree)
      (unique-find-anywhere-if predicate
                               (car tree)
                               (unique-find-anywhere-if predicate
                                                        (cdr tree)
                                                        found-so-far))
      (if (predicate tree)
          (if (memq tree found-so-far)
              found-so-far
              (cons tree found-so-far))
          found-so-far)))

(define (variables-in exp)
  (unique-find-anywhere-if variable? exp '()))

(define (sublis bindings tree)
  (if (pair? tree)
      (reuse-cons (sublis bindings (car tree))
                  (sublis bindings (cdr tree))
                  tree)
      (cond
        [(assq tree bindings)
         => (lambda (binding) (cdr binding))]
        [else tree])))

(define (rename-variables x)
  (sublis (map (lambda (var) (cons var (gensym var)))
               (variables-in x))
          x))

; TO CPS
(define (search-choices goal clauses bindings other-goals cut-k)
  (define (inner lst k)
    (if (null? lst)
        (k fail)
        (let ([new-clause (rename-variables (car lst))])
          (prove-all (append (clause-body new-clause) other-goals)
                     (unify goal (clause-head new-clause) bindings)
                     cut-k
                     (lambda (test)
                       (if (eq? fail test)
                           (inner (cdr lst) k)
                           (k test)))))))
  (inner clauses cut-k))

; TO CPS
(define (prove goal bindings other-goals cut-k k)
  (if (eq? goal '!)
      (begin (format "[TRACE] found cut\n")
             (prove-all other-goals bindings cut-k cut-k))
      (let ([clauses (get-clauses (predicate goal))])
        (display "HERE:")
        (display clauses)
        (if (procedure? clauses)
            (clauses (cdr goal) bindings other-goals cut-k k)
            (search-choices goal clauses bindings other-goals k)))))

; TO CPS
(define (prove-all goals bindings cut-k k)
(display "in prove-all\n")
  (if (eq? cut-k k)
      (format "cut-k = k\n")
      (format "cut-k != k\n"))
  (format "[TRACE]\n")
  (cond
    [(eq? bindings fail)
     (k fail)]
    [(null? goals)
     (k bindings)]
    [else
     (prove (car goals) bindings (cdr goals) cut-k k)]))

(define (continue?)
  (case (read-char)
    [(#\;) #t]
    [(#\.) #f]
    [(#\newline) (continue?)]
    [else (display " Type ; to see more or . to stop\n")
          (continue?)]))

; TO CPS
;; this also serves as a prototype for primitives in CPS form
(define (show-prolog-vars vars bindings other-goals cut-k k)
(display "\nshow prolog vars\n")
(display vars)
(display "\n")
(display bindings)
(display "\n")
(display other-goals)
(display "\n")
(display cut-k)
(display "\n")
(display k)
(display "\n")
  (if (null? vars)
      (display "\nYes.")
      (for-each (lambda (var)
                  (format "\n~a = ~a" var (subst-bindings bindings var)))
                vars))
  (if (continue?)
      (k fail)
      (prove-all other-goals bindings cut-k k)))

;;(putprop 'show-prolog-vars 'clauses show-prolog-vars)
(hashtable-update!
  db 'show-prolog-vars
 (lambda (x) show-prolog-vars) '())

; TO-CPS
(define (top-level-prove goals)
  (let ([k (lambda (_)
             (format "\nNo.")
             )])
    (prove-all `(,@goals (show-prolog-vars ,@(variables-in goals)))
               no-bindings
               k
               k)))

(define-syntax ?-
  (syntax-rules ()
    [(_ . goals)
     (top-level-prove (replace-?-variables 'goals))]))

;; =============================================================================
;; SAMPLE DATA

(<- (father albert barnaby))
(<- (father albert babar))

(<- (mother anna   barnaby))
(<- (mother anna   babar))

(<- (father alain  bob))
(<- (father alain  ben))

(<- (mother alice  bob))
(<- (mother alice  ben))

(<- (father ben    carla))
(<- (mother carla  dany))

(<- (parent Parent Child) (father Parent Child))
(<- (parent Parent Child) (mother Parent Child))

(<- (ancestor X Z) (parent X Z))
(<- (ancestor X Z) (parent X Y) (ancestor Y Z))

(<- (append () T T))
(<- (append (H . T) L2 (H . TR))
       (append T L2 TR))
