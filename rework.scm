;; PROLOG IN SCHEME - TEMPLATE
;; -----------------------------------------------------------------------------
;;
;; - Inside the rule database, predicates are represented by a (<name> .
;;   <arity>) pair (<arity> count the paramaters + 1 for the predicate name).
;;
;; - The rule database (`db`) maps predicates to a list of list of clauses.
;;   Each inner list corresponds to a rule, whose first item is the head.
;;
;; - Both goals and rule heads are represented by a list whose first item is a
;;   symbol designates the predicate.
;;
;; - Given a goal, use `rules-for` to return a list of rules applicable to that
;;   goal. It's not necessary to touch `db` directly.
;;
;; - Scheme symbols starting with an uppercase letter are taken to be Prolog
;;   variables.
;;
;; - Within your implementation you will need to manipulate a set of bindings,
;;   which maps from variables to their value (or to another variable). You
;;   should represent these bindings as an alist (a list of pairs), where each
;;   pair contains a variable and a value (or another variable). This alist
;;   should be treated as immutable. You can add a binding by prepending a pair
;;   (use `add-binding`) and you can backtrack by going back to a tail of the
;;   bindings. Use `lookup` to perform lookups in the bindings.
;;
;; - `unify` expects the two terms it receives to be pairs whose car is the term
;;   itself and whose cdr is a number representing the scope of the term.
;;   Scoping is crucial, as it helps distinguish variables with the same name.
;;
;;   Scopes are introduced by rules (each rule, even for the same predicate, has
;;   its own scope). Multiple applications of the same rule have different
;;   scopes!
;;
;;   As you decompose terms, it's important to remember to keep track of the
;;   scope.
;;
;;   It's probably a good idea to also represent each goal as a pair whose cdr
;;   is a scope. `?-` sets this up via the `scoped-goals` local variable.
;;
;; - Be careful when binding variables to variables: you shouldn't introduce
;;   cycles between variables, and you shouldn't rebind variables.

;; *** *** *** *** *** *** *** *** *** *** *** *** *** *** *** *** *** *** ***
;; Version modified by Group 4 for LSINF2335 - Programming Paradigms' course
;; Group 4 composition :
;;  - HALLET Adrien (adrien.hallet@student.uclouvain.be)
;;  - RUCQUOY Alexandre (alexandre.rucquoy@student.uclouvain.be)
;;
;; This work has been done alongside the reading of Peter Norvig's
;; "Paradigms or Artificial Intelligence Programming" (chapter 11) which was a
;; great help in the understanding of this project and its goals.

(import
  (srfi 27 random-bits)
  (scheme base)
  (scheme char)
  (scheme hash-table)
  (scheme list))
;; =============================================================================
;; DATA STRUCTURES

(define (printer vars bindings) ;TODO find a better way
  (display "(")
  (for-each
    (lambda (var) (subprint var (subst-var var bindings)))
   vars)
  (display ")")
)
(define (subprint var val)
  (display "(")
  (display var)
  (display " ")
  (display val)
  (display ")")
)

(define (predicate goal)
  ;; From a goal, returns a predicate: a (<name> . <arity>) pair.
  (car goal))

(define db
  ;; Maps predicates to rules with the given predicate as their head.
  (make-hashtable equal-hash equal?))

(define (rules-for goal)
  ;; Returns a list of rules which have the predicate of `goal` on the left-hand
  ;; side.
  (hashtable-ref db (predicate goal) '()))

(define (var? x)
  ;; Is `x` a symbol representing a Prolog variable?
  (and (symbol? x) (char-upper-case? (string-ref (symbol->string x) 0))))

(define (svar? x)
  ;; Is `x` a scoped Prolog variable?
  (and (pair? x) (var? (car x))))

(define (lookup var bindings)
  ;; Looks a variable in the bindings alist, returning the binding or #f if
  ;; there are no bindings.
  ;(define pair (assoc var bindings))
  ;(if (not pair) #f (cdr pair)))
  ;Shorter version
  (assq var bindings))

(define (add-binding var value bindings)
  ;; Returns a modification of bindings adding a binding from var to value.
  ;; There must be no existing bindings for var.
  (cons (cons var value) bindings))

;; =============================================================================
;; UNIFICATION

(define (unify t1 t2 bindings)
  ;; Returns new bindings that unify the two terms.
  (cond
    [(eq? bindings #f) #f]
    [(eq? t1 t2) bindings]
    [(var? t1) (unify-variable t1 t2 bindings)]
    [(var? t2) (unify-variable t2 t1 bindings)]
    [(and (pair? t1) (pair? t2))
     (unify (cdr t1)
            (cdr t2)
            (unify (car t1) (car t2) bindings))]
    [(equal? t1 t2) bindings]
    [else #f]))

(define (unify-variable var val bindings)
  (if (equal? var val)
    bindings ; var is val, no need to bind
    (let ((exist (lookup var bindings))) ; Check if contained
      (if (not exist)
        (if (occurs-check var val bindings)
          (add-binding var val bindings)
          #f)
          (unify (cdr exist)
          val
          bindings)))))
          
(define (occurs-check var exp bindings)
  (cond
    ((not (pair? exp)) #t)
      ((var? exp)
      (if (equal? var exp) #f
      (let ((exist (lookup exp bindings)))
        (if (not exist) #t
            (occurs-check var (cdr exist) bindings)))))
    ((occurs-check var (car exp) bindings) (occurs-check var (cdr exp) bindings))
    (else #f)))
    
 (define (reuse-cons a d p)
 (if (and (eq? a (car p)) (eq? d (cdr p)))
     p
     (cons a d)))
;; =============================================================================
;; (I can't get no ...)
;; SATISFACTION

;; Stores continue information after a successful call to `satisfy`, enabling
;; the retrieval of further solutions.
(define continue-info)

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
  (unique-find-anywhere-if var? exp '()))

(define (show-prolog-vars vars bindings scoped-goals)
 (if (null? vars)
     (display "()\n") ; Nothing to print (SAT request)
     (printer vars bindings)) ; Print the answers
 (if (continue?)
      #f ;; Stop recursion otherwise we print temporary variables
     (prove-all scoped-goals bindings)))

(hashtable-update! db 'show-prolog-vars (lambda (x) show-prolog-vars) '())
  ;; Callback to function

(define (continue?)
 (case (read-char)
   [(#\newline) #t]
   [else #f]
  ))

(define (prove-all goals bindings)
 (cond
   [(eq? bindings #f)
    #f]
   [(null? goals)
    bindings]
   [else
    (satisfy (car goals) bindings (cdr goals))]))

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
   (sublis (map (lambda (var) (cons var (format-var var)))
                (variables-in x))
           x))

(define (search-choices goal clauses bindings scoped-goals)
 (define (loop lst)
   (if (null? lst)
       #f
       (let* ([new-clause (rename-variables (car lst))]
              [test (prove-all (append (cdr new-clause) scoped-goals)
                               (unify goal (car new-clause) bindings))])
         (if (eq? #f test)
             (loop (cdr lst))
             test))))
 (loop clauses))

(define (satisfy goal bindings scope-goals)
      (let ([clauses (rules-for goal)])
        (if (procedure? clauses)
            (clauses (cdr goal) bindings scope-goals)
            (search-choices goal clauses bindings scope-goals))))

;; =============================================================================
;; DISPLAYING BINDINGS

(define (format-var var)
  ;; Returns a symbol representation of a variable.
  ;; Modified to solve "not a number" and avoir collision
  (if (symbol? var)
    (string->symbol
      (string-append
        (symbol->string var)
          (number->string (random-integer 100000000))))
    (string->symbol
      (string-append var
        (number->string (random-integer 100000000))))))

(define (subst-var var bindings)
  (cond
    [(eq? bindings #f) #f]
    [(eq? bindings '()) var]
    [(and (var? var) (lookup var bindings))
     => (lambda (binding) (subst-var (cdr binding) bindings))]
    [(pair? var)
     (reuse-cons (subst-var (car var) bindings )
                 (subst-var (cdr var) bindings)
                 var)]
    [else var]))

(define (subst-vars x scope bindings)
  ;; Returns the value corresponding to the given item (a variable, pair or
  ;; another value) after recursively substituting any variable within it.
  (cond ((var? x)   (subst-var (cons x scope) bindings))
        ((pair? x)  (cons (subst-vars (car x) scope bindings)
                          (subst-vars (cdr x) scope bindings)))
        (else       x)))

(define (extract-top-vars bindings)
  ;; From an alist of bindings, extracts a (name value) list for top-level
  ;; variables which have a binding.
  (define top-pairs (filter (lambda (pair) (eqv? (cdar pair) 0)) bindings))
  (define top-vars  (map (lambda (pair) (car pair)) top-pairs))
  (define names     (map (lambda (var) (car var)) top-vars))
  (define values    (map (lambda (var) (subst-var var bindings)) top-vars))
  (zip names values))

;; =============================================================================
;; TOP-LEVEL MACROS

(define-syntax <-
  ;; Macro for rule definitions. Pass a head clause and 0+ body clauses.
  (syntax-rules ()
    ((_ head . body)
     (hashtable-update!
       db (predicate 'head)
      (lambda (clauses) (append clauses (list (cons 'head 'body)))) '()))))

(define-syntax !!
  ;; Macro rule for unification. Pass two terms to unify.
  (syntax-rules ()
    ((_ c1 c2)
     (let ((bindings (unify 'c1 'c2 '())))
       (if (not bindings) #f
            bindings)))))

(define-syntax ?-
  ;; Macro rule for querying. Pass one or more goals.
  (syntax-rules ()
    ((_ . goals0)
    (let* ((_              (read-char)) ;; swallow first newline
          (goals          `goals0)
          (scoped-goals   (map (lambda (x) (cons x 0)) goals))
          (rules          (rules-for (car goals))))
          ;(bindings       (satisfy #| TODO |# '())))
      (if (not goals) #f
          (prove-all `(,@goals (show-prolog-vars ,@(variables-in goals))) '() ))))))

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

;; =============================================================================
