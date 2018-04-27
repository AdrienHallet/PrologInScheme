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

(import
  (scheme base)
  (scheme char)
  (scheme hash-table)
  (scheme list))

;; =============================================================================
;; DATA STRUCTURES

(define (predicate goal)
  ;; From a goal, returns a predicate: a (<name> . <arity>) pair.
  (cons (car goal) (length goal)))

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
  (define pair (assoc var bindings))
  (if (not pair) #f (cdr pair)))

(define (add-binding var value bindings)
  ;; Returns a modification of bindings adding a binding from var to value.
  ;; There must be no existing bindings for var.
  (cons (cons var value) bindings))

;; =============================================================================
;; UNIFICATION

(define (unify t1 t2 bindings)
  (cond ((eq? bindings #f) #f)
        ((equal? t1 t2) bindings)
        ((var? t1) (unify-variable t1 t2 bindings))
        ((var? t2) (unify-variable t2 t1 bindings))
        ((and (pair? t1) (pair? t2))
         (unify (cdr t1) (cdr t2)
                (unify (car t1) (car t2) bindings)))
        (#t #f)))

(define (unify-variable var x bindings)
  (cond ((get-binding var bindings)
         (unify (lookup var bindings) x bindings))
        ((and (var? x) (get-binding x bindings))
         (unify var (lookup x bindings) bindings))
        ((and #t (occurs-check var x bindings))
         #f)
        (#t (extend-bindings var x bindings))))

(define (occurs-check var x bindings)
  (cond ((eq? var x) #t)
        ((and (var? x) (get-binding x bindings))
         (occurs-check var (lookup x bindings) bindings))
        ((pair? x) (or (occurs-check var (car x) bindings)
                       (occurs-check var (cdr x) bindings)))
        (#t '())))

;; =============================================================================
;; SATISFACTION

;; Stores continue information after a successful call to `satisfy`, enabling
;; the retrieval of further solutions.
(define continue-info)

(define (satisfy #| TODO |# bindings)
  ;; Returns new bindings that satisfy the goals, or #f if no such bindings
  ;; exist. If successful, should set `continue-info`.
  '()
  #| TODO |#)

;; =============================================================================
;; DISPLAYING BINDINGS

(define (format-var var)
  ;; Returns a symbol representation of a variable.
  (if (eqv? (cdr var) 0)
      (car var)
      (string->symbol (string-append
                       (symbol->string (car var))
                       (number->string (cdr var))))))

(define (subst-var var bindings)
  ;; Returns the value corresponding to the given variable in the bindings,
  ;; recusively substituting any variable in that value for their own values. If
  ;; there is no value binding, a representation of the last variable in the
  ;; path is returned.
  (define pair (assoc var bindings))
  (cond ((not pair)            (format-var var))
        ((svar? (cdr pair))    (subst-var (cdr pair)  bindings))
        (else                  (subst-vars (cadr pair) (cddr pair) bindings))))

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
       db (predicate `head)
      (lambda (clauses) (append clauses (list (cons `head `body)))) '()))))

(define-syntax !!
  ;; Macro rule for unification. Pass two terms to unify.
  (syntax-rules ()
    ((_ c1 c2)
     (let ((bindings (unify (cons `c1 0) (cons `c2 0) '())))
       (if (not bindings) #f
           (extract-top-vars bindings))))))

(define (search-loop bindings)
  (if bindings (begin
                 (display (extract-top-vars bindings))
                 (read-line)
                 (search-loop
                  '()
                  #| TODO: Replace arg to continue search based on continue-info |#))
      #f))

(define-syntax ?-
  ;; Macro rule for querying. Pass one or more goals.
  (syntax-rules ()
    ((_ . goals0)
     (let* ((_              (read-char)) ;; swallow first newline
            (goals          `goals0)
            (scoped-goals   (map (lambda (x) (cons x 0)) goals))
            (rules          (rules-for (car goals)))
            (bindings       (satisfy #| TODO |# '())))
       (if (not bindings) #f
           (search-loop bindings))))))

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
