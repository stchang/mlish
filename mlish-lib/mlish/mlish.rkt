#lang turnstile/base

;; ML-like language, extends stlc core langs with:
;; - top level recursive functions
;; - user-definable algebraic datatypes
;; - pattern matching
;; - (local) type inference

(extends turnstile/examples/optimize/ext-stlc
         #:except define #%app λ let let* letrec)
(reuse inst
       #:from turnstile/examples/optimize/sysf)
(reuse × tup proj define-type-alias
       #:from turnstile/examples/optimize/stlc+rec-iso)
(reuse Ref ref deref :=
       #:from turnstile/examples/optimize/stlc+box)
(reuse List member length reverse list-ref cons nil isnil head tail list
       #:from turnstile/examples/optimize/stlc+cons)

(provide
 define match λ define-type define-types let let* letrec cond when unless set!
 #%brackets (rename-out [mlish:#%app #%app] [tc-top #%top])
 Channel make-channel
 Thread
 Vector vector make-vector
 Sequence in-range in-naturals in-lines
 for for* for/list for/vector for*/vector for*/list for/fold for/hash for/sum
 Hash hash hash-ref
 (rename-out [proj get]) rec ×× ; records from stlc+reco+var
 String-Port Input-Port read write-string printf format
 string-length string-copy! number->string string-append
 quotient+remainder
 provide-type (rename-out [mlish-provide provide]) require-typed only-in
 Regexp
 (typed-out/unsafe  [max : (→ Int Int Int)]
                    [min : (→ Int Int Int)]
                    [<= : (→ Int Int Bool)]
                    [>= : (→ Int Int Bool)]
                    [< : (→ Int Int Bool)]
                    [> : (→ Int Int Bool)]
                    [modulo : (→ Int Int Int)]
                    [abs : (→ Int Int)]
                    [even? : (→ Int Bool)]
                    [odd? : (→ Int Bool)]
                    [random : (→ Int Int)]
                    [integer->char : (→ Int Char)]
                    [string->list : (→ String (stlc+cons:List Char))]
                    [string->number : (→ String Int)]
                    [string : (→ Char String)]
                    [sleep : (→ Int Unit)]
                    [string=? : (→ String String Bool)]
                    [string<? : (→ String String Bool)]
                    [string>? : (→ String String Bool)]
                    [string<=? : (→ String String Bool)]
                    [string>=? : (→ String String Bool)]
                    [char=? : (→ Char Char Bool)]
                    [newline : (→ Unit)]
                    [open-output-string : (→ String-Port)]
                    [get-output-string : (→ String-Port String)]
                    [string-upcase : (→ String String)]
                    [make-string : (→ Int String)]
                    [string-set! : (→ String Int Char Unit)]
                    [string-ref : (→ String Int Char)]
                    [fl+ : (→ Float Float Float)]
                    [fl- : (→ Float Float Float)]
                    [fl* : (→ Float Float Float)]
                    [fl/ : (→ Float Float Float)]
                    [fl= : (→ Float Float Bool)]
                    [flsqrt : (→ Float Float)]
                    [flceiling : (→ Float Float)]
                    [inexact->exact : (→ Float Int)]
                    [exact->inexact : (→ Int Float)]
                    [char->integer : (→ Char Int)]
                    [real->decimal-string : (→ Float Int String)]
                    [fx->fl : (→ Int Float)]
                    [quotient : (→ Int Int Int)]
                    [regexp-match : (→ Regexp String (stlc+cons:List String))]
                    [regexp : (→ String Regexp)]
                    [channel-get : (∀ (X) (→ (Channel X) X))]
                    [channel-put : (∀ (X) (→ (Channel X) X Unit))]
                    [thread : (∀ (X) (→ (→ X) Thread))]
                    [vector-length : (∀ (X) (→ (Vector X) Int))]
                    [vector-ref : (∀ (X) (→ (Vector X) Int X))]
                    [vector-set! : (∀ (X) (→ (Vector X) Int X Unit))]
                    [vector-copy! : (∀ (X) (→ (Vector X) Int (Vector X) Unit))]
                    [in-vector : (∀ (X) (→ (Vector X) (Sequence X)))]
                    [in-list : (∀ (X) (→ (stlc+cons:List X) (Sequence X)))]
                    [display : (∀ (X) (→ X Unit))]
                    [displayln : (∀ (X) (→ X Unit))]
                    [list->vector : (∀ (X) (→ (stlc+cons:List X) (Vector X)))]
                    [in-hash : (∀ (K V) (→ (Hash K V) (Sequence (stlc+rec-iso:× K V))))]
                    [hash-set! : (∀ (K V) (→ (Hash K V) K V Unit))]
                    [hash-has-key? : (∀ (K V) (→ (Hash K V) K Bool))]
                    [hash-count : (∀ (K V) (→ (Hash K V) Int))]
                    [equal? : (∀ (X) (→ X X Bool))])
 (for-syntax make-extra-info-transformer)
 →/test ?Λ ?∀ (for-syntax ~?∀ ~List List? ×? ~×) ⊔
 unquote ; for tuple matching, TODO: update reader to get better err msg
 ;; to show user ability to extend the type system, see fasta.mlish
 (for-syntax ~seq ... x+τ))

(require
 (postfix-in - racket/fixnum)
 (postfix-in - racket/flonum)
 (only-in racket/match [match match-])
 (for-syntax racket/set racket/string
             macrotypes/type-constraints macrotypes/variance-constraints)
 (for-meta 2 racket/base)

 (only-in turnstile/examples/optimize/sysf ~∀ ∀ ∀? mk-∀- Λ)
 (only-in turnstile/examples/optimize/stlc+rec-iso ~× ×?)
 (only-in turnstile/examples/optimize/stlc+cons ~List List? mk-List-)
 (only-in turnstile/examples/optimize/stlc+reco+var tup proj × mk-×-))

;; creating possibly polymorphic types
;; ?∀ only wraps a type in a forall if there's at least one type variable
(define-syntax ?∀
  (lambda (stx)
    (syntax-case stx ()
      [(?∀ () body)
       #'body]
      [(?∀ (X ...) body)
       #'(∀ (X ...) body)])))

;; ?Λ only wraps an expression in a Λ if there's at least one type variable
(define-syntax ?Λ
  (lambda (stx)
    (syntax-case stx ()
      [(?Λ () body)
       #'body]
      [(?Λ (X ...) body)
       #'(Λ (X ...) body)])))

;; some syntax classes to help with brackets
(begin-for-syntax
  (define-syntax-class x+τ #:description "type-annotated binder"
    (pattern [(~optional (~literal #%brackets)) x:id (~datum :) τ]
             #:with x+τ #'[x : τ])) ; drop #%brackets
  (define-syntax-class x+e #:description "a let-like binder"
    (pattern [(~optional (~literal #%brackets)) x:id e]
             #:with x+e #'[x e])) ; drop #%brackets
  (define-syntax-class brack
    (pattern [(~optional (~literal #%brackets)) . items])))

(define-syntax ××
  (syntax-parser [(_ b:brack ...) #'(× b.items ...)])) ; record from stlc+reco+var

(define-syntax rec
  (syntax-parser
    [(_ b:brack ...) #'(tup b.items ...)])) ; record from stlc+reco+var

;; literal lists
(define-syntax #%brackets
  (syntax-parser
    [(_) #'stlc+cons:nil]
    [(_ x ((~literal unquote) y) ...) #'(stlc+cons:list x y ...)]))

(begin-for-syntax 
  ;; matching possibly polymorphic types
  (define-syntax ~?∀
    (pattern-expander
     (lambda (stx)
       (syntax-case stx ()
         [(?∀ vars-pat body-pat)
          #'(~or (~∀ vars-pat body-pat)
                 (~and (~not (~∀ _ _))
                       (~parse vars-pat #'())
                       body-pat))]))))

  ;; find-free-Xs : (Stx-Listof Id) Type -> (Listof Id)
  ;; finds the free Xs in the type
  (define (find-free-Xs Xs ty)
    (for/list ([X (in-stx-list Xs)]
               #:when (stx-contains-id? ty X))
      X))

  ;; solve for Xs by unifying quantified fn type with the concrete types of stx's args
  ;;   stx = the application stx = (#%app e_fn e_arg ...)
  ;;   tyXs = input and output types from fn type
  ;;          ie (typeof e_fn) = (-> . tyXs)
  ;; It infers the types of arguments from left-to-right,
  ;; and it expands and returns all of the arguments.
  ;; It returns list of 3 values if successful, else throws a type error
  ;;  - a list of all the arguments, expanded
  ;;  - a list of all the type variables
  ;;  - the constraints for substituting the types
  (define (solve Xs tyXs stx)
    (syntax-parse tyXs
      [(τ_inX ... τ_outX)
       ;; generate initial constraints with expected type and τ_outX
       #:with (~?∀ Vs expected-ty)
              (and (get-expected-type stx)
                   ((current-type-eval) (get-expected-type stx)))
       (define initial-cs
         (if (and (syntax-e #'expected-ty) (stx-null? #'Vs))
             (add-constraints Xs '() (list (list #'expected-ty #'τ_outX)))
             '()))
       (syntax-parse stx
         [(_ e_fn . args)
          (define-values (as- cs)
              (for/fold ([as- null] [cs initial-cs])
                        ([a (in-stx-list #'args)]
                         [tyXin (in-stx-list #'(τ_inX ...))])
                (define ty_in (inst-type/cs/orig Xs cs tyXin datum=?))
                (define/with-syntax [a- ty_a]
                  (infer+erase (if (null? (find-free-Xs Xs ty_in))
                                   (add-expected-type a ty_in)
                                   a)))
                (values
                 (cons #'a- as-)
                 (add-constraints Xs cs (list (list ty_in #'ty_a))
                                  (list (list (inst-type/cs/orig
                                               Xs cs ty_in
                                               datum=?)
                                              #'ty_a))))))

         (list (reverse as-) Xs cs)])]))

  (define (mk-app-poly-infer-error stx expected-tys given-tys e_fn)
    (format (string-append
             "Could not infer instantiation of polymorphic function ~s.\n"
             "  expected: ~a\n"
             "  given:    ~a")
            (syntax->datum (get-orig e_fn))
            (string-join (stx-map type->str expected-tys) ", ")
            (string-join (stx-map type->str given-tys) ", ")))

  ;; covariant-Xs? : Type -> Bool
  ;; Takes a possibly polymorphic type, and returns true if all of the
  ;; type variables are in covariant positions within the type, false
  ;; otherwise.
  (define (covariant-Xs? ty)
    (syntax-parse ((current-type-eval) ty)
      [(~?∀ Xs ty)
       (for/and ([X (in-stx-list #'Xs)])
         (covariant-X? X #'ty))]))

  ;; find-X-variance : Id Type [Variance] -> Variance
  ;; Returns the variance of X within the type ty
  (define (find-X-variance X ty [ctxt-variance covariant])
    (car (find-variances (list X) ty ctxt-variance)))

  ;; covariant-X? : Id Type -> Bool
  ;; Returns true if every place X appears in ty is a covariant position, false otherwise.
  (define (covariant-X? X ty)
    (variance-covariant? (find-X-variance X ty covariant)))

  ;; contravariant-X? : Id Type -> Bool
  ;; Returns true if every place X appears in ty is a contravariant position, false otherwise.
  (define (contravariant-X? X ty)
    (variance-contravariant? (find-X-variance X ty covariant)))

  ;; find-variances : (Listof Id) Type [Variance] -> (Listof Variance)
  ;; Returns the variances of each of the Xs within the type ty,
  ;; where it's already within a context represented by ctxt-variance.
  (define (find-variances Xs ty [ctxt-variance covariant])
    (syntax-parse ty
      [A:id
       (for/list ([X (in-list Xs)])
         (cond [(free-identifier=? X #'A) ctxt-variance]
               [else irrelevant]))]
      [(~Any tycons)
       (stx-map (λ _ irrelevant) Xs)]
      [(~?∀ () (~Any tycons τ ...))
       #:when (get-arg-variances #'tycons)
       #:when (stx-length=? #'[τ ...] (get-arg-variances #'tycons))
       (define τ-ctxt-variances
         (for/list ([arg-variance (in-list (get-arg-variances #'tycons))])
           (variance-compose ctxt-variance arg-variance)))
       (for/fold ([acc (stx-map (λ _ irrelevant) Xs)])
                 ([τ (in-stx-list #'[τ ...])]
                  [τ-ctxt-variance (in-list τ-ctxt-variances)])
         (map variance-join
              acc
              (find-variances Xs τ τ-ctxt-variance)))]
      [ty
       #:when (not (for/or ([X (in-list Xs)])
                     (stx-contains-id? #'ty X)))
       (stx-map (λ _ irrelevant) Xs)]
      [_ (stx-map (λ _ invariant) Xs)]))

  ;; find-variances/exprs : (Listof Id) Type [Variance-Expr] -> (Listof Variance-Expr)
  ;; Like find-variances, but works with Variance-Exprs instead of
  ;; concrete variance values.
  (define (find-variances/exprs Xs ty [ctxt-variance covariant])
    (syntax-parse ty
      [A:id
       (for/list ([X (in-list Xs)])
         (cond [(free-identifier=? X #'A) ctxt-variance]
               [else irrelevant]))]
      [(~Any tycons)
       (stx-map (λ _ irrelevant) Xs)]
      [(~?∀ () (~Any tycons τ ...))
       #:when (get-arg-variances #'tycons)
       #:when (stx-length=? #'[τ ...] (get-arg-variances #'tycons))
       (define τ-ctxt-variances
         (for/list ([arg-variance (in-list (get-arg-variances #'tycons))])
           (variance-compose/expr ctxt-variance arg-variance)))
       (for/fold ([acc (stx-map (λ _ irrelevant) Xs)])
                 ([τ (in-list (syntax->list #'[τ ...]))]
                  [τ-ctxt-variance (in-list τ-ctxt-variances)])
         (map variance-join/expr
              acc
              (find-variances/exprs Xs τ τ-ctxt-variance)))]
      [ty
       #:when (not (for/or ([X (in-list Xs)])
                     (stx-contains-id? #'ty X)))
       (stx-map (λ _ irrelevant) Xs)]
      [_ (stx-map (λ _ invariant) Xs)]))

  ;; current-variance-constraints : (U False (Mutable-Setof Variance-Constraint))
  ;; If this is false, that means that infer-variances should return concrete Variance values.
  ;; If it's a mutable set, that means that infer-variances should mutate it and return false,
  ;; and type constructors should return the list of variance vars.
  (define current-variance-constraints (make-parameter #false))

  ;; infer-variances :
  ;; ((-> Stx) -> Stx) (Listof Variance-Var) (Listof Id) (Listof Type-Stx)
  ;; -> (U False (Listof Variance))
  (define (infer-variances with-variance-vars-okay variance-vars Xs τs)
    (cond
      [(current-variance-constraints)
       (define variance-constraints (current-variance-constraints))
       (define variance-exprs
         (for/fold ([exprs (stx-map (λ _ irrelevant) variance-vars)])
                   ([τ (in-list τs)])
           (define/syntax-parse (~?∀ Xs* τ*)
             ;; This can mutate variance-constraints!
             ;; This avoids causing an infinite loop by having the type
             ;; constructors provide with-variance-vars-okay so that within
             ;; this call they declare variance-vars for their variances.
             (with-variance-vars-okay
              (λ () ((current-type-eval) #`(∀ #,Xs #,τ)))))
           (map variance-join/expr
                exprs
                (find-variances/exprs (syntax->list #'Xs*) #'τ* covariant))))
       (for ([var (in-list variance-vars)]
             [expr (in-list variance-exprs)])
         (set-add! variance-constraints (variance= var expr)))
       #f]
      [else
       (define variance-constraints (mutable-set))
       ;; This will mutate variance-constraints!
       (parameterize ([current-variance-constraints variance-constraints])
         (infer-variances with-variance-vars-okay variance-vars Xs τs))
       (define mapping
         (solve-variance-constraints variance-vars
                                     (set->list variance-constraints)
                                     (variance-mapping)))
       (for/list ([var (in-list variance-vars)])
         (variance-mapping-ref mapping var))]))

  ;; make-arg-variances-proc :
  ;; (Listof Variance-Var) (Listof Id) (Listof Type-Stx) -> (Stx -> (U (Listof Variance)
  ;;                                                                   (Listof Variance-Var)))
  (define (make-arg-variances-proc arg-variance-vars Xs τs)
    ;; variance-vars-okay? : (Parameterof Boolean)
    ;; A parameter that determines whether or not it's okay for
    ;; this type constructor to return a list of Variance-Vars
    ;; for the variances.
    (define variance-vars-okay? (make-parameter #false))
    ;; with-variance-vars-okay : (-> A) -> A
    (define (with-variance-vars-okay f)
      (parameterize ([variance-vars-okay? #true])
        (f)))
    ;; arg-variances : (Boxof (U False (List Variance ...)))
    ;; If false, means that the arg variances have not been
    ;; computed yet. Otherwise, stores the complete computed
    ;; variances for the arguments to this type constructor.
    (define arg-variances (box #f))
    ;; arg-variances-proc : Stx -> (U (Listof Variance) (Listof Variance-Var))
    (define (arg-variance-proc stx)
      (or (unbox arg-variances)
          (cond
            [(variance-vars-okay?)
             arg-variance-vars]
            [else
             (define inferred-variances
               (infer-variances
                with-variance-vars-okay
                arg-variance-vars
                Xs
                τs))
             (cond [inferred-variances
                    (set-box! arg-variances inferred-variances)
                    inferred-variances]
                   [else
                    arg-variance-vars])])))
    arg-variance-proc)

  ;; compute unbound tyvars in one unexpanded type ty
  (define (compute-tyvar1 ty)
    (syntax-parse ty
      [X:id #'(X)]
      [() #'()]
      [(C t ...) (stx-appendmap compute-tyvar1 #'(t ...))]))
  ;; computes unbound ids in (unexpanded) tys, to be used as tyvars
  (define (compute-tyvars tys)
    (define Xs (stx-appendmap compute-tyvar1 tys))
    (filter 
     (lambda (X) 
       (with-handlers
        ([exn:fail:syntax:unbound? (lambda (e) #t)]
         [exn:fail:type:infer? (lambda (e) #t)])
        (let ([X+ ((current-type-eval) X)])
          (not (type? X+)))))
     (stx-remove-dups Xs))))

;; define --------------------------------------------------
;; for function defs, define infers type variables
;; - since the order of the inferred type variables depends on expansion order,
;;   which is not known to programmers, to make the result slightly more
;;   intuitive, we arbitrarily sort the inferred tyvars lexicographically
(define-typed-syntax define
  [(_ x:id e) ≫
   [⊢ e ≫ e- ⇒ τ]
   #:with x- (generate-temporary)
   --------
   [≻ (begin-
        (define-typed-variable-rename x ≫ x- : τ)
        (define- x- e-))]]
  ; explicit "forall"
  [(_ Ys (f:id :x+τ ... (~or (~datum ->) (~datum →)) τ_out) e_body ... e) ≫
   #:when (brace? #'Ys)
   ;; TODO; remove this code duplication
   #:with f- (add-orig (generate-temporary #'f) #'f)
   #:with e_ann (syntax/loc #'e (add-expected e τ_out))
   #:with (τ+orig ...) (stx-map (λ (t) (add-orig t t)) #'(τ ... τ_out))
   #:with (~and ty_fn_expected (~?∀ _ (~→ _ ... out_expected)))
          (set-stx-prop/preserved
            ((current-type-eval) #'(?∀ Ys (ext-stlc:→ τ+orig ...)))
            'orig
            (list #'(→ τ+orig ...)))
   --------
   [≻ (begin-
        (define-typed-variable-rename f ≫ f- : ty_fn_expected)
        (define- f-
          (Λ Ys (ext-stlc:λ ([x : τ] ...) (ext-stlc:begin e_body ... e_ann)))))]]
  ;; alternate type sig syntax, after parameter names
  [(_ (f:id x:id ...) (~datum :) ty ... (~or (~datum ->) (~datum →)) ty_out . b) ≫
   --------
   [≻ (define (f [x : ty] ... -> ty_out) . b)]]
  [(_ (f:id :x+τ ... (~or (~datum ->) (~datum →)) τ_out)
     e_body ... e) ≫
   #:with (Y ...) (compute-tyvars #'(τ ... τ_out))
   ---------------
   [≻ (define {Y ...} (f [x : τ] ... -> τ_out) e_body ... e)]])

;; define-type -----------------------------------------------

(define-for-syntax (make-type-constructor-transformer
                     name           ; Name of type constructor we're defining
                     internal-name  ; Identifier used for internal rep of type
                    op             ; numeric operator to compare expected arg count
                     n              ; Expected arity, relative to op
                    )
  (define/syntax-parse τ- internal-name)
  (syntax-parser
    [(_ . args)
     #:fail-unless (op (stx-length #'args) n)
     (format
       "wrong number of arguments, expected ~a ~a"
       (object-name op) n)
     #:with (arg- ...) (expands/stop #'args #:stop-list? #f)
     ;; args are validated on the next line rather than above
     ;; to ensure enough stx-parse progress for proper err msg,
     ;; ie, "invalid type" instead of "improper tycon usage"
     #:with (~! _:type ...) #'(arg- ...)
     (add-orig (mk-type (syntax/loc this-syntax (#%plain-app- τ- arg- ...))) this-syntax)]
    [_ ;; else fail with err msg
      (type-error #:src this-syntax
                  #:msg
                  (string-append
                    "Improper usage of type constructor ~a: ~a, expected ~a ~a arguments")
                  #`#,name this-syntax #`#,(object-name op) #`#,n)]))


(begin-for-syntax
  (define-syntax-class constructor
    (pattern
      ;; constructors must have the form (Cons τ ...)
      ;; but the first ~or clause accepts 0-arg constructors as ids;
      ;; the ~and is a workaround to bind the duplicate Cons ids (see Ryan's email)
      (~and C (~or
                ; Nullary constructor, without parens. Like `Nil`.
                ; Ensure fld, τ are bound though empty.
                (~and IdCons:id
                      (~parse (Cons [fld (~datum :) τ] ...) #'(IdCons)))
                ; With named fields
                (~and ((~optional (~literal #%brackets)) Cons f:x+τ ...)
                      (~parse ([fld τ] ...) #'([f.x f.τ] ...)))
                ; Fields not named; generate internal names
                (~and [(~optional (~literal #%brackets)) Cons τ ...]
                      (~parse (fld ...) (generate-temporaries #'(τ ...)))))))))

;; defines a set of mutually recursive datatypes
(define-syntax (define-types stx)
  (syntax-parse stx
    [(_ [(~optional (~literal #%brackets)) (Name:id X:id ...)
         c:constructor ...]
        ...)
     ;; validate tys
     #:with ((ty_flat ...) ...) (stx-map (λ (tss) (stx-flatten tss)) #'(((c.τ ...) ...) ...))
     #:with ((_ _ (_ _ (_ _ (_ _ ty+ ...)))) ...)
            (stx-map expand/df
              #`((lambda (X ...)
                   (let-syntax
                       ([X (make-rename-transformer (mk-type #'X))] ...
                        ; Temporary binding of the type we are now defining,
                        ; so that we can expand the types of constructor arguments
                        ; that refer to it. This binding is the reason we can't use infer
                        ; here; infer is specifically about attaching types, not binding
                        ; general transformers.
                        [Name
                         (make-type-constructor-transformer
                           #'Name #'void = (stx-length #'(X ...)))] ...)
                     (void ty_flat ...))) ...))
     #:when (stx-map
             (λ (ts+ ts)
               (stx-map
                (lambda (t+ t) (unless (type? t+)
                                 (type-error #:src t
                                             #:msg "~a is not a valid type" t)))
                ts+ ts))
             #'((ty+ ...) ...) #'((ty_flat ...) ...))
     #:with (NameExtraInfo ...) (stx-map (λ (n) (format-id n "~a-extra-info" n)) #'(Name ...))
     #:with (n ...) (stx-map (λ (Xs) #`#,(stx-length Xs)) #'((X ...) ...))
     #:with (arg-variance-vars ...) (generate-temporaries #'(Name ...))
     #:with (arg-var-fn ...) (generate-temporaries #'(Name ...))
     #`(begin-
         (begin-for-syntax
           ;; arg-variance-vars : (List Variance-Var ...)
           (define arg-variance-vars
             (list (variance-var (syntax-e (generate-temporary 'X))) ...)) ...
           (define arg-var-fn
             (make-arg-variances-proc arg-variance-vars
                                      (list #'X ...)
                                      (list #'c.τ ... ...))) ...)
         (define-type-constructor Name
           #:arity = n
           #:arg-variances arg-var-fn
           #:extra-info 'NameExtraInfo) ...
         (define-type-rest (Name X ...) c.C ...) ...
         )]))

;; defines the runtime components of a define-datatype
(define-syntax (define-type-rest stx)
  (syntax-parse stx
    [(_ (Name:id X:id ...)
        c:constructor ...)
     #:with Name? (mk-? #'Name)
     #:with NameExtraInfo (format-id #'Name "~a-extra-info" #'Name)
     #:with (StructName ...) (generate-temporaries #'(c.Cons ...))
     #:with ((exposed-acc ...) ...)
            (stx-map 
             (λ (C fs) (stx-map (λ (f) (format-id C "~a-~a" C f)) fs))
             #'(c.Cons ...) #'((c.fld ...) ...))
     #:with ((acc ...) ...)
            (stx-map
             (λ (S fs) (stx-map (λ (f) (format-id S "~a-~a" S f)) fs))
             #'(StructName ...) #'((c.fld ...) ...))
     #:with (Cons? ...) (stx-map mk-? #'(StructName ...))
     #:with (exposed-Cons? ...) (stx-map mk-? #'(c.Cons ...))
     #`(begin-
         (define-syntax NameExtraInfo
           (make-extra-info-transformer
            #'(X ...)
            #'(#%plain-app- (#%plain-app- 'c.Cons 'StructName Cons? [#%plain-app- acc c.τ] ...) ...)))
         (struct- StructName (c.fld ...) #:reflection-name 'c.Cons #:transparent) ...
         (define-syntax exposed-acc ; accessor for records
           (make-variable-like-transformer
             (assign-type #'acc #'(?∀ (X ...) (ext-stlc:→ (Name X ...) c.τ)))))
         ... ...
         (define-syntax exposed-Cons? ; predicates for each variant
           (make-variable-like-transformer
             (assign-type #'Cons? #'(?∀ (X ...) (ext-stlc:→ (Name X ...) Bool))))) ...
         (define-syntax c.Cons
           (make-constructor-transformer #'((X ...) (c.τ ...) Name StructName)))
         ...)]))

;; defines a single datatype; dispatches to define-types
(define-syntax (define-type stx)
  (syntax-parse stx
    [(_ Name:id . rst)
     #:with NewName (generate-temporary #'Name)
     #:with Name2 (add-orig #'(NewName) #'Name)
     #`(begin-
         (define-type Name2 . #,(subst #'Name2 #'Name #'rst))
         (stlc+rec-iso:define-type-alias Name Name2))]
    [(_ Name . Cs) #'(define-types [Name . Cs])]))

(begin-for-syntax
  (define (make-extra-info-transformer Xs stuff)
    (syntax-parser
      [(_ Y ...)
       (substs #'(Y ...) Xs stuff)]))

  (define make-constructor-transformer
    (syntax-parser
      [((X ...) (τ ...) Name StructName)
       #:with fn-ty-body #'(ext-stlc:→ τ ... (Name X ...))
       #:with fn-ty #'(?∀ (X ...) fn-ty-body)
       #:with StructName/ty (assign-type #'StructName #'fn-ty)
       ;; stx/loc transfers expected-type (mlish:#%app needs for inference)
    (lambda (stx)
      (syntax-parse/typecheck stx
         [C:id ≫ #:when (stx-null? #'(τ ...)) ; id, as unary constructor applied w/o parens
          --------
          [≻ #,(syntax/loc this-syntax (C))]]
         [_:id ≫
          ----
          [≻ StructName/ty]]             ; id, as HO fn
         [(C τs . args) ≫ ; explicit instantiation
          #:when (brace? #'τs) ; commit to this clause
          #:with fn-ty-inst (inst-type #'τs #'(X ...) #'fn-ty-body)
          #:with StructName/inst/orig (add-orig (assign-type #'StructName #'fn-ty-inst) #'C)
          -----------------
          [≻ #,(syntax/loc this-syntax (mlish:#%app StructName/inst/orig . args))]]
         [(C . args) ≫   ; no explicit instantiation, defer inference to mlish:#%app
          #:with StructName/orig (add-orig #'StructName/ty #'C)
          ---------------
          [≻ #,(syntax/loc this-syntax (mlish:#%app StructName/orig . args))]]))])))


;; match --------------------------------------------------
(define-syntax unquote
  (syntax-parser
    [_ (raise-syntax-error 'comma
                           "can't be used outside list literal or match pattern"
                           this-syntax)]))

;; helper stx classes for match
(begin-for-syntax
  ;; matching tuples --------------------
  (define-splicing-syntax-class tup-match-pat
    #:description "tuple match pattern"
    #:literals (unquote) #:attributes ([x 1])
    (pattern (x0 (unquote x1) ...) #:with (x ...) #'(x0 x1 ...)    )
    (pattern (~seq x0 (unquote x1) ...) #:with (x ...) #'(x0 x1 ...))
    (pattern pat
             #:and (~fail
                    (format
                     "Invalid pattern for tuple type (maybe missing commas?): ~a"
                     (stx->datum #'pat)))
             #:with (x ...) #'()))

  (define-syntax-class (tup-match-clauses τ_e)
    #:description "tuple match clauses"
    #:auto-nested-attributes ; inherit (x ...) attrs from tup-match-pat
    ;; #:attributes: ([x 1] body) (commented bc using auto-nested-attrs)
    #:datum-literals (->) #:literals (#%brackets)
    (pattern ([(~optional #%brackets) :tup-match-pat -> body]) ; only 1 clause
             #:with (~× ty0 ...) τ_e
             #:fail-unless (stx-length=? #'(ty0 ...) #'(x ...))
             (format "match tuple pattern does not match type ~a"
                     (type->str τ_e))))

  (define-template-metafunction $mk-tup-match-term
    (syntax-parser
      [(_ e- (x- ...) body-)
       #:with z (generate-temporary)
       #:with (acc ...)
              (for/list ([i (stx-length #'(x- ...))])
                #`(#%plain-lambda- (s) (#%plain-app- list-ref- s '#,i)))
       #`(let-values- ([(z) e-])
           (let-values- ([(x-) (#%plain-app- acc z)] ...) body-))]))

  ;; matching lists --------------------
  (define-splicing-syntax-class lst-match-pat
    #:description "list match pattern"
    #:attributes ([x 1] xs rst)
    (pattern (~and xs [(~optional (~literal #%brackets)) x ...])
             #:with rst (generate-temporary))
    (pattern (~seq (~seq x (~datum ::)) ... rst:id)
             #:with xs #'()))

  (define-syntax-class lst-match-clauses #:description "list match clauses"
    #:auto-nested-attributes ; inherit x, xs, rst attrs from lst-match-pat
    ;; #:attributes ([x 2] [xs 1] [rst 1] [body 1]) (commented bc using auto-nested-attrs)
    #:datum-literals (->) #:literals (#%brackets)
    (pattern ([(~optional #%brackets) :lst-match-pat -> body] ...)
             #:fail-unless (stx-ormap
                            (λ (xx) (or (and (brack? xx) (= 1 (stx-length xx)))
                                        (zero? (stx-length xx))))
                            #'(xs ...))
                           "match: missing empty list case"
             #:fail-unless (not (and (stx-andmap brack? #'(xs ...))
                                     (= 1 (stx-length #'(xs ...)))))
             "match: missing non-empty list case"))

  (define-template-metafunction $mk-lst-match-term
    (syntax-parser
      [(_ e- (xs ...) ((x- ...) ...) (rst- ...) (body- ...))
       #:with z (generate-temporary)
       #:with ((pred? (acc1 ...) acc2) ...)
       (for/list ([xs (in-stx-list #'(xs ...))] ; wrong len bc of #%brackets
                  [xs- (in-stx-list #'((x- ...) ...))])
         (define len (stx-length xs-))
         (define op (if (brack? xs) #'=- #'>=-))
         (list
          #`(#%plain-lambda- (lst)   ; pred?
              (#%plain-app- #,op (#%plain-app- length- lst) '#,len))
          (for/list ([i len])        ; (acc1 ...)
            #`(#%plain-lambda- (lst)
                (#%plain-app- list-ref- lst '#,i)))
          #`(#%plain-lambda- (lst)   ; acc2
              (#%plain-app- list-tail- lst '#,len))))
       #`(let-values- ([(z) e-])
           (cond-
            [(#%plain-app- pred? z)
             (let-values- ([(x-) (#%plain-app- acc1 z)] ...
                           [(rst-) (#%plain-app- acc2 z)])
               body-)] ...))]))

  ;; matching user-defined datatpyes (variants) --------------------
  (define-splicing-syntax-class var-match-pat
    #:description "datatype match pattern"
    #:attributes (Clause [x 1] guard)
    (pattern (~seq Clause:id x:id ...
                   (~optional (~seq #:when guard)
                     #:defaults ([guard #'(ext-stlc:#%datum . #t)])))))

  (define-syntax-class (var-match-clauses τ_e) #:description "datatype match clauses"
    #:auto-nested-attributes ; inherits Clause (x ...) guard from var-match-pat
    ;; #:attributes ([x 2] [guard 1] [body 1] [Cons? 1] [acc 2] [τ 2]) (commented bc using auto-nested-attrs)
    #:datum-literals (->) #:literals (#%brackets)
    ; # of clauses may be > len #'info, due to guards
    (pattern ([(~optional #%brackets) :var-match-pat -> body] ...)
             #:with info-body (get-extra-info τ_e) ; TODO: check #f?
             #:with (_ (_ (_ ConsAll) . _) ...) #'info-body
             #:do[(define Clause-symbs (syntax->datum #'(Clause ...)))]
             #:fail-unless (set=? Clause-symbs (syntax->datum #'(ConsAll ...)))
             (type-error #:src #'match-expr
                         #:msg (string-append
                                "match: clauses not exhaustive; missing: "
                                (string-join
                                 (map symbol->string
                                      (set-subtract
                                       (syntax->datum #'(ConsAll ...))
                                       Clause-symbs))
                                 ", ")))
             #:with ((_ _ _ Cons? [_ acc τ] ...) ...)
                    (map ; ok to compare symbols bc clause names can't be rebound
                     (λ (Cl)
                       (stx-findf
                        (syntax-parser
                          [(_ 'C . _) (equal? Cl (syntax->datum #'C))])
                        (stx-cdr #'info-body))) ; drop leading #%app
                     Clause-symbs)))

  (define-template-metafunction $mk-var-match-term
    (syntax-parser
      [(_ e- (Cons? ...) ((acc ...) ...) ((x- ...) ...) (guard- ...) (body- ...))
       #:with z (generate-temporary) ; dont duplicate eval of test expr
       #'(let-values- ([(z) e-])
           (cond-
            [(and- (#%plain-app- Cons? z)
                   (let-values- ([(x-) (#%plain-app- acc z)] ...) guard-))
             (let-values- ([(x-) (#%plain-app- acc z)] ...) body-)] ...))])))

(define-typed-syntax match #:datum-literals (with)
  [(_ e with c ...+) ⇐ τ_expected ≫
   [⊢ e ≫ e- ⇒ τ_e]
   [⊢ (match/ty/expected τ_e e- c ...) ≫ m- ⇐ τ_expected]
   ------
   [⊢ m-]]
  [(_ e with c ...+) ≫
   [⊢ e ≫ e- ⇒ τ_e]
   ------
   [≻ (match/ty τ_e e- c ...)]])

(define-typed-syntax match/ty/expected
  ;; e is a tuple --------------------
  [(_ (~and (~× ty ...) τ_e) ~! e- . (~var || (tup-match-clauses #'τ_e))) ⇐ τ_expected ≫
   [[x ≫ x- : ty] ... ⊢ body ≫ body- ⇐ τ_expected]
   --------
   [⊢ ($mk-tup-match-term e- (x- ...) body-)]]
  ;; e is a list --------------------
  [(_ (~and (~List ty) τ_e) ~! e- . :lst-match-clauses) ⇐ τ_expected ≫
   [[x ≫ x- : ty] ... [rst ≫ rst- : τ_e] ⊢ body ≫ body- ⇐ τ_expected] ...
   --------
   [⊢ ($mk-lst-match-term e- (xs ...) ((x- ...) ...) (rst- ...) (body- ...))]]
  ;; e is a variant --------------------
  [(_ τ_e ~! e- . (~var || (var-match-clauses #'τ_e))) ⇐ τ_expected ≫
   [[x ≫ x- : τ] ... ⊢ [guard ≫ guard- ⇐ Bool] [body ≫ body- ⇐ τ_expected]] ...
   --------
   [⊢ ($mk-var-match-term
       e- (Cons? ...) ((acc ...) ...) ((x- ...) ...) (guard- ...) (body- ...))]])

(define-typed-syntax match/ty ; no expected type
  ;; e is a tuple --------------------
  [(_ (~and (~× ty ...) τ_e) ~! e- . (~var || (tup-match-clauses #'τ_e))) ≫
   [[x ≫ x- : ty] ... ⊢ body ≫ body- ⇒ τ_body]
   --------
   [⊢ ($mk-tup-match-term e- (x- ...) body-) ⇒ τ_body]]
  ;; e is a list --------------------
  [(_ (~and (~List ty) τ_e) ~! e- . :lst-match-clauses) ≫
   [[x ≫ x- : ty] ... [rst ≫ rst- : τ_e] ⊢ body ≫ body- ⇒ τ_body] ...
   --------
   [⊢ ($mk-lst-match-term e- (xs ...) ((x- ...) ...) (rst- ...) (body- ...))
      ⇒ (⊔ τ_body ...)]]
  ;; e is a variant --------------------
  [(_ τ_e ~! e- . (~var || (var-match-clauses #'τ_e))) ≫
   [[x ≫ x- : τ] ... ⊢ [guard ≫ guard- ⇐ Bool] [body ≫ body- ⇒ τ_body]] ...
   --------
   [⊢ ($mk-var-match-term
       e- (Cons? ...) ((acc ...) ...) ((x- ...) ...) (guard- ...) (body- ...))
      ⇒ (⊔ τ_body ...)]])

; special arrow that computes free vars; for use with tests
; (because we can't write explicit forall
(define-syntax →/test 
  (syntax-parser
    [(→/test (~and Xs (X:id ...)) . rst)
     #:when (brace? #'Xs)
     #'(?∀ (X ...) (ext-stlc:→ . rst))]
    [(→/test . rst)
     #:with Xs (compute-tyvars #'rst)
     #'(?∀ Xs (ext-stlc:→ . rst))]))

; all λs have type (?∀ (X ...) (→ τ_in ... τ_out))
(define-typed-syntax λ #:datum-literals (:)
  [(λ (x:id ...) body) ⇐ (~?∀ (X ...) (~→ τ_in ... τ_out)) ≫
   #:fail-unless (stx-length=? #'[x ...] #'[τ_in ...])
   (format "expected a function of ~a arguments, got one with ~a arguments"
           (stx-length #'[τ_in ...]) (stx-length #'[x ...]))
   [([X ≫ _ :: #%type] ...) ([x ≫ x- : τ_in] ...) ⊢ [body ≫ body- ⇐ (ev/m τ_out)]]
   --------
   [⊢ (#%plain-lambda- (x- ...) body-)]]
  [(λ (b:x+τ ...) body) ⇐ (~?∀ (V ...) (~→ τ_in ... τ_out)) ≫
   #:with [X ...] (compute-tyvars #'(b.τ ...))
   #:with ((X- ...) (τ_x-:type ...)) (expands/tvctx #'(b.τ ...) #'(X ...))
;   [[X ≫ X- :: #%type] ... ⊢ [τ_x ≫ τ_x- ⇐ :: #%type] ...]
   [τ_in τ⊑ τ_x- #:for b.x] ...
   ;; TODO is there a way to have λs that refer to ids defined after them?
   [([V ≫ _ :: #%type] ... [X- ≫ _ :: #%type] ...) ([b.x ≫ x- : τ_x-] ...) ⊢ body ≫ body- ⇐ τ_out]
   --------
   [⊢ (#%plain-lambda- (x- ...) body-)]]
  [(λ (b:x+τ ...) body) ≫
   #:with [X ...] (compute-tyvars #'(b.τ ...))
   ;; TODO is there a way to have λs that refer to ids defined after them?
   [([X ≫ X- :: #%type] ...) ([b.x ≫ x- : b.τ] ...) ⊢ body ≫ body- ⇒ τ_body]
   #:with [τ_x* ...] (inst-types/cs #'[X ...] #'([X X-] ...) #'[b.τ ...])
   #:with τ_fn (add-orig #'(?∀ (X- ...) (ext-stlc:→ τ_x* ... τ_body))
                         #`(→ #,@(stx-map get-orig #'[τ_x* ...]) #,(get-orig #'τ_body)))
   --------
   [⊢ (#%plain-lambda- (x- ...) body-) ⇒ τ_fn]])


;; #%app --------------------------------------------------
(define-typed-syntax mlish:#%app
  [(_ e_fn e_arg ...) ≫
   ;; compute fn type (ie ∀ and →)
   [⊢ e_fn ≫ e_fn- ⇒ (~?∀ Xs (~→ . tyX_args))]
   ;; solve for type variables Xs
   #:with [[e_arg- ...] Xs* cs] (solve #'Xs #'tyX_args this-syntax)
   ;; instantiate polymorphic function type
   #:with [τ_in ... τ_out] (inst-types/cs/orig #'Xs* #'cs #'tyX_args datum=?)
   #:with (unsolved-X ...) (find-free-Xs #'Xs* #'τ_out)
   ;; arity check
   #:fail-unless (stx-length=? #'[τ_in ...] #'[e_arg ...])
                 (num-args-fail-msg #'e_fn #'[τ_in ...] #'[e_arg ...])
   ;; compute argument types
   #:with (τ_arg ...) (stx-map typeof #'(e_arg- ...))
   ;; typecheck args
   [τ_arg τ⊑ τ_in #:for e_arg] ...
   #:with τ_out* (if (stx-null? #'(unsolved-X ...))
                     #'τ_out
                     (syntax-parse #'τ_out
                       [(~?∀ (Y ...) τ_out)
                        #:fail-unless (→? #'τ_out)
                        (mk-app-poly-infer-error this-syntax #'(τ_in ...) #'(τ_arg ...) #'e_fn)
                        (for ([X (in-list (syntax->list #'(unsolved-X ...)))])
                          (unless (covariant-X? X #'τ_out)
                            (raise-syntax-error
                             #f
                             (mk-app-poly-infer-error this-syntax #'(τ_in ...) #'(τ_arg ...) #'e_fn)
                             this-syntax)))
                        (mk-∀- #'(unsolved-X ... Y ...) #'(τ_out))]))
   --------
   [⊢ (#%plain-app- e_fn- e_arg- ...) ⇒ τ_out*]])


;; cond and other conditionals
(define-typed-syntax cond
  [(_ [(~optional (~literal #%brackets))
       (~or (~and (~datum else) (~parse test #'(ext-stlc:#%datum . #t)))
               test)
          b ... body] ...+) ⇐ τ_expected ≫
   [⊢ test ≫ test- ⇐ Bool] ...
   [⊢ (ext-stlc:begin b ... body) ≫ body- ⇐ τ_expected] ...
   --------
   [⊢ (cond- [test- body-] ...)]]
  [(_ [(~optional (~literal #%brackets))
       (~or (~and (~datum else) (~parse test #'(ext-stlc:#%datum . #t)))
               test)
          b ... body] ...+) ≫
   [⊢ test ≫ test- ⇐ Bool] ...
   [⊢ (ext-stlc:begin b ... body) ≫ body- ⇒ τ_body] ...
   --------
   [⊢ (cond- [test- body-] ...) ⇒ (⊔ τ_body ...)]])
(define-typed-syntax (when test body ...) ≫
 ----------------
 [≻ #,(syntax/loc this-syntax (cond [test body ... (mlish:#%app void)]))])
(define-typed-syntax (unless test body ...) ≫
 -------
 [≻ #,(syntax/loc this-syntax (cond [test (mlish:#%app void)]
                                    [else body ... (mlish:#%app void)]))])

;; sync channels and threads
(define-type-constructor Channel)

(define-typed-syntax make-channel
  [(make-channel (~and tys {ty:type})) ≫
   #:when (brace? #'tys)
   --------
   [⊢ (#%plain-app- make-channel-) ⇒ : #,(mk-Channel- #'(ty.norm))]])

(define-base-type Thread)

(define-typed-syntax number->string
  [number->string:id ≫
   --------
   [⊢ number->string- ⇒ : #,(mk-→- (list Int+ String+))]]
  [(number->string n) ≫
   --------
   [≻ (number->string n (ext-stlc:#%datum . 10))]]
  [(number->string n rad) ≫
   [⊢ [n ≫ n- ⇐ : #,Int+]]
   [⊢ [rad ≫ rad- ⇐ : #,Int+]]
   --------
   [⊢ (#%plain-app- number->string- n- rad-) ⇒ : #,String+]])

(define-typed-syntax string-append
  [(string-append str ...) ≫
   [⊢ [str ≫ str- ⇐ : #,String+] ...]
   --------
   [⊢ (#%plain-app- string-append- str- ...) ⇒ : #,String+]])

;; vectors
(define-type-constructor Vector)

(define-typed-syntax vector
  [(vector (~and tys {ty:type})) ≫
   #:when (brace? #'tys)
   --------
   [⊢ (#%plain-app- vector-) ⇒ : #,(mk-Vector- #'(ty.norm))]]
  [(vector v ...) ⇐ : (Vector ty) ≫
   [⊢ [v ≫ v- ⇐ : ty] ...]
   --------
   [⊢ (#%plain-app- vector- v- ...)]]
  [(vector v ...) ≫
   [⊢ [v ≫ v- ⇒ : ty] ...]
   #:when (same-types? #'(ty ...))
   #:with one-ty (stx-car #'(ty ...))
   --------
   [⊢ (#%plain-app- vector- v- ...) ⇒ : #,(mk-Vector- #'(one-ty))]])
(define-typed-syntax make-vector
  [(make-vector n) ≫
   --------
   [≻ (make-vector n (ext-stlc:#%datum . 0))]]
  [(make-vector n e) ≫
   [⊢ [n ≫ n- ⇐ : #,Int+]]
   [⊢ [e ≫ e- ⇒ : ty]]
   --------
   [⊢ (#%plain-app- make-vector- n- e-) ⇒ : #,(mk-Vector- #'(ty))]])

;; sequences and for loops

(define-type-constructor Sequence)

(define-typed-syntax in-range
  [(in-range end) ≫
   --------
   [≻ (in-range (ext-stlc:#%datum . 0) end (ext-stlc:#%datum . 1))]]
  [(in-range start end) ≫
   --------
   [≻ (in-range start end (ext-stlc:#%datum . 1))]]
  [(in-range start end step) ≫
   [⊢ [start ≫ start- ⇐ : #,Int+]]
   [⊢ [end ≫ end- ⇐ : #,Int+]]
   [⊢ [step ≫ step- ⇐ : #,Int+]]
   --------
   [⊢ (#%plain-app- in-range- start- end- step-) ⇒ : #,(mk-Sequence- (list Int+))]])

(define-typed-syntax in-naturals
 [(in-naturals) ≫
  --------
  [≻ (in-naturals (ext-stlc:#%datum . 0))]]
 [(in-naturals start) ≫
  [⊢ [start ≫ start- ⇐ : #,Int+]]
  --------
  [⊢ (#%plain-app- in-naturals- start-) ⇒ : #,(mk-Sequence- (list Int+))]])

(define-typed-syntax in-lines
  [(in-lines e) ≫
   [⊢ [e ≫ e- ⇐ : #,String+]]
   --------
   [⊢ (#%plain-app- in-lines- (#%plain-app- open-input-string- e-)) ⇒ : #,(mk-Sequence- (list String+))]])

(define-typed-syntax for
  [(for (s:x+e ...) b ... body) ≫
   [⊢ s.e ≫ e- ⇒ (~Sequence ty)] ...
   [[s.x ≫ x- : ty] ... ⊢ [b ≫ b- ⇒ _] ... [body ≫ body- ⇒ _]]
   --------
   [⊢ (for- ([x- e-] ...) b- ... body-) ⇒ #,Unit+]])
(define-typed-syntax for*
  [(for* (s:x+e ...) b ... body) ≫
   [⊢ s.e ≫ e- ⇒ (~Sequence ty)] ...
   [[s.x ≫ x- : ty] ... ⊢ [b ≫ b- ⇒ _] ... [body ≫ body- ⇒ _]]
   --------
   [⊢ (for*- ([x- e-] ...) b- ... body-) ⇒ #,Unit+]])

(define-typed-syntax for/list
  [(for/list (s:x+e ...) body) ≫
   [⊢ s.e ≫ e- ⇒ (~Sequence ty)] ...
   [[s.x ≫ x- : ty] ... ⊢ body ≫ body- ⇒ ty_body]
   --------
   [⊢ (for/list- ([x- e-] ...) body-) ⇒ #,(mk-List- #'(ty_body))]])
(define-typed-syntax for/vector
  [(for/vector (s:x+e ...) body) ≫
   [⊢ s.e ≫ e- ⇒ (~Sequence ty)] ...
   [[s.x ≫ x- : ty] ... ⊢ body ≫ body- ⇒ ty_body]
   --------
   [⊢ (for/vector- ([x- e-] ...) body-) ⇒ #,(mk-Vector- #'(ty_body))]])
(define-typed-syntax for*/vector
  [(for*/vector (s:x+e ...) body) ≫
   [⊢ s.e ≫ e- ⇒ (~Sequence ty)] ...
   [[s.x ≫ x- : ty] ... ⊢ body ≫ body- ⇒ ty_body]
   --------
   [⊢ (for*/vector- ([x- e-] ...) body-) ⇒ #,(mk-Vector- #'(ty_body))]])
(define-typed-syntax for*/list
  [(for*/list (s:x+e ...) body) ≫
   [⊢ s.e ≫ e- ⇒ (~Sequence ty)] ...
   [[s.x ≫ x- : ty] ... ⊢ body ≫ body- ⇒ ty_body]
   --------
   [⊢ (for*/list- ([x- e-] ...) body-) ⇒ #,(mk-List- #'(ty_body))]])
(define-typed-syntax for/fold
  [(for/fold (acc:x+e) (s:x+e ...) b) ⇐ τ_expected ≫
   [⊢ acc.e ≫ init- ⇐ τ_expected]
   [⊢ s.e ≫ e- ⇒ (~Sequence ty)] ...
   [[acc.x ≫ acc- : τ_expected] [s.x ≫ x- : ty] ... ⊢ [b ≫ b- ⇐ τ_expected]]
   --------
   [⊢ (for/fold- ([acc- init-]) ([x- e-] ...) b-)]]
  [(for/fold (acc:x+e) (s:x+e ...) body) ≫
   [⊢ acc.e ≫ init- ⇒ τ_init]
   [⊢ s.e ≫ e- ⇒ (~Sequence ty)] ...
   [[acc.x ≫ acc- : τ_init] [s.x ≫ x- : ty] ... ⊢ [body ≫ body- ⇐ τ_init]]
   --------
   [⊢ (for/fold- ([acc- init-]) ([x- e-] ...) body-) ⇒ τ_init]])

(define-typed-syntax for/hash
  [(for/hash (s:x+e ...) body) ≫
   [⊢ s.e ≫ e- ⇒ (~Sequence ty)] ...
   [[s.x ≫ x- : ty] ... ⊢ body ≫ body- ⇒ (~× ty_k ty_v)]
   --------
   [⊢ (for/hash- ([x- e-] ...)
             (let-values- ([(t) body-])
               (values- (#%plain-app- car- t) (#%plain-app- cadr- t))))
       ⇒ #,(mk-Hash- #'(ty_k ty_v))]])

(define-typed-syntax for/sum
  [(for/sum (s:x+e ... (~optional (~seq #:when guard)
                         #:defaults ([guard #'(ext-stlc:#%datum . #t)])))
     body) ≫
   [⊢ s.e ≫ e- ⇒ (~Sequence ty)] ...
   [[s.x ≫ x- : ty] ... ⊢ [guard ≫ guard- ⇒ _] [body ≫ body- ⇐ #,Int+]]
   --------
   [⊢ (for/sum- ([x- e-] ... #:when guard-) body-) ⇒ #,Int+]])

; printing and displaying
(define-typed-syntax printf
  [(printf str e ...) ≫
   [⊢ [str ≫ s- ⇐ : #,String+]]
   [⊢ [e ≫ e- ⇒ : ty] ...]
   --------
   [⊢ (#%plain-app- printf- s- e- ...) ⇒ : #,Unit+]])
(define-typed-syntax format
  [(format str e ...) ≫
   [⊢ [str ≫ s- ⇐ : #,String+]]
   [⊢ [e ≫ e- ⇒ : ty] ...]
   --------
   [⊢ (#%plain-app- format- s- e- ...) ⇒ : #,String+]])

(define-typed-syntax let ; add named let
  [(let name:id (~datum :) ty:type ~! (:x+e ...) b ... body) ≫
   [⊢ e ≫ e- ⇒ ty_e] ...
   [[name ≫ name- : (→ ty_e ... ty.norm)] [x ≫ x- : ty_e] ...
     ⊢ [b ≫ b- ⇒ _] ... [body ≫ body- ⇐ ty.norm]]
   --------
   [⊢ (letrec-values- ([(name-) (λ- (x- ...) b- ... body-)])
             (name- e- ...))
       ⇒ ty.norm]]
  [(let (:x+e ...) body ...) ≫
   --------
   [≻ (ext-stlc:let (x+e ...) (ext-stlc:begin body ...))]])

(define-typed-syntax let*
  [(_ (:x+e ...) b ...) ≫
   --------
   [≻ (ext-stlc:let* (x+e ...) b ...)]])

(define-typed-syntax letrec
  [(_ ([(~optional (~literal #%brackets)) x+ty ...] ...) b ...) ≫
   --------
   [≻ (ext-stlc:letrec ([x+ty ...] ...) b ...)]])

;; hash
(define-type-constructor Hash #:arity = 2)

; mutable hashes
(define-typed-syntax hash
  [(hash (~and tys {ty_key:type ty_val:type})) ≫
   #:when (brace? #'tys)
   --------
   [⊢ (#%plain-app- make-hash-) ⇒ : #,(mk-Hash- #'(ty_key.norm ty_val.norm))]]
  [(hash (~seq k v) ...) ≫
   [⊢ [k ≫ k- ⇒ : ty_k] ...]
   [⊢ [v ≫ v- ⇒ : ty_v] ...]
   #:when (same-types? #'(ty_k ...))
   #:when (same-types? #'(ty_v ...))
   #:with ty_key (stx-car #'(ty_k ...))
   #:with ty_val (stx-car #'(ty_v ...))
   --------
   [⊢ (#%plain-app- make-hash- (#%plain-app- list- (#%plain-app- cons- k- v-) ...)) ⇒ : #,(mk-Hash- #'(ty_key ty_val))]])
(define-typed-syntax hash-ref
  [(hash-ref h k) ≫
   [⊢ [h ≫ h- ⇒ : (~Hash ty_k ty_v)]]
   [⊢ [k ≫ k- ⇐ : ty_k]]
   --------
   [⊢ (#%plain-app- hash-ref- h- k-) ⇒ : ty_v]]
  [(hash-ref h k fail) ≫
   [⊢ [h ≫ h- ⇒ : (~Hash ty_k ty_v)]]
   [⊢ [k ≫ k- ⇐ : ty_k]]
   [⊢ [fail ≫ fail- ⇐ : (→ ty_v)]]
   --------
   [⊢ (#%plain-app- hash-ref- h- k- fail-) ⇒ : ty_val]])

(define-base-type String-Port)
(define-base-type Input-Port)

(define-primop/unsafe string-length : (→ String Int))

(define-typed-syntax write-string
 [(write-string str out) ≫
  --------
  [≻ (write-string str out (ext-stlc:#%datum . 0) (mlish:#%app string-length str))]]
 [(write-string str out start end) ≫
  [⊢ [str ≫ str- ⇐ : #,String+]]
  [⊢ [out ≫ out- ⇐ : #,String-Port+]]
  [⊢ [start ≫ start- ⇐ : #,Int+]]
  [⊢ [end ≫ end- ⇐ : #,Int+]]
  --------
  [⊢ (begin- (#%plain-app- write-string- str- out- start- end-) (#%plain-app- void-)) ⇒ : #,Unit+]])

(define-typed-syntax string-copy!
  [(string-copy! dest dest-start src) ≫
   --------
   [≻ (string-copy!
         dest dest-start src (ext-stlc:#%datum . 0) (mlish:#%app string-length src))]]
  [(string-copy! dest dest-start src src-start src-end) ≫
   [⊢ [dest ≫ dest- ⇐ : #,String+]]
   [⊢ [src ≫ src- ⇐ : #,String+]]
   [⊢ [dest-start ≫ dest-start- ⇐ : #,Int+]]
   [⊢ [src-start ≫ src-start- ⇐ : #,Int+]]
   [⊢ [src-end ≫ src-end- ⇐ : #,Int+]]
   --------
   [⊢ (#%plain-app- string-copy!- dest- dest-start- src- src-start- src-end-) ⇒ : #,Unit+]])

(define-typed-syntax quotient+remainder
  [(quotient+remainder x y) ≫
   [⊢ [x ≫ x- ⇐ : #,Int+]]
   [⊢ [y ≫ y- ⇐ : #,Int+]]
   --------
   [⊢ (let-values- ([[a b] (#%plain-app- quotient/remainder- x- y-)])
             (#%plain-app- list- a b))
       ⇒ : #,(mk-×- (list Int+ Int+))]])

(define-typed-syntax set!
  [(set! x:id e) ≫
   [⊢ [x ≫ x- ⇒ : ty_x]]
   [⊢ [e ≫ e- ⇐ : ty_x]]
   --------
   [⊢ (set!- x- e-) ⇒ : #,Unit+]])

(define-typed-syntax provide-type
  [(provide-type ty ...) ≫
   --------
   [≻ (provide- ty ...)]])

(define-typed-syntax mlish-provide
  [(provide x:id ...) ≫
   [⊢ [x ≫ x- ⇒ : ty_x] ...]
   ; TODO: use hash-code to generate this tmp
   #:with (x-ty ...) (stx-map (lambda (y) (format-id y "~a-ty" y)) #'(x ...))
   --------
   [≻ (begin-
          (provide- x ...)
          (stlc+rec-iso:define-type-alias x-ty ty_x) ...
          (provide- x-ty ...))]])
(define-typed-syntax require-typed
  [(require-typed x:id ... #:from mod) ≫
   #:with (x-ty ...) (stx-map (lambda (y) (format-id y "~a-ty" y)) #'(x ...))
   #:with (x- ...) (generate-temporaries #'(x ...))
   --------
   [≻ (begin-
          (require- (rename-in (only-in mod x ... x-ty ...) [x x-] ...))
          (define-typed-variable-rename x ≫ x- : x-ty) ...)]])

(define-base-type Regexp)

(define-typed-syntax read-int
  [(read-int) ≫
   --------
   [⊢ (let-values- ([(x) (#%plain-app- read-)])
        (if- (#%plain-app- exact-integer?- x)
             x
             (#%plain-app- error- 'read-int "expected an int, given: ~v" x)))
       ⇒ : #,Int+]])
