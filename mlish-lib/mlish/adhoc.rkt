#lang turnstile/base

;; mlish library implementing ad-hoc polymorphism, ie type classes

(provide define-typeclass
         define-instance
         (rename-out [liftedλ λ]
                     [adhoc:#%app #%app]
                     [define/tc define])
         → →/test
         => =>/test)

(require (for-syntax racket/set racket/string macrotypes/type-constraints)
         (for-meta 2 racket/base syntax/parse racket/syntax)
 (only-in turnstile/examples/optimize/ext-stlc [λ ext-stlc:λ])
 (only-in "mlish.rkt"
          [~→ ~mlish:→] [→ mlish:→] [#%app mlish:#%app] [λ mlish:λ]
          [define mlish:define] [begin mlish:begin]
          #%brackets x+τ →? ?Λ ~?∀ ?∀))

(define-type-constructor => #:arity > 0)

;; type class helper fns
(begin-for-syntax
  (define (mk-app-err-msg stx #:expected [expected-τs #'()]
                              #:given [given-τs #'()]
                              #:note [note ""]
                              #:name [name #f]
                              #:action [other #f])
    (syntax-parse stx
      [(app e_fn e_arg ...)
       (define fn-name
         (if name name
             (format "function ~a"
                     (syntax->datum (or (get-orig #'e_fn) #'e_fn)))))
       (define action (if other other "applying"))
       (string-append
        (format "~a (~a:~a):\nType error "
                (syntax-source stx) (syntax-line stx) (syntax-column stx))
        action " "
        fn-name ". " note "\n"
        (format "  Expected: ~a argument(s) with type(s): " (stx-length expected-τs))
        (types->str expected-τs) "\n"
        "  Given:\n"
        (string-join
         (map (λ (e t) (format "    ~a : ~a" e t)) ; indent each line
              (syntax->datum #'(e_arg ...))
              (if (stx-length=? #'(e_arg ...) given-τs)
                  (stx-map type->str given-τs)
                  (stx-map (lambda (e) "?") #'(e_arg ...))))
         "\n")
        "\n")]))
  (define (type-hash-code tys) ; tys should be fully expanded
    (equal-hash-code (syntax->datum (if (syntax? tys) tys #`#,tys))))
  (define (mangle o tys)
    (format-id o "~a~a" o (type-hash-code tys)))
  ;; pattern expander for type class
  (define-syntax ~TC
    (pattern-expander
     (syntax-parser
       [(_ [generic-op ty-concrete-op] (~and ooo (~literal ...)))
        #'(_ (_ (_ generic-op) ty-concrete-op) ooo)]
       [(_ . ops+tys) 
        #:with expanded (generate-temporary)
        #'(~and expanded
            (~parse (_ (_ (_ gen-op) ty-op) (... ...)) 
                    #'expanded)
            (~parse ops+tys #'((gen-op ty-op) (... ...))))])))
  (define-syntax ~TC-base
    (pattern-expander
     (syntax-parser
      [(_ . pat)
       #:with expanded (generate-temporary)
       #'(~and expanded
              (~parse ((~TC . pat) . _) (flatten-TC #'expanded)))])))
  (define-syntax ~TCs
    (pattern-expander
     (syntax-parser
      ;; pat should be of shape ([op ty] ...)
      [(_ pat (~and ooo (~literal ...)))
       #:with expanded (generate-temporary)
       ;; (stx-map (compose remove-dups flatten-TC) #'expanded) 
       ;;  produces [List [List [List op+ty]]]
       ;; - inner [List op+ty] is from the def of a TC
       ;; - second List is from the flattened subclass TCs
       ;; - outer List is bc this pattern matces multiple TCs
       ;; This pattern expander collapses the inner two Lists
       #'(~and expanded
              (~parse (((~TC [op ty] (... ...)) (... ...)) ooo)
                      (stx-map (compose remove-dups flatten-TC) #'expanded))
              (~parse (pat ooo) #'(([op ty] (... ...) (... ...)) ooo)))])))
  (define (flatten-TC TC)
    (syntax-parse TC
      [(~=> sub-TC ... base-TC)
       (cons #'base-TC (stx-appendmap flatten-TC #'(sub-TC ...)))]))
  (define (remove-dups TCs)
    (syntax-parse TCs
      [() #'()]
      [(TC . rst)
       (cons #'TC (stx-filter (lambda (s) (not (typecheck? s #'TC))) (remove-dups #'rst)))])))

;; type inference constraint solving
(begin-for-syntax 
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

  (define (raise-app-poly-infer-error stx expected-tys given-tys e_fn)
    (type-error #:src stx
     #:msg (mk-app-err-msg stx #:expected expected-tys #:given given-tys
            #:note (format "Could not infer instantiation of polymorphic function ~a."
                           (syntax->datum (get-orig e_fn))))))

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
(define-typed-syntax define/tc
  [(_ (f:id :x+τ ... (~seq #:where TC ...) (~or (~datum ->) (~datum →)) τ_out)
      e_body ... e) ≫
   #:with (~and Ys (Y ...)) (compute-tyvars #'(τ ... τ_out))
   #:with f- (add-orig (generate-temporary #'f) #'f)
   #:with e_ann (syntax/loc #'e (add-expected e τ_out)) ; must be macro bc t_out may have unbound tvs
   #:with (τ+orig ...) (stx-map (λ (t) (add-orig t t)) #'(τ ... τ_out))
   ;; TODO: check that specified return type is correct
   ;; - currently cannot do it here; to do the check here, need all types of
   ;;  top-lvl fns, since they can call each other
   #:with (~and ty_fn_expected (~?∀ _ (~=> _ ... (~mlish:→ _ ... out_expected))))
          (syntax-property 
           ((current-type-eval)
            #'(?∀ Ys (=> TC ... (mlish:→ τ+orig ...))))
            'orig
            (list #'(→ τ+orig ...)))
   --------
   [≻ (begin-
        (define-typed-variable-rename f ≫ f- : ty_fn_expected)
        #,(quasisyntax/loc this-syntax
            (define- f-
              (liftedλ {Y ...} ([x : τ] ... #:where TC ...) 
               #,(syntax/loc #'e_ann (mlish:begin e_body ... e_ann))))))]]
  [(_ . rst) ≫ --- [≻ (mlish:define . rst)]])

(define-syntax → ; wrapping →
  (syntax-parser
    [(_ ty ... #:TC TC ...)
     #'(=> TC ... (mlish:→ ty ...))]
    [(_ Xs . rst)
     #:when (brace? #'Xs)
     #:with (X ...) #'Xs
     (syntax-property 
       #'(?∀ (X ...)  (mlish:→ . rst))
       'orig (list #'(→ . rst)))]
    [(_ . ts) (set-stx-prop/preserved #'(mlish:→ . ts) 'orig `(,#'(→ . ts)))]))

; special arrow that computes free vars; for use with tests
; (because we can't write explicit forall)
(define-syntax →/test 
  (syntax-parser
    [(_ (~and Xs (X:id ...)) . rst)
     #:when (brace? #'Xs)
     #'(?∀ (X ...) (mlish:→ . rst))]
    [(_ . rst)
     #:with Xs (compute-tyvars #'rst)
     #'(?∀ Xs (mlish:→ . rst))]))

(define-syntax =>/test 
  (syntax-parser
    [(_ . (~and rst (TC ... (_arr . tys_arr))))
     #:with Xs (compute-tyvars #'rst)
     #'(?∀ Xs (=> TC ... (mlish:→ . tys_arr)))]))

;; λ --------------------------------------------------------------------------
(define-typed-syntax BindTC
  [(_ (TC ...) body) ≫
   #:with (~and (TC+ ...) (~TCs ([op-sym ty-op] ...) ...))
          (stx-map expand/df #'(TC ...))
   #:with (op* ...)
          (stx-appendmap
           (lambda (os tc)
             (stx-map (lambda (o) (format-id tc "~a" o)) os))
           #'((op-sym ...) ...) #'(TC ...))
   #:with (ty-op* ...) (stx-flatten #'((ty-op ...) ...))
   #:with ty-in-tagsss (stx-map get-fn-ty-in-tags #'(ty-op* ...))
   #:with (mangled-op ...) (stx-map mangle #'(op* ...) #'ty-in-tagsss)
   [[mangled-op ≫ mangled-op- : ty-op*] ... ⊢ body ≫ body- ⇒ t-]
   --------
   [⊢ (#%plain-lambda- (mangled-op- ...) body-) ⇒ #,(mk-=>- #'(TC+ ... t-))]])

(define-typed-syntax liftedλ
  [(_ (:x+τ ... #:where TC ...) body) ≫
   #:with (X ...) (compute-tyvars #'(τ ...))
   --------
   [≻ (liftedλ {X ...} ([x : τ] ... #:where TC ...) body)]]
  [(_ (~and Xs (X ...)) (:x+τ ... #:where TC ...) body) ≫
   #:when (brace? #'Xs)
   --------
   [≻ (?Λ (X ...) (BindTC (TC ...) (ext-stlc:λ ([x : τ] ...) body)))]]
  [(_ . rst) ≫ --- [≻ (mlish:λ . rst)]])

;; #%app --------------------------------------------------
(define-typed-syntax adhoc:#%app
  [(_ e_fn . e_args) ≫
   ;; ) compute fn type, with TCs
   [⊢ e_fn ≫ e_fn- ⇒ (~?∀ Xs (~=> TCX ... (~mlish:→ . tyX_args)))]
   ;; ) solve for type variables Xs
   #:with ((e_arg1- ...) Xs* cs) (solve #'Xs #'tyX_args this-syntax)
   ;; ) instantiate polymorphic function type, to get concrete types
   #:with ((TC ...) (τ_in ... τ_out))
          (inst-types/cs/orig #'Xs #'cs #'((TCX ...) tyX_args) datum=?)
   #:with (unsolved-X ...) (find-free-Xs #'Xs* #'τ_out)
   #:with (~TCs ([generic-op ty-concrete-op] ...) ...) #'(TC ...)
   #:with (op ...)
          (stx-appendmap
           (lambda (gen-ops conc-op-tys TC)
             (map
              (lambda (o tys)
                (with-handlers
                  ([exn:fail:syntax:unbound?
                    (lambda (e)
                      (type-error
                       #:src this-syntax
                       #:msg
                       (format
                        (string-append
                         "~a instance undefined. "
                         "Cannot instantiate function with constraints "
                         "~a with:\n  ~a")
                        (type->str
                         (let* ([old-orig (get-orig TC)]
                                [new-orig
                                 (and
                                  old-orig
                                  (substs
                                   (stx-map get-orig (lookup-Xs/keep-unsolved #'Xs #'cs))
                                   #'Xs old-orig
                                   (lambda (x y)
                                     (equal? (syntax->datum x)
                                             (syntax->datum y)))))])
                           (syntax-property TC 'orig (list new-orig))))
                        (types->str #'(TCX ...))
                        (string-join
                         (stx-map 
                          (lambda (X ty-solved)
                            (string-append (type->str X) " : " (type->str ty-solved)))
                          #'Xs (lookup-Xs/keep-unsolved #'Xs #'cs)) ", "))))]
                   [(lambda _ #t)
                    (lambda (e) (displayln "other exn")(displayln e)
                            (error 'lookup))])
                  (lookup-op o tys)))
              (stx-map (lambda (o) (format-id this-syntax "~a" o #:source this-syntax)) gen-ops)
              (stx-map
               (syntax-parser
                 [(~?∀ _ (~mlish:→ ty_in ... _)) #'(ty_in ...)])
               conc-op-tys)))
           #'((generic-op ...) ...) #'((ty-concrete-op ...) ...) #'(TC ...))
   ;; ) arity check
   #:fail-unless (stx-length=? #'(τ_in ...) #'e_args)
                 (mk-app-err-msg this-syntax #:expected #'(τ_in ...)
                                 #:note "Wrong number of arguments.")
   ;; ) compute argument types; re-use args expanded during solve
   #:with ([e_arg2- τ_arg2] ...) (let ([n (stx-length #'(e_arg1- ...))])
                                   (infers+erase
                                    (stx-map
                                     add-expected-type
                                     (stx-drop #'e_args n)
                                     (stx-drop #'(τ_in ...) n))))
   #:with (τ_arg1 ...) (stx-map typeof #'(e_arg1- ...))
   #:with (τ_arg ...) #'(τ_arg1 ... τ_arg2 ...)
   #:with (e_arg- ...) #'(e_arg1- ... e_arg2- ...)
   ;; ) typecheck args
   #:fail-unless (typechecks? #'(τ_arg ...) #'(τ_in ...))
                 (mk-app-err-msg this-syntax
                  #:given #'(τ_arg ...)
                  #:expected
                  (stx-map
                   (lambda (tyin)
                     (define old-orig (get-orig tyin))
                     (define new-orig
                       (and old-orig
                            (substs
                             (stx-map
                              get-orig
                              (lookup-Xs/keep-unsolved #'Xs #'cs)) #'Xs old-orig
                             (lambda (x y)
                               (equal? (syntax->datum x) (syntax->datum y))))))
                     (syntax-property tyin 'orig (list new-orig)))
                   #'(τ_in ...)))
   #:with τ_out* (if (stx-null? #'(unsolved-X ...))
                     #'τ_out
                     (syntax-parse #'τ_out
                       [(~?∀ (Y ...) τ_out)
                        (unless (→? #'τ_out)
                          (raise-app-poly-infer-error this-syntax
                            #'(τ_in ...) #'(τ_arg ...) #'e_fn))
                        #'(?∀ (unsolved-X ... Y ...) τ_out)]))
   ------
   [⊢ (#%plain-app- (#%plain-app- e_fn- op ...) e_arg- ...) ⇒ τ_out*]]
  [(_ . rst) ≫ --- [≻ (mlish:#%app . rst)]])

(begin-for-syntax
 ;; - this function should be wrapped with err handlers,
 ;; for when an op with the specified generic op and input types does not exist,
 ;; otherwise, will get "unbound id" err with internal mangled id
 ;; - gen-op must be identifier, eg should already have proper context
 ;; and mangled-op is selected based on input types,
 ;; ie, dispatch to different concrete fns based on input tpyes
 ;; TODO: currently using input types only, but sometimes may need output type
 ;; eg, Read typeclass, this is currently unsupported
 ;; - need to use expected-type?
 (define (lookup-op gen-op tys)
  (define (transfer-gen-op-ctx o) (format-id gen-op "~a" o))
  (define (transfer-gen-op-ctxs os) (stx-map transfer-gen-op-ctx os))
  (syntax-parse/typecheck tys
   ;; TODO: for now, only handle uniform tys, ie tys must be all
   ;;  tycons or all base types or all tyvars
   ;; tycon --------------------------------------------------
   ;; - recur on ty-args
   [((~Any tycon ty-arg ...) ...) ≫
    ;; 1) look up concrete op corresponding to generic op and input tys
    [⊢ #,(mangle gen-op #'(tycon ...)) ≫ conc-op
       ⇒ (~?∀ Xs (~=> TC ... (~mlish:→ . ty-args)))]
    ;; 2) compute sub-ops based on TC constraints
    ;;    (will include gen-op --- for smaller type)
    #:with (~TCs ([op _] ...) ...) #'(TC ...) ; order matters, must match order of arg types
    #:with ((sub-op ...) ...) (stx-map transfer-gen-op-ctxs #'((op ...) ...))
    ----------
    [⊢ (conc-op 
        ;; 3) recursively call lookup-op for each subop and input ty-args
        #,@(apply stx-appendmap
                  (lambda (ops . tys) (stx-map (lambda (o) (lookup-op o tys)) ops))
                  #'((sub-op ...) ...)
                  (syntax->list #'((ty-arg ...) ...))))
       ;; 4) drop the TCs in result type, the proper subops are already applied
       ⇒ (?∀ Xs (mlish:→ . ty-args))]] ; conc type, TCs dropped
   ;; base type --------------------------------------------------
   [(((~literal #%plain-app) ty-internal) ...) ≫
    [⊢ #,(mangle gen-op #'(ty-internal ...)) ≫ op- ⇒ t-]
    -------
    [⊢ op- ⇒ t-]]
   ;; tyvars --------------------------------------------------
   [_ ≫
    [⊢ #,(mangle gen-op tys) ≫ op- ⇒ t-]
    -------
    [⊢ op- ⇒ t-]]))

 ;; gets the internal id in a type representation
  (define (get-type-tag t)
    (syntax-parse t
      [((~literal #%plain-app) tycons . _) #'tycons]
      [X:id #'X]
      [_ (type-error #:src t #:msg "Can't get internal id: ~a" t)]))
  (define (get-type-tags ts)
    (stx-map get-type-tag ts))
  (define (get-fn-ty-in-tags ty-fn)
   (syntax-parse ty-fn
     [(~?∀ _ (~mlish:→ ty_in ... _))
      (get-type-tags #'(ty_in ...))]
     [(~?∀ _ (~=> _ ... (~mlish:→ ty_in ... _)))
      (get-type-tags #'(ty_in ...))]))
 (define (TC-exists? TC #:ctx [ctx TC]) ; throws exn if fail
   (syntax-parse TC
     [(~TC-base [gen-op ty-op] . _) ; only need 1st op
      (with-handlers 
        ([exn:fail:syntax:unbound? 
           (lambda (e) 
             (type-error #:src ctx
                         #:msg "No instance defined for ~a" TC))])
      (expand/df
        (mangle (format-id ctx "~a" #'gen-op)
                (get-fn-ty-in-tags #'ty-op))))]))
 (define (TCs-exist? TCs #:ctx [ctx TCs])
   (stx-map (lambda (tc) (TC-exists? tc #:ctx ctx)) TCs)))

;; adhoc polymorphism ---------------------------------------------------------

;; lifted transformer fns, to avoid stx-parse expansion overhead
(begin-for-syntax
  ;; TODO: can this just be variable-like-transformer?
  (define (make-typeclass-op-transformer)
    (syntax-parser
      [(o . es)
       #:with ([e- ty_e] ...) (infers+erase #'es)
       #:with out-op
       (with-handlers
         ([exn:fail:syntax:unbound?
           (lambda (e)
             (type-error #:src #'o
                         #:msg (format
                                "~a operation undefined for input types: ~a"
                                (syntax->datum #'o)
                                (types->str #'(ty_e ...)))))])
         (lookup-op #'o #'(ty_e ...)))
       #:with app (datum->syntax #'o '#%app)
       (datum->syntax this-syntax (cons #'app (cons #'out-op #'(e- ...))))]))
  (define (make-typeclass-transformer TCs ops+tys Xs Name-stx)
    (define/syntax-parse (TC ...) TCs)
    (define/syntax-parse Name Name-stx)
    (syntax-parser
      [(_ . rst)
       #:when (= (stx-length Xs) (stx-length #'rst))
       (add-orig
        (substs #'rst Xs #`(=> TC ... #,(mk-type ops+tys)))
        #'(Name . rst))])))

;; TODO: make this a formal type?
;; - or at least define a pattern expander - DONE 2016-05-01
;; A TC is a #'(=> subclassTC ... ([generic-op gen-op-ty] ...))
(define-syntax define-typeclass
  (syntax-parser
    [(~or (_ TC ... (~datum =>) (Name X ...) :x+τ ...)
          (~and (_ (Name X ...) :x+τ ...) (~parse (TC ...) #'()))) ; no subclass
     #'(begin-
         (define-syntax- x (make-typeclass-op-transformer)) ...
         (define-syntax- Name
           (make-typeclass-transformer
            #'(TC ...) #'(#%plain-app- (#%plain-app- 'x τ) ...) #'(X ...) #'Name)))]))

(define-typed-syntax define-instance
  ;; base type, possibly with subclasses  ------------------------------------
  [(_ (Name ty ...) [(~optional (~literal #%brackets)) generic-op concrete-op] ...) ≫
   #:with (~=> TC ... (~TC [generic-op-expected ty-concrete-op-expected] ...))
          (expand/df #'(Name ty ...))
   #:when (TCs-exist? #'(TC ...) #:ctx this-syntax)
   #:fail-unless (set=? (syntax->datum #'(generic-op ...)) 
                        (syntax->datum #'(generic-op-expected ...)))
                 (type-error #:src this-syntax
                  #:msg (format "Type class instance ~a incomplete, missing: ~a"
                          (syntax->datum #'(Name ty ...))
                          (string-join
                           (map symbol->string 
                                (set-subtract 
                                 (syntax->datum #'(generic-op-expected ...)) 
                                 (syntax->datum #'(generic-op ...))))
                           ", ")))
   ;; sort, using order from define-typeclass
   #:with ([generic-op-sorted concrete-op-sorted] ...) 
          (stx-map
           (lambda (expected-op) 
             (stx-findf
              (lambda (gen+conc) 
                (equal? (syntax->datum (stx-car gen+conc)) 
                        (syntax->datum expected-op)))
              #'([generic-op concrete-op] ...)))
           #'(generic-op-expected ...))
   ;; typecheck type of given concrete-op with expected type from define-typeclass
   [⊢ concrete-op-sorted ≫ concrete-op+ ⇐ ty-concrete-op-expected] ...
   ;; generate mangled name from tags in input types
   #:with (ty_in-tags ...) (stx-map get-fn-ty-in-tags #'(ty-concrete-op-expected ...))
   ;; use input types
   #:with (mangled-op ...) (stx-map mangle #'(generic-op ...) #'(ty_in-tags ...))
  --------
  [≻ (begin-
       (define-syntax- mangled-op
         (make-variable-like-transformer
          (assign-type #'concrete-op+ #'ty-concrete-op-expected))) ...)]]
  ;; tycon, possibly with subclasses -----------------------------------------
  [(_ TC ... (~datum =>) (Name ty ...) [(~optional (~literal #%brackets)) generic-op concrete-op] ...) ≫
   #:with (X ...) (compute-tyvars #'(ty ...))
   ;; ok to drop TCsub ...? I think yes
   ;; - the same TCsubs will be part of TC+,
   ;;   so proper op will be looked up, depending on input args, 
   ;;   using inherited ops in TC+
   ;; This is assuming Name and TC ... are the same typeclass
   ;; Won't work for, eg (TC1 (List X)) that depends on some other (TC2 X)
   #:with (Xs+ 
           (TC+ ... 
                (~=> TCsub ... 
                     (~TC [generic-op-expected ty-concrete-op-expected] ...))))
           (expands/tvctx #'(TC ... (Name ty ...)) #'(X ...) #:stop-list? #f)
   ;; this produces #%app bad stx err, so manually call infer for now
   ;; 2018-04-02: still wont work bc of stop-list (?)
   ;; [([X ≫ X- :: #%type] ...) () ⊢ (TC ... (Name ty ...)) ≫
   ;;                                (TC+ ... 
   ;;                                 (~=> TCsub ... 
   ;;                                  (~TC [generic-op-expected ty-concrete-op-expected] ...)))
   ;;                                ⇒ _]
   ;; #:with Xs+ #'(X- ...)
   #:when (TCs-exist? #'(TCsub ...) #:ctx this-syntax)
   ;; simulate as if the declared concrete-op* has TC ... predicates
   #:with (ty-concrete-op-expected-withTC ...) 
          (stx-map
           (lambda (t) #`(?∀ Xs+ (=> TC+ ... #,t)))
           #'(ty-concrete-op-expected ...))
   #:fail-unless (set=? (syntax->datum #'(generic-op ...)) 
                        (syntax->datum #'(generic-op-expected ...)))
                 (type-error #:src this-syntax
                  #:msg (format "Type class instance ~a incomplete, missing: ~a"
                          (syntax->datum #'(Name ty ...))
                          (string-join
                           (map symbol->string 
                                (set-subtract 
                                 (syntax->datum #'(generic-op-expected ...)) 
                                 (syntax->datum #'(generic-op ...))))
                           ", ")))
   ;; - sort, using order from define-typeclass
   ;; - insert TC ... if lambda
   #:with ([generic-op-sorted concrete-op-sorted] ...) 
          (stx-map
           (lambda (expected-op) 
             (syntax-parse
                 (stx-findf
                  (lambda (gen+conc) 
                    (equal? (syntax->datum (stx-car gen+conc)) 
                            (syntax->datum expected-op)))
                  #'([generic-op concrete-op] ...))
               [(g c) 
                (syntax-parse #'c
                  ;; add TCs to (unexpanded) lambda
                  [((~and lam (~literal liftedλ)) (args ...) . body) 
                   #'(g (lam (args ... #:where TC ...) . body))]
                  [_ #'(g c)])]))
           #'(generic-op-expected ...))
   ;; ;; for now, dont expand (and typecheck) concrete-op
   ;; #:with ([concrete-op+ ty-concrete-op] ...) (infers+erase #'(concrete-op ...))
   ;; #:when (typechecks? #'(ty-concrete-op ...) #'(ty-concrete-op-expected ...))
   ;; TODO: right now, dont recur to get nested tags
   ;; but may need to do so, ie if an instance needs to define more than one concrete op,
   ;; eg (define-instance (Eq (List Int)) ...)
   #:with (ty_in-tags ...) (stx-map get-fn-ty-in-tags #'(ty-concrete-op-expected ...))
   #:with (mangled-op ...) (stx-map mangle #'(generic-op ...) #'(ty_in-tags ...))
   ;; need a name for concrete-op because concrete-op and generic-op may be
   ;; mutually recursive, eg (Eq (List X))
   #:with (f ...) (generate-temporaries #'(concrete-op-sorted ...))
  --------
  [≻ (begin-
        (define- f concrete-op-sorted) ...
        (define-typed-variable-rename mangled-op ≫ f
          : ty-concrete-op-expected-withTC) ...)]])

