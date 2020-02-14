#lang mlish
(require rackunit/turnstile)

;; example from jsmaniac
(define (f [x : X] [g : (→ X Y)] -> Y) (g x))

;; make sure errs prints instantiated types
(typecheck-fail
 (ann
  (λ ([a : Int]) (f a number->string))
  : Int)
 #:with-msg "type mismatch: expected Int, given \\(→ Int String\\)")

;; make sure errs prints instantiated types
(typecheck-fail
 (add1
  (λ ([a : Int]) (f a number->string)))
 #:with-msg "couldn't unify Int and \\(→ Int String\\)")
