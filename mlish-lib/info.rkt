#lang info

(define collection 'multi)

(define deps
  '(("base" #:version "7.0")
    ("macrotypes-lib" #:version "0.3.4")
    ("turnstile-lib" #:version "0.5.1")
    ("turnstile-example" #:version "0.5")))

(define build-deps '())

(define pkg-desc "MLish: an extensible ML language.")
(define pkg-authors '(stchang))

(define version "0.1")
