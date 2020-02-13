#lang racket/base
(require (except-in "mlish.rkt" → →/test #%app λ define provide)
         "adhoc.rkt")

(provide (all-from-out "mlish.rkt")
         (all-from-out "adhoc.rkt"))
