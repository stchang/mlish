#lang racket/base
(require (except-in "mlish.rkt"
                    → →/test inst #%app λ define provide
                    fl* fl+ fl- fl=
                    - + < = * > <=
                    string=? string<=?)
         "adhoc.rkt")

(provide (all-from-out "mlish.rkt")
         (all-from-out "adhoc.rkt"))
