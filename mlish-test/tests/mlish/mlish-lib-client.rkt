#lang mlish

;; ensure stx props not lost
;; see issue#73
(require "mlish-lib.rkt")
(+ 1 one)
