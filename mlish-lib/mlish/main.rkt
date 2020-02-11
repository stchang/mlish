#lang racket/base
(require (except-in "mlish.rkt" provide))
(require (only-in "mlish.rkt" [provide mlish:provide]))
(provide (all-from-out "mlish.rkt"))
(provide (rename-out [mlish:provide provide]))
