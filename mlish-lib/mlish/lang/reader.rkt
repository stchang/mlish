#lang s-exp syntax/module-reader
mlish/main
#:read
(λ (in)
  (parameterize ([read-square-bracket-with-tag #t])
    (read in)))
#:read-syntax
(λ (src in)
  (parameterize ([read-square-bracket-with-tag #t])
    (read-syntax src in)))
