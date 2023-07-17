#lang racket
(require graph)
(require "utilities.rkt")
(provide (all-defined-out))
(require "compiler.rkt")
(require "graph-printing.rkt")
(require "interp.rkt")

;;; test exercise 3.3

(define p0 (read-program "./tests/eco_test_9.rkt"))

(define p1 (shrink p0))

(define p2 (uniquify p1))

(define p3 (remove-complex-opera* p2))

(define p4 (explicate-control p3))

(define p5 (select-instructions p4))

; (define cfg (build-cfg p5))

(define p6 (uncover-live p5))

(define p7 (build-interference p6))

(define p8 (allocate-registers p7))
; (interp-pseudo-x86-1 p8)