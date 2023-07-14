#lang racket
(require racket/set racket/stream)
(require graph)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "utilities.rkt")
(require "compiler.rkt")

;;; test exercise 3.3
; (define p0 (read-program "./tests/eco_test_4.rkt"))
(define p0 (read-program "./tests/eco_test_8.rkt"))


(define p1 (shrink p0))

(define p2 (uniquify p1))

(define p3 (remove-complex-opera* p2))

(define p4 (explicate-control p3))

;;; todo

#|
if if thn els
thn
els
|#

#|
if cnd
if cnd thn els
els
|#
