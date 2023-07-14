#! /usr/bin/env racket
#lang racket

(require "utilities.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp.rkt")
(require "compiler.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "type-check-Lif.rkt")
(require "interp-Lif.rkt")
(require "interp-Cif.rkt")
(require "type-check-Cif.rkt")


;; (debug-level 1)
;; (AST-output-syntax 'concrete-syntax)

;; all the files in the tests/ directory with extension ".rkt".
(define all-tests
  (map (lambda (p) (car (string-split (path->string p) ".")))
       (filter (lambda (p)
                 (string=? (cadr (string-split (path->string p) ".")) "rkt"))
               (directory-list (build-path (current-directory) "tests")))))

(define (tests-for r)
  (map (lambda (p)
         (caddr (string-split p "_")))
       (filter
        (lambda (p)
          (string=? r (car (string-split p "_"))))
        all-tests)))

; (define passes
;   (list (list "uniquify" uniquify interp-Lvar type-check-Lvar)
;         (list "remove-complex" remove-complex-opera* interp-Lvar type-check-Lvar)
;         (list "explicate control" explicate-control interp-Cvar type-check-Cvar)
;         (list "instruction selection" select-instructions interp-pseudo-x86-0)
;         (list "assign homes" assign-homes interp-x86-0)
;         (list "patch instructions" patch-instructions interp-x86-0)
;         (list "prelude and conclusion" prelude-and-conclusion interp-x86-0)
;         ))

; (define passes
;   (list (list "uniquify" uniquify interp-Lvar type-check-Lvar)
;         (list "remove-complex" remove-complex-opera* interp-Lvar type-check-Lvar)
;         (list "explicate control" explicate-control interp-Cvar type-check-Cvar)
;         (list "instruction selection" select-instructions interp-pseudo-x86-0)
;         (list "uncover live" uncover-live interp-pseudo-x86-0)
;         (list "build interference" build-interference interp-pseudo-x86-0)
;         (list "allocate registers" allocate-registers interp-x86-0)
;         (list "patch instructions" patch-instructions interp-x86-0)
;         (list "prelude and conclusion" prelude-and-conclusion interp-x86-0)
;         ))

(debug-level 1)
; (interp-tests "var" #f passes interp-Lvar "var_test" (tests-for "var"))
; (interp-tests "int" #f passes interp-Lvar "int_test" (tests-for "int"))
; (interp-tests "var" #f passes interp-Lvar "var_test" (tests-for "var"))
; (interp-tests "rco" #f passes interp-Lvar "rco_test" (tests-for "rco"))
; (interp-tests "eco" #f passes interp-Lvar "eco_test" (tests-for "eco"))
; (interp-tests "insel" #f passes interp-Lvar "insel_test" (tests-for "insel"))
; (interp-tests "homes" #f passes interp-Lvar "homes_test" (tests-for "homes"))
; (interp-tests "patch" #f passes interp-Lvar "patch_test" (tests-for "patch"))
; (interp-tests "precon" #f passes interp-Lvar "precon_test" (tests-for "precon"))

(define passes
  (list (list "shrink" shrink interp-Lif type-check-Lif)
        (list "uniquify" uniquify interp-Lif type-check-Lif)
        (list "remove-complex" remove-complex-opera* interp-Lif type-check-Lif)
        (list "explicate-control" explicate-control interp-Cif type-check-Cif)))

; (interp-tests "cond" type-check-Lif passes interp-Lif "cond_test" (tests-for "cond"))
; (interp-tests "shrink test" type-check-Lif passes interp-Lif "shrink_test" (tests-for "shrink"))
; (interp-tests "var" type-check-Lif passes interp-Lvar "var_test" (tests-for "var"))
(interp-tests "eco" type-check-Lif passes interp-Lif "eco_test" (tests-for "eco"))


;; Uncomment the following when all the passes are complete to
;; test the final x86 code.
; (compiler-tests "var" #f passes "var_test" (tests-for "var"))
; (compiler-tests "cond" type-check-Lif passes "cond_test" (tests-for "cond"))


