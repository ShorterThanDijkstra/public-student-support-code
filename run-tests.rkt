#! /usr/bin/env racket
#lang racket

(require "utilities.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp.rkt")
(require "compiler.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")

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

(define passes
  (list (list "uniquify" uniquify interp-Lvar type-check-Lvar)
        (list "remove-complex" remove-complex-opera* interp-Lvar type-check-Lvar)
        (list "explicate control" explicate-control interp-Cvar type-check-Cvar)
        ))

(debug-level 1) 
; (interp-tests "var" #f compiler-passes interp-Lvar "var_test" (tests-for "var"))
; (interp-tests "var" #f passes interp-Lvar "var_test" (tests-for "var"))
; (interp-tests "rco" #f passes interp-Lvar "rco_test" (tests-for "rco"))
(interp-tests "eco" #f passes interp-Lvar "eco_test" (tests-for "eco"))



;; Uncomment the following when all the passes are complete to
;; test the final x86 code.
;; (compiler-tests "var" #f compiler-passes "var_test" (tests-for "var"))

