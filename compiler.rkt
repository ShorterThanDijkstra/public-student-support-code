#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "utilities.rkt")
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lint examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following compiler pass is just a silly one that doesn't change
;; anything important, but is nevertheless an example of a pass. It
;; flips the arguments of +. -Jeremy
(define (flip-exp e)
  (match e
    [(Var x) e]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (Prim '- (list (flip-exp e1)))]
    [(Prim '+ (list e1 e2)) (Prim '+ (list (flip-exp e2) (flip-exp e1)))]))

(define (flip-Lint e)
  (match e
    [(Program info e) (Program info (flip-exp e))]))


;; Next we have the partial evaluation pass described in the book.
(define (pe-neg r)
  (match r
    [(Int n) (Int (fx- 0 n))]
    [else (Prim '- (list r))]))

(define (pe-add r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [(_ _) (Prim '+ (list r1 r2))]))

(define (pe-exp e)
  (match e
    [(Int n) (Int n)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]))

(define (pe-Lint p)
  (match p
    [(Program info e) (Program info (pe-exp e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (make-gen-sym)
  (let ([id 0])
    (lambda (sym)
      (set! id (+ id 1))
      (symbol-append sym
                     (symbol-append
                      (string->symbol ".")
                      (string->symbol (number->string id)))))))

(define gen-sym (make-gen-sym))

(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x)
       (Var (dict-ref env x))
       ;  (error "TODO: code goes here (uniquify-exp, symbol?)")
       ]
      [(Int n) (Int n)]
      [(Let x e body)
       ;  (error "TODO: code goes here (uniquify-exp, let)")
       (let ([new_x (gen-sym x)])
         (let ([new_env (dict-set env x new_x)])
           (Let new_x
                ((uniquify-exp env) e)
                ((uniquify-exp new_env) body))))

       ]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

(define (show-exp e d)
  (match e
    [(Var x) (symbol->string x)]
    [(Int n) (number->string n)]
    [(Prim '- (list e)) (string-append "-" (show-exp e d))]
    [(Prim '+ (list e1 e2)) (string-append "(" (show-exp e1 d) " + " (show-exp e2 d) ")")]
    [(Prim '- (list e1 e2)) (string-append "(" (show-exp e1 d) " - " (show-exp e2 d) ")" )]
    [(Let x e body)
     (let ([prefix (string-append "let " (symbol->string x) " = ")])
       (string-append prefix (show-exp e (+ d (string-length prefix))) "\n"
                      (make-string d #\ ) "in " (show-exp body (+ d 3))))]))
(define (show p)
  (match p
    [(Program info e) (display (show-exp e 0))]))


; let a = let b = 3 in let c = 4 in c + b
; in a



; x1: a
; e1: let b = 3 in let c = 4 in c + b
; body1: a

; x2: b
; e2: 3
; body2: let c = 4 in c + b
; (anf-exp (Let b 3 (Let a (Let c 4 (+ c b)) a)))


; x1: b
; e1: 3
; body1: let a = let c = 4 in c + b in a
; (Let b 3 (anf-exp (Let a (Let c 4 (+ c b)) a)))


; x1: a
; e1: let c = 4 in c + b
; body1: a

; x2: c
; e2: 4
; body2: c + b
; (Let b 3 (anf-exp (Let c 4 (Let a (+ c b) a))))

; (Let b 3 (Let c 4 (Let a (+ c b)) a))
(define (anf-exp e)
  (match e
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Prim op es) (Prim op es)]
    [(Let x1 e1 body1)
     (match e1
       [(Var _) (Let x1 e1 (anf-exp body1))]
       [(Int _) (Let x1 e1 (anf-exp body1))]
       [(Prim op es) (Let x1 e1 (anf-exp body1))]
       [(Let x2 e2 body2)
        (anf-exp (Let x2 e2 (Let x1 body2 body1)))])]))
; (anf-exp (Let x2 e2 (anf-exp (Let x1 body2 (anf-exp body1)))))])]))

(define (rco-exp e)
  (match e
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Let x e body)
     (Let x
          (rco-exp e)
          (rco-exp body))]
    [(Prim op es)
     (let loop ([es es] [atoms '()])
       (if (null? es)
           (Prim op (reverse atoms))
           (if (atm? (car es))
               (loop (cdr es) (cons (car es) atoms))
               (let ([sym (gen-sym 'tmp)]
                     [new-e (rco-exp (car es))])
                 (Let sym new-e
                      (loop (cdr es) (cons (Var sym) atoms)))))))]))

;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info (rco-exp e))]))
         
    ; [(Program info e) (Program info (anf-exp (rco-exp e)))]))
; (error "TODO: code goes here (remove-complex-opera*)"))

(define (explicate-tail e)
  (match e
    [(Var x) (Return e)]
    [(Int n) (Return e)]
    [(Prim op es) (Return e)]
    [(Let x rhs body) (explicate-assign rhs x (explicate-tail body))]
    [else (error "explicate_tail unhandled case" e)]))

(define (explicate-assign e x cont)
  (match e
    [(Var _) (Seq (Assign (Var x) e) cont)]
    [(Int _) (Seq (Assign (Var x) e) cont)]
    [(Prim op es)  (Seq (Assign (Var x) e) cont)]
    [(Let y rhs body) (explicate-assign rhs y (explicate-assign body x cont))]
    [else (error "explicate_assign unhandled case" e)]))

; ;; explicate-control : R1 -> C0
(define (explicate-control p)
  (match p [(Program info body)
            (CProgram info (list (cons 'start (explicate-tail body))))]))
;   (error "TODO: code goes here (explicate-control)"))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (error "TODO: code goes here (select-instructions)"))

;; assign-homes : pseudo-x86 -> pseudo-x86
(define (assign-homes p)
  (error "TODO: code goes here (assign-homes)"))

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (error "TODO: code goes here (patch-instructions)"))

;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
  (error "TODO: code goes here (prelude-and-conclusion)"))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( ("uniquify" ,uniquify ,interp-Lvar ,type-check-Lvar)
     ;; Uncomment the following passes as you finish them.
     ;; ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
     ;; ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
     ;; ("instruction selection" ,select-instructions ,interp-x86-0)
     ;; ("assign homes" ,assign-homes ,interp-x86-0)
     ;; ("patch instructions" ,patch-instructions ,interp-x86-0)
     ;; ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))
