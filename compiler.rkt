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

(define (insts-atm c-var-ele)
  (match c-var-ele
    [(Int n)  (Imm n)]
    [(Var x) (Var x)]
    [else (error 'insts-atm)]))

; (define (insts-exp c-var-ele)
;   (match c-var-ele
;     [(Prim 'read '()) (list (Callq 'read_int) 0)]
;     [(Prim '- (list atm)) (list (Instr 'negq (insts-atm atm)))]
;     [(Prim '+ (list atm1 atm2)) (list (Instr 'movq (insts-atm atm1) (Reg 'rax))
;                                       (Instr 'addq (insts-atm atm2) (Reg 'rax)))]
;     [(Prim '- (list atm1 atm2)) (list (Instr 'movq (insts-atm atm1) (Reg 'rax))
;                                       (Instr 'subq (insts-atm atm2) (Reg 'rax)))]
;     [else (error 'insts-exp)]))
(define (eq-var? var sym)
  (match var
    [(Var x) (eqv? x sym)]
    [else #f]))

(define (insts-exp e)
  (match e
    [(Var x) (list (Instr 'movq (list (Var x) (Reg 'rax))))]
    [(Int n) (list (Instr 'movq (list (Int n) (Reg 'rax))))]
    [(Prim 'read '())
     (list (Callq 'read_int 0))]
    [(Prim '- (list atm))
     (list (Instr 'movq (list (insts-atm atm) (Reg 'rax))))]
    [(Prim '+ (list atm1 atm2))
     (list (Instr 'movq (list (insts-atm atm1) (Reg 'rax)))
           (Instr 'addq (list (insts-atm atm2) (Reg 'rax))))]

    [(Prim '-(list atm1 atm2))
     (list (Instr 'movq (list (insts-atm atm1) (Reg 'rax)))
           (Instr 'subq (list (insts-atm atm2) (Reg 'rax))))]
    [else (error 'insts-exp)]))

(define (insts-stmt c-var-ele)
  (match c-var-ele
    [(Assign (Var x) e)
     (match e
       [(Var x1)
        (list (Instr 'movq (list (Var x1) (Var x))))]
       [(Int n)
        (list (Instr 'movq (list (Imm n) (Var x))))]
       [(Prim 'read '())
        (list (Callq 'read_int 0)
              (Instr 'movq (list (Reg 'rax) (Var x))))]
       [(Prim '- (list atm))
        (list (Instr 'movq (list (insts-atm atm) (Var x)))
              (Instr 'negq (list (Var x))))]

       [(Prim '+ (list atm1 atm2))
        (if (eq-var? atm1 x)
            (list (Instr 'addq (list (insts-atm atm2) (Var x) )))
            (if (eq-var? atm2 x)
                (list (Instr 'addq (list (insts-atm atm1) (Var x))))
                (list (Instr 'movq (list (insts-atm atm1) (Var x)))
                      (Instr 'addq (list (insts-atm atm2) (Var x))))))]
       [(Prim '- (list atm1 atm2))
        (if (eq-var? atm1 x)
            (list (Inst 'subq (list (insts-atm atm2) (Var x))))
            (list (Instr 'movq (list (insts-atm atm1) (Var x)))
                  (Instr 'subq (list (insts-atm atm2) (Var x)))))])]
    [else (error 'insts-stmt)]))

(define (insts-tail c-var-ele)
  (match c-var-ele
    [(Return e) (append (insts-exp e) (list (Jmp 'conclusion)))]
    [(Seq stmt tail) (append (insts-stmt stmt) (insts-tail tail))]
    [else (error 'insts-tail)]))

(define (insts c-var-ele)
  (match c-var-ele
    [(Int n) (insts-atm c-var-ele)]
    [(Var x) (insts-atm c-var-ele)]
    [(Prim op es) (insts-atm c-var-ele)]
    [(Assign (Var x) e) (insts-stmt  c-var-ele)]
    [(Return e) (insts-tail c-var-ele)]
    [(Seq stmt tail) (insts-tail c-var-ele)]))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (match p
    [(CProgram info label&blocks)
     (X86Program info (for/list ([label&block label&blocks])
                        (cons (car label&block)
                              (Block '() (insts (cdr label&block))))))]))

; (error "TODO: code goes here (select-instructions)"))

(define (type-space type)
  (match type
    ['Integer 8]
    [else (error 'type-space)]))
; homes: listof (sym . int)
(define (assign-arg arg locals-types homes)
  (match arg
    [(Imm n) (list (Imm n) homes)]
    [(Reg reg) (list (Reg reg) homes)]
    [(Deref reg n) (Deref reg n)]
    [(Var x) (let ([exist (dict-ref homes x #f)])
               (if exist
                   (list (Deref 'rbp exist) homes)
                   (let ([type (dict-ref locals-types x)]
                         [top (if (null? homes) 0 (cdar homes))])
                     (let ([new-top (- top (type-space type))])
                       (let ([new-homes (cons (cons x new-top) homes)])
                         (list (Deref 'rbp new-top) new-homes))))))]
    [else (error 'assign-arg)]))

(define (assign-instr instr locals-types homes)
  (match instr
    [(Instr name args) (let loop ([args args]
                                  [new-args '()]
                                  [homes homes])
                         (if (null? args)
                             (list (Instr name (reverse new-args)) homes)
                             (let ([res (assign-arg (car args) locals-types homes)])
                               (let ([new-arg (car res)]
                                     [new-homes (cadr res)])
                                 (loop (cdr args) (cons new-arg new-args) new-homes)))))]
    [(Callq label n) (list (Callq label n) homes)]
    [(Retq) (list (Retq) homes)]
    [(Jmp label) (list (Jmp label) homes)]
    [else (error 'assign-instr)]))

(define (ceil-16 n)
  (let ([m (modulo n 16)])
    (if (zero? m)
        n
        (+ n (- 16 m)))))

(define (assign-block block locals-types)
  (match block
    [(Block info instrs)
     ;  (displayln instrs)
     (let loop ([instrs instrs] [new-instrs '()] [homes '()])
       (if (null? instrs)
           (list (ceil-16(-(cdar homes))) (reverse new-instrs))
           (let ([res (assign-instr (car instrs) locals-types homes)])
             (loop (cdr instrs) (cons (car res) new-instrs) (cadr res)))))]
    [else (error 'assign-block "~s" block)]))


;; assign-homes : pseudo-x86 -> pseudo-x86
(define (assign-homes p)
  (match p
    [(X86Program info label&blocks)
     (let ([locals-types (dict-ref info 'locals-types)])
       (let loop ([label&blocks label&blocks]
                  [labels '()]
                  [block-instrs '()]
                  [spaces '()])
         (if (null? label&blocks)
             (X86Program (append (list (cons 'stack-space spaces)) info)
                         (for/list ([label labels] [instrs block-instrs])
                           (cons label (Block '() instrs))))
             (let ([curr-label (caar label&blocks)]
                   [curr-block (cdar label&blocks)])
               ;  (displayln curr-label)
               ;  (displayln curr-block)
               (let ([res (assign-block curr-block locals-types)])
                 (let ([space (car res)]
                       [new-block-instrs (cadr res)])
                   (loop (cdr label&blocks)
                         (cons curr-label labels)
                         (cons new-block-instrs block-instrs)
                         (cons (cons curr-label space) spaces))))))))]))

(define (deref-args-instr? instr)
  (match instr
    [(Instr name (list (Deref reg1 n1) (Deref reg2 n2))) #t]
    [else #f]))

(define (patch-instr instr)
  (match instr
    [(Instr 'addq (list deref1 deref2))
     (list (Instr 'movq (list deref1 (Reg 'rax)))
           (Instr 'addq (list (Reg 'rax) deref2)))]
    [(Instr 'subq (list deref1 deref2))
     (list (Instr 'movq (list deref1 (Reg 'rax)))
           (Instr 'subq (list (Reg 'rax) deref2)))]
    [(Instr 'movq (list deref1 deref2))
     (list (Instr 'movq (list deref1 (Reg 'rax)))
           (Instr 'movq (list (Reg 'rax) deref2)))]))

; (define (patch-instr instr)
;   (match instr
;     [(Instr name args)
;      (if (deref-pair? args)
;          (patch-instr-arg instr)
;          (Instr name args))]
;     [(Callq label n) (Callq label n) ]
;     [(Retq) (Retq) ]
;     [(Jmp label) (Jmp label) ]
;     [else (error 'assign-instr)]))

(define (patch block)
  (match block
    [(Block info instrs)
     (Block info (let loop ([instrs instrs] [new-instrs '()])
                   (if (null? instrs)
                       (reverse new-instrs)
                       (if (deref-args-instr? (car instrs))
                           (let ([patched-instrs (patch-instr (car instrs))])
                             (loop (cdr instrs) (append (reverse patched-instrs) new-instrs)))
                           (loop (cdr instrs) (cons (car instrs) new-instrs))))))]
    [else (error "patch")]))

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (match p
    [(X86Program info label&blocks)
     (X86Program info (for/list ([label&block label&blocks])
                        (cons (car label&block)
                              (patch (cdr label&block)))))]))
; (error "TODO: code goes here (patch-instructions)"))

(define p (read-program "./examples/p4.example"))
(define p1 (uniquify p))
(define p2 (remove-complex-opera* p1))
(define p3 (explicate-control p2))
(define p4 (type-check-Cvar p3))
(define p5 (select-instructions p4))
(define p6  (assign-homes p5))
(define p7 (patch-instructions p6))

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
