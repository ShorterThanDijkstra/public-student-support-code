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
(require "priority_queue.rkt")
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

(define (pe-sub r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx- n1 n2))]
    [(_ _) (Prim '- (list r1 r2))]))

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

; store result in %rax
(define (insts-exp e)
  (match e
    [(Var x) (list (Instr 'movq (list (Var x) (Reg 'rax))))]
    [(Int n) (list (Instr 'movq (list (Imm n) (Reg 'rax))))]
    [(Prim 'read '())
     (list (Callq 'read_int 0))]
    [(Prim '- (list atm))
     (list (Instr 'movq (list (insts-atm atm) (Reg 'rax)))
           (Instr 'negq (list (Reg 'rax))))]
    [(Prim '+ (list atm1 atm2))
     (list (Instr 'movq (list (insts-atm atm1) (Reg 'rax)))
           (Instr 'addq (list (insts-atm atm2) (Reg 'rax))))]

    [(Prim '- (list atm1 atm2))
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
    [(Return e)
    ;  (displayln e)
    ;  (displayln (insts-exp e))
     (append (insts-exp e) (list (Jmp 'conclusion)))]
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
           (let ([top (if (null? homes) 0 (cdar homes))])
             (list (ceil-16(- top)) (reverse new-instrs)))
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
                  [block-infos '()]
                  [block-instrs '()]
                  [spaces '()])
         (if (null? label&blocks)
             (X86Program (append (list (cons 'stack-space spaces)) info)
                         (for/list ([label labels] [block-info block-infos] [instrs block-instrs])
                           (cons label (Block block-info instrs))))
             (let ([curr-label (caar label&blocks)]
                   [curr-block (cdar label&blocks)])
               ;  (displayln curr-label)
               ;  (displayln curr-block)
               (let ([res (assign-block curr-block locals-types)]
                     [block-info (Block-info curr-block)]
                     )
                 (let ([space (car res)]
                       [new-block-instrs (cadr res)])
                   (loop (cdr label&blocks)
                         (cons curr-label labels)
                         (cons block-info block-infos)
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

(define (prelude space)
  (Block '() (list (Instr 'pushq (list (Reg 'rbp)))
                   (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))
                   (Instr 'subq (list (Imm space) (Reg 'rsp)))
                   (Jmp 'start))))

(define (conclusion space)
  (Block '() (list (Instr 'addq (list (Imm space) (Reg 'rsp)))
                   (Instr 'popq (list (Reg 'rbp)))
                   (Retq))))

(define (prefix-underscore label)
  (string->symbol (string-append "_" (symbol->string label))))

(define (if-macosx-instr instr)
  (match instr
    [(Jmp label) (Jmp (prefix-underscore label))]
    [(Callq label n) (Callq (prefix-underscore label) n)]
    [else instr]))

(define (if-macosx-block block)
  (match block
    [(Block '() instrs)
     (Block '() (map if-macosx-instr instrs))]))


(define (if-macosx p)
  (if (eqv? (system-type 'os) 'macosx)
      (match p
        [(X86Program info label&blocks)
         (X86Program info (for/list ([label&block label&blocks])
                            (let ([label (car label&block)]
                                  [block (cdr label&block)])
                              (let ([new-label (prefix-underscore label)])
                                (cons new-label (if-macosx-block block))))))])
      p))
;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
  (match p
    [(X86Program info label&blocks)
     (let ([start-space (dict-ref (dict-ref info 'stack-space) 'start)])
       (if-macosx (X86Program info
                              (cons (cons 'main (prelude start-space))
                                    (append label&blocks
                                            (list (cons 'conclusion (conclusion start-space))))))))]))

; (define (pe-exp-lvar env e)
;   (match e
;     [(Var x) (dict-ref env x)]
;     [(Int n) (Int n)]
;     [(Let x rhs body)
;      (let ([e-val (pe-exp-lvar env rhs)])
;        (if (Int? e-val)
;            (let ([new-env (cons (cons x e-val) env)])
;              (pe-exp-lvar new-env body))
;            (Let x e-val (pe-exp-lvar env body))))]
;     [(Prim 'read '()) (Prim 'read '())]
;     [(Prim '- (list rand))
;      (let ([rand-val (pe-exp-lvar env rand)])
;        (pe-neg rand-val))]
;     [(Prim '- (list rand1 rand2))
;      (let ([rand1-val (pe-exp-lvar env rand1)]
;            [rand2-val (pe-exp-lvar env rand2)])
;        (pe-sub rand1-val rand2-val))]
;     [(Prim '+ (list rand1 rand2))
;      (let ([rand1-val (pe-exp-lvar env rand1)]
;            [rand2-val (pe-exp-lvar env rand2)])
;        (pe-add rand1-val rand2-val))]))

(define (pe-neg-res env r)
  (match r
    [(Int n) (Int (fx- 0 n))]
    [(Var x) (Int (fx- 0 (dict-ref env x)))]
    [else (Prim '- (list r))]))

(define (pe-add-res env r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [((Int n) (Var x) )  (Int (fx+ (dict-ref env x) n))]
    [((Int n) (Prim '- (Var x)) ) (Int (fx- (dict-ref env x) n))]
    [((Int n1) (Prim '+ (list (Int n2) inert))) (Prim '+ (list (Int (fx+ n1 n2)) inert))]
    [(inert (Int n)) (pe-add-res env (Int n) inert)]
    [(_ _) (Prim '+ (list r1 r2))]))

(define (add-res-trans e)
  (match e
    [(Prim '+ (list (Int n1) r2)) (Prim '+ (list (Int n1) (add-res-trans r2)))]
    [(Prim '+ (list r1 (Int n2))) (Prim '+ (list (Int n2) (add-res-trans r1)))]
    [(Prim '+ (list r1 r2)) (Prim '+ (list  (add-res-trans r1) (add-res-trans r2)))]
    [else e]))

(define (pe-sub-res env r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx- n1 n2))]
    [((Var x1) (Int n2)) (Int (fx- (dict-ref env x1) n2))]
    [((Int n1) (Var x2)) (Int (fx- n1 (dict-ref env x2)))]
    [((Var x1) (Var x2)) (Int (fx- (dict-ref env x1) (dict-ref env x2)))]
    [(_ _) (Prim '- (list r1 r2))]))

(define (pe-exp-lvar env e)
  (match e
    [(Var x) (dict-ref env x)]
    [(Int n) (Int n)]
    [(Let x rhs body)
     (let ([e-val (pe-exp-lvar env rhs)])
       (if (Int? e-val)
           (let ([new-env (cons (cons x e-val) env)])
             (pe-exp-lvar new-env body))
           (Let x e-val (pe-exp-lvar env body))))]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list rand))
     (let ([rand-val (pe-exp-lvar env rand)])
       (pe-neg-res env rand-val))]
    [(Prim '- (list rand1 rand2))
     (let ([rand1-val (pe-exp-lvar env rand1)]
           [rand2-val (pe-exp-lvar env rand2)])
       (pe-sub-res env rand1-val rand2-val))]
    [(Prim '+ (list rand1 rand2))
     (let ([rand1-val (pe-exp-lvar env rand1)]
           [rand2-val (pe-exp-lvar env rand2)])
       (pe-add-res env rand1-val rand2-val))]))

(define (pe-Lvar p)
  (match p
    [(Program '() e) (Program '() (pe-exp-lvar '() e))]))

(define caller-saved
  '(rax rcx rdx rsi rdi r8 r9 r10 r11))

(define callee-saved
  '(rsp rbp rbx r12 r13 r14 r15))

(define argument-pass
  '(rdi rsi rdx rcx r8 r9))

(define (live-arg arg)
  (match arg
    [(Imm n) (set)]
    [(Reg reg) (set reg)]
    [(Deref reg int) (set reg)]
    [(Var x) (set x)]))

(define (read-instr instr)
  (match instr
    [(Instr 'addq (list arg1 arg2))
     (set-union (live-arg arg1) (live-arg arg2))]
    [(Instr 'subq (list arg1 arg2))
     (set-union (live-arg arg1) (live-arg arg2))]
    [(Instr 'negq (list arg1)) (live-arg arg1)]
    [(Instr 'movq (list arg1 arg2)) (live-arg arg1)]
    [(Instr 'pushq (list arg1)) (live-arg arg1)]
    [(Instr 'popq (list arg1)) (set)]
    [(Callq label n) (list->set (take argument-pass n))]
    [(Jmp 'conclusion) (set 'rax 'rsp)] ;todo
    ))

(define (write-instr instr)
  (match instr
    [(Instr 'addq (list arg1 arg2))
     (live-arg arg2)]
    [(Instr 'subq (list arg1 arg2))
     (live-arg arg2)]
    [(Instr 'negq (list arg1)) (live-arg arg1)]
    [(Instr 'movq (list arg1 arg2)) (live-arg arg2)]
    [(Instr 'pushq (list arg1)) (set)]
    [(Instr 'popq (list arg1)) (live-arg arg1)]
    [(Callq label n) (list->set caller-save)]
    [(Jmp 'conclusion) (set 'rbp)] ;todo
    ))

(define (live-instr instr live-after)
  (let ([reads (read-instr instr)]
        [writes (write-instr instr)])
    (set-union (set-subtract live-after writes) reads)))

(define (live-block block)
  (match block
    [(Block info instrs)
     (let loop ([instrs-rev (reverse instrs)]
                [lives '()]
                [live-after (set)])
       (if (null? instrs-rev)
           (Block (append (list (cons 'lives lives)) info) instrs)
           (let ([new-live-after (live-instr (first instrs-rev) live-after)])
             ;  (displayln new-live-after)
             (loop (rest instrs-rev) (cons new-live-after lives) new-live-after))))]))

;;;x86-var -> x86-var
(define (uncover-live p)
  (match p
    [(X86Program info label&blocks)
     (let ([labels (map car label&blocks)]
           [blocks (map cdr label&blocks)])
       (X86Program info (map (lambda (label block) (cons label block)) labels (map live-block blocks))))]))

(define (link g s d)
  (begin (add-edge! g s d) g))

(define (mov-interfence s d after g)
  (let loop ([after  after]
             [g g])
    (if (null? after)
        g
        (let ([v (first after)])
          (if (or (eqv? s v) (eqv? d v))
              (loop (rest after) g)
              (loop (rest after) (link g v d)))))))

(define (other-interfence writes after g)
  (if (null? writes)
      g
      (let ([d (first writes)])
        (let loop ([after-iter after] [g g])
          (if (null? after-iter)
              (other-interfence (cdr writes) after g)
              (let ([v (first after-iter)])
                (if (eqv? v d)
                    (loop (rest after-iter) g)
                    (loop (rest after-iter) (link g v d)))))))))

(define (mov-arg-sym arg)
  (match arg
    [(Imm n) '()]
    [(Reg reg)  reg]
    [(Deref reg int) '()]
    [(Var x) x]))

(define (live-instr-interfence after instr g)
  (match instr
    [(Instr 'movq (list arg1 arg2))
     (mov-interfence (mov-arg-sym arg1) (mov-arg-sym arg2) (set->list after) g)]
    [else (let ([writes (write-instr instr)])
            (other-interfence (set->list writes) (set->list after) g))]
    ))

(define (block-interfence block)
  (match block
    [(Block info instrs)
     (let ([lives (dict-ref info 'lives)]
           [g (undirected-graph (append caller-saved callee-saved argument-pass))])
       (let loop ([lives (rest lives)]
                  [instrs instrs]
                  [g g])
         (if (null? lives)
             g
             (loop (rest lives) (rest instrs) (live-instr-interfence (first lives) (first instrs) g)))))]))

;x86_var -> x86_var
(define (build-interference p)
  (match p
    [(X86Program info label&blocks)
     (let ([labels (map car label&blocks)]
           [blocks (map cdr label&blocks)])
       (let ([conflicts (map block-interfence blocks)])
         (let ([new-info (append (list (cons 'conflicts (map cons labels conflicts))) info)])
           (X86Program new-info label&blocks))))]))


(define (graph-of-program-start p)
  (match p
    [(X86Program info body)
     (dict-ref (dict-ref info 'conflicts) 'start)]))

(struct Vertex (name color staturation) #:transparent #:mutable)

(define (put-staturation-vertex! vertex s)
  (match vertex
    [(Vertex color name staturation)
     (let ([new-staturation (if (member s staturation) staturation (cons s staturation))])
       (begin
         (set-Vertex-staturation! vertex new-staturation)
         vertex))]))

(define the-reg-color-map
  '((rcx . 0) (rdx . 1) (rsi . 2) (rdi . 3) (r8 . 4) (r9 . 5)
              (r10 . 6) (rbx . 7) (r12 . 8) (r13 . 9) (r14 . 10)
              (rax . -1) (rsp . -2) (rbp . -3) (r11 . -4) (r15 . -5)))

(define (reg-of-the-reg-color-map color)
  (let loop ([reg-color-map the-reg-color-map])
    (if (null? reg-color-map)
        (error 'reg-of-the-reg-color-map)
        (let ([reg (car (first reg-color-map))] [reg-color (cdr (first reg-color-map))])
          (if (= reg-color color)
              reg
              (loop (rest reg-color-map)))))))

(define (every? pred lst)
  (if (null? lst)
      #t
      (and (pred (first lst))
           (every? pred (rest lst)))))

(define (color-graph g vars)
  (define NOCOLOR '-)
  (define (cmp v1 v2)
    (let ([len1 (length (Vertex-staturation v1))]
          [len2 (length (Vertex-staturation v2))])
      (if (= len1 len2)
          (symbol<? (Vertex-name v1) (Vertex-name v2))
          (> len1 len2))))

  (define (update-queue! que handle-map vertex)
    (let ([name (Vertex-name vertex)])
      (let ([handle (dict-ref handle-map name #f)])
        (if handle
            (pqueue-decrease-key! que handle)
            'void))))

  (define (fill-staturation-vertex! vertex-sym neighbors vertex-map handle-map que)
    (let ([vertex (dict-ref vertex-map vertex-sym)])
      (let loop ([neighbors neighbors])
        (if (null? neighbors)
            'void
            (let ([neighbor (first neighbors)])
              (let ([neighbor-vertex (dict-ref vertex-map neighbor)])
                (let ([neighbor-color (Vertex-color neighbor-vertex)])
                  (if (eqv? neighbor-color NOCOLOR)
                      (loop (rest neighbors))
                      (begin
                        (put-staturation-vertex! vertex neighbor-color)
                        (update-queue! que handle-map vertex)
                        (loop (rest neighbors)))))))))))

  (define (fill-staturation-graph! g vars vertex-map handle-map que)
    (for/list ([var vars])
      (let ([neighbors (sequence->list (in-neighbors g var))])
        (fill-staturation-vertex! var neighbors vertex-map handle-map que))))

  (define (init!)
    (let ([que (make-pqueue cmp)]) ; 存放未着色节点
      (let loop ([vs vars] [vertex-map '()] [handle-map '()])
        (if (null? vs)
            (begin (fill-staturation-graph! g vars vertex-map handle-map que) (values que vertex-map handle-map))
            (let ([color (dict-ref the-reg-color-map (first vs) NOCOLOR)])
              (let ([vertex (Vertex (first vs) color '())])
                (if (eqv? color NOCOLOR)
                    (let ([handle  (pqueue-push! que vertex)])
                      (loop (rest vs)
                            (cons (cons (first vs) vertex) vertex-map)
                            (cons (cons (first vs) handle) handle-map)))
                    (loop (rest vs)
                          (cons (cons (first vs) vertex) vertex-map)
                          handle-map))))))))

  (define (next-color staturation)
    (let loop ([color 0])
      ; (display color)
      (if (member color staturation)
          (loop (+ color 1))
          color)))

  (define (update-neighbors-staturation! vertex vertex-map handle-map que)
    ; (displayln vertex-map)
    (match vertex
      [(Vertex name color staturation)
       (let loop ([neighbors (sequence->list (in-neighbors g name))])
         (if (null? neighbors)
             'void
             (let ([neighbor (first neighbors)])
               (let ([neighbor-vertex (dict-ref vertex-map neighbor)])
                 (begin
                   (put-staturation-vertex! neighbor-vertex color)
                   (update-queue! que handle-map neighbor-vertex)
                   (loop  (rest neighbors)))))))]))

  ; dsatur 算法：给某个结点染色，更新邻结点的saturation，更新后的邻结点可能会产生冲突吗？
  ; 不会，所以不需要这个方法
  ; (define (check-neighbors vertex vertex-map)
  ;   ; (displayln vertex-map)
  ;   (define (check-1 vertex) ; 1层neighbor检查
  ;     (match vertex
  ;       [(Vertex name color staturation)
  ;        (let loop ([neighbors (sequence->list (in-neighbors g name))])
  ;          (if (null? neighbors)
  ;              #t
  ;              (let ([neighbor-vertex (dict-ref vertex-map (first neighbors))])
  ;                (and (not (member (Vertex-color neighbor-vertex) (Vertex-staturation neighbor-vertex)))
  ;                     (loop (rest neighbors))))))]))
  ;   (let ([neighbors (sequence->list (in-neighbors g (Vertex-name vertex)))])
  ;     (every? check-1 (map (lambda (v) (dict-ref vertex-map v)) neighbors))))

  (define (dsatur-color! que vertex-map handle-map)
    (if (zero? (pqueue-count que))
        vertex-map
        (let ([vertex (pqueue-pop! que)])
          (match vertex
            [(Vertex name color staturation)
             (if (not (eqv? color NOCOLOR))
                 (error 'dsatur-color!)
                 (let ([new-color (next-color staturation)])
                   (begin
                     (set-Vertex-color! vertex new-color)
                     (update-neighbors-staturation! vertex vertex-map handle-map que)
                     (dsatur-color! que vertex-map handle-map))))])))) ; what if fail to color graph?

  (define-values (que vertex-map handle-map) (init!))

  (let ([vertex-map (dsatur-color! que vertex-map handle-map)])
    (let loop ([vertex-map vertex-map] [color-map '()])
      (if (null? vertex-map)
          color-map
          (let ([var (car (first vertex-map))]
                [color (Vertex-color (cdr (first vertex-map)))])
            (loop (rest vertex-map) (cons (cons var color) color-map))))))
  )


(define (vars-in-graph g)
  (filter (lambda (v) (> (length (sequence->list (in-neighbors g v))) 0))
          (sequence->list (in-vertices g))))

(define (allocate-registers p)
  (define (build-var-map color-map reg-avaliable)
    (let loop ([color-map color-map] [var-map '()])
      (if (null? color-map)
          var-map
          (let ([var (car (first color-map))]
                [color (cdr (first color-map))])
            (let ([location (if (< color reg-avaliable)
                                (Reg (reg-of-the-reg-color-map color))
                                (let ([offset (* (- (+ color 1) reg-avaliable) -8)]) ; todo: other types
                                  (Deref 'rbp offset)))])
              (loop (rest color-map) (cons (cons var location) var-map)))))))

  (define (assign-arg arg var-map)
    (match arg
      [(Var name) (dict-ref var-map name)]
      [(Imm n) (Imm n)]
      [(Reg name) (Reg name)]
      [(Deref reg offset) (Deref reg offset)]))

  (define (assign-instr instr var-map)
    (match instr
      [(Instr name args)
       (Instr name (map (lambda (arg) (assign-arg arg var-map)) args))]
      [else instr]))

  (define (assign-location block var-map)
    (match block
      [(Block info instrs)
       (Block info (map (lambda (instr) (assign-instr instr var-map)) instrs))]))

  (define (allocate-reg-start-body var-map body)
    (let ([labels (map car body)] [blocks (map cdr body)])
      (for/list ([label labels] [block blocks])
        (if (eqv? label 'start)
            (cons label (assign-location block var-map))
            (cons label block)))))

  (match p
    [(X86Program info body)
     (let* ([g-start (dict-ref (dict-ref info 'conflicts) 'start)]
            [vars (vars-in-graph g-start)]
            [color-map (color-graph g-start vars)]
            [var-map (build-var-map color-map 1)]
            [new-body (allocate-reg-start-body var-map body)])
       (X86Program info new-body))]))


; (define p (read-program "./examples/p9.example"))
; ; (define p0 (pe-Lvar p))
; (define p0 p)
; ; (define p1 (uniquify p0))
; (define p1 p0)
; (define p2 (remove-complex-opera* p1))
; (define p3 (explicate-control p2))
; (define p4 (type-check-Cvar p3))
; (define p5 (select-instructions p4))
; (define p6 (uncover-live p5))
; (define p7  (assign-homes p6))
; (define p8 (patch-instructions p7))
; (define p9 (prelude-and-conclusion p8))
; (display (print-x86 p9))


;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( ("partial eval" ,pe-Lvar ,interp-Lvar ,type-check-Lvar)
     ("uniquify" ,uniquify ,interp-Lvar ,type-check-Lvar)
     ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
     ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
     ("instruction selection" ,select-instructions ,interp-pseudo-x86-0)
     ("assign homes" ,assign-homes ,interp-x86-0)
     ("patch instructions" ,patch-instructions ,interp-x86-0)
     ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))
