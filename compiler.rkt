#lang racket
(require racket/set racket/stream)
(require graph)
(require racket/promise)
(require "multigraph.rkt")
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
       (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Bool b) (Bool b)]
      [(Let x e body)
       (let ([new_x (gen-sym x)])
         (let ([new_env (dict-set env x new_x)])
           (Let new_x
                ((uniquify-exp env) e)
                ((uniquify-exp new_env) body))))]
      [(If cnd thn els)
       (If ((uniquify-exp env) cnd)
           ((uniquify-exp env) thn)
           ((uniquify-exp env) els))]
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
    [(Bool b) (Bool b)]
    [(Let x e body)
     (Let x
          (rco-exp e)
          (rco-exp body))]
    [(If cnd thn els)
     (If (rco-exp cnd)
         (rco-exp thn)
         (rco-exp els))]
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

(define basic-blocks 'UNINTIATED)

(define (init-basic-blocks!)
  (set! basic-blocks '()))

; (define (create-block tail)
;   (match tail
;     [(Goto label) (Goto label)]
;     [else
;      (let ([label (gensym 'block)])
;        (set! basic-blocks (cons (cons label tail) basic-blocks))
;        (Goto label))]))

;;; 默认参数和输出都是promise,当需要构建ast时，force
(define (create-block tail)
  (delay
    (define t (forces tail))
    (match t
      [(Goto label) (Goto label)]
      [else
       (let ([label (gensym 'block)])
         (set! basic-blocks (cons (cons label t) basic-blocks))
         (Goto label))])))

(define (explicate-pred cnd thn els)
  (delay
    (match (forces cnd)
      [(Var x)
       (let ([thn-goto (forces (create-block thn))]
             [els-goto (forces (create-block els))])
         ;  (IfStmt cnd thn-goto els-goto))] ;;; pred must be a Prim of cmp
         (IfStmt (Prim 'eq? (list (Var x) (Bool #t))) thn-goto els-goto))]
      [(Let x rhs body)
       (explicate-assign rhs x
                         (explicate-pred body thn els))]
      [(Prim 'not (list e)) (explicate-pred e els thn)]
      [(Prim op es) #:when (or (eq? op 'eq?) (eq? op '<)
                               (eq? op '<=) (eq? op '>) (eq? op '>=))
                    (IfStmt (Prim op es)
                            (forces (create-block thn))
                            (forces (create-block els)))]
      [(Bool b) (if b thn els)]
      [(If cnd^ thn^ els^)
       (let ([thn-goto (create-block thn)]
             [els-goto (create-block els)])
         (let ([thn^-goto (create-block (explicate-pred thn^ thn-goto els-goto))]
               [els^-goto  (create-block (explicate-pred els^ thn-goto els-goto))])
           (explicate-pred cnd^ thn^-goto els^-goto)))]
      [else (error "explicate-pred unhandled case" cnd)])))

(define (explicate-tail e)
  (delay
    (match (forces e)
      [(Var x) (Return (forces e))]
      [(Int n) (Return (forces e))]
      [(Bool b) (Return (forces e))]
      [(Prim op es) (Return (forces e))]
      [(Let x rhs body) (explicate-assign rhs x (explicate-tail body))]
      [(If cnd thn els) (explicate-pred cnd (explicate-tail thn) (explicate-tail els))]
      [else (error "explicate-tail unhandled case" e)])))

(define (explicate-assign e x cont)
  (delay
    (match (forces e)
      [(Var x) (Seq (Assign (Var x) e) (forces cont))]
      [(Int n) (Seq (Assign (Var x) e) (forces cont))]
      [(Bool n) (Seq (Assign (Var x) e) (forces cont))]
      [(Prim op es)  (Seq (Assign (Var x) e) (forces cont))]
      [(Let y rhs body) (explicate-assign rhs y (explicate-assign body x cont))]
      [(If cnd thn els) (let ([new-thn (explicate-assign thn x cont)]
                              [new-els (explicate-assign els x cont)])
                          (explicate-pred cnd new-thn new-els))]
      [else (error "explicate-assign unhandled case" e)])))

(define (forces p)
  (if (promise? p)
      (forces (force p))
      p))

; ;; explicate-control : R1 -> C0
(define (explicate-control p)
  (init-basic-blocks!)
  (match p [(Program info body)
            (let ([blocks (forces (explicate-tail body))])
                  (CProgram info (cons (cons 'start blocks) basic-blocks)))]))
;   (error "TODO: code goes here (explicate-control)"))

(define (insts-atm c-var-ele)
  (match c-var-ele
    [(Int n)  (Imm n)]
    [(Var x) (Var x)]
    [(Bool n) (if n (Imm 1) (Imm 0))]
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
    [(Bool b) (list (Instr 'movq (list (Imm 1) (Reg 'rax))))]
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
    [(Prim 'not (list atm1))
     (let ([arg1 (insts-atm atm1)])
       (list (Instr 'movq (list arg1 (Reg 'rax)))
             (Instr 'xorq (list (Imm 1) (Reg 'rax)))))]
    [(Prim 'eq? (list atm1 atm2))
     (instr-prim-cmp atm1 atm2 'e (Reg 'rax))]
    [(Prim '< (list atm1 atm2))
     (instr-prim-cmp atm1 atm2 'l (Reg 'rax))]
    [(Prim '<= (list atm1 atm2))
     (instr-prim-cmp atm1 atm2 'le (Reg 'rax))]
    [(Prim '> (list atm1 atm2))
     (instr-prim-cmp atm1 atm2 'g (Reg 'rax))]
    [(Prim '>= (list atm1 atm2))
     (instr-prim-cmp atm1 atm2 'ge (Reg 'rax))]
    [else (error 'insts-exp)]))

(define (instr-prim-cmp atm1 atm2 cc to)
  (let ([arg1 (insts-atm atm1)]
        [arg2 (insts-atm atm2)])
    (list (Instr 'cmpq (list arg2 arg1))
          (Instr 'set (list cc (ByteReg 'al)))
          (Instr 'movzbq (list (ByteReg 'al) to)))))

(define (insts-stmt c-var-ele)
  (match c-var-ele
    [(Assign (Var x) e)
     (match e
       [(Var x1)
        (list (Instr 'movq (list (Var x1) (Var x))))]
       [(Int n)
        (list (Instr 'movq (list (Imm n) (Var x))))]
       [(Bool b)
        (list (Instr 'movq (list (Imm 1) (Var x))))]
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
                  (Instr 'subq (list (insts-atm atm2) (Var x)))))]
       [(Prim 'not (list atm1))
        (match atm1
          [(Var sym) #:when (eqv? sym x)
                     (list (Instr 'xnorq (list (Imm 1) (Var sym))))]
          [else (let ([arg1 (insts-atm atm1)])
                  (list (Instr 'movq (list arg1 (Var x)))
                        (Instr 'xorq (list (Imm 1) (Var x)))))])]
       [(Prim 'eq? (list atm1 atm2))
        (instr-prim-cmp atm1 atm2 'e (Var x))]
       [(Prim '< (list atm1 atm2))
        (instr-prim-cmp atm1 atm2 'l (Var x))]
       [(Prim '<= (list atm1 atm2))
        (instr-prim-cmp atm1 atm2 'le (Var x))]
       [(Prim '> (list atm1 atm2))
        (instr-prim-cmp atm1 atm2 'g (Var x))]
       [(Prim '>= (list atm1 atm2))
        (instr-prim-cmp atm1 atm2 'ge (Var x))])]
    [else (error 'insts-stmt)]))

(define (instr-tail-prim-cmp atm1 atm2 thn-label els-label cmp)
  (define (build arg1 arg2 cc)
    (list (Instr 'cmpq (list arg2 arg1))
          (JmpIf cc thn-label)
          (Jmp els-label)))
  (define (cmp->cc)
    (match cmp
      ['eq? 'e]
      ['< 'l]
      ['<= 'le]
      ['> 'g]
      ['>= 'ge]))
  (let ([arg1 (insts-atm atm1)]
        [arg2 (insts-atm atm2)])
    (build arg1 arg2 (cmp->cc))))

(define (insts-tail c-var-ele)
  (match c-var-ele
    [(Return e)
     ;  (displayln e)
     ;  (displayln (insts-exp e))
     (append (insts-exp e) (list (Jmp 'conclusion)))]
    [(Goto label) (list (Jmp label))]
    [(IfStmt (Prim cmp (list atm1 atm2)) (Goto thn-label) (Goto els-label))
     (instr-tail-prim-cmp atm1 atm2 thn-label els-label cmp)]
    [(Seq stmt tail) (append (insts-stmt stmt) (insts-tail tail))]
    [else (error 'insts-tail)]))

(define (insts c-var-ele)
  (match c-var-ele
    [(Int n) (insts-atm c-var-ele)]
    [(Var x) (insts-atm c-var-ele)]
    [(Bool b) (insts-atm c-var-ele)]
    [(Prim op es) (insts-exp c-var-ele)]
    [(Assign (Var x) e) (insts-stmt  c-var-ele)]
    [(Return e) (insts-tail c-var-ele)]
    [(Goto label) (insts-tail c-var-ele)]
    [(IfStmt pred thn els)
     (insts-tail c-var-ele)]
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
    [(ByteReg reg) (ByteReg reg)]
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
    [(JmpIf cc label) (list (JmpIf cc label) homes)]
    [else (error 'assign-instr)]))

(define (align16 n)
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
             (list (align16(- top)) (reverse new-instrs)))
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
    [(Instr 'movq (list (Deref reg1 n1) (Deref reg2 n2))) #t]
    [(Instr 'movzbq (list (Deref reg1 n1) (Deref reg2 n2))) #t]
    [else #f]))

(define (arg-equal? arg1 arg2)
  (match* (arg1 arg2)
    [((Var name1) (Var name2)) (eqv? name1 name2)]
    [((Reg name1) (Reg name2)) (eqv? name1 name2)]
    [((Imm n1) (Imm n2)) (eqv? n1 n2)]
    [((Deref name1 offset1) (Deref name2 offset2)) (and (eqv? name1 name2)
                                                        (eqv? offset1 offset2))]
    [(_ _) #f]))

(define (trival-mov? instr)
  (match instr
    [(Instr name (list arg1 arg2))
     (arg-equal? arg1 arg2)]
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
           (Instr 'movq (list (Reg 'rax) deref2)))]
    [(Instr 'movzbq (list deref1 deref2))
     (list (Instr 'movzbq (list deref1 (Reg 'rax)))
           (Instr 'movq (list (Reg 'rax) deref2)))]
    [(Instr 'cmpq (list deref1 deref2))
     (list (Instr 'movq (list deref1 (Reg 'rax)))
           (Instr 'cmpq (list (Reg 'rax) deref2)))]
    [else (error 'patch-instr)]))

(define (problematic-cmpq? instr)
  (match instr
    [(Instr 'cmpq (list arg1 (Imm n2))) #t]
    [else #f]))

(define (patch-problematic-cmpq instr)
  (match instr
    [(Instr 'cmpq (list arg1 (Imm n2)))
     (list (Instr 'movq (list (Imm n2) (Reg 'rax)))
           (Instr 'cmpq (list arg1 (Reg 'rax))))]
    [else (error 'patch-problematic-cmpq)]))
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
                       (cond [(trival-mov? (first instrs))
                              (loop (rest instrs) new-instrs)]
                             [(deref-args-instr? (first instrs))
                              (let ([patched-instrs (patch-instr (first instrs))])
                                (loop (rest instrs) (append (reverse patched-instrs) new-instrs)))]
                             [(problematic-cmpq? (first instrs))
                              (let ([patched-instrs (patch-problematic-cmpq (first instrs))])
                                (loop (rest instrs) (append (reverse patched-instrs) new-instrs)))]
                             [else (loop (rest instrs) (cons (first instrs) new-instrs))]))))]
    [else (error "patch")]))

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (match p
    [(X86Program info label&blocks)
     (X86Program info (for/list ([label&block label&blocks])
                        (cons (car label&block)
                              (patch (cdr label&block)))))]))
; (error "TODO: code goes here (patch-instructions)"))
(define (prelude used-callee frame-sub)
  (Block '() (append (list (Instr 'pushq (list (Reg 'rbp)))
                           (Instr 'movq (list (Reg 'rsp) (Reg 'rbp))))
                     (append (map (lambda (reg) (Instr 'pushq (list (Reg reg)))) used-callee)
                             (list (Instr 'subq (list (Imm frame-sub) (Reg 'rsp)))
                                   (Jmp 'start))))))

(define (conclusion used-callee frame-sub)
  (Block '() (cons (Instr 'addq (list (Imm frame-sub) (Reg 'rsp)))
                   (append (map (lambda (reg) (Instr 'popq (list (Reg reg)))) used-callee)
                           (list (Instr 'popq (list (Reg 'rbp)))
                                 (Retq))))))

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
; (define (prelude-and-conclusion p)
;   (match p
;     [(X86Program info label&blocks)
;      (let ([start-space (dict-ref (dict-ref info 'stack-space) 'start)])
;        (if-macosx (X86Program info
;                               (cons (cons 'main (prelude start-space))
;                                     (append label&blocks
;                                             (list (cons 'conclusion (conclusion start-space))))))))]))

(define (re-offset-instr instr used-callee-space)

  (define (re-offset-arg arg)
    (match arg
      [(Deref reg offset) (Deref reg (- offset used-callee-space))]
      [else arg]))

  (match instr
    [(Instr name args)
     (Instr name (map re-offset-arg args))]
    [else instr]))

(define (re-offset-start label&blocks used-callee-space)
  (let ([labels (map car label&blocks)] [blocks (map cdr label&blocks)])
    (for/list ([label labels] [block blocks])
      (if (eqv? label 'start)
          (cons label (match block
                        [(Block info instrs)
                         (Block info
                                (map (lambda (instr) (re-offset-instr instr used-callee-space))
                                     instrs))]))
          (cons label block)))))

(define (prelude-and-conclusion p)
  (match p
    [(X86Program info label&blocks)
     (let ([used-callee (dict-ref info 'used-callee)] [spill-space (dict-ref info 'spill-space)])
       (let ([used-callee-space (* 8 (length used-callee))])
         (let ([frame-sub (- (align16 (+ used-callee-space spill-space)) used-callee-space)])
           (if-macosx (X86Program info
                                  (cons (cons 'main (prelude used-callee frame-sub))
                                        (append (re-offset-start label&blocks used-callee-space)
                                                (list (cons 'conclusion (conclusion used-callee frame-sub))))))))))]))

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

(define label->live 'UNINITIATED)

(define (init-labeo->live!)
  (set!  label->live (list (cons 'conclusion (set 'rax 'rsp)))))

(define (live-arg arg)
  (match arg
    [(Imm n) (set)]
    [(Reg reg) (set reg)]
    [(Deref reg int) (set reg)]
    [(Var x) (set x)]
    [(Bool n) (set)]
    [(ByteReg reg) (set reg)]))

(define (read-instr instr)
  (match instr
    [(Instr 'addq (list arg1 arg2))
     (set-union (live-arg arg1) (live-arg arg2))]
    [(Instr 'subq (list arg1 arg2))
     (set-union (live-arg arg1) (live-arg arg2))]
    [(Instr 'negq (list arg1)) (live-arg arg1)]
    [(Instr 'movq (list arg1 arg2)) (live-arg arg1)]
    [(Instr 'xorq (list arg1 arg2))
     (set-union (live-arg arg1) (live-arg arg2))]
    [(Instr 'cmpq (list arg1 arg2))
     (set-union (live-arg arg1) (live-arg arg2))]
    [(Instr 'set (list cc arg2))
     (set)]
    [(Instr 'movzbq (list arg1 arg2))
     (live-arg arg1)]
    [(Instr 'pushq (list arg1)) (live-arg arg1)]
    [(Instr 'popq (list arg1)) (set)]
    [(Callq label n) (list->set (take argument-pass n))]
    [(Jmp label) (set)]
    [(JmpIf cc label) (set)]
    ))

(define (write-instr instr)
  (match instr
    [(Instr 'addq (list arg1 arg2))
     (live-arg arg2)]
    [(Instr 'subq (list arg1 arg2))
     (live-arg arg2)]
    [(Instr 'negq (list arg1)) (live-arg arg1)]
    [(Instr 'movq (list arg1 arg2)) (live-arg arg2)]
    [(Instr 'xorq (list arg1 arg2))
     (live-arg arg2)]
    [(Instr 'cmpq (list arg1 arg2))
     (set)]
    [(Instr 'set (list cc arg2))
     (live-arg arg2)]
    [(Instr 'movzbq (list arg1 arg2))
     (live-arg arg2)]
    [(Instr 'pushq (list arg1)) (set)]
    [(Instr 'popq (list arg1)) (live-arg arg1)]
    [(Callq label n) (list->set caller-save)]
    [(Jmp label) (set)]
    [(JmpIf cc label) (set)]
    ))

; (define (live-instr instr live-after)
;   (let ([reads (read-instr instr)]
;         [writes (write-instr instr)])
;     (set-union (set-subtract live-after writes) reads)))

(define (live-instr instr pre live-after)
  (match instr
    [(Jmp label) (set-union (dict-ref label->live label) live-after)]
    [(JmpIf cc label)
     (begin (assert #t (Jmp? pre))
            (set-union (dict-ref label->live label) live-after))]
    [else
     (let ([reads (read-instr instr)]
           [writes (write-instr instr)])
       (set-union (set-subtract live-after writes) reads))]))

(define (live-block label block)
  (match block
    [(Block info instrs)
     (let loop ([instrs-rev (reverse instrs)]
                [lives '()]
                [live-after (set)]
                [pre #f])
       (if (null? instrs-rev)
           (begin
             (set! label->live (cons (cons label live-after) label->live))
             (Block (append (list (cons 'lives lives)) info) instrs))
           (let ([new-live-after (live-instr (first instrs-rev) pre live-after)])
             (loop (rest instrs-rev)
                   (cons new-live-after lives)
                   new-live-after
                   (first instrs-rev)
                   ))))]))

(define (build-cfg-body label&blocks)
  (define (init-cfg)
    (let ([cfg (make-multigraph '())])
      (let ([labels (map car label&blocks)])
        (begin (for ([label labels])
                 (add-vertex! cfg label))
               cfg))))

  (define (successors-instr instr)
    (match instr
      [(Jmp label) label]
      [(JmpIf cc label) label]
      [else #f]))
  (define (successors block)
    (match block
      [(Block info instrs)
       (foldl (lambda (instr succs) (let ([succ (successors-instr instr)])
                                      (if (and succ (not (member succ succs)))
                                          (cons succ succs)
                                          succs)))
              '()
              instrs)]))

  (let ([cfg (init-cfg)])
    (let ([labels (map car label&blocks)]
          [blocks (map cdr label&blocks)])
      (begin
        (for ([label labels] [block blocks])
          (let ([succs (successors block)])
            (for ([succ succs])
              (add-directed-edge! cfg label succ))))
        cfg))))

(define (build-cfg p)
  (match p
    [(X86Program info body)
     (build-cfg-body body)]))

;;;x86-var -> x86-var
(define (uncover-live p)
  (init-labeo->live!)
  (match p
    [(X86Program info label&blocks)
     (let ([labels (map car label&blocks)]
           [blocks (map cdr label&blocks)])
       (X86Program info
                   (let* ([cfg (build-cfg-body label&blocks)]
                          [cfg^t (transpose cfg)]
                          [order (tsort cfg^t)])
                     (begin
                       (assert #t (eqv? (first order) 'conclusion))
                       (for/list ([label (rest order)])
                         (let ([block (dict-ref label&blocks label)])
                           (cons label (live-block label block))))))))]))

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
    [(ByteReg reg) reg]
    [(Deref reg int) '()]
    [(Var x) x]))

(define (live-instr-interfence after instr g)
  (match instr
    [(Instr 'movq (list arg1 arg2))
     (mov-interfence (mov-arg-sym arg1) (mov-arg-sym arg2) (set->list after) g)]
    [(Instr 'movzbq (list arg1 arg2))
     (mov-interfence (mov-arg-sym arg1) (mov-arg-sym arg2) (set->list after) g)]
    [else (let ([writes (write-instr instr)])
            (other-interfence (set->list writes) (set->list after) g))]
    ))

(define (block-interfence block g)
  (match block
    [(Block info instrs)
     (let ([lives (dict-ref info 'lives)])
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
     (let loop ([blocks (map cdr label&blocks)]
                [g (undirected-graph (append caller-saved callee-saved argument-pass))])
       (if (null? blocks)
           (let ([new-info (append (list (cons 'conflicts g)) info)])
             (X86Program new-info label&blocks))
           (loop (rest blocks)
                 (block-interfence (first blocks) g))))]))

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

;;; for test, page 50
; (define the-reg-color-map
;   '((rcx . 0) (rbx . 1)
;               (rax . -1) (rsp . -2) (rbp . -3) (r11 . -4) (r15 . -5)))

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


(define (color-graph g vars program)
  (define NOCOLOR '-)
  (define (make-cmp move-related-graph)
    (lambda (v1 v2)
      (let ([len1 (length (Vertex-staturation v1))]
            [len2 (length (Vertex-staturation v2))])
        (if (= len1 len2)
            (let ([name1 (Vertex-name v1)] [name2 (Vertex-name v2)])
              (let ([neighbors-move-related-v1
                     (if (has-vertex? move-related-graph name1)
                         (sequence->list (in-neighbors move-related-graph name1))
                         '())]
                    [neighbors-move-related-v2
                     (if (has-vertex? move-related-graph name2)
                         (sequence->list (in-neighbors move-related-graph name2))
                         '())])
                (let ([related-len1 (length neighbors-move-related-v1)]
                      [related-len2 (length neighbors-move-related-v2)])
                  (if (= related-len1 related-len2)
                      (symbol<? name1 name2) ; text book
                      (> related-len1 related-len2)))))
            (> len1 len2)))))

  (define (build-move-related-graph)
    (define (loop-block-instrs block)
      (let loop ([edges '()] [instrs (Block-instr* block)]) ; todo
        (if (null? instrs)
            edges
            (let ([instr (first instrs)])
              (match instr
                [(Instr 'movq (list (Var name1) (Var name2)))
                 (loop (cons (list name1 name2) edges) (rest instrs))]
                [else (loop edges (rest instrs))])))))
    (match program
      [(X86Program info body)
       (undirected-graph (flatten (map loop-block-instrs (map cdr body))))]))

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
    (let ([move-related-graph (build-move-related-graph)])
      ; (displayln (graphviz move-related-graph))
      (let ([que (make-pqueue (make-cmp move-related-graph))]) ; 存放未着色节点
        (let loop ([vs vars] [vertex-map '()] [handle-map '()])
          (if (null? vs)
              (begin (fill-staturation-graph! g vars vertex-map handle-map que)
                     (values que vertex-map handle-map move-related-graph))
              (let ([color (dict-ref the-reg-color-map (first vs) NOCOLOR)])
                (let ([vertex (Vertex (first vs) color '())])
                  (if (eqv? color NOCOLOR)
                      (let ([handle  (pqueue-push! que vertex)])
                        (loop (rest vs)
                              (cons (cons (first vs) vertex) vertex-map)
                              (cons (cons (first vs) handle) handle-map)))
                      (loop (rest vs)
                            (cons (cons (first vs) vertex) vertex-map)
                            handle-map)))))))))

  (define (next-color v-name staturation move-related-graph vertex-map)
    (define (move-related-color)
      (let ([related (if (has-vertex? move-related-graph v-name)
                         (sequence->list (in-neighbors move-related-graph v-name))
                         '())])
        (let loop ([related related])
          (if (null? related)
              #f
              (let ([related-vertex (dict-ref vertex-map (first related))])
                (let ([related-color (Vertex-color related-vertex)])
                  (if (eqv? related-color NOCOLOR)
                      (loop (rest related))
                      (if (member related-color staturation)
                          (loop (rest related))
                          related-color))))))))

    (let ([related-color (move-related-color)])
      (if related-color
          related-color
          (let loop ([color 0])
            (if (member color staturation)
                (loop (+ color 1))
                color)))))

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

  (define (dsatur-color! que vertex-map handle-map move-related-graph)
    (if (zero? (pqueue-count que))
        vertex-map
        (let ([vertex (pqueue-pop! que)])
          (match vertex
            [(Vertex name color staturation)
             (if (not (eqv? color NOCOLOR))
                 (error 'dsatur-color!)
                 (let ([new-color (next-color name staturation move-related-graph vertex-map)])
                   (begin
                     (set-Vertex-color! vertex new-color)
                     (update-neighbors-staturation! vertex vertex-map handle-map que)
                     (dsatur-color! que vertex-map handle-map move-related-graph))))])))) ; what if fail to color graph?

  (define-values (que vertex-map handle-map move-related-graph) (init!))

  (let ([vertex-map (dsatur-color! que vertex-map handle-map move-related-graph)])
    (let loop ([vertex-map vertex-map] [color-map '()])
      (if (null? vertex-map)
          color-map
          (let ([var (car (first vertex-map))]
                [color (Vertex-color (cdr (first vertex-map)))])
            (loop (rest vertex-map) (cons (cons var color) color-map)))))))

(define (vars-in-graph g)
  (filter (lambda (v) (> (length (sequence->list (in-neighbors g v))) 0))
          (sequence->list (in-vertices g))))

(define (allocate-registers p)
  (define REG-AVALIABLE 11)
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
      [(ByteReg name) (ByteReg name)]
      [(Deref reg offset) (Deref reg offset)]))

  (define (assign-instr instr var-map)
    (match instr
      [(Instr 'set (list cc arg))
       (Instr 'set (list cc (assign-arg arg var-map)))]
      [(Instr name args)
       (Instr name (map (lambda (arg) (assign-arg arg var-map)) args))]
      [else instr]))

  (define (assign-location block var-map)
    (match block
      [(Block info instrs)
       (Block info (map (lambda (instr) (assign-instr instr var-map)) instrs))]))

  (define (allocate-reg-body var-map body)
    (let ([labels (map car body)] [blocks (map cdr body)])
      (for/list ([label labels] [block blocks])
        (cons label (assign-location block var-map)))))

  (define (written-callee body)
    (define (callee-block block)
      (match block
        [(Block info instrs)
         (list->set
          (filter (lambda (reg)
                    (and (member reg callee-saved)
                         (not (eqv? 'rbp reg))))
                  (set->list (foldl (lambda (writes res) (set-union writes res))
                                    (set)
                                    (map write-instr instrs)))))]))
    (set->list (foldl (lambda (block writes) (set-union (callee-block block) writes))
                      (set)
                      (map cdr body))))


  (define (calc-spill-space var-map)
    (let loop ([space 0] [var-map var-map])
      (if (null? var-map)
          space
          (match (cdr (first var-map))
            [(Reg name) (loop space (rest var-map))]
            [(Deref name offset)
             (loop (max space (- offset)) (rest var-map))]
            [else (error "calc-spill-space: ~s" (first var-map))]))))

  (match p
    [(X86Program info body)
     (let* ([g (dict-ref info 'conflicts)]
            [vars (vars-in-graph g)]
            [color-map (color-graph g vars p)]
            [var-map (build-var-map color-map REG-AVALIABLE)]
            [new-body (allocate-reg-body var-map body )]
            [used-callee (written-callee new-body)]
            [spill-space (calc-spill-space var-map)])
       (X86Program (append (list (cons 'spill-space spill-space))
                           (list (cons 'used-callee used-callee))
                           info)
                   new-body))]))

(define (shrink-expr expr)
  (match expr
    [(Int n) (Int n)]
    [(Var sym) (Var sym)]
    [(Bool b) (Bool b)]
    [(Let var rhs body)
     (Let var (shrink-expr rhs) (shrink-expr body))]
    [(If cnd thn els)
     (If (shrink-expr cnd)
         (shrink-expr thn)
         (shrink-expr els))]
    [(Prim 'and (list e1 e2))
     (If (shrink-expr e1)
         (shrink-expr e2)
         (Bool #f))]
    [(Prim 'or (list e1 e2))
     (If (shrink-expr e1)
         (Bool #t)
         (shrink-expr e2))]
    [(Prim op args) (Prim op (map shrink-expr args))]))

;;; Lif -> Lif
(define (shrink p)
  (match p
    [(Program info expr)
     (Program info (shrink-expr expr))]))

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
