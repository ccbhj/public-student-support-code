#lang racket
(require racket/set racket/stream racket/dict)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp.rkt")
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

(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x) (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Let x e body)
       (let* ([new-x (gensym x)]
              [new-env (dict-set env x new-x)])
         (Let new-x ((uniquify-exp env) e) ((uniquify-exp new-env) body)))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

;; uniquify : Lvar -> Lvar
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

;; (uniquify (Program '() (Let 'x (Int 10) 
;;                           (Let 'x (Prim '+ (list (Int 1) (Var 'x))) (Var 'x)))]))

(define merge-dict
  (lambda (x y)
    (letrec ([merge (lambda (yi)
                      (if (not yi)
                          x
                          (dict-set (merge (dict-iterate-next y yi)) (dict-iterate-key y yi) (dict-iterate-value y yi))))])
      (merge (dict-iterate-first y)))))

(define DEBUG 
  (lambda (msg x) (display (format "~a: ~a\n" msg x)) x))

;; return an atom from an expression it returns an atom and a mapping of a var to a expr.
;; rco-atom: exp -> exp * (var * exp) list
(define (rco-atom e)
  (match e
    [(Var _) (values e '())]
    [(Int _) (values e '())]
    ;; [(Prim 'read '()) (let ([sym (gensym 'tmp)]) (values (Var sym) (dict-set '() sym e)))]
    [(Let x rhs body)
     (define new-rhs (rco-expr rhs))
     (define-values (new-body body-ss) (rco-atom body))
     (values new-body (append `((,x . ,new-rhs)) body-ss))]
    [(Prim op es) 
     (define-values (new-es sss)
       (for/lists (l1 l2) ([e es]) (rco-atom e)))
     (define ss (append* sss))
     (define tmp (gensym 'tmp))
     (values (Var tmp) (append ss `((,tmp . ,(Prim op new-es)))))]))
  
     
;; (rco-atom (Prim '+ (list (Int 1) (Int 2)))) 
;; (rco-atom (Prim '+ (list (Prim '- (list (Int 1))) (Int 2)))) 
;; (make-let (second (rco-atom (Prim '- (list (Int 10)))))) |#
;; (rco-atom (Prim '- (list (Prim '- (list (Int 10))))))
;; (rco-atom (Prim '- (list (Prim '- (list (Prim '- (list (Int 10))))))))

;; returns expression that don't need to be atoms
(define (rco-expr p)
    (match p 
       [(Var v) (Var v)]
       [(Int n) (Int n)]
       [(Prim 'read '()) (Prim 'read '())]
       [(Prim op es) 
        (define-values (new-es sss)
           (for/lists (l1 l2) ([e es]) (rco-atom e)))
        (make-lets (append* sss) (Prim op new-es))]
       [(Let x e body) 
        (Let x (rco-expr e) (rco-expr body))]))

;; (rco-expr (Prim '- (list (Int 10))))
;; (rco-expr (Prim '+ (list (Int 1) (Int 2)))) 
(rco-expr (Prim '+ (list (Prim '- (list (Int 1))) (Int 2))))
(rco-expr (Let 'x
               (Prim '+ (list (Prim '- (list (Int 1))) (Int 2)))
               (Prim '+ (list (Var 'x) (Int 2)))))

(rco-expr (Let 'x
               (Prim '+ (list (Prim '- (list (Int 1))) (Int 2)))
               (Let 'y
                    (Prim '+ (list (Var 'x) (Int 2)))
                    (Prim '- (list (Prim '+ (list (Var 'x) (Var 'y))))))))
                    
(rco-expr 
  (Let 'v (Int 1) 
       (Let 'w (Int 42)
            (Let 'x (Prim '+ (list (Var 'v) (Int 7)))
                 (Let 'y (Var 'x) 
                      (Let 'z (Prim '+ (list (Var 'x) (Var 'w)))
                           (Prim '+ (list (Var 'z) (Prim '- (list (Var 'y)))))))))))


;; remove-complex-opera* : Lvar -> Lvar^mon
(define (remove-complex-opera* p)
  rco-expr p)

;; takes an expr in tail position to produce a tail in C0 and produces local variables.
(define (explicate-tail p) 
  (match p
    [(Var v) (values (Return p) (list v))]
    [(Int _) (values (Return p) '())]
    [(Prim _ _) (values (Return p) '())] ;; all the arguments in Prim are already atoms(because of the remove-complex-opera*)
    [(Let x e body) (letrec-values ([(expr vars) (explicate-tail body)]
                                    [(tail locals) (explicate-assign x e expr)])
                                   (values tail (append vars locals)))]))


;; takes an expr that is the RHS of Let, a var from the Let and a tail of the body of the Let after recursion, output a C0 tail and an var list
(define (explicate-assign var expr tail) 
  (match expr 
    [(Int _) (values (Seq (Assign (Var var) expr) tail) (list var))]
    [(Var v) (values (Seq (Assign (Var var) expr) tail) (list v var))]
    ;;[(Prim _ args) (letrec ([locals (foldl (lambda (arg result)
    ;;                                         (second (explicate-tail arg result))) tail args
    ;;                 (values (Seq (Assign (Var var) expr) tail ) locals)]
    [(Prim _ args) (letrec ([locals (foldl (lambda (arg result)
                                             (let-values ([(_ local) (explicate-tail arg)])
                                               (append result local)))
                                           '() args)])
                     (values (Seq (Assign (Var var) expr) tail) locals))]
    [(Let x e body) (letrec-values ([(xtail xvar) (explicate-assign var body tail)]
                                    [(ytail yvar) (explicate-assign x e xtail)])
                      (values ytail (append* yvar xvar)))]))
  
;; explicate-control : Lvar^mon -> Cvar
(define (explicate-control p)
  (match p
    [(Program _ body)
     (define-values (tail _) (explicate-tail body)) 
     (CProgram '() (dict-set '() 'start tail))]))
    
;; (explicate-tail (Let
;;                   'tmp15958
;;                   (Prim '- (list (Int 1)))
;;                   (Prim '+ (list (Var 'tmp15958) (Int 2))))]))
;; 
;; (explicate-tail (Let 'tmp15958 (Int 10) (Var 'tmp15958)))

;; (explicate-tail 
;;   (Let
;;    'v
;;    (Int 1)
;;    (Let
;;     'w
;;     (Int 42)
;;     (Let
;;      'x
;;      (Prim '+ (list (Var 'v) (Int 7)))
;;      (Let
;;       'y
;;       (Var 'x)
;;       (Let
;;        'z
;;        (Prim '+ (list (Var 'x) (Var 'w)))
;;        (Let
;;         'tmp20762
;;         (Prim '- (list (Var 'y)))
;;         (Prim '+ (list (Var 'z) (Var 'tmp20762))))))))))

;; (explicate-tail
;;   (Let
;;    'v
;;    (Int 1)
;;    (Let
;;     'w
;;     (Int 42)
;;     (Let
;;      'x
;;      (Prim '+ (list (Var 'v) (Int 7)))
;;      (Let
;;       'y
;;       (Var 'x)
;;       (Let
;;        'z
;;        (Prim '+ (list (Var 'x) (Var 'w)))
;;        (Prim '+ (list (Var 'z) (Prim '- (list (Var 'y)))))))))))

(define (convert-atm atm)
  (match atm
    [(Var v) (Var v)]
    [(Int v) (Imm v)]
    [v #:when (symbol? v) (Reg v)]))


(define (convert-exp exp)
  (match exp
    [(Prim 'read _) (list (Callq 'read_int 0))]
    [(Prim '- (list atm)) (list (Instr 'negq (list (convert-atm atm))))]
    [(Prim '+ (list atmx atmy)) (list (Instr 'addq (list (convert-atm atmx) (convert-atm atmy))))]
    [atm #:when (atm? atm) (list (convert-atm atm))]))

(define (convert-assign dst src) 
  (match src
    [(Prim 'read _) (append (convert-exp src) (convert-assign dst 'rax))]
    [(Prim '- (list arg)) #:when (equal? arg dst) (convert-exp src)]
    [(Prim '- (list arg)) (list (convert-assign dst arg)
                                (list (Instr 'negq (list (convert-atm dst)))))]
    [(Prim '+ args) #:when (member dst args)
                          (let ([atm (first (remw dst args))])
                            (list (Instr 'addq (list (convert-atm atm) (convert-atm dst)))))]
    [(Prim '+ args) (append (convert-assign dst (first args))
                            (list (Instr 'addq (list (convert-atm (second args)) (convert-atm dst)))))]
    [_ (list (Instr 'movq (list (convert-atm src) (convert-atm dst))))]))

;; (convert-assign (Var 'e) (Int 10))
;; (convert-assign (Var 'e) (Var 'f))
;; (convert-assign (Var 'e) (Prim '- (list (Int 10))))
;; (convert-assign (Var 'e) (Prim '- (list (Var 'e))))
;; (convert-assign (Var 'e) (Prim '+ (list (Var 'e) (Int 10))))
;; (convert-assign (Var 'e) (Prim '+ (list (Var 'f) (Int 10))))

(define (convert-return expr) 
  (match expr
    [(Prim 'read _) (append (convert-exp expr) (Jmp 'conclusion))]
    [_ (append (convert-assign 'rax expr) (list (Jmp 'conclusion)))]))

;; (convert-return (Var 'e))
;; (convert-return (Prim '+ (list (Int 10) (Var 'e))))
;; (convert-return (Prim 'read '()))
;; (convert-return (Prim '- (list (Int 10))))

;; (let ([x (let ([y (- 42)]) y)]) (- x))
;; select-instructions : Cvar -> x86var
(define (select-instructions p)
  (match-let ([(CProgram info block) p])
    (letrec ([expr (dict-ref block 'start)]
             [iter (lambda (ast) 
                     (match ast
                       [(Return e) (convert-return e)]
                       [(Assign v e) (convert-assign v e)]
                       [(Seq s t) (append (iter s) (iter t))]
                       [v #:when (atm? v) (list (convert-atm v))]
                       [_ '()]))]) 
      (X86Program info (dict-set '() 'start (Block '() (iter expr)))))))


(define (create-homes locals)
  (foldl (lambda (local ret)
           (dict-set ret (car local) (Deref 'rbp (* -8 (+ 1 (dict-count ret))))))
         '()
         locals))

(define (replace-home instrs homes)
  (letrec ([map-var (lambda (v)
                      (match v
                        [(Var localname) (dict-ref homes localname)]
                        [_ v]))]
           [map-args (lambda (instr)
                       (match instr
                         [(Instr op args) (Instr op (map map-var args))]
                         [_ instr]))])
    (map map-args instrs)))

;; (replace-home 
;;   (list (Instr 'mov (list (Var 'x) (Var 'y)))
;;         (Instr 'mov (list (Imm 10) (Var 'x))))
;;   (create-homes (list 'x 'y)))

;; assign-homes : x86var -> x86var
(define (assign-homes p)
  (match-letrec ([(X86Program info blocks) p]
                 [(Block binfo instrs) (dict-ref blocks 'start)]
                 [homes (create-homes (dict-ref info 'locals-types))])
    (X86Program (dict-set info 'stack-space (* 8 (dict-count homes)))
               (dict-set blocks 'start (Block binfo (replace-home instrs homes))))))

;; (assign-homes
;;   (X86Program
;;    (dict-set '() 'locals-types  (list 'x))
;;    (list
;;     (cons
;;      'start
;;      (Block
;;       '()
;;       (list (Instr 'movq (list (Var 'x) (Reg 'rax))) (Jmp 'conclusion)))))))

(define (patch-instr instr instrs)
  (match instr
    [(Instr op (list l r)) #:when (and (Deref? l) (Deref? r))
     (append instrs (list (Instr 'movq (list l (Reg 'rax))) (Instr op (list (Reg 'rax) r))))]
    [_ (append instrs (list instr))]))

;; (foldl patch-instr '() 
;;        (list 
;;          (Instr 'negq (list (Deref  'rbp -8)))
;;          (Instr 'movq (list (Deref 'rbp -8) (Deref 'rbp -8))))]))

;; patch-instructions : x86var -> x86int
(define (patch-instructions p)
  (match-letrec ([(X86Program info blocks) p]
                 [(Block binfo instrs) (dict-ref blocks 'start)])
    (X86Program info
                (dict-set blocks 'start (Block binfo
                                                    (foldl patch-instr '() instrs))))))

(define (conclusion-block stack-size)
   (Block '() (list (Instr 'addq (list (Imm stack-size) (Reg 'rsp)))
                  (Instr 'popq (list (Reg 'rbp)))
                  (Retq)))) 

(define (prelude-block stack-size)
   (Block '() (list (Instr 'pushq (list (Reg 'rbp)))
                  (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))
                  (Instr 'sub (list (Imm stack-size) (Reg 'rsp)))
                  (Jmp 'start)))) 

;; prelude-and-conclusion : x86int -> x86int
(define (prelude-and-conclusion p)
  (match-letrec ([(X86Program info blocks) p]
                 [stack-size (dict-ref info 'stack-space)])
    (X86Program info
                (dict-set (dict-set blocks 'main (prelude-block stack-size))
                          'conclusion (conclusion-block stack-size)))))


;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
     ;; Uncomment the following passes as you finish them.
     ("uniquify" ,uniquify ,interp-Lvar ,type-check-Lvar)
     ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
     ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
     ("instruction selection" ,select-instructions ,interp-pseudo-x86-0)
     ("assign homes" ,assign-homes ,interp-x86-0)
     ("patch instructions" ,patch-instructions ,interp-x86-0)
     ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)))
