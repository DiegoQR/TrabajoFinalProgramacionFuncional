#lang play
(print-only-errors #f) ; Para ver solo los errores.
; RFAE -> Recursive - Functions - Arithmetic - Expressions
#|
Práctica 4 - FAE-L (Completa parte)
Corregido Fun x caso de fallo correguido
Mas primitivas aadidas
Nombre: Matheo Leonardo Quiroga Sanchez

Asignatura: Programación Funcional

|#
#|
<FAE> ::=   <num> | <bool> | <id>
            | (+ <FAE> <FAE>)
            | (- <FAE> <FAE>)
            | (zero?? <FAE>)
            | (if-tf <FAE> <FAE> <FAE>)
            | (with <id> <FAE> <FAE>)
            | (app <FAE> <FAE>) ; puedo aplicar una funcion a otra funcion / puedo usar una funcion como argumento. 
            | (fun <id> <FAE>) ; fun(que es una lambda) nombre-arg body
            | (rec <id> <FAE> <FAE>)
            | (lazzy <id> <FAE>)
|#

; Ejemplos de uso de una funcion como valor
; {fun {x} {+ x 1}}
; {{fun {x} {+ x 1}} 10} --> 11
; {with {apply10 {fun {f} {f 10}}} {apply10 add1}}
; {{addN 10} 20}

(deftype Expr
  [num n]                                 ; <num>
  [bool b]                                ; <bool>
  [lst ls]
  [strings str]
  [prim name args]                        ; (prim <FAE> <FAE>)
  [zero n]
  [if-tf c et ef]                         ; (if-tf <FAE> <FAE> <FAE>)
;  [with id-name named-expr body-expr]     ; (with <id> <FAE> <FAE>)
  [delay expr]
  [force expr]
  [id name]                               ; <id> 
  [app fname arg-expr]                    ; (app <FAE> <FAE>) ; ahora podemos aplicar una funcion a otra
  [fun arg body]                          ; (fun <id> <FAE>) ; mantenemos el <id> como el nombre del argumento
  [rec id-name named-expr body-expr]
  [lazy b]
) 
(define primitives
  (list
   (cons '+ +)
   (cons '- -)
   (cons '* *)
   (cons '/ /)
   (cons '< <)
   (cons '> >)
   (cons '<= <=)
   (cons '>= >=)
   (cons '== eq?)
   (cons '!= (λ(x y) (not (eq? x y))))
   (cons 'and (λ (x y) (and x y)))
   (cons 'or (λ (x y) (or x y)))
;   (cons 'zero? (λ (x) (eq? x 0)))
   ))
(define lstPrimitives
  (list
   (cons 'first (λ (x) (first x)))
   (cons 'rest (λ (x) (rest x)))
   (cons 'lst-length (λ (x) (length x)))
   )
  )

(define strPrimitives
  (list
   (cons 'str-length (λ (x) (string-length x)))

   )
  )
(define allPrimitives
  (list
   primitives strPrimitives lstPrimitives
   )
  )
#|
<env> ::= (mtEnv)
          | (aEnv <id> <val> <env>)
          | (aRecEnv <id> <boxed-val> <env>)
|#
(deftype Env
  (mtEnv)
  (aEnv id val env)
;  (aRecEnv id boxed-val env) ; ambiente recursivo 
  )

; empty-env -> (mtEnv)
(define empty-env (mtEnv))

; extend-env:: <id> <val> <env> -> <env>
(define extend-env aEnv)
; env-lookup :: <id> <env> -> <val>
; buscar el valor de una variable dentro del ambiente
(define (env-lookup x env)
  (match env
    [(mtEnv) (error "undefined: " x)]
    [(aEnv id val tail)(if (eq? id x) val (env-lookup x tail))]
;    [(aRecEnv id bval tail)(if (eq? id x) (unbox bval) (env-lookup x tail))]
    )
  )
(define (isPrim primName primit)
  (match primit
    [(? empty?) #f]
    [(cons head tail) (if (eq? (car head) primName)
                          #t
                          (isPrim primName tail)
                          )]
    )
  )

;isPrim:: <prim-op> <list-of-all-primitives> -> <bool>
(define (ifPrimitive arg primi)
  (match primi
    [(cons head tail) (if (empty? tail)
                          (isPrim arg head)
                          (if (isPrim arg head)
                              #t
                              (ifPrimitive arg tail)
                              )
                          )]
    )
  )
; parse: Src -> Expr
; parsea codigo fuente
(define (parse src)
  (match src
    [(? number?) (num src)]
    [(? boolean?) (bool src)]
    [(? symbol?) (id src)]
    [(? string?) (strings src)]
    [(list 'zero?? n) (zero (parse n))]
    [(list 'lazy fun ) (lazy (parse fun))]
    [(list 'delay expr) (if (ifPrimitive (first expr) allPrimitives)
                            (delay (parse expr))
                            (error "Error only delay prim opetations: this is not prim ->"(first expr))
                            )]
    [(list 'force expr) (match expr
                          [(list 'delay e) (force (parse expr))]
                          [else (if (ifPrimitive (first expr) allPrimitives)
                            (force (parse expr))
                            (error "Error only force prim opetations and promise expr: this is not prim ->"(first expr))
                            )]
                          )
                        ]
    [(list 'if-tf c et ef) (if-tf (parse c) (parse et) (parse ef))]
    [(list 'with (list x e) b) (app (fun x (parse b)) (parse e))]
    [(list 'rec (list x e) b) (parse `{with {,x {Y {fun {,x} ,e}}} ,b})]
    [(list 'lst arg) (if (list? arg)
                    (lst (map parse arg))
                    (lst (parse arg))
                    )]
    [(list arg) (match arg
                  [(cons head tail) (if (symbol? head)
                                        (prim head (parse tail))
                                    (lst (map parse arg))    
                                        )]
                  [(? symbol?) (parse arg)]
                  [else (lst (parse arg))]
                  )]
    [(list args  e) 
     (if (ifPrimitive args allPrimitives)
         (match e
           [(cons head tail) (if (ifPrimitive head allPrimitives)
                                 (prim args (prim head (parse tail)))
                                 (prim args (parse e))
                                 )]
           [else (prim args (parse e)) ]
           )
         (match args
           [(? number?) (lst (map parse (list args e)))]
           [(? string?) (lst (map parse (list args e)))]
           [(? bool?) (lst (map parse (cons args e)))]
           [else (match e
           [(cons head tail) (if (symbol? head)
                                 (app (parse args) (parse e))
                                 (match args
                                   [(list 'fun arg body) (if (list? arg)
                                                             (if (empty? (rest arg))
                                                                 (app (parse args) (parse e))
                                                                 (concadApp e  (parse args))
                                                                 )
                                                             (app (parse args) (parse e))
                                                             )]
                                   
                                   [else (app (parse args) (parse e))]
                                   )
                                 )]
           [else (app (parse args) (parse e))]
           )]
           )
         )
                    ]
     
    ;[(list arg (cons e1 e2) (app (parse arg) (map parse (cons e1 e2))))]
    ;[(list 'fun (list arg) body) (fun arg (parse body))] ; 1. Agregar el caso del fun
    [(list 'fun args body) (concadFun args (parse body))]
    [(cons prim-name args) (if (symbol? prim-name)
                               (if (list? args)
                               (prim prim-name (map parse args))
                               (prim prim-name (parse args))
                               )
                               (if (list? args)
                               (lst (map parse (cons prim-name args)))
                               (lst (map parse (list prim-name args)))
                               )
                               )]
    ;[(? list?) (list src)]
    )
  )

(define (concadFun lstArg body)
  (match lstArg
    [(cons head tail) (if (empty? tail)
                          (fun head  body)
                          (fun head (concadFun tail body))
                          )]
    )
  )
(define (concadApp lstArg body)
  (match lstArg
    ;[(? number?) (app body (parse lstArg))]
    [(cons head tail) (if (empty? tail)
                          (app body (parse head))
                          (concadApp tail (concadApp head body ))
                          
                          ;(concadApp head (concadApp tail body))
                          )]
    [else (app body (parse lstArg))]
    
    )
  )

(deftype Val
  (valV v) ; numero, booleano, string, byte, etc.
  (closureV arg body env) ; closure = fun + env
  (promiseV expr env) ;promise = expr+env
  )

(define (strict val)
  (match val
    [(promiseV e env) (strict (interp e env))]
    [else val]
    )
  )

; interp :: Expr  Env -> Val
; interpreta una expresion
(define (interp expr env)
  (match expr
    [(num n) (valV n)]
    [(bool b) (valV b)]
    [(lst ls) (if (list? ls)
                  (valV (map (λ (x) (valV-v (interp x env))) ls))
                  (valV (map (λ (x) (valV-v (interp x env))) (list ls)))
                  )]
    [(strings str) (valV str)]
    [(delay e) (promiseV e env)]
    [(force e) (strict (interp e env))]
    [(lazy fun) (promiseV fun env)]
    [(id x) (env-lookup x env)]; buscar el valor de x en env
    [(prim prim-name args) (if (list? args)
                               (prim-ops prim-name (map (λ (x) (interp x env)) args))
                               (prim-ops prim-name  (interp args env))
                               )]
    [(zero n) (zeroV (interp n env))]
    [(if-tf c et ef) (if (valV-v (interp c env))
                         (interp et env)
                         (interp ef env))]
;    [(with x e b) (interp b (extend-env x (interp e env) env))] ; Si asociamos una funcion a una variable, la funcion entra al env
    [(fun arg body) (closureV arg body env)] ; Por ahora, devolvemos la misma expresion que nos llego
    [(app f e)
     (def (closureV arg body fenv) (strict (interp f env))) ; Esto permite encontrar (fun 'x (add (id 'x) (id 'x))) por ejemplo y tomar arg y body
    
     (interp body (extend-env arg (interp e env) fenv)) ; parece que no funciona ni con estatico ni dinamico
     ]
))


#|
El interprete usa recursividad
|#

#|
(define (prim-ops op-name args)
  (let ([vals (map (λ (x) (valV-v x)) args)])
    (valV (apply (cdr (assq op-name primitives)) vals))
    )
  )|#
(define (prim-ops op-name args)
  (cond
    [(isPrim op-name lstPrimitives) (let ([vals (map (λ (x) x) (valV-v args))])
                                     (valV ((cdr (assq op-name lstPrimitives)) vals))
                                     )]
    [(isPrim op-name strPrimitives) (if (list? args)
                                        (let ([val (map (λ (x) (valV-v x)) args)])
        (valV ((cdr (assq op-name strPrimitives)) (car val)))
        )
                                        (let ([val (map (λ (x) (valV-v x)) (list args))])
        (valV ((cdr (assq op-name strPrimitives)) (car val)))
        )
                                        )]
    [else (let ([vals (map (λ (x) (valV-v x)) args)])
            (valV (apply (cdr (assq op-name primitives)) vals))
            )]
    )
  
)
(define (zeroV n)
  (valV (eq? 0 (valV-v n))))

; run: Src -> Src
; corre un programa
(define (run prog)
  (let* ([rec-env (extend-env 'Y (interp (parse '{fun {f} {with {h {fun {g} {fun {n} {{f {g g}} n}}}} {h h}}})
                                         empty-env) empty-env)]
         [res (interp (parse prog) rec-env)])
    (match res
      [(valV v) v]
      [(closureV arg body env) res]
      [else res]
      )
    )
  )
(test (run '{+ 3 4}) 7)
(test (run '{- 5 1}) 4)

(test (run '{with {x 3} 2}) 2)
(test (run '{with {x 3} x}) 3)
(test (run '{with {x 3} {with {y 4} x}}) 3)
(test (run '{with {x 3} {+ x 4}}) 7)
(test (run '{with {x 3} {with {x 10} {+ x x}}}) 20)
(test (run '{with {x 3} {with {x x} {+ x x}}}) 6)
(test (run '{with {x 3} {with {y 2} {+ x y}}}) 5)
(test (run '{with {x 3} {+ 1 {with {y 2} {+ x y}}}}) 6)
(test (run '{with {x 3} {with {y {+ 2 x}} {+ x y}}}) 8)
(test (run '{with {x 3} {if-tf {+ x 1} {+ x 3} {+ x 9}}}) 6)
(test/exn (run '{f 10}) "undefined")

(test (run '{with {f {fun {x} {+ x x}}}{f 10}}) 20)

(test (run '{{fun {x} {+ x x}} 10}) 20)

(test (run '{with {add1 {fun {x} {+ x 1}}}{add1 {add1 {add1 10}}}}) 13)

(test (run '{with {add1 {fun {x} {+ x 1}}}
                  {with {foo {fun {x} {+ {add1 x} {add1 x}}}}
                        {foo 10}}}) 22)

(test (run '{with {add1 {fun {x} {+ x 1}}}
                  {with {foo {fun {f} {+ {f 10} {f 10}}}}
                        {foo add1}}}) 22)

(test (run '{{fun {x}{+ x 1}} {+ 2 3}}) 6)
(test (run '{with {apply10 {fun {f} {f 10}}}
                  {with {add1 {fun {x} {+ x 1}}}
                        {apply10 add1}}}) 11)


(test (run '{with {addN {fun {n}
                       {fun {x} {+ x n}}}}
            {{addN 10} 20}}) 30)



;Test para fun {n ....}
(test (run '{{fun (a b) {+ a b}} {3 2}}) 5)
(test (run '{{fun (a b c) {+ a {- b c}}} {3 2 1}}) 4)
(test (run '{{fun {x y z t u} {- u {+ t {- z {- y x}}}}} {4 8 6 3 8}}) 3)
(test (run '{{fun {x y z t u s}  {+ s {- u {+ t {- z {- y x}}}}}} {4 8 6 3 5 7}}) 7)

#|
Errores encontrados en los la aplicacion de funcion debido a que me deveuelve un clousureV con su envierment vacio
en vez de un valV  con la respuesta de la aplicacion de funcion en esta misma
|#
#|Factorial|#
(printf "Factorial: ~n")

(test (run '{rec {factorial {fun {n} {if-tf {zero?? n}
                                       1
                                       {* n {factorial {- n 1}}}
                                       }}} {factorial 0}}) 1)

(test (run '{rec {factorial {fun {n} {if-tf {zero?? n}
                                       1
                                       {* n {factorial {- n 1}}}
                                       }}} {factorial 5}}) 120)
;Fibonachi
(printf "Fibonachi: ~n")
(test (run '{rec {fibonachi {fun {n} {if-tf {< n 2}
                                            n
                                            {+ {fibonachi {- n 1}} {fibonachi {- n 2}}}
                                            }}} {fibonachi 0}}) 0)
(test (run '{rec {fibonachi {fun {n} {if-tf {< n 2}
                                            n
                                            {+ {fibonachi {- n 1}} {fibonachi {- n 2}}}
                                            }}} {fibonachi 1}}) 1)
(test (run '{rec {fibonachi {fun {n} {if-tf {< n 2}
                                            n
                                            {+ {fibonachi {- n 1}} {fibonachi {- n 2}}}
                                            }}} {fibonachi 2}}) 1)
(test (run '{rec {fibonachi {fun {n} {if-tf {< n 2}
                                            n
                                            {+ {fibonachi {- n 1}} {fibonachi {- n 2}}}
                                            }}} {fibonachi 8}}) 21)
(printf "Listas: ~n")
(test (run '{lst {1 2 3 4}}) (run '{{1 2 3 4}}))
(test (run '{lst {"hola" "como" "estas" "?"}}) (run '{{"hola" "como" "estas" "?"}}))
(test (run '{lst {#f #t #f}}) (run '{{#f #t #f}}))
(test (run '{first {1 2 3 4}}) (first '{1 2 3 4}))
(test (run '{rest {1 2 3 4}}) (rest '{1 2 3 4}))
(test (run '{lst-length {1 2 3 4}}) (length '(1 2 3 4)))
(test (run '{ {fun {x} {first x}} {6 4 1 7}}) ( (λ (x) (first x)) '(6 4 1 7)))
(test (run '{ {fun {x} {first {first x}}} {lst {{6 4} {1 7}}}}) ( (λ (x) (first (first x))) '((6 4) (1 7))))

(printf "Primitivas: ~n")
(test (run '{* 5 4 3 2 1}) 120)
(test (run '{+ 6 1 3 5}) 15)
(test (run '{- 40 4 7 1}) 28)
(test (run '{/ 60 2 3 5}) 2)

(printf "Delay and Force: ~n")
(test (run '{delay {+ 5 3 2}}) (promiseV (parse '{+ 5 3 2}) (extend-env 'Y (interp (parse '{fun {f} {with {h {fun {g} {fun {n} {{f {g g}} n}}}} {h h}}})
                                         empty-env) empty-env)))
(test/exn (run '{delay {fun {x} {x}}}) "Error only delay prim opetations: this is not prim -> 'fun")
(test (run '{force {delay {+ 6 7 2}}}) 15)
(test (run '{force {* 5 6 2}}) 60)
(test/exn (run '{force { {fun {x} {+ x x}} 2}}) "Error only force prim opetations and promise expr: this is not prim -> '(fun (x) (+ x x))")

(printf "Lazy functions: ~n")
(test (run '{lazy {fun {x} {+ x x}}}) (promiseV (parse '{fun {x} {+ x x}}) (extend-env 'Y (interp (parse '{fun {f} {with {h {fun {g} {fun {n} {{f {g g}} n}}}} {h h}}})
                                         empty-env) empty-env)))
(test (run '{{lazy {fun {x} {+ x x}}} 5}) 10)


#|
(if (list? args)
      (let ([vals (map (λ (x) (valV-v x)) args)])
        (if (isPrim op-name lstPrimitives)
            (valV ((cdr (assq op-name lstPrimitives)) vals)) 
            (valV (apply (cdr (assq op-name primitives)) vals))
        )
    )
      (let ([val (valV-v args)])
        (valV ((cdr (assq op-name strPrimitives)) val))
        )
      )
|#