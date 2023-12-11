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

(deftype Expr
  [num n]                                 ; <num>
  [bool b]                                ; <bool>
  [lst ls]
  [strings str]
  [prim name args]                        ; (prim <FAE> <FAE>)
  [zero n]
  [if-tf c et ef]                         ; (if-tf <FAE> <FAE> <FAE>)
  [delay expr]
  [force expr]
  [id name]                               ; <id> 
  [app fname arg-expr]                    ; (app <FAE> <FAE>) ; ahora podemos aplicar una funcion a otra
  [fun arg body]                          ; (fun <id> <FAE>) ; mantenemos el <id> como el nombre del argumento
  [rec id-name named-expr body-expr]
  [lazy b]
  [seqn e1 e2]
  [set id v]
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
   (cons '&& (λ (x y) (and x y)))
   (cons 'or (λ (x y) (or x y)))
   (cons '|| (λ (x y) (or x y)))
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
|#
(deftype Env
  (mtEnv)
  (aEnv id loc env)
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
    [(aEnv id loc tail)(if (eq? id x) loc (env-lookup x tail))]
    )
  )
;defincion storage
(deftype Sto
  (mtSto)
  (aSto loc val Sto)
  )
;empty-sto
(define empty-sto (mtSto))
;extend-sto
(define extend-sto aSto)
;sto-lookup
(define (sto-lookup lc sto)
  (match sto
    [(mtSto) (error "segmentation fail: " lc)]
    [(aSto loc val tail) (if (eq? lc loc) val (sto-lookup lc tail))]
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
    [(list 'seqn  e ) (parseSeqN (map parse e))]
    [(list 'seqn e1 e2 ) (seqn (parse e1) (parse e2))]
    [(list 'set id e) (set id (parse e)) ]
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

(define (parseSeqN  e)
  (match e
    [(cons head tail) (if (empty? (rest tail))
                          (seqn  head (car tail))
                          (seqn  head (parseSeqN tail)))
                          ]
    ;[else (seqn (first e) e2)]
    )
  )
;concadFun <FAE> <FAE> -> <FAE>
(define (concadFun lstArg body)
  (match lstArg
    [(cons head tail) (if (empty? tail)
                          (fun head  body)
                          (fun head (concadFun tail body))
                          )]
    )
  )
;concadApp <FAE> <FAE> -> <FAE>
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

;soporte pares v*s
(deftype Val
  (valV v) ; numero, booleano, string, byte, etc.
  (closureV arg body env ) ; closure = fun + env
  (promiseV e env)
  (v*s val sto) 
  (boxV loc)
  (voidV)
  )
;strict <v*s> -> <v*s>
(define (strict val)
  (match val
    [(v*s v st)
     (match v
       [(promiseV e env) (strict (interp e env st))]
       [else val]
       )
     ]
    [(promiseV e env) (strict (interp e env empty-sto))]
    [else val]
    )
  )

; interp :: Expr  Env -> Val
; interpreta una expresion
(define (interp expr env sto)
  (match expr
    [(num n) (v*s (valV n) sto)]
    [(bool b) (v*s (valV b) sto)]
    [(lst ls) (if (list? ls)
                  (v*s (valV (map (λ (x) (valV-v (v*s-val (interp x env sto)))) ls)) sto)
                  (v*s (valV (map (λ (x) (valV-v (v*s-val (interp x env sto)))) (list ls))) sto)
                  )]
    [(strings str) (v*s (valV str) sto)]
    [(delay e) (v*s (promiseV e env) sto)]
    [(force e) (strict (interp e env sto))]
    [(lazy fun) (v*s (promiseV fun env) sto)]
    [(id x) (v*s (sto-lookup (env-lookup x env) sto) sto)]; buscar el valor de x en env
    [(prim prim-name args) (if (list? args)
                               (v*s (prim-ops prim-name (map (λ (x) (interp x env sto)) args)) sto)
                               (v*s (prim-ops prim-name  (interp args env sto)) sto)
                               )]
    [(zero n) (v*s (zeroV (interp n env sto)) sto)]
    [(if-tf c et ef) (def (v*s c-val c-sto) (interp c env sto))
     (if (valV-v c-val)
         (interp et env c-sto)
         (interp ef env c-sto))]
;    [(with x e b) (interp b (extend-env x (interp e env) env))] ; Si asociamos una funcion a una variable, la funcion entra al env
    [(fun arg body) (v*s (closureV arg body env) sto)] ; Por ahora, devolvemos la misma expresion que nos llego
     [(seqn e1 e2)
     ;1-interpretar e1
     (def (v*s e1-val e1-sto) (interp e1 env sto))
     ;2-interp e2 con e1-sto
     (def (v*s e2-val e2-sto) (interp e2 env e1-sto))
     ;3- devolver e2
     (v*s e2-val e2-sto)
     ]
    [(set id e)
     ;1-interp e
     (def (v*s e-val v-sto) (interp e env sto))
     (def lock (env-lookup id env))
     ;2-return void (extend-sto ... e-val sto)
     (v*s (voidV) (delete-sto (extend-sto lock e-val v-sto) empty-sto))
     ]
    
    [(app f e)
     ;1-interp de f
     (def (v*s (closureV arg body fenv) fun-sto) (strict (interp f env sto)))
     ;2-interp e
     (def (v*s arg-val arg-sto) (interp e env fun-sto))
     ;3-obtener direccion de memoria
     (def new-lock (malloc arg-sto))
     ;4- extender enviroment
     ;(def (closureV arg body fenv) (interp f env sto))
     (interp body (extend-env arg new-lock fenv)
             (delete-sto (extend-sto new-lock arg-val arg-sto) empty-sto)
             )]
))
(define (malloc sto)
  (match sto
    [(mtSto) 0]
    [(aSto loc val tail) (+ 1 (malloc tail))]
    )
  )
;contains-sto: lock Sto -> Bool
(define (contains-sto lck sto)
  (match sto
    [(mtSto) #f]
    [(aSto loc val tail) (if (eq? lck loc)
                             #t
                             (contains-sto lck tail)
                             )]
    )
  )
;delete-sto: Sto Sto -> Sto
(define (delete-sto sto new-Sto)
  (match sto
    [(mtSto) new-Sto]
    [(aSto loc val tail) (if (contains-sto loc new-Sto)
                             (delete-sto tail new-Sto)
                             (delete-sto tail (extend-sto loc val new-Sto))
                             )
                         ]
    )
  )
(define (new-sto lock sto)
  (match sto
    [(mtSto) (mtSto)]
    [(aSto loc val tail) (if (eq? lock loc)
                             (new-sto lock tail)
                             (aSto loc val (new-sto lock tail))
                             )]
    )
  )

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
    [(isPrim op-name lstPrimitives) (let ([vals (map (λ (x) x) (valV-v (v*s-val args)))])
                                     (valV ((cdr (assq op-name lstPrimitives)) vals))
                                     )]
    [(isPrim op-name strPrimitives) (if (list? args)
                                        (let ([val (map (λ (x) (valV-v (v*s-val x))) args)])
        (valV ((cdr (assq op-name strPrimitives)) (car val)))
        )
                                        (let ([val (map (λ (x) (valV-v (v*s-val x))) (list args))])
        (valV ((cdr (assq op-name strPrimitives)) (car val)))
        )
                                        )]
    [else (let ([vals (map (λ (x)  (valV-v (v*s-val x))) args)])
            (valV (apply (cdr (assq op-name primitives)) vals))
            )]
    )
  
)
(define (zeroV n)
  (valV (eq? 0 (valV-v (v*s-val n)))))

; run: Src -> Src
; corre un programa
(define (run prog)
   ;5. Actualizar arg run
         ;[res*sto (def (v*s res r-sto) (interp (parse prog) rec-env empty-sto))]
    (def (v*s res r-sto) (interp (parse prog) (extend-env 'Y 0 empty-env) (extend-sto 0 (v*s-val (interp (parse '{fun {f} {with {h {fun {g} {fun {n} {{f {g g}} n}}}} {h h}}})
                                         empty-env empty-sto)) empty-sto)))
    (match res
      [(valV v) v]
      [(closureV arg body env) res]
      [else res]
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



#|
Errores encontrados en los la aplicacion de funcion debido a que me deveuelve un clousureV con su envierment vacio
en vez de un valV  con la respuesta de la aplicacion de funcion en esta misma
|#

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


#|

PROBLEMA 1:
Extienda el lenguaje base para soportar booleanos, strings, una sentencia if, una sentencia seqn y
soporte de listas. Para strings, soporte tres operaciones sobre listas (a eleccion del grupo) y para listas
soporte list, car, cdr y empty.

|#
(printf "Test Basicos Problema 1 ~n")

; TEST BOOLEANOS
(test (run '#t) #t)
(test (run '#f) #f)
; TEST STRINGS
(test (run '"Hello World!") "Hello World!")
; TEST IF
(test (run '{if-tf #t 2 3}) 2)
(test (run '{if-tf #f 1 2}) 2)
; TEST SEQN
(test (run '{seqn {+ 21 3} {- 45 2}}) (begin (+ 21 3) (- 45 2)))
(test (run '{with {x 5}
                  {seqn {set x 10} {+ x 5}}
                  }) 15)
(test (run '{with {x 10}
                  {with {y 20}
                        {seqn {{set x 10} {set y -2} {+ x y}}}
                        }
                  }) 8)

; TODO

; TEST LISTAS
(test (run '{lst {1 2 3 4}}) '{1 2 3 4})
(test (run '{lst {"hola" "como" "estas" "?"}}) '{"hola" "como" "estas" "?"})
(test (run '{lst {#f #t #f}}) '{#f #t #f})
(test (run '{first {1 2 3 4}}) 1)
(test (run '{rest {1 2 3 4}}) '{2 3 4})
(test (run '{lst-length {1 2 3 4}}) 4)
(test (run '{ {fun {x} {first x}} {6 4 1 7}}) ( (λ (x) (first x)) '(6 4 1 7)))
(test (run '{ {fun {x} {first {first x}}} {lst {{6 4} {1 7}}}}) ( (λ (x) (first (first x))) '((6 4) (1 7))))
; TODO EMPTY

; OPERACIONES STRINGS

; TODO 2 OPERACIONES (str-length ya esta)

#|

PROBLEMA 2:
Extienda el lenguaje base para que las operaciones primitivas soporten infinitos argumentos (si es
necesario), documente las primitivas y las restricciones que tengan (si aceptan n o menos argumentos).
El comportamiento de aceptar n argumentos tambi ́en debe ser posible en with y en la declaracion de
funciones. 

|#
(printf "Tests Basicos Problema 2 ~n")
; TEST PRIMITIVAS
(test (run '{* 5 4 3 2 1}) 120)
(test (run '{+ 6 1 3 5}) 15)
(test (run '{- 40 4 7 1}) 28)
(test (run '{/ 60 2 3 5}) 2)

; TEST WITH

; TODO?

; TEST FUNCION
(test (run '{{fun (a b) {+ a b}} {3 2}}) 5)
(test (run '{{fun (a b c) {+ a {- b c}}} {3 2 1}}) 4)
(test (run '{{fun {x y z t u} {- u {+ t {- z {- y x}}}}} {4 8 6 3 8}}) 3)
(test (run '{{fun {x y z t u s}  {+ s {- u {+ t {- z {- y x}}}}}} {4 8 6 3 5 7}}) 7)

#|

PROBLEMA 3:
Introduce la funcionalidad delay/force tal que delay crea una promesa de evaluacion de una expresion
arbitraria y force fuerza la evaluacion de una promesa a un valor (o retorna el valor si su argumento
no es una promesa). 

|#
(printf "Tests Basicos Problema 3 ~n")
; TEST DELAY
(test (run '{delay {+ 5 3 2}}) (promiseV (parse '{+ 5 3 2}) (extend-env 'Y 0 empty-env)))
(test/exn (run '{delay {fun {x} {x}}}) "Error only delay prim opetations: this is not prim -> 'fun")

; TEST FORCE
(test (run '{force {delay {+ 6 7 2}}}) 15)
(test (run '{force {* 5 6 2}}) 60)
(test/exn (run '{force { {fun {x} {+ x x}} 2}}) "Error only force prim opetations and promise expr: this is not prim -> '(fun (x) (+ x x))")

#|

PROBLEMA 4:
Extienda el interprete FAE para permitir la definici ́on de funciones recursivas como azucar sint ́actico
y manteniendo el lambda calculo. 

|#
(printf "Tests Basicos Problema 4 ~n")
;TEST RECURSIVIDAD

; Factorial

(test (run '{rec {factorial {fun {n} {if-tf {zero?? n}
                                       1
                                       {* n {factorial {- n 1}}}
                                       }}} {factorial 0}}) 1)

(test (run '{rec {factorial {fun {n} {if-tf {zero?? n}
                                       1
                                       {* n {factorial {- n 1}}}
                                       }}} {factorial 5}}) 120)
; Fibonachi
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

#|

PROBLEMA 5:
Extienda el interprete FAE para la creaci ́on de funciones con evaluacion perezosa, usando el keyword
lazy para definirlas, escribe pruebas basicas que demuestran el correcto funcionamiento de tu implementacion 

|#

(printf "Tests Basicos Problema 5 ~n")

; TEST LAZY
(test (run '{lazy {fun {x} {+ x x}}}) (promiseV (parse '{fun {x} {+ x x}}) (aEnv 'Y 0 (mtEnv))))
(test (run '{{lazy {fun {x} {+ x x}}} 5}) 10)

(printf "Tests Basicos ~n")
(test (run '{+ 3 4}) 7)
(test (run '{- 5 1}) 4)
(test (run '{+ 3 4}) 7)
(test (run '{- 5 1}) 4)
(test (run '{+ 1 2 3 4}) 10)
(test (run '{* 2 3 4}) 24)
(test (run '{/ 12 2 2}) 3)
(test (run '{< 12 3}) #f)
(test (run '{<= 12 3}) #f)
(test (run '{< 12 12}) #f)
(test (run '{<= 12 12}) #t)
(test (run '{> 12 3}) #t)
(test (run '{>= 12 3}) #t)
(test (run '{> 12 12}) #f)
(test (run '{>= 12 12}) #t)
(test (run '{>= 12 12}) #t)
(test (run '{== 12 12}) #t)
(test (run '{== 12 11}) #f)
(test (run '{!= 12 12}) #f)
(test (run '{!= 12 11}) #t)
(test (run '{&& 12 11}) 11)
(test (run '{&& #f #t}) #f)
(test (run '{|| #f #t}) #t)
(test (run '{|| 12 11}) 12)
(test (run '{with {x 3} 2}) 2)
(test (run '{with {x 3} x}) 3)
(test (run '{with {x 3} {with {y 4} x}}) 3)
(test (run '{with {x 3} {+ x 4}}) 7)
(test (run '{with {x 3} {with {x 10} {+ x x}}}) 20)
(test (run '{with {x 3} {with {x x} {+ x x}}}) 6)
(test (run '{with {x 3} {with {y 2} {+ x y}}}) 5)
(test (run '{with {x 3} {+ 1 {with {y 2} {+ x y}}}}) 6)
(test (run '{with {x 3} {with {y {+ 2 x}} {+ x y}}}) 8)
(test (run '{* 1 1 1 1}) 1)

(test (run '{with {x 3} {+ x x}}) 6)
(test (run '{withn {x 3} {with {y 2} {+ x y}}}) 5)
(test (run '{withn {{x 3} {y 2}} {+ x y}}) 5)
(test (run '{with {{x 3} {x 5}} {+ x x}}) 10)
(test (run '{withn {{x 3} {y {+ x 3}}} {+ x y}}) 9)
(test (run '{withn {{x 10} {y 2} {z 3}} {+ x {+ y z}}}) 15)
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