#lang eopl
;Autores: Santiago Serrano Morales 2477006, Laura Sofía Echeverry González 2477067, Nicolás Cardona García 2477349, Samuel Peña Jaramillo 2477399 

;; Taller 2 — El intérprete de Cauca.
;; Batería de pruebas con rackunit. Llega escrita en el fork y no se
;; modifica: las pruebas del grupo se agregan después, en suites nuevas
;; que se suman a la cuenta de fallidas del final.
;;
;; Requiere solamente la fachada, nunca un módulo de src/ por separado.
;;
;; Se ejecuta con:  racket pruebas-cauca.rkt

(require rackunit)
(require rackunit/text-ui)
(require (only-in racket/base exn:fail?))
(require "interprete-cauca.rkt")

;; corre : string -> valor
;; proposito analiza y evalua un programa en cauca dado como cadena de texto
(define corre (lambda (texto) (interpretar texto)))

(define base
  (test-suite
   "Parte 1: interprete base"
   (test-case "literales y variables del ambiente inicial"
              (check-equal? (corre "42") 42)
              (check-equal? (corre "-7") -7)
              (check-equal? (corre "3.5") 3.5)
              (check-equal? (corre "n") 10)
              (check-equal? (corre "r") 5))
   (test-case "booleanos"
              (check-equal? (corre "true") #t)
              (check-equal? (corre "false") #f))
   (test-case "primitivas aritmeticas n-arias"
              (check-equal? (corre "+(1, 2, 3)") 6)
              (check-equal? (corre "-(10, 3, 2)") 5)
              (check-equal? (corre "*(2, 3, 4)") 24)
              (check-equal? (corre "/(100, 5, 2)") 10))
   (test-case "primitivas unarias"
              (check-equal? (corre "add1(n)") 11)
              (check-equal? (corre "sub1(n)") 9)
              (check-equal? (corre "not(true)") #f))
   (test-case "primitivas relacionales"
              (check-equal? (corre ">(n, m)") #t)
              (check-equal? (corre ">=(m, m)") #t)
              (check-equal? (corre "<(q, r)") #t)
              (check-equal? (corre "<=(r, q)") #f)
              (check-equal? (corre "==(n, 10)") #t))
   (test-case "primitivas booleanas binarias"
              (check-equal? (corre "and(true, false)") #f)
              (check-equal? (corre "or(true, false)") #t))
   (test-case "condicional"
              (check-equal? (corre "if >(n, m) then n else m end") 10)
              (check-equal? (corre "if <(n, m) then n else m end") 3))
   (test-case "ligaduras locales"
              (check-equal? (corre "let x = 2 y = 3 in *(x, y) end") 6)
              (check-equal? (corre "let x = 1 in let x = 2 in x end end") 2)
              (check-equal? (corre "let x = 1 in +(x, n) end") 11))
   (test-case "el ejemplo del area del rectangulo"
              (check-equal? (corre "// el area de un rectangulo, con el condicional que valida los lados
let base = 8
    altura = 5
in
  if and(>(base, 0), >(altura, 0))
  then *(base, altura)
  else 0
  end
end") 40))
   (test-case "la condicion del if debe ser booleana"
              (check-exn exn:fail? (lambda () (corre "if n then 1 else 2 end"))))
   (test-case "una variable no ligada es un error"
              (check-exn exn:fail? (lambda () (corre "z"))))
   (test-case "los comentarios se ignoran"
              (check-equal? (corre "// esto no cuenta
7") 7))))

(define primitivas-nuevas
  (test-suite
   "Parte 2: primitivas nuevas"
   (test-case "abs"
              (check-equal? (corre "abs(-7)") 7)
              (check-equal? (corre "abs(7)") 7)
              (check-equal? (corre "abs(-3.5)") 3.5))
   (test-case "mcd"
              (check-equal? (corre "mcd(12, 18)") 6)
              (check-equal? (corre "mcd(7, 13)") 1)
              (check-equal? (corre "mcd(12, 18, 24)") 6))
   (test-case "mcm"
              (check-equal? (corre "mcm(4, 6)") 12)
              (check-equal? (corre "mcm(3, 5)") 15)
              (check-equal? (corre "mcm(2, 3, 4)") 12))
   (test-case "promedio"
              (check-equal? (corre "promedio(1, 2, 3, 4)") 5/2)
              (check-equal? (corre "promedio(10)") 10)
              (check-equal? (corre "promedio(n, m)") 13/2))
   (test-case "xor"
              (check-equal? (corre "xor(true, false)") #t)
              (check-equal? (corre "xor(true, true)") #f)
              (check-equal? (corre "xor(false, false)") #f))
   (test-case "implica"
              (check-equal? (corre "implica(true, false)") #f)
              (check-equal? (corre "implica(false, false)") #t)
              (check-equal? (corre "implica(true, true)") #t))
   (test-case "entre"
              (check-equal? (corre "entre(5, 1, 10)") #t)
              (check-equal? (corre "entre(1, 1, 10)") #t)
              (check-equal? (corre "entre(11, 1, 10)") #f))
   (test-case "las primitivas verifican el tipo de sus argumentos"
              (check-exn exn:fail? (lambda () (corre "mcd(1.5, 2)")))
              (check-exn exn:fail? (lambda () (corre "xor(1, true)")))
              (check-exn exn:fail? (lambda () (corre "abs(true)")))
              (check-exn exn:fail? (lambda () (corre "entre(1, 2)"))))))

(define procedimientos
  (test-suite
   "Parte 3: procedimientos y clausuras"
   (test-case "procedimiento de un parametro"
              (check-equal? (corre "let escalar = proc (v) *(v, 2) end
                                    in apply escalar (21) end") 42))
   (test-case "procedimiento sin parametros"
              (check-equal? (corre "let f = proc () 7 end in apply f () end") 7))
   (test-case "procedimiento de varios parametros"
              (check-equal? (corre "let f = proc (a, b, c) +(a, b, c) end
                                    in apply f (1, 2, 3) end") 6))
   (test-case "un procedimiento recibe otro como argumento"
              (check-equal? (corre "let aplicardos = proc (f, x) apply f (apply f (x)) end
                                        doble = proc (v) *(v, 2) end
                                    in apply aplicardos (doble, 5) end") 20))
   (test-case "un procedimiento retorna otro procedimiento"
              ;; el resultado de una aplicacion se liga antes de volver a
              ;; aplicarlo: <expresion> no puede empezar con parentesis
              (check-equal? (corre "let sumador = proc (a) proc (b) +(a, b) end end
                                    in let suma3 = apply sumador (3)
                                       in apply suma3 (4) end
                                    end") 7))
   (test-case "el cuerpo se evalua en el ambiente de la definicion"
              (check-equal? (corre "let factor = 10
in
  let escalar = proc (v) *(v, factor) end
  in
    let factor = 1000
    in
      apply escalar (5)
    end
  end
end") 50))
   (test-case "aplicar algo que no es procedimiento es un error"
              (check-exn exn:fail? (lambda () (corre "apply 5 (1)"))))
   (test-case "la cantidad de argumentos debe coincidir"
              (check-exn exn:fail?
                         (lambda () (corre "let f = proc (a, b) +(a, b) end
                                            in apply f (1) end"))))))

(define recursion-y-case
  (test-suite
   "Parte 4: recursion y seleccion por valor"
   (test-case "el ejemplo de potencia"
              (check-equal? (corre "letrec
  potencia (base, exp) = if ==(exp, 0)
                         then 1
                         else *(base, apply potencia (base, sub1(exp)))
                         end
in
  apply potencia (2, 10)
end") 1024))
   (test-case "recursion simple"
              (check-equal? (corre "letrec
  factorial (n) = if ==(n, 0) then 1 else *(n, apply factorial (sub1(n))) end
in apply factorial (5) end") 120))
   (test-case "recursion mutua en el mismo letrec"
              (check-equal? (corre "letrec
  par? (n) = if ==(n, 0) then true else apply impar? (sub1(n)) end
  impar? (n) = if ==(n, 0) then false else apply par? (sub1(n)) end
in apply par? (10) end") #t)
              (check-equal? (corre "letrec
  par? (n) = if ==(n, 0) then true else apply impar? (sub1(n)) end
  impar? (n) = if ==(n, 0) then false else apply par? (sub1(n)) end
in apply impar? (7) end") #t))
   (test-case "letrec con un procedimiento pasado como argumento"
              (check-equal? (corre "letrec
  aplicarn (f, x, veces) = if ==(veces, 0)
                           then x
                           else apply f (apply aplicarn (f, x, sub1(veces)))
                           end
in let doble = proc (v) *(v, 2) end
   in apply aplicarn (doble, 1, 5) end
end") 32))
   (test-case "el ejemplo de case"
              (check-equal? (corre "let dia = 3
in
  case dia
    of 1 => 100
    of 3 => 300
    of 7 => 700
    otherwise => 0
  end
end") 300))
   (test-case "case con la rama otherwise activa"
              (check-equal? (corre "let dia = 5
in case dia of 1 => 100 of 3 => 300 otherwise => 0 end end") 0))
   (test-case "case evalua la expresion de control una sola vez"
              (check-equal? (corre "case +(1, 2) of 2 => 20 of 3 => 30 otherwise => 0 end") 30))
   (test-case "el control de case debe ser numero"
              (check-exn exn:fail?
                         (lambda () (corre "case true of 1 => 1 otherwise => 0 end"))))))

;; Suites del grupo

(define primitivas-grupo
  (test-suite
   "Parte 2: Bateria de pruebas"

   (test-case "abs con negativos y positivos"
              (check-equal? (corre "abs(-15)") 15)
              (check-equal? (corre "abs(42)") 42)
              (check-equal? (corre "abs(-(10, 25))") 15)
              (check-exn exn:fail? (lambda () (corre "abs(true)"))))

   (test-case "mcd con dos y tres enteros"
              (check-equal? (corre "mcd(24, 36)") 12)
              (check-equal? (corre "mcd(100, 25, 15)") 5)
              (check-equal? (corre "mcd(17, 13)") 1)
              (check-exn exn:fail? (lambda () (corre "mcd(24, 3.5)"))))

   (test-case "mcm con dos y tres enteros"
              (check-equal? (corre "mcm(4, 6)") 12)
              (check-equal? (corre "mcm(3, 5, 7)") 105)
              (check-equal? (corre "mcm(12, 18, 24)") 72)
              (check-exn exn:fail? (lambda () (corre "mcm(12)"))))

   (test-case "promedio con uno y varios numeros"
              (check-equal? (corre "promedio(10)") 10)
              (check-equal? (corre "promedio(10, 20, 30)") 20)
              (check-equal? (corre "promedio(4, 5, 6, 7)") 11/2)
              (check-exn exn:fail? (lambda () (corre "promedio(10, false)"))))

   (test-case "xor con valores de verdad y fallo con numero"
              (check-equal? (corre "xor(true, false)") #t)
              (check-equal? (corre "xor(true, true)") #f)
              (check-equal? (corre "xor(false, false)") #f)
              (check-exn exn:fail? (lambda () (corre "xor(true, 5)"))))

   (test-case "implica con valores de verdad y fallo de tipo"
              (check-equal? (corre "implica(true, false)") #f)
              (check-equal? (corre "implica(true, true)") #t)
              (check-equal? (corre "implica(false, false)") #t)
              (check-exn exn:fail? (lambda () (corre "implica(false, 0)"))))

   (test-case "entre dentro, en frontera y fuera de rango"
              (check-equal? (corre "entre(5, 1, 10)") #t)
              (check-equal? (corre "entre(10, 10, 20)") #t)
              (check-equal? (corre "entre(25, 1, 20)") #f)
              (check-exn exn:fail? (lambda () (corre "entre(5, true, 10)"))))))

;; procedimientos-grupo: suite de pruebas adicionales de la Parte 3.
;; Proposito: comprobar clausuras, ambientes y errores de aplicacion.
(define procedimientos-grupo
  (test-suite
   "Parte 3: pruebas adicionales de Soku"

   (test-case "crear un procedimiento no evalua su cuerpo"
     (check-equal?
      (corre
       "let pendiente = proc () variableinexistente end
        in 42 end")
      42))

   (test-case "aplicar un procedimiento si evalua su cuerpo"
     (check-exn
      #rx"Variable no ligada: variableinexistente"
      (lambda ()
        (corre
         "let pendiente = proc () variableinexistente end
          in apply pendiente () end"))))

   (test-case "un parametro oculta una variable exterior"
     (check-equal?
      (corre
       "let x = 100
        in
          let identidad = proc (x) x end
          in apply identidad (7) end
        end")
      7))

   (test-case "los argumentos se evaluan en el ambiente de llamada"
     (check-equal?
      (corre
       "let x = 10
        in
          let sumarx = proc (y) +(x, y) end
          in
            let x = 100
            in apply sumarx (x) end
          end
        end")
      110))

   (test-case "la clausura retornada conserva su ambiente"
     (check-equal?
      (corre
       "let creador = proc (a)
                       proc (b) +(a, b) end
                     end
        in
          let sumar8 = apply creador (8)
          in
            let a = 1000
            in apply sumar8 (2) end
          end
        end")
      10))

   (test-case "se rechazan argumentos de mas"
     (check-exn
      #rx"se esperaban 1 argumento"
      (lambda ()
        (corre
         "let identidad = proc (x) x end
          in apply identidad (1, 2) end"))))

   (test-case "se rechazan argumentos de menos"
     (check-exn
      #rx"se esperaban 2 argumento"
      (lambda ()
        (corre
         "let sumar = proc (a, b) +(a, b) end
          in apply sumar (1) end"))))

   (test-case "el operador se verifica antes de evaluar argumentos"
     (check-exn
      #rx"el operador no es un procedimiento"
      (lambda ()
        (corre "apply 5 (variableinexistente)"))))

   (test-case "los argumentos se evaluan de izquierda a derecha"
     (check-exn
      #rx"Variable no ligada: primera"
      (lambda ()
        (corre
         "let tomar = proc (a, b) a end
          in apply tomar (primera, segunda) end"))))))

;; Recursion y seleccion por valor: suite de pruebas adiccionales de la parte 4
;; Proposito: Validar la recursion con letrec y la seleccion de casos con case
(define recursion-y-case-grupo
  (test-suite
   "Parte 4: pruebas del grupo de Santiago"

   (test-case "letrec: factorial recursivo"
     (check-equal?
      (corre
       "letrec
          factorial(n) =
            if ==(n, 0)
            then 1
            else *(n, apply factorial(sub1(n)))
            end
        in apply factorial(6) end") 720))
   
   (test-case "letrec: potencia con dos parametros"
     (check-equal?
      (corre
       "letrec
          potencia(base, exp) =
            if ==(exp, 0)
            then 1
            else *(base, apply potencia(base, sub1(exp)))
            end
        in apply potencia(3, 4) end") 81))

   (test-case "letrec: procedimientos mutuamente recursivos"
     (check-equal?
      (corre
       "letrec
          par?(n) =
            if ==(n, 0)
            then true
            else apply impar?(sub1(n))
            end
          impar?(n) =
            if ==(n, 0)
            then false
            else apply par?(sub1(n))
            end
        in apply par?(9) end") #f)
     (check-equal?
      (corre
       "letrec
          par?(n) =
            if ==(n, 0)
            then true
            else apply impar?(sub1(n))
            end
          impar?(n) =
            if ==(n, 0)
            then false
            else apply par?(sub1(n))
            end
        in apply impar?(8) end") #f))

   (test-case "letrec: procedimiento pasado como argumento"
     (check-equal?
      (corre
       "letrec
          aplicarn(f, x, veces) =
            if ==(veces, 0)
            then x
            else apply f(apply aplicarn(f, x, sub1(veces)))
            end
        in
          let doble = proc(v) *(v, 2) end
          in
            apply aplicarn(doble, 3, 3) end end") 24))

   (test-case "case: selecciona la primera coincidencia"
     (check-equal?
      (corre
       "case 2
          of 2 => 100
          of 2 => 200
          otherwise => 0 end") 100))

   (test-case "case: ejecuta otherwise"
     (check-equal?
      (corre
       "case 8
          of 1 => 100
          of 3 => 300
          otherwise => 99 end") 99))

   (test-case "case: selecciona la rama correcta"
     (check-equal?
      (corre
       "case +(1, 2)
          of 1 => 100
          of 3 => 300
          otherwise => 0 end") 300))

   (test-case "case: rechaza un control booleano"
     (check-exn
      exn:fail?
      (lambda ()
        (corre
         "case false
            of 1 => 100
            otherwise => 0 end"))))
   
   (test-case "letrec: suma recursiva"
    (check-equal?
      (corre
        "letrec
           suma(n) =
             if ==(n, 0)
             then 0
             else +(n, apply suma(sub1(n))) end
         in
           apply suma(5) end") 15))

  (test-case "letrec: factorial de cero"
    (check-equal?
      (corre
        "letrec
           factorial(n) =
             if ==(n, 0)
             then 1
             else *(n, apply factorial(sub1(n)))
             end
         in
           apply factorial(0) end") 1))

  (test-case "letrec: potencia con exponente cero"
    (check-equal?
      (corre
        "letrec
           potencia(base, exp) =
             if ==(exp, 0)
             then 1
             else *(base, apply potencia(base, sub1(exp)))
             end
         in
           apply potencia(7, 0) end") 1))

  (test-case "letrec: potencia de dos parametros"
    (check-equal?
      (corre
        "letrec
           potencia(base, exp) =
             if ==(exp, 0)
             then 1
             else *(base, apply potencia(base, sub1(exp)))
             end
         in
           apply potencia(2, 5) end") 32))

  (test-case "letrec: procedimiento como argumento"
    (check-equal?
      (corre
        "letrec
           aplicar(f, n) = apply f(n)
           doble(x) = *(2, x)
         in
           apply aplicar(doble, 6) end") 12))

  (test-case "case: selecciona una coincidencia posterior"
    (check-equal?
      (corre
        "case 7 of
           1 => 10
         of 4 => 40
         of 7 => 70
         otherwise => 0 end") 70))

  (test-case "case: coincidencia en rama posterior"
    (check-equal?
      (corre
        "case 4 of
           1 => 10
         of 2 => 20
         of 4 => 40
         otherwise => 0 end") 40))

  (test-case "case: otherwise con numero negativo"
    (check-equal?
      (corre
        "case -5 of
           1 => 10
         of 2 => 20
         otherwise => 99 end") 99))

  (test-case "case: control calculado"
    (check-equal?
      (corre
        "case +(2, 4) of
           1 => 10
         of 3 => 30
         otherwise => 99 end") 99))

  (test-case "case: coincidencia con cero"
    (check-equal?
      (corre
        "case 0 of
           0 => 100
         of 1 => 200
         otherwise => 300 end") 100))))

;; scanner-parser-grupo
;; tokens-de-clase : string x symbol -> lista
;; proposito extrae los lexemas de los tokens que pertenecen a una clase lexica dada

(define tokens-de-clase
  (lambda (texto clase)
    (letrec ((recoger (lambda (tokens)
                        (cond
                          ((null? tokens) '())
                          ((eq? (car (car tokens)) clase)
                           (cons (cadr (car tokens)) (recoger (cdr tokens))))
                          (else (recoger (cdr tokens)))))))
      (recoger (scanner texto)))))

(define scanner-parser-grupo
  (test-suite
   "Scanner y parser: pruebas de Nicolas"

   ;;scanner 
   (test-case "scanner: identificadores con letras, digitos, _ y ?"
              (check-equal? (tokens-de-clase "x y2 z_1 par?" 'identificador)
                            '(x y2 z_1 par?)))
   (test-case "scanner: enteros y flotantes con signo"
              (check-equal? (tokens-de-clase "42 -7 3.14 -0.5" 'numero)
                            '(42 -7 3.14 -0.5)))
   (test-case "scanner: comentarios y espacios se ignoran"
              (check-equal? (scanner "// solo un comentario\n   ") '())
              (check-equal? (tokens-de-clase "// c\n 7 // otro" 'numero) '(7)))
   (test-case "scanner: una primitiva con sus argumentos son seis tokens"
              (check-equal? (length (scanner "+(1, 2)")) 6))
   (test-case "scanner: el guion abre un numero negativo"
              (check-equal? (tokens-de-clase "aplicar-5" 'identificador) '(aplicar))
              (check-equal? (tokens-de-clase "aplicar-5" 'numero) '(-5)))
   (test-case "scanner: las palabras reservadas no son identificadores"
              (check-equal? (tokens-de-clase "if then else end let in true false" 'identificador)
                            '()))

   ;; parser gramatica base
   (test-case "parser: literal, variable y booleanos"
              (check-equal? (parser "42") (a-program (lit-exp 42)))
              (check-equal? (parser "x") (a-program (var-exp 'x)))
              (check-equal? (parser "true") (a-program (true-exp)))
              (check-equal? (parser "false") (a-program (false-exp))))
   (test-case "parser: primitiva con sus argumentos"
              (check-equal? (parser "+(1, 2)")
                            (a-program (prim-exp (sum-prim) (list (lit-exp 1) (lit-exp 2)))))
              (check-equal? (parser "add1(x)")
                            (a-program (prim-exp (add-prim) (list (var-exp 'x))))))
   (test-case "parser: condicional"
              (check-equal? (parser "if true then 1 else 2 end")
                            (a-program (if-exp (true-exp) (lit-exp 1) (lit-exp 2)))))
   (test-case "parser: let con varias ligaduras y let anidado"
              (check-equal? (parser "let a = 1 b = 2 in a end")
                            (a-program (let-exp '(a b)
                                                (list (lit-exp 1) (lit-exp 2))
                                                (var-exp 'a))))
              (check-equal? (parser "let a = 1 in let b = 2 in b end end")
                            (a-program (let-exp '(a) (list (lit-exp 1))
                                                (let-exp '(b) (list (lit-exp 2)) (var-exp 'b))))))

   ;; parser extensiones
   (test-case "parser: primitiva nueva"
              (check-equal? (parser "abs(-3)")
                            (a-program (prim-exp (abs-prim) (list (lit-exp -3))))))
   (test-case "parser: proc y apply"
              (check-equal? (parser "proc (x, y) x end")
                            (a-program (proc-exp '(x y) (var-exp 'x))))
              (check-equal? (parser "apply f (1, 2)")
                            (a-program (app-exp (var-exp 'f) (list (lit-exp 1) (lit-exp 2))))))
   (test-case "parser: letrec"
              (check-equal? (parser "letrec f (a) = a in apply f (1) end")
                            (a-program (letrec-exp '(f) '((a)) (list (var-exp 'a))
                                                   (app-exp (var-exp 'f) (list (lit-exp 1)))))))
   (test-case "parser: case con una y con varias ramas"
              (check-equal? (parser "case 7 of 1 => 10 otherwise => 0 end")
                            (a-program (case-exp (lit-exp 7) 1 (lit-exp 10) '() '() (lit-exp 0))))
              (check-equal? (parser "case 7 of 1 => 10 of 2 => 20 otherwise => 0 end")
                            (a-program (case-exp (lit-exp 7) 1 (lit-exp 10)
                                                 '(2) (list (lit-exp 20)) (lit-exp 0)))))

   ;; errores sintactico
   (test-case "parser: errores sintacticos"
              (check-exn exn:fail? (lambda () (parser "if true then 1 else 2")))
              (check-exn exn:fail? (lambda () (parser "let x 5 in x end")))
              (check-exn exn:fail? (lambda () (parser "+(1, 2")))
              (check-exn exn:fail? (lambda () (parser "case 1 otherwise => 0 end"))))

   ;;errores de la base que la bateria original no cubre
   (test-case "primitivas: tipo, cantidad y division por cero"
              (check-exn exn:fail? (lambda () (corre "+(1, true)")))
              (check-exn exn:fail? (lambda () (corre "not(1)")))
              (check-exn exn:fail? (lambda () (corre "add1(1, 2)")))
              (check-exn exn:fail? (lambda () (corre "/(1, 0)"))))
   (test-case "let evalua las expresiones en el ambiente externo"
              (check-equal? (corre "let n = 1 m = n in m end") 10))))

;; las suites que agregue el grupo se declaran arriba y se suman aqui

(define fallidas
  (+ (run-tests base)
     (run-tests primitivas-nuevas)
     (run-tests primitivas-grupo)
     (run-tests procedimientos)
     (run-tests procedimientos-grupo)
     (run-tests recursion-y-case)
     (run-tests recursion-y-case-grupo)
     (run-tests scanner-parser-grupo)))

(eopl:printf "~%==========================================~%")
(eopl:printf "  pruebas fallidas en total: ~s~%" fallidas)
(eopl:printf "==========================================~%")