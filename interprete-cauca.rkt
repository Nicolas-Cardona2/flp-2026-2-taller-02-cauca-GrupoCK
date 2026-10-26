#lang eopl
;Autores: Santiago Serrano Morales 2477006, Laura Sofía Echeverry González 2477067, Nicolás Cardona García 2477349, Samuel Peña Jaramillo 2477399 


;; Taller 2 — El intérprete de Cauca.
;; Fachada: reúne los seis módulos de src/ y reexporta todo lo que
;; definen, de modo que quien la requiera vea todos los nombres sin
;; requerir los módulos uno por uno.
;;
;;   src/sintaxis.rkt    especificación léxica y gramatical, scanner, parser
;;   src/valores.rkt     el valor procedimiento
;;   src/ambiente.rkt    el TAD ambiente y el ambiente inicial
;;   src/primitivas.rkt  las primitivas y sus verificaciones
;;   src/interprete.rkt  la evaluación y la aplicación de procedimientos
;;   src/interfaz.rkt    el punto de entrada y el REPL
;;
;; Los require van en un solo sentido. Racket no carga dos módulos que se
;; requieran entre sí.

(require "src/sintaxis.rkt")
(require "src/valores.rkt")
(require "src/ambiente.rkt")
(require "src/primitivas.rkt")
(require "src/interprete.rkt")
(require "src/interfaz.rkt")

(provide (all-from-out "src/sintaxis.rkt"
                       "src/valores.rkt"
                       "src/ambiente.rkt"
                       "src/primitivas.rkt"
                       "src/interprete.rkt"
                       "src/interfaz.rkt"))

;;; ==========================================================
;;; Ejemplos
;;; ==========================================================

#|
  Aquí van los ejemplos que pide el enunciado: 5 del scanner, 5 del
  parser y los de ejecución de cada parte, con el resultado de cada uno
  escrito al lado. Las pruebas con rackunit viven en pruebas-cauca.rkt.


  Scanner, parser y ejecucion del lenguaje base - Parte 1
  
  1. Reconocimiento de un numero.
  (scanner "25")
  => ((numero 25 1))

  2. Reconocimiento de un identificador.
  (scanner "variable")
  => ((identificador variable 1))

  3. Reconocimiento de un booleano como token literal.
  (scanner "true")
  => ((literal-string51 "true" 1))

  4. Reconocimiento de una primitiva y sus argumentos.
  (scanner "+(2, 3)")
  => tokens para +, (, 2, ,, 3 y ).

  5. Reconocimiento de las palabras de un condicional.
  (scanner "if true then 10 else 20 end")
  => tokens para if, true, then, 10, else, 20 y end.

  6. Expresion numerica.
  (parser "25")
  => a-program que contiene lit-exp 25.

  7. Expresion booleana.
  (parser "true")
  => a-program que contiene true-exp.

  8. Primitiva aritmetica.
  (parser "+(2, 3)")
  => a-program que contiene prim-exp con sum-prim.

  9. Expresion condicional.
  (parser "if true then 10 else 20 end")
  => a-program que contiene if-exp.

  10. Declaracion de una variable.
  (parser "let x = 5 in +(x, 3) end")
  => a-program que contiene let-exp.

  11. Literal numerico.
  (interpretar "25")
   => 25

  12. Suma con tres argumentos.
  (interpretar "+(2, 3, 4)")
  => 9

  13. Multiplicacion y variable local.
  (interpretar "let x = 5 in *(x, 2) end")
  => 10

  14. Condicional verdadero.
  (interpretar "if <(3, 5) then 100 else 200 end")
  => 100

  15. Variables locales anidadas.
  (interpretar "let x = 10 in let y = 20 in +(x, y) end end")
  => 30

  16. Booleano verdadero.
  (interpretar "true")
  => #t

  17. Booleano falso.
  (interpretar "false")
  => #f

  18. Resta.
  (interpretar "-(10, 3)")
  => 7

  19. Comparacion numerica.
  (interpretar ">(8, 4)")
  => #t

  20. Condicional falso.
  (interpretar "if false then 100 else 200 end")
  => 200

  21. Division.
  (interpretar "/(20, 2, 2)")
  => 5

  22. Division entre cero: error esperado.
  (interpretar "/(10, 0)")
  => error: Division por cero.

  23. Incrementar un numero.
  (interpretar "add1(4)")
  => 5

  24. Decrementar un numero.
  (interpretar "sub1(4)")
  => 3

  25. Comparacion mayor o igual.
  (interpretar ">=(5, 5)")
  => #t

  26. Comparacion menor o igual.
  (interpretar "<=(4, 5)")
  => #t

  27. Comparacion de igualdad.
  (interpretar "==(4, 4)")
  => #t

  28. Negacion logica.
  (interpretar "not(false)")
  => #t

  29. Conjuncion logica.
  (interpretar "and(true, false)")
  => #f

  30. Disyuncion logica.
  (interpretar "or(false, true)")
  => #t

  31. Error por condicion no booleana.
  (interpretar "if 5 then 10 else 20 end")
  => error: la condicion debe ser booleana.

   Primitivas nuevas - Parte 2

   1. abs
      (evaluar-primitiva (abs-prim) '(-15))      => 15
      (evaluar-primitiva (abs-prim) '(42))       => 42
      (evaluar-primitiva (abs-prim) '(-3.14))    => 3.14
      (evaluar-primitiva (abs-prim) '(#t))       => error: "abs: El argumento debe ser un numero: #t"
  
   2. mcd
      (evaluar-primitiva (mcd-prim) '(24 36))    => 12
      (evaluar-primitiva (mcd-prim) '(100 25 15))=> 5
      (evaluar-primitiva (mcd-prim) '(17 13))    => 1
      (evaluar-primitiva (mcd-prim) '(24 3.5))   => error: "mcd: El argumento debe ser un entero: 3.5"
  
   3. mcm
      (evaluar-primitiva (mcm-prim) '(4 6))      => 12
      (evaluar-primitiva (mcm-prim) '(3 5 7))    => 105
      (evaluar-primitiva (mcm-prim) '(12 18 24)) => 72
      (evaluar-primitiva (mcm-prim) '(12))       => error: "mcm: Se esperaban al menos 2 argumentos y llegaron 1"
  
   4. promedio
      (evaluar-primitiva (promedio-prim) '(10))       => 10
      (evaluar-primitiva (promedio-prim) '(10 20 30)) => 20
      (evaluar-primitiva (promedio-prim) '(4 5 6 7))  => 11/2
      (evaluar-primitiva (promedio-prim) '(10 #f))    => error: "promedio: El argumento debe ser un numero: #f"
  
   5. xor
      (evaluar-primitiva (xor-prim) '(#t #f))    => #t
      (evaluar-primitiva (xor-prim) '(#t #t))    => #f
      (evaluar-primitiva (xor-prim) '(#f #f))    => #f
      (evaluar-primitiva (xor-prim) '(#t 5))     => error: "xor: El argumento debe ser un booleano: 5"
  
   6. implica
      (evaluar-primitiva (implica-prim) '(#t #f))=> #f
      (evaluar-primitiva (implica-prim) '(#t #t))=> #t
      (evaluar-primitiva (implica-prim) '(#f #f))=> #t
      (evaluar-primitiva (implica-prim) '(#f 0)) => error: "implica: El argumento debe ser un booleano: 0"
  
   7. entre
      (evaluar-primitiva (entre-prim) '(5 1 10)) => #t
      (evaluar-primitiva (entre-prim) '(10 10 20))=> #t
      (evaluar-primitiva (entre-prim) '(25 1 20))=> #f
      (evaluar-primitiva (entre-prim) '(5 #t 10))=> error: "entre: El argumento debe ser un numero: #t"

  procedimientos y clausuras — parte 3

  1. procedimiento sin parametros
     (interpretar
      "let constante = proc () 7 end
       in apply constante () end")
     => 7

  2. procedimiento de un parametro
     (interpretar
      "let doble = proc (x) *(x, 2) end
       in apply doble (6) end")
     => 12

  3. procedimiento de varios parametros
     (interpretar
      "let sumar = proc (a, b, c) +(a, b, c) end
       in apply sumar (2, 3, 4) end")
     => 9

  4. procedimiento que recibe otro procedimiento
     (interpretar
      "let aplicardos = proc (f, x) apply f (apply f (x)) end
           doble = proc (v) *(v, 2) end
       in apply aplicardos (doble, 5) end")
     => 20

  5. procedimiento que retorna otro procedimiento
     (interpretar
      "let sumador = proc (a)
                      proc (b) +(a, b) end
                    end
       in
         let suma3 = apply sumador (3)
         in apply suma3 (4) end
       end")
     => 7

  6. contraste: se conserva el ambiente de definicion
     (interpretar
      "let factor = 10
       in
         let escalar = proc (v) *(v, factor) end
         in
           let factor = 1000
           in apply escalar (5) end
         end
       end")
     => 50

  7. error: el operador no es un procedimiento
     (interpretar "apply 5 (1)")
     => error de app-exp:
        "el operador no es un procedimiento: 5"

  8. error: cantidad incorrecta de argumentos
     (interpretar
      "let sumar = proc (a, b) +(a, b) end
       in apply sumar (1) end")
     => error de apply-procedure:
        "se esperaban 2 argumento(s) y llegaron 1"

  Recursion y seleccion multiple(letrec y case) - Parte 4
  
  1. Factorial recursivo.
      (interpretar
       "letrec factorial(n) =
          if ==(n, 0)
          then 1
          else *(n, apply factorial (-(n, 1)))
          end
        in apply factorial (5)
        end")
      => 120

   2. Suma recursiva desde 1 hasta n.
      (interpretar
       "letrec sumar_hasta(n) =
          if ==(n, 0)
          then 0
          else +(n, apply sumar_hasta (-(n, 1)))
          end
        in apply sumar_hasta (5)
        end")
      => 15

   3. Procedimientos mutuamente recursivos: numero par.
      (interpretar
       "letrec par?(n) =
          if ==(n, 0)
          then true
          else apply impar? (-(n, 1))
          end
        impar?(n) =
          if ==(n, 0)
          then false
          else apply par? (-(n, 1))
          end
        in apply par? (8)
        end")
      => #t

   4. Procedimientos mutuamente recursivos: determinar si un numero es impar.
      par? e impar? se llaman entre si hasta llegar al caso base.
      (interpretar
       "letrec par?(n) =
          if ==(n, 0)
          then true
          else apply impar? (-(n, 1))
          end
        impar?(n) =
          if ==(n, 0)
          then false
          else apply par? (-(n, 1))
          end
        in apply impar? (8)
        end")
      => #f
  
    5. Procedimiento recursivo pasado como argumento.
        factorial se pasa como argumento al procedimiento aplicar.
        (interpretar
         "letrec factorial(n) =
            if ==(n, 0)
            then 1
            else *(n, apply factorial (-(n, 1)))
            end
          in
            let aplicar = proc (f, x) apply f (x) end
            in apply aplicar (factorial, 5)
            end
          end")
        => 120

   6. case: coincide con la primera alternativa.
      (interpretar
       "case 1 of
          1 => 100
        of 2 => 200
        otherwise => 300
        end")
      => 100

   7. case: coincide con una alternativa posterior.
      (interpretar
       "case 2 of
          1 => 100
        of 2 => 200
        otherwise => 300
        end")
      => 200

   8. case: se activa otherwise.
      (interpretar
       "case 5 of
          1 => 100
        of 2 => 200
        otherwise => 300
        end")
      => 300

   9. case: error si el valor de control no es numerico.
      (interpretar
       "case true of
          1 => 100
        of 2 => 200
        otherwise => 300
        end")
      => error de case-exp:
         "El valor de control debe ser numerico: #t"

|#
