#lang eopl
;Autores: Nombre1 Codigo1, Nombre2 Codigo2

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

  Scanner
    (scanner "...")   =>

  Parser
    (parser "...")    =>

  Ejecución del lenguaje base
    (interpretar "...")   =>

;; Primitivas nuevas

;; 1. abs
;;    (evaluar-primitiva (abs-prim) '(-15))      => 15
;;    (evaluar-primitiva (abs-prim) '(42))       => 42
;;    (evaluar-primitiva (abs-prim) '(-3.14))    => 3.14
;;    (evaluar-primitiva (abs-prim) '(#t))       => error: "abs: El argumento debe ser un numero: #t"
;;
;; 2. mcd
;;    (evaluar-primitiva (mcd-prim) '(24 36))    => 12
;;    (evaluar-primitiva (mcd-prim) '(100 25 15))=> 5
;;    (evaluar-primitiva (mcd-prim) '(17 13))    => 1
;;    (evaluar-primitiva (mcd-prim) '(24 3.5))   => error: "mcd: El argumento debe ser un entero: 3.5"
;;
;; 3. mcm
;;    (evaluar-primitiva (mcm-prim) '(4 6))      => 12
;;    (evaluar-primitiva (mcm-prim) '(3 5 7))    => 105
;;    (evaluar-primitiva (mcm-prim) '(12 18 24)) => 72
;;    (evaluar-primitiva (mcm-prim) '(12))       => error: "mcm: Se esperaban al menos 2 argumentos y llegaron 1"
;;
;; 4. promedio
;;    (evaluar-primitiva (promedio-prim) '(10))       => 10
;;    (evaluar-primitiva (promedio-prim) '(10 20 30)) => 20
;;    (evaluar-primitiva (promedio-prim) '(4 5 6 7))  => 11/2
;;    (evaluar-primitiva (promedio-prim) '(10 #f))    => error: "promedio: El argumento debe ser un numero: #f"
;;
;; 5. xor
;;    (evaluar-primitiva (xor-prim) '(#t #f))    => #t
;;    (evaluar-primitiva (xor-prim) '(#t #t))    => #f
;;    (evaluar-primitiva (xor-prim) '(#f #f))    => #f
;;    (evaluar-primitiva (xor-prim) '(#t 5))     => error: "xor: El argumento debe ser un booleano: 5"
;;
;; 6. implica
;;    (evaluar-primitiva (implica-prim) '(#t #f))=> #f
;;    (evaluar-primitiva (implica-prim) '(#t #t))=> #t
;;    (evaluar-primitiva (implica-prim) '(#f #f))=> #t
;;    (evaluar-primitiva (implica-prim) '(#f 0)) => error: "implica: El argumento debe ser un booleano: 0"
;;
;; 7. entre
;;    (evaluar-primitiva (entre-prim) '(5 1 10)) => #t
;;    (evaluar-primitiva (entre-prim) '(10 10 20))=> #t
;;    (evaluar-primitiva (entre-prim) '(25 1 20))=> #f
;;    (evaluar-primitiva (entre-prim) '(5 #t 10))=> error: "entre: El argumento debe ser un numero: #t"

  Procedimientos
    (interpretar "...")   =>

  Recursión y case
    (interpretar "...")   =>
|#
