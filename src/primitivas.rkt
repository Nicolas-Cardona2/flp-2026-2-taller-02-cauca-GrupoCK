#lang eopl
;Autores: Nicolas <codigo>

;; Taller 2 — El intérprete de Cauca.
;; Las primitivas del lenguaje y las verificaciones de tipo y de
;; cantidad de argumentos que cada una exige. Requiere sintaxis.rkt.
;;
;; Aridades: +, -, *, / son n-arias; add1, sub1, not y abs son unarias;
;; las relacionales, and, or, xor e implica son binarias; entre es
;; ternaria; mcd y mcm son n-arias sobre enteros con al menos dos
;; argumentos; promedio es n-aria sobre números con al menos uno.

(require "sintaxis.rkt")

;; exigir-numeros : lista x symbol -> boolean
;; Retorna #t si todos los argumentos son números; si no, levanta
;; eopl:error a nombre de quien hizo la verificación.
(define exigir-numeros
  (lambda (args quien)
    (cond
      ((null? args) #t)
      ((number? (car args)) (exigir-numeros (cdr args) quien))
      (else (eopl:error quien "El argumento debe ser un numero: ~s" (car args))))))

;; exigir-enteros : lista x symbol -> boolean
;; Retorna #t si todos los argumentos son enteros; si no, levanta error.
(define exigir-enteros
  (lambda (args quien)
    (eopl:error 'exigir-enteros "Sin implementar")))

;; exigir-booleanos : lista x symbol -> boolean
;; Retorna #t si todos los argumentos son booleanos; si no, levanta error.
(define exigir-booleanos
  (lambda (args quien)
    (cond
      ((null? args) #t)
      ((boolean? (car args)) (exigir-booleanos (cdr args) quien))
      (else (eopl:error quien "El argumento debe ser un booleano: ~s" (car args))))))

;; exigir-cantidad : lista x int x symbol -> boolean
;; Retorna #t si llegaron exactamente n argumentos; si no, levanta error.
(define exigir-cantidad
  (lambda (args n quien)
    (if (= (length args) n)
        #t
        (eopl:error quien "Se esperaban ~s argumento(s) y llegaron ~s" n (length args)))))

;; exigir-minimo : lista x int x symbol -> boolean
;; Retorna #t si llegaron al menos n argumentos; si no, levanta error.
(define exigir-minimo
  (lambda (args n quien)
    (if (>= (length args) n)
        #t
        (eopl:error quien "Se esperaban al menos ~s argumentos y llegaron ~s" n (length args)))))

;; plegar-izquierda : (valor x valor -> valor) x lista -> valor
;; Aplica la operacion binaria de izquierda a derecha sobre una lista no
;; vacia: (op (op a b) c) ...
(define plegar-izquierda
  (lambda (op args)
    (letrec ((plegar (lambda (acc resto)
                       (if (null? resto)
                           acc
                           (plegar (op acc (car resto)) (cdr resto))))))
      (plegar (car args) (cdr args)))))

;; dividir : numero x numero -> numero
;; Divide a entre b y levanta eopl:error si b es cero.
(define dividir
  (lambda (a b)
    (if (= b 0)
        (eopl:error '/ "Division por cero")
        (/ a b))))

;; evaluar-primitiva : primitiva x lista de valores -> valor
;; Verifica la cantidad y el tipo de los argumentos y aplica la
;; primitiva. Se resuelve con cases sobre el datatype primitiva.
(define evaluar-primitiva
  (lambda (prim args)
    (cases primitiva prim
      (sum-prim ()
        (exigir-minimo args 2 '+) (exigir-numeros args '+)
        (plegar-izquierda + args))
      (minus-prim ()
        (exigir-minimo args 2 '-) (exigir-numeros args '-)
        (plegar-izquierda - args))
      (mult-prim ()
        (exigir-minimo args 2 '*) (exigir-numeros args '*)
        (plegar-izquierda * args))
      (div-prim ()
        (exigir-minimo args 2 '/) (exigir-numeros args '/)
        (plegar-izquierda dividir args))
      (add-prim ()
        (exigir-cantidad args 1 'add1) (exigir-numeros args 'add1)
        (+ (car args) 1))
      (sub-prim ()
        (exigir-cantidad args 1 'sub1) (exigir-numeros args 'sub1)
        (- (car args) 1))
      (mayor-prim ()
        (exigir-cantidad args 2 '>) (exigir-numeros args '>)
        (> (car args) (cadr args)))
      (mayorigual-prim ()
        (exigir-cantidad args 2 '>=) (exigir-numeros args '>=)
        (>= (car args) (cadr args)))
      (menor-prim ()
        (exigir-cantidad args 2 '<) (exigir-numeros args '<)
        (< (car args) (cadr args)))
      (menorigual-prim ()
        (exigir-cantidad args 2 '<=) (exigir-numeros args '<=)
        (<= (car args) (cadr args)))
      (igual-prim ()
        (exigir-cantidad args 2 '==) (exigir-numeros args '==)
        (= (car args) (cadr args)))
      (not-prim ()
        (exigir-cantidad args 1 'not) (exigir-booleanos args 'not)
        (not (car args)))
      (and-prim ()
        (exigir-cantidad args 2 'and) (exigir-booleanos args 'and)
        (and (car args) (cadr args)))
      (or-prim ()
        (exigir-cantidad args 2 'or) (exigir-booleanos args 'or)
        (or (car args) (cadr args))))))

(provide (all-defined-out))