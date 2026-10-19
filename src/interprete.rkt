#lang eopl
;Autores: Nicolas <codigo>

;; Taller 2 — El intérprete de Cauca.
;; El recorrido de la sintaxis abstracta y la aplicación de
;; procedimientos. Requiere sintaxis.rkt, valores.rkt, ambiente.rkt y
;; primitivas.rkt.
;;
;; apply-procedure vive aquí y no en valores.rkt porque llama a
;; evaluar-expresion.

(require "sintaxis.rkt")
(require "valores.rkt")
(require "ambiente.rkt")
(require "primitivas.rkt")

;; apply-procedure : procval x lista de valores -> valor
;; Verifica que la cantidad de argumentos coincida con la de parámetros
;; y evalúa el cuerpo en el ambiente de la clausura extendido con las
;; ligaduras de los parámetros, no en el ambiente de la llamada.
(define apply-procedure
  (lambda (proc args)
    (eopl:error 'apply-procedure "Sin implementar")))

;; evaluar-programa : programa -> valor
;; Punto de entrada: evalúa la expresión del programa en el ambiente
;; inicial.
(define evaluar-programa
  (lambda (pgm)
    (cases programa pgm
      (a-program (exp)
        (evaluar-expresion exp (ambiente-inicial))))))

;; evaluar-rands : lista de expresiones x ambiente -> lista de valores
;; Evalúa las expresiones de izquierda a derecha en el mismo ambiente.
(define evaluar-rands
  (lambda (rands env)
    (if (null? rands)
        '()
        (let ((valor (evaluar-expresion (car rands) env)))
          (cons valor (evaluar-rands (cdr rands) env))))))

;; evaluar-expresion : expresion x ambiente -> valor
;; Recorre el árbol de sintaxis abstracta con cases y evalúa cada
;; variante según la semántica del enunciado. El if liga el resultado de
;; la condición a test-value, lo verifica con boolean? y solo entonces
;; ramifica; el case evalúa la expresión de control una sola vez.
(define evaluar-expresion
  (lambda (exp env)
    (cases expresion exp
      (lit-exp (dato) dato)
      (var-exp (id) (apply-env env id))
      (true-exp () #t)
      (false-exp () #f)
      (prim-exp (prim rands)
        (let ((args (evaluar-rands rands env)))
          (evaluar-primitiva prim args)))
      (if-exp (test rama-then rama-else)
        (let ((test-value (evaluar-expresion test env)))
          (if (boolean? test-value)
              (if test-value
                  (evaluar-expresion rama-then env)
                  (evaluar-expresion rama-else env))
              (eopl:error 'if-exp "La condicion debe ser booleana: ~s" test-value))))
      (let-exp (ids rands body)
        (let ((args (evaluar-rands rands env)))
          (evaluar-expresion body (ambiente-extendido ids args env)))))))

(provide (all-defined-out))