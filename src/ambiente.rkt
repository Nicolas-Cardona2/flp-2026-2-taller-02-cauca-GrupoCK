#lang eopl
;Autores: Nicolás Cardona García 2477349, Santiago Serrano Morales 2477006

;; Taller 2 — El intérprete de Cauca.
;; El TAD ambiente, la búsqueda de ligaduras y el ambiente inicial.
;; Requiere sintaxis.rkt y valores.rkt.
;;
;; Aquí se declara con define-datatype el tipo ambiente, con tres
;; variantes:
;;
;;   ambiente-vacio()
;;   ambiente-extendido(ids, valores, env)
;;     ids      (list-of symbol?)
;;     valores  list?
;;     env      ambiente?
;;   ambiente-recursivo(proc-names, idss, bodies, env)
;;     proc-names  (list-of symbol?)   los nombres declarados en el letrec
;;     idss        list?               la lista de parámetros de cada uno
;;     bodies      (list-of expresion?) los cuerpos, guardados sin evaluar
;;     env         ambiente?
;;
;; La variante recursiva no construye clausuras: las arma apply-env en el
;; momento de la búsqueda, y el ambiente que les entrega es el propio
;; ambiente-recursivo (EOPL, sección 3.4, figura 3.9).

(require "sintaxis.rkt")
(require "valores.rkt")

;; Datatype ambiente (Parte 1: variantes ambiente-vacio y ambiente-extendido).
(define-datatype ambiente ambiente?
  (ambiente-vacio)
  (ambiente-extendido
   (ids (list-of symbol?))
   (valores list?)
   (env ambiente?))
  (ambiente-recursivo ;; Datatype ambiente (Parte 4: variante ambiente-recursivo)
   (proc-names (list-of symbol?))
   (idss list?)
   (bodies list?)
   (env ambiente?)))

;; posicion-de : symbol x lista de symbol -> int | #f
;; Retorna la posicion de la primera aparicion de id en la lista, o #f si
;; no esta.
(define posicion-de
  (lambda (id ids)
    (letrec ((buscar (lambda (lst i)
                       (cond
                         ((null? lst) #f)
                         ((eqv? (car lst) id) i)
                         (else (buscar (cdr lst) (+ i 1)))))))
      (buscar ids 0))))

;; apply-env : ambiente x symbol -> valor
;; Busca el identificador en el ambiente, respetando el shadowing de las
;; ligaduras más recientes, y levanta eopl:error si no está ligado.
(define apply-env
  (lambda (env id)
    (cases ambiente env
      (ambiente-vacio ()
        (eopl:error 'apply-env "Variable no ligada: ~s" id))
      (ambiente-extendido (ids valores env-padre)
        (let ((pos (posicion-de id ids)))
          (if (number? pos)
              (list-ref valores pos)
              (apply-env env-padre id))))
      (ambiente-recursivo (proc-names idss bodies env-padre) ;; Datatype ambiente (Parte 4: variante ambiente-recursivo)
        (let ((pos (posicion-de id proc-names)))
          (if pos
              (cerradura (list-ref idss pos)
                         (list-ref bodies pos) env)
              (apply-env env-padre id)))))))

;; ambiente-inicial : -> ambiente
;; El ambiente con que arranca todo programa:
;; n = 10, m = 3, p = 7, q = 2, r = 5.
(define ambiente-inicial
  (lambda ()
    (ambiente-extendido '(n m p q r)
                        '(10 3 7 2 5)
                        (ambiente-vacio))))

(provide (all-defined-out))