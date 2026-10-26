#lang eopl
;Autores: Nicolás Cardona García 2477349, Laura Sofía Echeverry González 2477067, Santiago Serrano Morales 2477006

;; Taller 2 — El intérprete de Cauca.
;; Especificación léxica, especificación gramatical, scanner y parser.
;; Este módulo no requiere ningún otro.
;;
;; Lo que se escribe aquí:
;;
;;   especificacion-lexica      comentarios que empiezan con //, espacios
;;                              en blanco, números enteros y flotantes con
;;                              signo, e identificadores que empiezan por
;;                              letra y siguen con letras, dígitos, guion
;;                              bajo o signo de interrogación
;;   especificacion-gramatical  las producciones de <programa>,
;;                              <expresion> y <primitiva>, con los nombres
;;                              de constructor que indican los recuadros
;;                              del enunciado
;;   scanner : string -> lista de tokens   se construye con
;;                                         sllgen:make-string-scanner
;;   parser  : string -> programa          se construye con
;;                                         sllgen:make-string-parser
;;
;; La llamada a sllgen:make-define-datatypes genera los datatypes
;; programa, expresion y primitiva a partir de la gramática, con sus
;; constructores y sus predicados. Mientras la gramática esté vacía no
;; genera ninguno.

;; especificacion-lexica : lista de reglas de SLLGEN
;; Espacios y comentarios // se ignoran; identificadores (letra seguida de
;; letras, digitos, _ o ?) y numeros enteros y flotantes con signo.
(define especificacion-lexica
  '((espacio (whitespace) skip)
    (comentario ("//" (arbno (not #\newline))) skip)
    (identificador (letter (arbno (or letter digit "_" "?"))) symbol)
    (numero (digit (arbno digit)) number)
    (numero ("-" digit (arbno digit)) number)
    (numero (digit (arbno digit) "." digit (arbno digit)) number)
    (numero ("-" digit (arbno digit) "." digit (arbno digit)) number)))

;; especificacion-gramatical : lista de producciones de SLLGEN
;; Gramatica base de Cauca (Parte 1). Los constructores del AST llevan los
;; nombres indicados en el enunciado.
(define especificacion-gramatical
  '((programa (expresion) a-program)

    (expresion (numero) lit-exp)
    (expresion (identificador) var-exp)
    (expresion ("true") true-exp)
    (expresion ("false") false-exp)
    (expresion (primitiva "(" (separated-list expresion ",") ")") prim-exp)
    (expresion ("if" expresion "then" expresion "else" expresion "end") if-exp)
    (expresion ("let" (arbno identificador "=" expresion) "in" expresion "end") let-exp)
;; Parte 4: definicion de procedimientos recursivos y seleccion de alternativas con case
    (expresion ("letrec" (arbno identificador "(" ( separated-list identificador ",") ")" "=" expresion) "in" expresion "end") letrec-exp)
    (expresion ("case" expresion "of" numero "=>" expresion (arbno "of" numero "=>" expresion) "otherwise" "=>" expresion "end") case-exp)
    

;; parte 3: definicion y aplicacion de procedimientos.
    (expresion
     ("proc" "(" (separated-list identificador ",") ")" expresion "end")
     proc-exp)

    (expresion
     ("apply" expresion "(" (separated-list expresion ",") ")")
     app-exp)

    (primitiva ("+") sum-prim)
    (primitiva ("-") minus-prim)
    (primitiva ("*") mult-prim)
    (primitiva ("/") div-prim)
    (primitiva ("add1") add-prim)
    (primitiva ("sub1") sub-prim)
    (primitiva (">") mayor-prim)
    (primitiva (">=") mayorigual-prim)
    (primitiva ("<") menor-prim)
    (primitiva ("<=") menorigual-prim)
    (primitiva ("==") igual-prim)
    (primitiva ("not") not-prim)
    (primitiva ("and") and-prim)
    (primitiva ("or") or-prim)
    (primitiva ("abs") abs-prim)
    (primitiva ("mcd") mcd-prim)
    (primitiva ("mcm") mcm-prim)
    (primitiva ("promedio") promedio-prim)
    (primitiva ("xor") xor-prim)
    (primitiva ("implica") implica-prim)
    (primitiva ("entre") entre-prim)))

(sllgen:make-define-datatypes especificacion-lexica especificacion-gramatical)

;; mostrar-datatypes : -> void
;; Lista en pantalla los datatypes que SLLGEN genera a partir de la
;; gramática. Sirve para revisar los nombres de los constructores.
(define mostrar-datatypes
  (lambda ()
    (sllgen:list-define-datatypes especificacion-lexica especificacion-gramatical)))

;; scanner : string -> lista de tokens
;; Convierte el texto de un programa en la lista de sus tokens.
(define scanner
  (lambda (texto)
    ((sllgen:make-string-scanner especificacion-lexica especificacion-gramatical) texto)))

;; parser : string -> programa
;; Convierte el texto de un programa en su árbol de sintaxis abstracta.
(define parser
  (lambda (texto)
    ((sllgen:make-string-parser especificacion-lexica especificacion-gramatical) texto)))

(provide (all-defined-out))