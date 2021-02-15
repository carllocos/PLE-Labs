;
; Slip: Lisp in 100 lines - Theo D'Hondt: SOFT: VUB - 2010
;
;       Simple recursive version in Scheme
;
;       Version 3 - extension with a while iterator, clean define and 
;                   meta-level infrastructure
;
; <expression>  ::= <computation>|<lambda>|<quote>|<variable>|
;                   <literal>|<null>|<let>|<cond>
; <computation> ::= <definition>|<assignment>|<sequence>|
;                   <conditional>|<iteration>|<application>
; <definition>  ::= (define <variable> <expression>)
; <definition>  ::= (define <pattern> <expression>+)
; <assignment>  ::= (set! <variable> <expression>)
; <sequence>    ::= (begin <expression>+)
; <conditional> ::= (if <expression> <expression> <expression>)
; <conditional> ::= (if <expression> <expression>)
; <iteration>   ::= (while <expression> <expression>+)
; <application> ::= (<variable>+)
; <lambda>      ::= (lambda () <expression>+)
; <lambda>      ::= (lambda <variable> <expression>+)
; <lambda>      ::= (lambda (<pattern>) <expression>+)
; <quote>       ::= '[s-expression]
; <variable>    ::= [symbol]
; <pattern>     ::= (<variable>+)
; <pattern>     ::= (<variable>+ . <variable>)
; <literal>     ::= [number]|[character]|[string]|#t|#f
; <null>        ::= ()
; <let>         ::= (let (<binding spec>*) <expression>)
; <binding>     ::= (<variable> <expression>)
; <cond>        ::= (cond <cond clause>+ (else <expression>))
; <cond clause> ::= (<expression> <expression>)

(begin
  (define circularity-level 0)
  (define meta-level-eval eval)
  (define eval '())
  (define environment '())

  (define primitives-loaded #f)
  (define primitives-approach1
    (list
         '(define (++ z x) (+ (* z z) (* x x)))
         '(define (greet p) (display (string-append "hello " p)))))

  ;primitives apporach 2
  (define (spanish-greet p)
    (display (string-append "hola " p)))
  (define (other++ x y)
         (+ (* x x) (* y y)))

  (define (loop output)
    (define rollback environment)

    (define (error message qualifier)
      (display message)
      (set! environment rollback)
      (loop qualifier))

;
; functions
;

    (define (bind-variable variable value)
      (define binding (cons variable value))
      (set! environment (cons binding environment)))

    (define (bind-parameters parameters arguments)
      (if (symbol? parameters)
        (bind-variable parameters arguments))
        (if (pair? parameters)
          (let 
            ((variable (car parameters))
             (value    (car arguments )))
            (bind-variable variable value)
            (bind-parameters (cdr parameters) (cdr arguments)))))

    (define (evaluate-sequence expressions)
      (define head (car expressions))
      (define tail (cdr expressions))
      (if (null? tail)
        (evaluate head)
        (begin
          (evaluate head)
          (evaluate-sequence tail))))

    (define (make-procedure parameters expressions)
      (define lexical-environment environment)
      (lambda arguments
        (define dynamic-environment environment)
        (set! environment lexical-environment)
        (bind-parameters parameters arguments)
        (let ((value (evaluate-sequence expressions)))
          (set! environment dynamic-environment)
          value)))

;
; evaluation functions
;

    (define (evaluate-application operator)
      (lambda operands
        (apply (evaluate operator) (map evaluate operands))))

    (define (evaluate-begin . expressions)
      (evaluate-sequence expressions))

    (define (evaluate-define pattern . expressions)
      (if (symbol? pattern)
        (let* ((value (evaluate (car expressions)))
               (binding (cons pattern value)))
          (set! environment (cons binding environment))
          value)
        (let* ((binding (cons (car pattern) '())))
          (set! environment (cons binding environment))
          (let ((procedure (make-procedure (cdr pattern) expressions)))
            (set-cdr! binding procedure)
            procedure))))

    (define (evaluate-if predicate consequent . alternative)
      (define boolean (evaluate predicate))
      (if (eq? boolean #f) 
        (if (null? alternative)
          '()
          (evaluate (car alternative)))
        (evaluate consequent)))

    (define (evaluate-lambda parameters . expressions)
      (make-procedure parameters expressions))

    (define (evaluate-quote expression)
      expression)

    (define (evaluate-set! variable expression)
      (define binding (assoc variable environment))
      (if binding
        (let ((value (evaluate expression)))
          (set-cdr! binding value)
          value)
        (error "inaccessible variable: " variable)))

    (define (evaluate-variable variable)
      (define binding (assoc variable environment))
      (if binding
        (cdr binding)
        (meta-level-eval variable (interaction-environment))))

    (define (evaluate-while predicate . expressions)
      (define save-environment environment)
      (define (iterate value)
        (set! environment save-environment)
        (let ((boolean (evaluate predicate)))
          (set! environment save-environment)
          (if (eq? boolean #f)
            value
            (iterate (evaluate-sequence expressions)))))
      (iterate '()))

    (define (evaluate-let bindings . expression)
      (define save-environment environment)
      (bind-parameters
       (map car bindings)
       (map (lambda (b)
             (evaluate (cadr b)))
           bindings))
      (let ((v (evaluate-sequence expression)))
        (set! environment save-environment)
        v
      ))

    (define (evaluate-cond . clauses)
      ; for more meaningfull error message
      ; define cluases eval as an inner loop.
      (if (null? clauses)
          (error "else-clause missing " clauses)
          (let* ((clause (car clauses))
                 (pred (car clause)))
            (if (eq? pred 'else)
                (evaluate-sequence (cdr clause))
                (if (evaluate pred)
                    (evaluate (cadr clause))
                    (apply evaluate-cond (cdr clauses)))))))
;
; evaluator
;

    (define (evaluate expression)
      (cond
        ((symbol? expression)
         (evaluate-variable expression))
        ((pair? expression)
         (let ((operator (car expression))
               (operands (cdr expression)))
           (apply
             (case operator
               ((begin)  evaluate-begin )
               ((define) evaluate-define)
               ((if)     evaluate-if    )
               ((lambda) evaluate-lambda)
               ((quote)  evaluate-quote ) 
               ((set!)   evaluate-set!  )
               ((while)  evaluate-while )
               ((let)    evaluate-let   )
               ((cond)   evaluate-cond  )
               (else     (evaluate-application operator))) operands)))
        (else
          expression)))
;
; load-primitives
;
    (if (not primitives-loaded)
        (begin (for-each (lambda(pm)
                  (evaluate pm))
                  primitives-approach1)
               (set! primitives-loaded #t)))

;
; read-eval-print
;

    (display output)
    (newline)
    (display ">>>")
    (set! eval evaluate)
    (loop (evaluate (read))))

  (loop "Slip version 3"))