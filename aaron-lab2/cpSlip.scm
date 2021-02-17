;
; Slip: Lisp in 100 lines - Theo D'Hondt: SOFT: VUB - 2010
;
;       CPS version
;
;       Version 0 - continuations with result value only
;                   
; <expression>  ::= <computation>|<lambda>|<quote>|<variable>|
;                   <literal>|<null> 
; <computation> ::= <definition>|<assignment>|<sequence>|
;                   <conditional>|<iteration>|<application>
; <definition>  ::= (define <variable> <expression>)
; <definition>  ::= (define <pattern> <expression>+)
; <assignment>  ::= (set! <variable> <expression>)
; <sequence>    ::= (begin <expression>+)
; <conditional> ::= (if <expression> <expression> <expression>)
; <conditional> ::= (if <expression> <expression>)
; <iteration>   ::= (while <expression> <expression>+)
; <application> ::= (<expression>+)
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
; <cond>        ::= (cond <cond clause>+ (else <expression>)?)
; <cond clause> ::= (<expression> <expression>)

; don't use syntactic constructs (e.g. cond, do, ...) or higher 
; order nativefunctions (e.g. map, for-each, ...) 

(begin
  (define meta-level-eval eval)
  
  (define environment '())
  
  ;
  ; read-eval-print
  ;
  
  (define (loop output)
    (define rollback environment)
    
    (define (error message qualifier)
      (set! environment rollback)
      (display message)
      (loop qualifier))
    
    ;
    ; functions
    ;
    
    (define (wrap-native-procedure native-procedure)
      (lambda (arguments continue)
        (define native-value (apply native-procedure arguments))
        (continue native-value)))
    
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
    
    (define (evaluate-sequence expressions continue)
      (define head (car expressions))
      (define tail (cdr expressions))
      (define (continue-with-sequence value)
        (evaluate-sequence tail continue))
      (if (null? tail)
          (evaluate head continue)
          (evaluate head continue-with-sequence)))
    
    (define (make-procedure parameters expressions)
      (define lexical-environment environment)
      (lambda (arguments continue)
        (define dynamic-environment environment)
        (define (continue-after-sequence value)
          (set! environment dynamic-environment)
          (continue value))
        (set! environment lexical-environment)
        (bind-parameters parameters arguments)
        (evaluate-sequence expressions continue-after-sequence)))
    
    ;
    ; evaluation functions
    ;
    
    (define (evaluate-application operator)
      (lambda operands
        (lambda (continue)
          (define (continue-after-operator procedure)
            (define (evaluate-operands operands arguments)
              (define (continue-with-operands value)
                (evaluate-operands (cdr operands) (cons value arguments)))
              (if (null? operands)
                  (procedure (reverse arguments) continue)
                  (evaluate (car operands) continue-with-operands)))
            (evaluate-operands operands '()))
          (evaluate operator continue-after-operator))))
    
    (define (evaluate-begin . expressions)
      (lambda (continue)
        (evaluate-sequence expressions continue)))
    
    (define (evaluate-define pattern . expressions)
      (lambda (continue)
        (define (continue-after-expression value)
          (define binding (cons pattern value))
          (set! environment (cons binding environment))
          (continue value))
        (if (symbol? pattern)
            (evaluate (car expressions) continue-after-expression))
        (let* ((binding (cons (car pattern) '())))
          (set! environment (cons binding environment))
          (let ((procedure (make-procedure (cdr pattern) expressions)))
            (set-cdr! binding procedure)
            (continue procedure)))))
    
    (define (evaluate-if predicate consequent . alternative)
      (lambda (continue)
        (define (continue-after-predicate boolean)
          (if (eq? boolean #f) 
              (if (null? alternative)
                  (continue '())
                  (evaluate (car alternative) continue))
              (evaluate consequent continue)))
        (evaluate predicate continue-after-predicate)))
    
    (define (evaluate-lambda parameters . expressions)
      (lambda (continue)
        (continue (make-procedure parameters expressions))))
    
    (define (evaluate-quote expression)
      (lambda (continue)
        (continue expression)))
    
    (define (evaluate-set! variable expression)
      (lambda (continue)
        (define (continue-after-expression value)
          (define binding (assoc variable environment))
          (if binding
              (set-cdr! binding value)
              (error "inaccessible variable: " variable))
          (continue value))
        (evaluate expression continue-after-expression)))
    
    (define (evaluate-variable variable continue)
      (define binding (assoc variable environment))
      (if binding
          (continue (cdr binding))
          (let ((native-value (meta-level-eval variable (interaction-environment))))
            (if (procedure? native-value)
                (continue (wrap-native-procedure native-value))
                (continue native-value)))))
    
    (define (evaluate-while predicate . expressions)
      (lambda (continue)
        (define save-environment environment)
        (define (iterate value)
          (define (continue-after-predicate boolean)
            (define (continue-after-expressions value)
              (set! environment save-environment)
              (iterate value))
            (set! environment save-environment)
            (if (eq? boolean #f)
                (continue value)
                (evaluate-sequence expressions continue-after-expressions)))
          (evaluate predicate continue-after-predicate))
        (iterate '())))

    (define (evaluate-let bindings . expressions)
      (lambda (continue)
        (define save-environment environment)
        (define (continue-after-let value)
          (set! environment save-environment)
          (continue value))
        (define (iterate bindings)
          (if (null? bindings)
              (evaluate-sequence expressions continue-after-let)
              (let* ((first            (car  bindings))
                     (variable         (car     first))
                     (expression       (cadr    first))
                     (rest             (cdr  bindings)))
                (define (continue-binding value)
                  (bind-variable variable value)
                  (iterate rest))
                (evaluate expression continue-binding))))
        (iterate bindings)))

    (define (evaluate-cond . clauses)
      (lambda (continue)
        (define (iterate clauses)
          (cond ((null? clauses) (continue 'void))
                ((eq? 'else (caar clauses))
                 (evaluate (cadar clauses) continue))
                (else (let* ((condition (caar  clauses))
                             (consequen (cadar clauses))
                             (rest      (cdr   clauses)))
                        (define (conditional boolean)
                          (if (eq? boolean #f)
                              (iterate rest)
                              (evaluate consequen continue)))
                        (evaluate condition conditional)))))
        (iterate clauses)))
    
    ;
    ; evaluator
    ;
    
    (define (evaluate expression continue)
      (cond
        ((symbol? expression)
         (evaluate-variable expression continue))
        ((pair? expression)
         (let ((operator (car expression))
               (operands (cdr expression)))
           ((apply
             (case operator
               ((begin)  evaluate-begin )
               ((define) evaluate-define)
               ((if)     evaluate-if    )
               ((let)    evaluate-let   )
               ((cond)   evaluate-cond  )
               ((lambda) evaluate-lambda)
               ((quote)  evaluate-quote ) 
               ((set!)   evaluate-set!  )
               ((while)  evaluate-while )
               (else     (evaluate-application operator))) operands) continue)))
        (else
         (continue expression))))
    
    ;
    ; read-eval-print
    ;
    
    (display output)
    (newline)
    (display ">>>")
    (evaluate (read) loop))
  
  (loop "cpSlip version 0"))