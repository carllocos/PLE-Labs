(defmacro while (cond . expr)
  `(let iter ((val '()))
     (if ,cond
         (iter ,(cons 'begin expr))
         val)))
         
(begin
  (define *first-task* ())
  (define *last-task* ())
  (define *return*     ())
  
  (define (enqueue cont)
    (if (null? *last-task*)
      (begin
        (set! *last-task* (list cont))
        (set! *first-task* *last-task*))
      (begin
        (set-cdr! *last-task* (list cont))
        (set! *last-task* (cdr *last-task*)))))
  
  (define (dequeue)
    (if (not (null? *first-task*))
      (let ((cont (car *first-task*)))
        (set! *first-task* (cdr *first-task*))
        (if (null? *first-task*)
          (set! *last-task* '()))
          (cont #f))
      (*return* #f)))
  
  (define (schedule task)
    (enqueue (lambda (ignore)
               (task)
               (dequeue))))
  
  (define (yield)
    (call-with-current-continuation 
      (lambda (cont)
        (enqueue cont)
        (dequeue))))
  
  (define (start)
    (call-with-current-continuation 
     (lambda (cont)
       (set! *return* cont)
       (dequeue))))
  
  (define (print op id)
    (display op) 
    (display " task ") 
    (display id) 
    (newline))

  (define (report id prime)
    (display id)
    (display " finds a prime > ")
    (display prime)
    (newline)
    (yield))
  
  (define (primes id n)
    (define mask (make-vector n #t))
    (define limit (sqrt n))
    (define i 2)
    (print "start" id) 
    (while (<= i limit)
      (if (vector-ref mask i)
        (begin
          (report id i)
          (let ((j (+ i i)))
          (while (< j n)
            (vector-set! mask j #f)
            (set! j (+ j i))))))
      (set! i (+ i 1)))
    (while (< i n)
      (if (vector-ref mask i)
        (report id i))
      (set! i (+ i 1)))
    (print "stop" id))
  
  (display "begin ParallelPrimes")
  (newline)
  (schedule (lambda () (primes 'A 12)))
  (schedule (lambda () (primes 'B 30)))
  (schedule (lambda () (primes 'C 20)))
  (start)
  (display "end ParallelPrimes")
  (newline))