#lang racket

#|
An MPlus is a list with a counter
|#
(define (++ m r)
  (match m
    [`(,ls . ,n)
     (if (<= n 0) m
         (match ls
           ['() r]
           [`(,a . ,d) (let ([res (++ `(,d . ,(sub1 n)) r)])
                         (match res
                           [`(,ls-res . ,n) (inj-mplus (cons a ls-res)
                                                       (max (sub1 n) 0))]))]
           [(? procedure? $) (++ ($) r)]))]))

(define mzero '(() . 0))
(define inj-mplus cons)
(define get (λ (x) (cons (cdr x) (cdr x))))
(define >>=
  (λ (m f)
    (match m
      [`(,ls . ,n)
       (if (<= n 0)
           (match m
             [(? procedure? $) (>>= ($) f)]
             [else m])
           (match ls
             ['() `(() . ,n)]
             [`(,a . ,d) (++ (f a) (>>= `(,d . ,(sub1 n)) f))]
             [(? procedure? $) (>>= ($) f)]))])))

(define mplus
  (λ (m1 m2)
    (match m1
      [`(,ls . ,n)
       (if (<= n 0) m2
           (match ls
             ['() m2]
             [`(,a . ,d)
              (match (mplus m2 `(,d . ,(sub1 n)))
                [`(,ls . ,m) (inj-mplus (cons a ls) m)])]
             [(? procedure? $) (mplus m2 ($))]))])))

(define-syntax go-on
  (syntax-rules ()
    [(go-on () b) b]
    [(go-on ([name exp] pr ...) b)
     (>>= exp
          (λ (name)
            (go-on (pr ...) b)))]))

(define (valof e n)
  (match e
    [(? symbol?) (inj-mplus (list (symbol->string e)) (sub1 n))]
    [0 (inj-mplus '() (sub1 n))]
    [1 (inj-mplus (list "") (sub1 n))]
    [`(,a + ,b) (mplus (valof a n) (valof b n #;(- n 1)))]
    [`(,a • ,b)
     (go-on ([sym1 (valof a n)]
             [sym2 (valof b n)])
            (inj-mplus (list (string-append sym1 sym2))
                       (- n 1)))]))