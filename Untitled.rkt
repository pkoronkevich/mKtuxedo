#lang racket
(require racket/trace
         "monads.rkt")

(define proc? procedure?)

;Vanilla
#|
(define take
  (λ (n ls)
    (if (zero? n) '()
        (match ls
          ['() '()]
          [`(,a . ,d) (cons a (take (sub1 n) d))]
          [(? proc?) (take n (ls))]))))

(define (map-inf f $)
  (match $
    ['() '()]
    [`(,a . ,d) (cons (f a) (map-inf f d))]
    [(? procedure?) (λ () (map-inf f ($)))]))

(define zip
  (λ (m1 m2)
    (match m1
      ['() m2]
      [`(,a . ,d) (cons a (zip m2 d))]
      [(? procedure?) (λ () (zip m2 (m1)))])))

(define zip2
  (λ (m1 m2 k)
    (match m1
      ['() (k m2)]
      [`(,a . ,d) (zip m2 d (λ (l) (k (cons a l))))]
      [(? procedure?) (k (λ (k) (m1 (λ (l) (zip m2 l k)))))])))

(define (conc A B)
  (match* (A B)
    [('() _) '()]
    [(_ '()) '()]
    [((? procedure? $) _) (λ () (conc ($) B))]
    [(_ (? procedure? $)) (λ () (conc A ($)))]
    [(`(,a . ,d) _)
     (zip (map-inf (λ (x) (string-append a x)) B)
          (conc d B))]))

(define (valof exp)
  (match exp
    [0 '()]
    [1 '("")]
    [(? symbol?) (list (symbol->string exp))]
    [`(,a + ,b)
     (zip (valof a)
          (valof b))]
    [`(,a • ,b)
     (let ([A (valof a)]
           [B (valof b)])
       (conc A B))]
    [`(,a *) (conc (valof a) (λ () (cons "" (valof `(,a *)))))]
    [`(,a +) (valof `(,a • (,a *)))]))

(define (get-n-chars n e)
  (take n (valof e)))

> (get-n-chars 1 '((c *) • (b *)))
'("cb")
> (get-n-chars 10 '((c *) • (b *)))
'("cb"
  "ccb"
  "cbb"
  "cbbb"
  "cccb"
  "ccbb"
  "cbbbb"
  "cbbbbb"
  "ccbbb"
  "cbbbbbb")
|#
#|

CPSed
|#

(define (map-inf f $ k)
  (match $
    ['() (k '())]
    [`(,a . ,d) (f a (λ (v) (map-inf f d (λ (l) (k (cons v l))))))]
    [(? proc?) (k (λ (k) ($ (λ ($) (map-inf f $ k)))))]))

(define zip
  (λ (m1 m2 k)
    (match m1
      ['() (k m2)]
      [`(,a . ,d) (zip m2 d (λ (l) (k (cons a l))))]
      [(? proc?) (k (λ (k) (m1 (λ (l) (zip m2 l k)))))])))

(define (conc A B k)
  (match* (A B)
    [('() _) (k '())]
    [(_ '()) (k '())]
    [((? procedure? $) _) ($ (λ ($) (k (λ (k) (conc A $ k)))))]
    [(_ (? procedure? $)) ($ (λ ($) (k (λ (k) (conc $ B k)))))]
    [(`(,a . ,d) _)
     (map-inf (λ (x k^) (k^ (string-append a x))) B
              (λ (m) (conc d B (λ (c) (zip m c k)))))]))

(define (valof exp k)
  (match exp
    [0 (k '())]
    [1 (k '(""))]
    [(? symbol?) (k (list (symbol->string exp)))]
    [`(,a + ,b) (valof a (λ (a) (valof b (λ (b) (zip a b k)))))]
    [`(,a • ,b) (valof a (λ (A) (valof b (λ (B) (conc A B k)))))]
    [`(,a *) (k (cons "" (λ (k) (valof a (λ (A) (valof `(,a *) (λ (v) (conc A v k))))))))]
    [`(,a +) (valof `(,a • (,a *)) k)]))

#;[`(,a *) (conc (valof a) (λ () (cons "" (valof `(,a *)))))] 
(define take
  (λ (n ls k)
    (if (zero? n) (k '())
        (match ls
          ['() (k '())]
          [`(,a . ,d) (take (sub1 n) d (λ (v) (k (cons a v))))]
          [(? proc? $) ($ (λ (l) (take n l k)))]))))

(define (get-n-chars n e)
  (valof e (λ (v) (take n v (λ (v) v)))))




