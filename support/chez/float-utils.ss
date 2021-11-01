(define-syntax unbool-1
  (syntax-rules ()
    ((unbool-1 func)
     (lambda (x)
       (if (func x) 1 0)))))

(define-syntax unbool-2
  (syntax-rules ()
    ((unbool-2 func)
     (lambda (x y)
       (if (func x y) 1 0)))))

(define-syntax unbool-3
  (syntax-rules ()
    ((unbool-3 func)
     (lambda (x y z)
       (if (func x y z) 1 0)))))

(define-syntax unbool-4
  (syntax-rules ()
    ((unbool-4 func)
     (lambda (w x y z)
       (if (func w x y z) 1 0)))))

(define-syntax unbool-apply
  (syntax-rules ()
    ((unbool-apply func)
     (lambda (args)
       (if (apply func args) 1 0)))))


; First two args will be erased implicits:
;   Ptr (SchemeVector n ty) -> Fin n -> ty
(define (idris-vector-ref erased-1 erased-2 vec idx)
  (vector-ref vec idx))


(define (idris-+nan.0) +nan.0)
(define idris-isnan (unbool-1 nan?))
(define (idris-notnan x)
  (if (not (nan? x)) 1 0))

(define (idris-+inf.0) +inf.0)
(define (idris--inf.0) -inf.0)

(define idris-flnonpositive (unbool-1 flnonpositive?))
(define idris-flnonnegative (unbool-1 flnonnegative?))

; decode-float: no wrapper needed
; fllp: no wrapper needed


(define idris-fl=-2 (unbool-2 fl=))
(define idris-fl=-3 (unbool-3 fl=))
(define idris-fl=-4 (unbool-4 fl=))
(define idris-fl=-apply (unbool-apply fl=))

(define idris-fl>-2 (unbool-2 fl>))
(define idris-fl>-3 (unbool-3 fl>))
(define idris-fl>-4 (unbool-4 fl>))
(define idris-fl>-apply (unbool-apply fl>))

(define idris-fl>=-2 (unbool-2 fl>=))
(define idris-fl>=-3 (unbool-3 fl>=))
(define idris-fl>=-4 (unbool-4 fl>=))
(define idris-fl>=-apply (unbool-apply fl>=))

(define idris-fl<-2 (unbool-2 fl<))
(define idris-fl<-3 (unbool-3 fl<))
(define idris-fl<-4 (unbool-4 fl<))
(define idris-fl<-apply (unbool-apply fl<))

(define idris-fl<=-2 (unbool-2 fl<=))
(define idris-fl<=-3 (unbool-3 fl<=))
(define idris-fl<=-4 (unbool-4 fl<=))
(define idris-fl<=-apply (unbool-apply fl<=))

; ; Idea by InPhase from Libera ##programming
; (define (idris-smart-compare x y)
;   (cond [(> x y) 1]
;         [(< x y) -1]
;         [else (- y x)]))

; Undefined behavior if one input is NaN but not the other. Should guard this
; behind Subset.
; NOTE: NaN technically should not equal NaN, but `compare nan nan === EQ`
; seems reasonable.
(define (idris-compare x y)
  (cond
    ((fl> x y) 1)
    ((fl< x y) -1)
    ((fl= x y) 0)
    (else 0)))  

(define (idris-max-apply args) (apply max args))
(define (idris-min-apply args) (apply min args))


; (define (idris-bad x) "oh no")
