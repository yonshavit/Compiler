

; works
(define append
  (let ((null? null?) (car car) (cdr cdr) (cons cons))
    (lambda args
      ((letrec ((f (lambda (ls args)
                     (if (null? args)
                         ls
                         ((letrec ((g (lambda (ls)
                                        (if (null? ls)
                                            (f (car args) (cdr args))
                                            (cons (car ls) (g (cdr ls)))))))
                            g) ls)))))
         f) '() args))))

; works
(define zero? 
  (let ((= =))
    (lambda (x) (= x 0))))

; works
(define list (lambda x x))

; works
(define list? 
  (let ((null? null?) (pair? pair?) (cdr cdr))
    (lambda (x)
      (or (null? x)
	  (and (pair? x) (list? (cdr x)))))))

; works
(define length
  (let ((null? null?) (pair? pair?) (cdr cdr) (+ +))
    (lambda (x)
      (letrec ((count 0) (loop (lambda (lst count)
				 (cond ((null? lst) count)
				       ((pair? lst) (loop (cdr lst) (+ 1 count)))
				       (else "this should be an error, but you don't support exceptions")))))
	(loop x 0)))))

; works
(define make-string
  (let ((null? null?)(make-string make-string)(car car)(= =)(length length))
    (lambda (x . y)
      (cond ((null? y) (make-string x #\nul))
	    ((= 1 (length y)) (make-string x (car y)))
	    (else "this should be an error, but you don't support exceptions")))))

; works
(define make-vector
  (let ((length length)(make-vector make-vector)(car car)(null? null?))
    (lambda (x . y)
      (cond ((null? y) (make-vector x 0))
	    ((= 1 (length y)) (make-vector x (car y)))
	    (else "this should be an error, but you don't support exceptions")))))


; works
(define not
  (let ((eq? eq?))
    (lambda (x)
      (if (eq? x #t) #f #t))))

; works
(define number?
  (let ((float? float?) (integer? integer?))
    (lambda (x)
      (or (float? x) (integer? x)))))

; works
(define map
  (let ((null? null?) (cons cons) (apply apply) (car car) (cdr cdr))
    (lambda (f ls . more)
      (if (null? more)
	  (let ([ls ls])
	    (letrec ((map1 (lambda (ls) 
			     (if (null? ls)
				 '()
				 (cons (f (car ls))
				       (map1 (cdr ls)))) )))
	      (map1 ls))
	    )
	  (let ([ls ls] [more more])
	    (letrec ((map-more (lambda (ls more)
				 (if (null? ls)
				     '()
				     (cons
				      (apply f (car ls) (map car more))
				      (map-more (cdr ls) (map cdr more)))))))
	      (map-more ls more))
	    )))))

; works
(define list->vector
  (let ((null? null?)(pair? pair?)(car car)(cdr cdr)(make-vector make-vector)(length length)(+ +))
    (lambda (lst)
      (letrec ((loop (lambda (lst vec count)
		       (cond ((null? lst) vec)
			     ((pair? lst) (loop (cdr lst) (begin (vector-set! vec count (car lst)) vec) (+ 1 count)))
			     (else "this should be an error, but you don't support exceptions")))))
	(loop lst (make-vector (length lst)) 0)))))

; works
(define vector->list
  (let ((< <)(vector-ref vector-ref)(cons cons)(vector-length vector-length)(- -))
    (lambda (vec)
      (letrec ((loop (lambda (vec lst count)
		       (cond ((< count 0) lst)
			     (else (loop vec (cons (vector-ref vec count) lst) (- count 1)))))))
	(loop vec '() (- (vector-length vec) 1))))))

; works
(define vector
  (let ((list->vector list->vector))
    (lambda x (list->vector x))))


; works
(define +
  (let ((null? null?)(+ +)(car car)(apply apply)(cdr cdr))
    (letrec ((loop (lambda x (if (null? x) 0 (+ (car x) (apply loop (cdr x)))))))
      loop)))

; works
(define *
  (let ((null? null?)(* *)(car car)(apply apply)(cdr cdr))
    (letrec ((loop (lambda x (if (null? x) 1 (* (car x) (apply loop (cdr x)))))))
      loop)))

; works
(define -
  (let ((null? null?)(- -)(+ +)(car car)(apply apply)(length length)(cdr cdr))
    (letrec ((loop (lambda x (if (null? x) 0 (- (apply loop (cdr x)) (car x) )))))
      (lambda num
	(cond ((null? num) "this should be an error, but you don't support exceptions")
	      ((= (length num) 1) (- 0 (car num)))
	      (else (+ (car num) (apply loop (cdr num)))))))))

; works
(define /
  (let ((null? null?)(/ /)(* *)(car car)(apply apply)(length length)(cdr cdr))
    (lambda num
      (cond ((null? num) "this should be an error, but you don't support exceptions")
	    ((= (length num) 1) (/ 1 (car num)))
	    (else (/ (car num) (apply * (cdr num))))))))

; works
(define =
  (let ((null? null?)(= =)(car car)(cdr cdr))
    (letrec ((loop (lambda (element lst) (if 
					  (null? lst) 
					  #t 
					  (if 
					   (= element (car lst))
					   (loop (car lst) (cdr lst))
					   #f)
					  ))))
      (lambda lst
	(cond ((null? lst) "this should be an error, but you don't support exceptions")
	      (else (loop (car lst) (cdr lst))))))))

; works
(define <
  (let ((null? null?)(< <)(car car)(cdr cdr))
    (letrec ((loop (lambda (element lst) (if 
					  (null? lst) 
					  #t 
					  (if 
					   (< element (car lst))
					   (loop (car lst) (cdr lst))
					   #f)
					  ))))
      (lambda lst
	(cond ((null? lst) "this should be an error, but you don't support exceptions")
	      (else (loop (car lst) (cdr lst))))))))

(define >
  (let ((null? null?)(< <)(= =)(not not)(car car)(cdr cdr))
    (letrec ((loop (lambda (element lst) (if 
					  (null? lst) 
					  #t 
					  (if 
					   (not (or (< element (car lst)) (= element (car lst))))
					   (loop (car lst) (cdr lst))
					   #f)
					  ))))
      (lambda lst
	(cond ((null? lst) "this should be an error, but you don't support exceptions")
	      (else (loop (car lst) (cdr lst))))))))

; works
(define equal?
  (let ((< <)(= =)(not not)(string-length string-length)(string-ref string-ref)(vector-ref vector-ref)(vector-length vector-length)(integer? integer?) (float? float?) (pair? pair?) (char? char?) (string? string?)(vector? vector?)(eq? eq?)(car car)(cdr cdr)(char->integer char->integer)(- -))
    (let ((compare-composite (lambda (container-1 container-2 container-ref-fun container-size-fun)
			       (letrec ((loop (lambda (container-1 container-2 container-ref-fun 				index)
						(if (< index 0)
						    #t
						    (and (equal? (container-ref-fun container-1 index) (container-ref-fun container-2 index)) (loop container-1 container-2 container-ref-fun (- index 1)))))))
				 (if (not (= (container-size-fun container-1) (container-size-fun container-2)))
				     #f
				     (loop container-1 container-2 container-ref-fun (- (container-size-fun container-1) 1)))))))
      
      (lambda (x y)
	(or 
	 (and (integer? x) (integer? y) (= x y))
	 (and (float? x) (float? y) (= x y))
	 (and (pair? x) (pair? y) (equal? (car x) (car y)) (equal? (cdr x) (cdr y)))
	 (and (char? x) (char? y) (= (char->integer x) (char->integer y)))
	 (and (string? x) (string? y) (compare-composite x y string-ref string-length))
	 (and (vector? x) (vector? y) (compare-composite x y vector-ref vector-length))
	 (eq? x y))))))
