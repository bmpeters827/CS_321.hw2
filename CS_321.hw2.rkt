#lang plai
(define eight-principles
  (list "Know your rights."
        "Acknowledge your sources."
        "Protect your work."
        "Avoid suspicion."
        "Do your own work."
        "Never falsify a record or permit another person to do so."
        "Never fabricate data, citations, or experimental results."
        "Always tell the truth when discussing your work with your instructor."))

(define-type FnWAE
  [num (n number?)]
  [add (lhs FnWAE?)
       (rhs FnWAE?)]
  [sub (lhs FnWAE?)
       (rhs FnWAE?)]
  [with (id symbol?)
        (expr FnWAE?)
        (body FnWAE?)]
  [id (name symbol?)]
  [app (fun-name symbol?)
       (arg (listof FnWAE?))]
  [if0 (expr1 FnWAE?)
       (expr2 FnWAE?)
       (expr3 FnWAE?)])

(define-type DefSub
  [mtSub]
  [aSub (name symbol?)
        (value number?)
        (rest DefSub?)])

(define-type FunDef
  [fundef (fun-name symbol?)
          (param-name (listof symbol?))
          (body FnWAE?)])

(define (check-pieces expression size what)
  (unless (and (list? expression)
               (= (length expression) size))
    (parse-error what expression)))

(define (check-piece expression size what)
  (unless (and (list? expression)
               (= (length expression) size))
    (parse-error what expression)))

(define (parse-error what expression)
  (error 'parser
         "expected: ~a, found: ~a"
         what
         expression))

(define (parse s-exp)
  (cond [(number? s-exp) (num s-exp)]
        [(symbol? s-exp) (id s-exp)]
        [(list? s-exp)
         (when (empty? s-exp)
           (error 'parse "the empty list is not a valid FnWAE"))
         (case (first s-exp)
           [(+)
            (check-pieces s-exp 3 "addition")
            (add (parse (second s-exp))
                 (parse (third s-exp)))]
           [(-)
            (check-pieces s-exp 3 "subtraction")
            (sub (parse (second s-exp))
                 (parse (third s-exp)))]
           [(with)
            (check-pieces s-exp 3 "with")
            (check-pieces (second s-exp) 2 "with binding pair")
            (unless (symbol? (first (second s-exp)))
              (error 'parse "expected variable name, got: ~a" (first (second s-exp))))
            (with (first (second s-exp))
                  (parse (second (second s-exp)))
                  (parse (third s-exp)))]
           [(if0)
            (check-pieces s-exp 4 "if0")
            (if0 (parse (second s-exp))
                 (parse (third s-exp))
                 (parse (fourth s-exp)))]
           [else
            (check-piece (list (first s-exp)) 1 "function application")
            (unless (symbol? (first s-exp))
              (error 'parse "expected a function name, got: ~a" (first s-exp)))
            (app (first s-exp)
                 (map parse (rest s-exp)))])]
        [else
         (error 'parse "expected an F1WAE, got: ~a" s-exp)]))

(define (parse-defn def-expr)
  (case (first def-expr)
    [(deffun)
       (check-pieces def-expr 3 "deffun")
       
       (define (illdef? def-expr bool-lst)
         (if (empty? def-expr) false
             (if (member (first def-expr) bool-lst)
                 true
                 (illdef? (rest def-expr) (append (list (first def-expr)) bool-lst)))))
       
       (cond
         [(illdef? (rest (second def-expr)) '()) (error "bad syntax" def-expr)]
         [else (fundef (first (second def-expr))
                       (rest (second def-expr))
                       (parse (third def-expr)))])]
    [else (parse-error "deffun" def-expr)]))

(define (lookup name ds)
  (type-case DefSub ds
    [mtSub () (error 'lookup "free identifier")]
    [aSub (n num rest)
          (if (equal? n name)
              num
              (lookup name rest))]))

(define (lookup-fundef name fundefs)
  (cond [(empty? fundefs)
         (error 'interp "undefined function: ~a" name)]
        [(equal? name (fundef-fun-name (first fundefs)))
         (first fundefs)]
        [else
         (lookup-fundef name (rest fundefs))]))

(define (interp an-fnwae fundefs ds)
  (type-case FnWAE an-fnwae
    [num (n) n]
    [add (l r) (+ (interp l fundefs ds) (interp r fundefs ds))]
    [sub (l r) (- (interp l fundefs ds) (interp r fundefs ds))]
    [with (name named-expr body)
          (interp
           body
           fundefs
           (aSub name (interp named-expr fundefs ds) ds))]
    [id (name) (lookup name ds)]
    ;can do better
    [if0 (expr1 expr2 expr3)
         (case (interp expr1 fundefs ds)
           [(0) (interp expr2 fundefs ds)]
           [else (interp expr3 fundefs ds)])]
    [app (fun-name arg)
         (local [(define a-fundef
                   (lookup-fundef fun-name fundefs))]

           (define (my-help body arg dslst)
             (if (and (not (empty? arg)) (empty? body)) (error "wrong arity")
               (if (and (empty? arg) (not (empty? body))) (error "wrong arity")
                   (if (empty? body)
                       dslst                 
                       (my-help (rest body)
                                (rest arg)
                                (aSub (first body)
                                      (interp (first arg) fundefs ds)
                                      dslst))))))
          
         (type-case FunDef a-fundef
           [fundef (fun-name param-name body)
                   (interp body
                           fundefs
                           (my-help param-name
                                    arg
                                    (mtSub)))]))]))

(define (interp-expr an-fnwae fundefs)
  (interp an-fnwae fundefs (mtSub)))

(define mult-and-neg-deffuns
  (list `{deffun {neg? x} {help1 x x}}
        `{deffun {mult x y} {if0 {neg? y}
                                 {- 0 {help2 x {- 0 y}}}
                                 {help2 x y}}}
        `{deffun {help1 x y} {if0 x 1 {if0 y 0 {help1 {- x 1} {+ y 1}}}}}
        `{deffun {help2 x y} {if0 y 0 {+ x {mult x {- y 1}}}}}))
        ; other deffuns okay, too, for your helpers

(test/exn (interp-expr (parse '{with {x y} 1})
                  (list))
          "free identifier")

(test/exn (interp-expr (parse '{f 1 2})
                  (list (parse-defn '{deffun {f x x} {+ x x}})))
          "bad syntax")

(test/exn (interp-expr (parse '{f x})
                  (list (parse-defn '{deffun {g a b c} c})))
          "undefined function")

(test/exn (interp-expr (parse '{f 1})
                  (list (parse-defn '{deffun {f x y} {+ x y}})))
          "wrong arity")

(test/exn (interp-expr (parse '{f x})
                  (list (parse-defn '{deffun {f a b c} c})))
          "free identifier")

(test/exn (interp-expr (parse '(f 1 2 3))
                  (list (parse-defn '(deffun (f x y) (+ x y)))))
          "wrong arity")

(test/exn (interp-expr (parse '(f 1 2 3 4 5))
                  (list (parse-defn '(deffun (f x y) (+ x y)))))
          "wrong arity")

(test/exn (interp-expr (parse '(f 8 2 7 11))
                  (list (parse-defn '(deffun (f x y z) (+ x y)))))
          "wrong arity")

(test (interp-expr (parse '{f 1 2})
                   (list (parse-defn '{deffun {f x y} {+ x y}})))
      3)

(test (interp-expr (parse '{+ {f} {f}})
                   (list (parse-defn '{deffun {f} 5})))
      10)

(test (parse '{f 1 2})
      (app 'f (list (num 1) (num 2))))

(test (parse '{if0 1 2})
      (app 'if0 (list (num 1) (num 2))))

(test (interp-expr (parse '{if0 {+ 0 0} {+ 0 10} 3}) '()) 10)

(test (interp-expr (parse '{if0 {+ 0 1} {+ 0 10} 3}) '()) 3)

(test (interp-expr (parse '{if0 0 1 2}) '()) 1)

(test (interp-expr (parse '{if0 1 2 3}) '()) 3)

(test (interp-expr (parse '{mult 3 9})
                   (list
                    (parse-defn (first mult-and-neg-deffuns))
                    (parse-defn (second mult-and-neg-deffuns))
                    (parse-defn (third mult-and-neg-deffuns))
                    (parse-defn (fourth mult-and-neg-deffuns))))
      27)

(test (interp-expr (parse '{mult -3 9})
                   (list
                    (parse-defn (first mult-and-neg-deffuns))
                    (parse-defn (second mult-and-neg-deffuns))
                    (parse-defn (third mult-and-neg-deffuns))
                    (parse-defn (fourth mult-and-neg-deffuns))))
      -27)

(test (interp-expr (parse '{mult 486 31})
                   (list
                    (parse-defn (first mult-and-neg-deffuns))
                    (parse-defn (second mult-and-neg-deffuns))
                    (parse-defn (third mult-and-neg-deffuns))
                    (parse-defn (fourth mult-and-neg-deffuns))))
      15066)

(test (interp-expr (parse '{mult 97 -73})
                   (list
                    (parse-defn (first mult-and-neg-deffuns))
                    (parse-defn (second mult-and-neg-deffuns))
                    (parse-defn (third mult-and-neg-deffuns))
                    (parse-defn (fourth mult-and-neg-deffuns))))
      -7081)