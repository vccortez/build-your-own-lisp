; test fibonacci function
(fun {fib n} {
  select
    { (== n 0) 0 }
    { (== n 1) 1 }
    { otherwise (+ (fib (- n 1)) (fib (- n 2))) }
})

(print "should print the first 21 fibonacci numbers")
(print (map fib (range 0 20)))
