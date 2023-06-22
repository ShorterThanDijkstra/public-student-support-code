; #lang racket
(let ([y (let ([x1 20])
           (let ([x2 22])
             (+ x1 x2)))])
  y)