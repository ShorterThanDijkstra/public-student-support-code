(let ([x (+ 42 (- 10 (let ([y 17]) (+ y (let ([z 13]) (+ z (- 11 12)))))))])
(+ x 10))