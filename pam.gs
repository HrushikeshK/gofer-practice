-- Write a function that take list of functions and apply on a single integer

pam1 : [a->b] -> a -> [b]
pam1.(f::fs).x = f.x :: pam1.fs.x
pam1.[].x = []

pam2 : [a->b] -> a -> [b]
pam2.fs.x = [ f.x | f <- fs ]

pam3.fs.x = map.(\h -> h.x).fs
pamEetaFn.x.fs = map.(.x).fs

{-
- Apply section rule and Eeta rule
- Section rules: x 'op' y = ('op'.x).y = ('op').x.y
- Eeta rule: If f.x = g.x then f = g
-}

