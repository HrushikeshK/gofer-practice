-- Write a function that take list of functions and apply on a single integer

pam1 : [a->b] -> a -> [b]
pam1.(f::fs).x = f.x :: pam1.fs.x
pam1.[].x = []

pam2 : [a->b] -> a -> [b]
pam2.fs.x = [ f.x | f <- fs ]

pam3.fs.x = map.(\h -> h.x).fs
pamEtaFn.x.fs = map.(.x).fs

-- Prove 1 and 2 are equivalent
pamdot.f.xs = [f.x | x <- xs]	-- 1
finalpam = flip.(flip.(.);map)	-- 2


{-
- Apply section rule and Eeta rule
- Section rules: x 'op' y = ('op'.x).y = ('op').x.y
- Eeta rule: If f.x = g.x then f = g
-}

