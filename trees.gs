
ctype BT where
  ET : BT
  MT : (Int, BT, BT) -> BT


bfs.ET = []
bfs.(MT.(x,l,r)) = [x] ++ bfsv.l ++ bfsv.r ++ prb.(app.([l] ++ [r]))
bfsv.(MT.(x,l,r)) = [x]
bfsv.ET = []
prb.(x::xs) = bfsv.x ++ prb.xs
prb.[] = []
app.(x::xs) = getl.x ++ getr.x ++ app.xs ++ app.(getl.x ++ getr.x)
--app.(MT.(i,l,r)::xs)  =
--app.(ET::xs)
app.[] = []
getl.(MT.(x,l,r)) = [l]
getl.ET = []
getr.(MT.(x,l,r)) = [r]
getr.ET = []

sumbt.(x) = sum.(bfs.x)

l0 = ET
l1 = MT.(1,l2,l3)
l2 = MT.(2,l4,l5)
l3 = MT.(3,l6,l7)
l4 = MT.(4,l8,l0)
l5 = MT.(5,l0,l0)
l6 = MT.(6,l0,l0)
l7 = MT.(7,l0,l0)
l8 = MT.(8,l0,l0)


-- Print last element of the list    
lst: [a] -> [a]     
lst.(x::(y::ys)) = lst.(y::ys)
lst.(x::xs) = [x]
lst.[] = []
