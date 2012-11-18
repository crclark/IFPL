module Variables where


type Variable = String

--infinite supply of variable names, for alpha conversion and such
variables :: [Variable] 
variables = az ++ (concat $ map aznum [1..])
 where az = [[x] | x <- ['a'..'z']]
       aznum n = map (++ (show n)) az
