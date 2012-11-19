{-Author: Connor Clark
This module defines a translation function from lambda calculus to SKI
todo: test the translation of nested abstractions! Such as \x -> \y -> y

-}
module LCtoSKI (translate) where

import LC as LC
import SKI as SKI
import Constants as C
import Variables

--Trans is an intermediate data type for translating LC to SKI. Basically just SKI + variables.
data Trans = TransVar Variable
             |TransConstant C.Constant
             |TransS
             |TransK
             |TransI
             |TransY
             |TransIf
             |TransApp Trans Trans
             deriving (Eq, Ord, Show, Read)

transToSKI :: Trans -> SKI.SKI
transToSKI (TransVar _) = error "Variable remaining in intermediate representation! Bug in translator!"
transToSKI (TransConstant c) = SKI.SKIConstant c
transToSKI (TransS) = SKI.S
transToSKI (TransK) = SKI.K
transToSKI (TransI) = SKI.I
transToSKI (TransApp x y) = SKI.SKIApp (transToSKI x) (transToSKI y)
transToSKI (TransIf) = SKI.SKIIf
transToSKI (TransY) = SKI.Y

translate :: LC.LC -> SKI.SKI
translate = transToSKI . translate'

translate' :: LC.LC -> Trans
translate' (LC.LCConstant c) = TransConstant c
translate' (LC.LCApp x y) = TransApp (translate' x) (translate' y)
translate' (LC.LCAbs var body) = abstract var (translate' body)
translate' (LC.LCVar v) = TransVar v
translate' (LC.LCIf) = TransIf
translate' (LC.LCY) = TransY

class Abstractable a where
 abstract :: Variable -> a -> Trans
 
instance Abstractable LC.LC where
 abstract x (LC.LCApp y z) = TransApp (TransApp TransS (abstract x y)) (abstract x z)
 abstract x (LC.LCVar y) = if x == y then TransI else TransApp TransK (TransVar y)
 abstract x (LC.LCConstant c) = TransApp TransK $ TransConstant c 

instance Abstractable Trans where
 abstract x (TransVar y) = if x == y then TransI else TransApp TransK (TransVar y)
 abstract x (TransConstant c) = TransApp TransK $ TransConstant c
 abstract x TransS = TransApp TransK TransS
 abstract x TransK = TransApp TransK TransK
 abstract x TransI = TransApp TransK TransI
 abstract x TransY = TransApp TransK TransY
 abstract x TransIf = TransApp TransK TransIf
 abstract x (TransApp y z) = TransApp (TransApp TransS (abstract x y)) (abstract x z)
