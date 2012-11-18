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
             |TransApp Trans Trans
             deriving (Eq, Ord, Show, Read)

transToSKI :: Trans -> SKI.SKI
transToSKI (TransVar _) = error "Variable remaining in intermediate representation! Bug in translator!"
transToSKI (TransConstant c) = SKI.SKIConstant c
transToSKI (TransS) = SKI.S
transToSKI (TransK) = SKI.K
transToSKI (TransI) = SKI.I
transToSKI (TransApp x y) = SKI.SKIApp (transToSKI x) (transToSKI y)

translate :: LC.LC -> SKI.SKI
translate = transToSKI . translate'

translate' :: LC.LC -> Trans
translate' (LC.LCConstant c) = TransConstant c
translate' (LC.LCApp x y) = TransApp (translate' x) (translate' y)
translate' (LC.LCAbs var body) = abstract var body
translate' (LC.LCVar v) = TransVar v

abstract :: Variable -> LC.LC -> Trans
abstract x (LC.LCApp y z) = TransApp (TransApp TransS (abstract x y)) (abstract x z)
abstract x (LC.LCVar y) = if x == y then TransI else TransApp TransK (TransVar y)
abstract x (LC.LCConstant c) = TransApp TransK $ TransConstant c 
