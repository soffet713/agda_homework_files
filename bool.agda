module bool where

open import level

----------------------------------------------------------------------
-- datatypes
----------------------------------------------------------------------

data 𝔹 : Set where
 tt : 𝔹
 ff : 𝔹

{-# BUILTIN BOOL  𝔹  #-}
{-# BUILTIN TRUE  tt  #-}
{-# BUILTIN FALSE ff #-}

{-# COMPILED_DATA 𝔹 Bool True False #-}

----------------------------------------------------------------------
-- syntax
----------------------------------------------------------------------

infix  7 ~_
infixl 6 _xor_
infixr 6 _&&_
infixr 5 _||_ 
infix  4 if_then_else_

----------------------------------------------------------------------
-- operations
----------------------------------------------------------------------

-- not
~_ : 𝔹 → 𝔹
~ tt = ff
~ ff = tt


-- and
_&&_ : 𝔹 → 𝔹 → 𝔹
tt && b = b
ff && b = ff

-- or
_||_ : 𝔹 → 𝔹 → 𝔹
tt || b = tt
ff || b = b

if_then_else_ : ∀ {ℓ} {A : Set ℓ} → 𝔹 → A → A → A
if tt then y else z = y
if ff then y else z = z

_xor_ : 𝔹 → 𝔹 → 𝔹 
tt xor ff = tt
ff xor tt = tt
tt xor tt = ff
ff xor ff = ff

