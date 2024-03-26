module list-test where

open import list
open import bool
open import eq

test1 : 𝕃 𝔹
test1 = tt :: tt :: tt :: []

test2 : 𝕃 𝔹
test2 = ff :: ff :: []

test3 = test1 ++ test2

test-lem : test3 ≡ tt :: tt :: tt :: ff :: ff :: []
test-lem = refl

test-lem2 : reverse test3 ≡ ff :: ff :: tt :: tt :: tt :: []
test-lem2 = refl