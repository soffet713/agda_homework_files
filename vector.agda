module vector where

open import bool
open import eq
open import nat
open import nat-thms

----------------------------------------------------------------------
-- datatypes
----------------------------------------------------------------------

data 𝕍 {ℓ} (A : Set ℓ) : ℕ → Set ℓ where
  []𝕍 : 𝕍 A 0
  _::𝕍_ : {n : ℕ} (x : A) (xs : 𝕍 A n) → 𝕍 A (suc n)

----------------------------------------------------------------------
-- syntax
----------------------------------------------------------------------

infixr 5 _::𝕍_ _++𝕍_

----------------------------------------------------------------------
-- operations
----------------------------------------------------------------------

[_]𝕍 : ∀ {ℓ} {A : Set ℓ} → A → 𝕍 A 1
[ x ]𝕍 = x ::𝕍 []𝕍

_++𝕍_ : ∀ {ℓ} {A : Set ℓ}{n m : ℕ} → 𝕍 A n → 𝕍 A m → 𝕍 A (n + m)
[]𝕍        ++𝕍 ys = ys
(x ::𝕍 xs) ++𝕍 ys = x ::𝕍 (xs ++𝕍 ys)

map𝕍 : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'}{n : ℕ} → (A → B) → 𝕍 A n → 𝕍 B n
map𝕍 f []𝕍       = []𝕍
map𝕍 f (x ::𝕍 xs) = f x ::𝕍 map𝕍 f xs

head𝕍 : ∀ {ℓ} {A : Set ℓ}{n : ℕ} → 𝕍 A (suc n) → A
head𝕍 (x ::𝕍 _) = x

tail𝕍 : ∀ {ℓ} {A : Set ℓ}{n : ℕ} → 𝕍 A (suc n) → 𝕍 A n
tail𝕍 (_ ::𝕍 xs) = xs

nth𝕍 : ∀ {ℓ} {A : Set ℓ} → (n : ℕ) → {m : ℕ} → n < m ≡ tt → 𝕍 A m → A
nth𝕍 0 _ (x ::𝕍 _) = x
nth𝕍 (suc n) p (_ ::𝕍 xs) = nth𝕍 n p xs
nth𝕍 (suc n) () []𝕍
nth𝕍 0 () []𝕍

repeat𝕍 : ∀ {ℓ} {A : Set ℓ} → (a : A)(n : ℕ) → 𝕍 A n
repeat𝕍 a 0 = []𝕍
repeat𝕍 a (suc n) = a ::𝕍 (repeat𝕍 a n)

foldl𝕍 : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'} → B → (B → A → B) → {n : ℕ} → 𝕍 A n → 𝕍 B n
foldl𝕍 b _f_ []𝕍 = []𝕍
foldl𝕍 b _f_ (x ::𝕍 xs) = let r = (b f x) in r ::𝕍 (foldl𝕍 r _f_  xs)

zipWith𝕍 : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ}{B : Set ℓ'}{C : Set ℓ''} → 
           (A → B → C) → {n : ℕ} → 𝕍 A n → 𝕍 B n → 𝕍 C n
zipWith𝕍 f []𝕍 []𝕍 = []𝕍
zipWith𝕍 _f_ (x ::𝕍 xs) (y ::𝕍 ys) = (x f y) ::𝕍 (zipWith𝕍 _f_ xs ys)

last𝕍 : ∀{ℓ}{A : Set ℓ}{n : ℕ} → (k : ℕ) → 𝕍 A (k + n) → 𝕍 A k
last𝕍{n = 0} k xs rewrite +0 k = xs
last𝕍{n = suc n} k xs rewrite +suc k n = last𝕍{n = n} k (tail𝕍 xs)

