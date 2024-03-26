module nat-todo where

open import lib

infixl 11 _pow_

-- 10 points to define x pow y so that it computes x to the power y.
-- So 2 pow 3 should equal 8, for example.
_pow_ : ℕ → ℕ → ℕ
x pow 0 = 1
x pow 1 = x
x pow y = (suc x) * x

-- 10 points.  The factorial of a number equals that number times all smaller numbers except 0.
-- So factorial 4 = 4 * 3 * 2 * 1 = 24.
factorial : ℕ → ℕ
factorial zero = 0
factorial 1 = 1
factorial x = (suc x) * x

-- 12 points
*1 : ∀ {n : ℕ} → n * 1 ≡ n
*1 {zero} = refl
*1 {suc x} rewrite *1 {x} = refl

-- 12 points
1-pow : ∀ {n : ℕ} → 1 pow n ≡ 1
1-pow {zero} = refl
1-pow {suc x} =  {!!}

-- 12 points
factorial-nonzero : ∀ (n : ℕ) → iszero (factorial n) ≡ ff
factorial-nonzero zero = {!!}
factorial-nonzero 1 = refl
factorial-nonzero (suc(suc x)) rewrite factorial-nonzero x = refl

-- 12 points. hint: try induction on y 
pow+ : ∀ (x y z : ℕ) → x pow (y + z) ≡ (x pow y) * (x pow z)
pow+ zero y z = refl
pow+ x y z rewrite *distribr x y z | +assoc z (x * z) (y * z) = refl

-- 12 points
nonzero< : ∀ {n : ℕ} → iszero n ≡ ff → 0 < n ≡ tt
nonzero< zero = refl

-- 12 points
--parity-odd : ∀ (x : ℕ) → parity (x * 2 + 1) ≡ tt
--parity-odd = {!!}

-- 12 points
=ℕ-sym : ∀ (x y : ℕ) → (x =ℕ y) ≡ (y =ℕ x)
=ℕ-sym x y = {!!}

-- another version of addition
_+'_ : ℕ → ℕ → ℕ
0 +' y = y
suc x +' y = x +' (suc y)

-- 12 points. You are not allowed to call +comm when proving this one
-- (though you can certainly borrow ideas from the code for +comm):
+'comm : ∀ (x y : ℕ) → x +' y ≡ y +' x
+'comm zero y = {!!}
+'comm (suc x) y = {!!}

-- 12 points
+'-equiv-+ : ∀ (x y : ℕ) → x + y ≡ x +' y
+'-equiv-+ = {!!}

-- 12 points
+inj1 : ∀ {x y z : ℕ} → x + y ≡ x + z → y ≡ z
+inj1 = {!!}

-- 12 points
+inj2 : ∀ {x y z : ℕ} → x + z ≡ y + z → x ≡ y
+inj2 = {!!}

-- 12 points
*distribl : ∀ (x y z : ℕ) → x * (y + z) ≡ x * y + x * z
*distribl = {!!}

-- 12 points
pow* : ∀ (x y z : ℕ) → x pow (y * z) ≡ (x pow y) pow z
pow* = {!!}

-- 12 points
*inj1 : ∀ {x y z : ℕ} → x ≢ 0 → x * y ≡ x * z → y ≡ z
*inj1 = {!!}

-- 12 points
*inj2 : ∀ {x y z : ℕ} → z ≢ 0 → x * z ≡ y * z → x ≡ y
*inj2 = {!!}

-- 13 points
factorial-mono : ∀ (x y : ℕ) → 0 < x ≡ tt → x < y ≡ tt → factorial x < factorial y ≡ tt
factorial-mono = {!!}

-- 13 points. x + y is odd (parity = tt) iff exactly one of x and y is odd
-- (either x is odd and y is even, or vice versa)
--parity-add : ∀ (x y : ℕ) → parity (x + y) ≡ (parity x) xor (parity y)
--parity-add = {!!}

-- 13 points. x * y is odd (parity = tt) iff x is odd and y is odd.
--parity-mult : ∀ (x y : ℕ) → parity (x * y) ≡ (parity x) && (parity y)
--parity-mult = {!!}

-- 15 points. [probably hard] this might require case-splitting on whether or not x > z
+∸ : ∀ (x y z : ℕ) → (x + y) ∸ z ≡ (x ∸ z) + (y ∸ (z ∸ x))
+∸ = {!!}

module nat-todo where

open import lib

infixl 11 _pow_

-- 10 points to define x pow y so that it computes x to the power y.
-- So 2 pow 3 should equal 8, for example.
_pow_ : ℕ → ℕ → ℕ
x pow 0 = 1
x pow 1 = x
x pow y = (suc x) * x

-- 10 points.  The factorial of a number equals that number times all smaller numbers except 0.
-- So factorial 4 = 4 * 3 * 2 * 1 = 24.
factorial : ℕ → ℕ
factorial zero = 0
factorial 1 = 1
factorial x = (suc x) * x

-- 12 points
*1 : ∀ {n : ℕ} → n * 1 ≡ n
*1 {zero} = refl
*1 {suc x} rewrite *1 {x} = refl

-- 12 points
1-pow : ∀ {n : ℕ} → 1 pow n ≡ 1
1-pow {zero} = {!refl!}
1-pow {suc x} = {!!}

-- 12 points
factorial-nonzero : ∀ (n : ℕ) → iszero (factorial n) ≡ ff
factorial-nonzero zero = {!!}
factorial-nonzero 1 = refl
factorial-nonzero (suc(suc x)) rewrite factorial-nonzero x = refl

-- 12 points. hint: try induction on y 
pow+ : ∀ (x y z : ℕ) → x pow (y + z) ≡ (x pow y) * (x pow z)
pow+ = {!!}

-- 12 points
nonzero< : ∀ {n : ℕ} → iszero n ≡ ff → 0 < n ≡ tt
nonzero< = {!!}

-- 12 points
parity-odd : ∀ (x : ℕ) → parity (x * 2 + 1) ≡ tt
parity-odd 0 = refl
parity-odd (suc x) rewrite parity-odd x = refl

-- 12 points
=ℕ-sym : ∀ (x y : ℕ) → (x =ℕ y) ≡ (y =ℕ x)
=ℕ-sym x y = {!!}

-- another version of addition
_+'_ : ℕ → ℕ → ℕ
0 +' y = y
suc x +' y = x +' (suc y)

-- 12 points. You are not allowed to call +comm when proving this one
-- (though you can certainly borrow ideas from the code for +comm):
+'comm : ∀ (x y : ℕ) → x +' y ≡ y +' x
+'comm = {!!}

-- 12 points
+'-equiv-+ : ∀ (x y : ℕ) → x + y ≡ x +' y
+'-equiv-+ 0 y = {!refl!}
+'-equiv-+ (suc x) y = {!!}

-- 12 points
+inj1 : ∀ {x y z : ℕ} → x + y ≡ x + z → y ≡ z
+inj1 = {!!}

-- 12 points
+inj2 : ∀ {x y z : ℕ} → x + z ≡ y + z → x ≡ y
+inj2 = {!!}

-- 12 points
*distribl : ∀ (x y z : ℕ) → x * (y + z) ≡ x * y + x * z
*distribl 0 y z = {!refl!}
*distribl (suc x) 0 z = {!!}
*distribl (suc x) (suc y) z = {!!}

-- 12 points
pow* : ∀ (x y z : ℕ) → x pow (y * z) ≡ (x pow y) pow z
pow* = {!!}

-- 12 points
*inj1 : ∀ {x y z : ℕ} → x ≢ 0 → x * y ≡ x * z → y ≡ z
*inj1 = {!!}

-- 12 points
*inj2 : ∀ {x y z : ℕ} → z ≢ 0 → x * z ≡ y * z → x ≡ y
*inj2 = {!!}

-- 13 points
factorial-mono : ∀ (x y : ℕ) → 0 < x ≡ tt → x < y ≡ tt → factorial x < factorial y ≡ tt
factorial-mono 0 y = {!!}
factorial-mono (suc x) y = {!!}

-- 13 points. x + y is odd (parity = tt) iff exactly one of x and y is odd
-- (either x is odd and y is even, or vice versa)
parity-add : ∀ (x y : ℕ) → parity (x + y) ≡ (parity x) xor (parity y)
parity-add 0 y = {!refl!}
parity-add (suc x) y rewrite parity-add x y = {!refl!}

-- 13 points. x * y is odd (parity = tt) iff x is odd and y is odd.
parity-mult : ∀ (x y : ℕ) → parity (x * y) ≡ (parity x) && (parity y)
parity-mult = {!!}

-- 15 points. [probably hard] this might require case-splitting on whether or not x > z
+∸ : ∀ (x y z : ℕ) → (x + y) ∸ z ≡ (x ∸ z) + (y ∸ (z ∸ x))
+∸ = {!!}

