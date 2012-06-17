module Monoids where
open import Data.Bool hiding ( T )
open import Data.Nat

infix 2 _≡_

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

cong : {A B : Set} {x y : A} (f : A → B) →
  x ≡ y → f x ≡ f y
cong f refl = refl

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

record Monoid : Set₁ where
  field
    S : Set
    e : S
    _⊙_ : (x y : S) → S
    ident : (x : S) →
      (e ⊙ x ≡ x) × (x ⊙ e ≡ x)
    assoc : (x y z : S) →
      (x ⊙ (y ⊙ z)) ≡ ((x ⊙ y) ⊙ z)

0+n≡n : (n : ℕ) →
  zero + n ≡ n
0+n≡n n = refl

n+0≡n : (n : ℕ) →
  n + zero ≡ n
n+0≡n zero = refl
n+0≡n (suc n) = cong suc (n+0≡n n)

+assoc : (x y z : ℕ) →
  (x + (y + z)) ≡ ((x + y) + z)
+assoc zero y z = refl
+assoc (suc x) y z = cong suc (+assoc x y z)

Monoid∶ℕ+0 : Monoid
Monoid∶ℕ+0 = record
  { S = ℕ
  ; e = 0
  ; _⊙_ = _+_
  ; ident = λ n → 0+n≡n n , n+0≡n n
  ; assoc = +assoc
  }

false∨b≡b : (b : Bool) →
  false ∨ b ≡ b
false∨b≡b b = refl

b∨false≡b : (b : Bool) →
  b ∨ false ≡ b
b∨false≡b true = refl
b∨false≡b false = refl

∨assoc : (x y z : Bool) →
  (x ∨ (y ∨ z)) ≡ ((x ∨ y) ∨ z)
∨assoc true y z = refl
∨assoc false y z = refl

Monoid∶Bool∨false : Monoid
Monoid∶Bool∨false = record
  { S = Bool
  ; e = false
  ; _⊙_ = _∨_
  ; ident = λ b → false∨b≡b b , b∨false≡b b
  ; assoc = ∨assoc
  }

id : {A : Set} → A → A
id a = a

_∘_ : {A B C : Set} (g : B → C) (f : A → B) → A → C
_∘_ g f a = g (f a)

record Isomorphism : Set₁ where
  field
    S T : Set
    to : S → T
    from : T → S
    from∘to≡id : (s : S) → (from ∘ to) s ≡ id s
    to∘from≡id : (t : T) → (to ∘ from) t ≡ id t

-- TODO Bool monoid and homomorphism
