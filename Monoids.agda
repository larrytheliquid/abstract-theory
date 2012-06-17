module Monoids where
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
    ident-law : (x : S) →
      (e ⊙ x ≡ x) × (x ⊙ e ≡ x)
    assoc-law : (x y z : S) →
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

ℕMonoid : Monoid
ℕMonoid = record
  { S = ℕ
  ; e = 0
  ; _⊙_ = _+_
  ; ident-law = λ n → 0+n≡n n , n+0≡n n
  ; assoc-law = +assoc
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
