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
  infixr 9 _⊙_

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

record Homomorphism (M M′ : Monoid) : Set₁ where
  open Monoid M
  open Monoid M′ renaming
    ( S to S′ ; e to e′ ; _⊙_ to _⊙′_ )

  field
    f : S → S′
    preserves-e : f e ≡ e′
    preserves-⊙ : (x y : S) →
      f (x ⊙ y) ≡ f x ⊙′ f y

-- preserves the properties of being greater than zero
gtz : ℕ → Bool
gtz zero = false
gtz (suc n) = true

gtz0≡false : gtz 0 ≡ false
gtz0≡false = refl

gtz-preserves+ : (m n : ℕ) →
  gtz (m + n) ≡ gtz m ∨ gtz n
gtz-preserves+ zero n = refl
gtz-preserves+ (suc m) n = refl

-- preserves the properties of being the unit element
kf : ℕ → Bool
kf n = false

kf0≡false : kf 0 ≡ false
kf0≡false = refl

kf-preserves+ : (m n : ℕ) →
  kf (m + n) ≡ kf m ∨ kf n
kf-preserves+ m n = refl

-- ℕ→Parity preserves the properties of being even or odd

Homomorphism∶gtz : Homomorphism Monoid∶ℕ+0 Monoid∶Bool∨false
Homomorphism∶gtz = record
  { f = gtz
  ; preserves-e = gtz0≡false
  ; preserves-⊙ = gtz-preserves+
  }

Homomorphism∶kf : Homomorphism Monoid∶ℕ+0 Monoid∶Bool∨false
Homomorphism∶kf = record
  { f = kf
  ; preserves-e = kf0≡false
  ; preserves-⊙ = kf-preserves+
  }

record NaturalTransformation {M M′ : Monoid} (F G : Homomorphism M M′) : Set₁ where
  open Homomorphism F
  open Homomorphism G renaming ( f to g )
  open Monoid M
  open Monoid M′ renaming
    ( S to S′ ; e to e′ ; _⊙_ to _⊙′_ )

  field
    h : S → S′
    natural : (x y z : S) →
      h (x ⊙ y ⊙ z) ≡ f x ⊙′ h y ⊙′ g z

kt : ℕ → Bool
kt n = true

kt-natural-for-gtz-kf : (m n o : ℕ) →
  kt (m + (n + o)) ≡ gtz m ∨ kt n ∨ kf o
kt-natural-for-gtz-kf zero n o = refl
kt-natural-for-gtz-kf (suc m) n o = refl

NaturalTransformation∶kt-gtz-kf : NaturalTransformation Homomorphism∶gtz Homomorphism∶kf
NaturalTransformation∶kt-gtz-kf = record
  { h = kt
  ; natural = kt-natural-for-gtz-kf
  }

----------------------------------------------------------------------

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
