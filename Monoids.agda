module Monoids where
open import Data.Bool hiding ( T )
open import Data.Nat hiding ( Ordering )
open import Prelude
open import Equiv

cong : {A B : Set} {x y : A} (f : A → B) →
  x ≡ y → f x ≡ f y
cong f equal = equal

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
0+n≡n n = equal

n+0≡n : (n : ℕ) →
  n + zero ≡ n
n+0≡n zero = equal
n+0≡n (suc n) = cong suc (n+0≡n n)

+assoc : (x y z : ℕ) →
  (x + (y + z)) ≡ ((x + y) + z)
+assoc zero y z = equal
+assoc (suc x) y z = cong suc (+assoc x y z)

Monoid∶ℕ+0 : Monoid
Monoid∶ℕ+0 = record
  { S = ℕ
  ; e = 0
  ; _⊙_ = _+_
  ; ident = λ n → 0+n≡n n , n+0≡n n
  ; assoc = +assoc
  }

data Order : Set where
  less same greater : Order

_⟪_ : Order → Order → Order
less ⟪ _ = less
same ⟪ y = y
greater ⟪ _ = greater

same⟪o≡o : (o : Order) →
  same ⟪ o ≡ o
same⟪o≡o o = equal

o⟪same≡o : (o : Order) →
  o ⟪ same ≡ o
o⟪same≡o less = equal
o⟪same≡o same = equal
o⟪same≡o greater = equal

⟪assoc : (x y z : Order) →
  (x ⟪ (y ⟪ z)) ≡ ((x ⟪ y) ⟪ z)
⟪assoc less y z = equal
⟪assoc same y z = equal
⟪assoc greater y z = equal

Monoid∶Order⟪same : Monoid
Monoid∶Order⟪same = record
  { S = Order
  ; e = same
  ; _⊙_ = _⟪_
  ; ident = λ o → same⟪o≡o o , o⟪same≡o o
  ; assoc = ⟪assoc
  }

false∨b≡b : (b : Bool) →
  false ∨ b ≡ b
false∨b≡b b = equal

b∨false≡b : (b : Bool) →
  b ∨ false ≡ b
b∨false≡b true = equal
b∨false≡b false = equal

∨assoc : (x y z : Bool) →
  (x ∨ (y ∨ z)) ≡ ((x ∨ y) ∨ z)
∨assoc true y z = equal
∨assoc false y z = equal

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
gtz0≡false = equal

gtz-preserves+ : (m n : ℕ) →
  gtz (m + n) ≡ gtz m ∨ gtz n
gtz-preserves+ zero n = equal
gtz-preserves+ (suc m) n = equal

-- preserves the properties of being the unit element
kf : ℕ → Bool
kf n = false

kf0≡false : kf 0 ≡ false
kf0≡false = equal

kf-preserves+ : (m n : ℕ) →
  kf (m + n) ≡ kf m ∨ kf n
kf-preserves+ m n = equal

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

record NaturalTransformation {M M′} (F G : Homomorphism M M′) : Set₁ where
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
kt-natural-for-gtz-kf zero n o = equal
kt-natural-for-gtz-kf (suc m) n o = equal

NaturalTransformation∶kt-gtz-kf : NaturalTransformation Homomorphism∶gtz Homomorphism∶kf
NaturalTransformation∶kt-gtz-kf = record
  { h = kt
  ; natural = kt-natural-for-gtz-kf
  }

----------------------------------------------------------------------

record Isomorphism : Set₁ where
  field
    S T : Set
    to : S → T
    from : T → S
    from∘to≡id : (s : S) → (from ∘ to) s ≡ id s
    to∘from≡id : (t : T) → (to ∘ from) t ≡ id t

record Isomorphism′ : Set₁ where
  field
    A B : Set
    f : A → B
    fº : B → A
    charn : (a : A) (b : B) →
      a ≡ fº b ⇔ b ≡ f a

-- TODO Bool monoid and homomorphism
