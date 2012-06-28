module Func (A : Set) where

infix 2 _≡_

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

A→A : Set
A→A = A → A

id : A→A
id a = a
 
_∙_ : A→A → A→A → A→A
_∙_ f g a = g (f a)

id∙f≡f : (f : A→A) (a : A) →
  (id ∙ f) a ≡ f a
id∙f≡f f a = refl

f∙id≡f : (f : A→A) (a : A) →
  (f ∙ id) a ≡ f a
f∙id≡f f a = refl

∙assoc : (f g h : A→A) (a : A) →
  (f ∙ (g ∙ h)) a ≡ ((f ∙ g) ∙ h) a
∙assoc f g h a = refl

-- A→AMonoid : Monoid
-- A→AMonoid = record
--   { Domain = A→A
--   ; e = id
--   ; ident-law = λ f → id∙f≡f f , f∙id≡f f
--   ; assoc-law = ∙assoc
--   }
  

