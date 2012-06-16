module Func (A : Set) where

infix 2 _≡_

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

Func : Set
Func = A → A

id : Func
id a = a

_∘_ : Func → Func → Func
_∘_ g f a = g (f a)

id∘f≡f : (f : Func) (a : A) →
  (id ∘ f) a ≡ f a
id∘f≡f f a = refl

f∘id≡f : (f : Func) (a : A) →
  (f ∘ id) a ≡ f a
f∘id≡f f a = refl

∘assoc : (h g f : Func) (a : A) →
  (h ∘ (g ∘ f)) a ≡ ((h ∘ g) ∘ f) a
∘assoc h g f a = refl

-- FuncMonoid : Monoid
-- FuncMonoid = record
--   { Domain = Func
--   ; e = id
--   ; ident-law = λ f → id∘f≡f f , f∘id≡f f
--   ; assoc-law = ∘assoc
--   }
  

