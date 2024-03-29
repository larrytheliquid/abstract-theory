module CCC where

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

data Bool : Set where
  false true : Bool

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

id : {A : Set} → A → A
id a = a

_▸_ : {A B C : Set} (f : A → B) (g : B → C) → A → C
_▸_ f g a = g (f a)

-- TODO explicit reductions via equivalence reasoning

f▸id≡f : {A B : Set} (f : A → B) (a : A) →
  (f ▸ id) a ≡ f a
f▸id≡f f a = refl

id▸f≡f : {A B : Set} (f : A → B) (a : A) →
  (id ▸ f) a ≡ f a
id▸f≡f f a = refl

▸assoc : {A B C D : Set} 
  (f : A → B) (g : B → C) (h : C → D) (a : A) →
  (f ▸ (g ▸ h)) a ≡ ((f ▸ g) ▸ h) a
▸assoc f g h a = refl

π₁ : {A B : Set} → A × B → A
π₁ (a , b) = a

π₂ : {A B : Set} → A × B → B
π₂ (a , b) = b

fork : {A B C : Set} (f : A → B) (g : A → C) → A → B × C
fork f g a = f a , g a

map : ∀ {A B} (f : A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

