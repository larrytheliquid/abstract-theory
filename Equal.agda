module Equal where

infix  2 _∎
infixr 2 _≡⟨_⟩_
infixr 9 _∘_

id : {A : Set} → A → A
id a = a

_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
_∘_ g f a = g (f a)

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

sym : {A : Set} {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl bc = bc

_∎ : {A : Set} (a : A) → a ≡ a
a ∎ = refl

_≡⟨_⟩_ : {A : Set} (a : A) {b c : A} →
  a ≡ b → b ≡ c → a ≡ c
a ≡⟨ ab ⟩ bc = trans ab bc



