module Equiv where

infix  2 _∎
infixr 2 _⇔⟨_⟩_
infixr 4 _,_
infixr 9 _∘_

id : {A : Set} → A → A
id a = a

_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
_∘_ g f a = g (f a)

record _⇔_ (A B : Set) : Set where
  constructor _,_
  field to : A → B
        from : B → A

refl : (A : Set) → A ⇔ A
refl A = id , id

sym : {A B : Set} → A ⇔ B → B ⇔ A
sym (to , from) = from , to

trans : {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
trans (ab , ba) (bc , cb) = bc ∘ ab , ba ∘ cb

_∎ : (A : Set) → A ⇔ A
_∎ = refl

_⇔⟨_⟩_ : (A : Set) {B C : Set} →
  A ⇔ B → B ⇔ C → A ⇔ C
A ⇔⟨ ab ⟩ bc = trans ab bc



