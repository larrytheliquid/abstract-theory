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

----------------------------------------------------------------------

infixr 4 _,_

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    π₁ : A
    π₂ : B
open _×_

fork : {A B C : Set} (f : A → B) (g : A → C) → A → B × C
fork f g a = f a , g a

π₁-eliminates-fork : {A B C : Set} (f : A → B) (g : A → C) (a : A) →
  (π₁ ∘ fork f g) a ≡ f a
π₁-eliminates-fork f g a =
  (π₁ ∘ fork f g) a
    ≡⟨ refl ⟩ -- composition
  π₁ (fork f g a)
    ≡⟨ refl ⟩ -- fork
  π₁ (f a , g a)
    ≡⟨ refl ⟩ -- π₁
  f a ∎

π₂-eliminates-fork : {A B C : Set} (f : A → B) (g : A → C) (a : A) →
  (π₂ ∘ fork f g) a ≡ g a
π₂-eliminates-fork f g a =
  (π₂ ∘ fork f g) a
    ≡⟨ refl ⟩ -- composition
  π₂ (fork f g a)
    ≡⟨ refl ⟩ -- fork
  π₂ (f a , g a)
    ≡⟨ refl ⟩ -- π₂
  g a ∎

pair-former-is-a-fork : {A B C : Set} (h : A → B × C) (a : A) →
  (fork (π₁ ∘ h) (π₂ ∘ h)) a ≡ h a
pair-former-is-a-fork h a =
  (fork (π₁ ∘ h) (π₂ ∘ h)) a
    ≡⟨ refl ⟩ -- composition
  π₁ (h a) , π₂ (h a)
    ≡⟨ {!!} ⟩
  h a ∎
