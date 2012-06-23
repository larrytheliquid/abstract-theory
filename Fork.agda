module Fork where
open import Data.Product
open import Function hiding ( id )
open import Relation.Binary.PropositionalEquality

infix 4 _≣_

id : {A : Set} → A → A
id x = x

_≣_ : {A B : Set} (f g : A → B) → Set
f ≣ g = ∀ a → f a ≡ g a

fork : {A B C : Set} (f : A → B) (g : A → C) → A → B × C
fork f g a = f a , g a

proj₁-eliminates-fork : {A B C : Set} {f : A → B} {g : A → C} →
  proj₁ ∘ fork f g ≣ f
proj₁-eliminates-fork a = refl

proj₂-eliminates-fork : {A B C : Set} {f : A → B} {g : A → C} →
  proj₂ ∘ fork f g ≣ g
proj₂-eliminates-fork a = refl

pair-former-is-a-fork : {A B C : Set} (h : A → B × C) →
  fork (proj₁ ∘ h) (proj₂ ∘ h) ≣ h
pair-former-is-a-fork h a with h a
... | b , c = refl

id-is-a-fork : {A B : Set} →
  fork proj₁ proj₂ ≣ id {A × B}
id-is-a-fork (a , b) = refl
