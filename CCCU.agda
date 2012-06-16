module CCCU where
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.List
open import Data.Product hiding ( map )

data U : Set where
  `⊤ `Bool `ℕ : U
  `List : (A : U) → U
  _`×_ _`→_ : (A B : U) → U

⟦_⟧ : U → Set
⟦ `⊤ ⟧ = ⊤
⟦ `Bool ⟧ = Bool
⟦ `ℕ ⟧ = ℕ
⟦ `List A ⟧ = List ⟦ A ⟧
⟦ A `× B ⟧ = ⟦ A ⟧ × ⟦ B ⟧
⟦ A `→ B ⟧ = ⟦ A ⟧ → ⟦ B ⟧

_∘_ : ∀ {A B C} (g : ⟦ B `→ C ⟧) (f : ⟦ A `→ B ⟧) → ⟦ A `→ C ⟧
_∘_ g f a = g (f a)

fork : ∀ {A B C} (f : ⟦ A `→ B ⟧) (g : ⟦ A `→ C ⟧) → ⟦ A `→ (B `× C) ⟧
fork f g a = f a , g a

fmap : ∀ {A B} (f : ⟦ A `→ B ⟧) → ⟦ `List A ⟧ → ⟦ `List B ⟧
fmap f [] = []
fmap {A} {B} f (x ∷ xs) = f x ∷ fmap {A} {B} f xs

