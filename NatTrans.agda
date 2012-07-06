module NatTrans where
open import Data.Maybe hiding ( maybe )
open import Data.List hiding ( map )
open import Data.Product hiding ( map )
open import Function hiding ( id )
open import Relation.Binary.PropositionalEquality

id : {A : Set} → A → A
id x = x

infix 4 _≣_
_≣_ : {A B : Set} (f g : A → B) → Set
f ≣ g = ∀ x → f x ≡ g x

----------------------------------------------------------------------

mmap : {A B : Set} (f : A → B) → Maybe A → Maybe B
mmap f (just x) = just (f x)
mmap f nothing = nothing

mmap-preserves-id : {A : Set} →
  mmap {A} id ≣ id
mmap-preserves-id (just x) = refl
mmap-preserves-id nothing = refl

mmap-preserves-∘ : {A B C : Set} {f : A → B} {g : B → C} →
  mmap (g ∘ f) ≣ (mmap g ∘ mmap f)
mmap-preserves-∘ (just x) = refl
mmap-preserves-∘ nothing = refl

----------------------------------------------------------------------

lmap : {A B : Set} (f : A → B) → List A → List B
lmap f [] = []
lmap f (x ∷ xs) = f x ∷ lmap f xs

lmap-preserves-id : {A : Set} →
  lmap {A} id ≣ id
lmap-preserves-id [] = refl
lmap-preserves-id (x ∷ xs) = cong (_∷_ x) (lmap-preserves-id xs)

lmap-preserves-∘ : {A B C : Set} {f : A → B} {g : B → C} →
  lmap (g ∘ f) ≣ (lmap g ∘ lmap f)
lmap-preserves-∘ [] = refl
lmap-preserves-∘ (x ∷ xs) = cong (_∷_ _) (lmap-preserves-∘ xs)

postulate
  reverse-natural : {A B : Set} → (f : A → B) →
    lmap f ∘ reverse ≣ reverse ∘ lmap f

maybeToList : {A : Set} → Maybe A → List A
maybeToList (just x) = x ∷ []
maybeToList nothing = []

postulate
  maybeToList-natural : {A B : Set} (f : A → B) →
    lmap f ∘ maybeToList ≣ maybeToList ∘ mmap f

----------------------------------------------------------------------

pmap : {A B A′ B′ : Set}
  (f : A → B) (g : A′ → B′) → A × A′ → B × B′
pmap f g (x , y) = f x , g y

pmap-preserves-id : {A A′ : Set} →
  pmap {A = A} {A′ = A′} id id ≣ id
pmap-preserves-id (x , y) = refl

pmap-preserves-∘ : {A B C A′ B′ C′ : Set}
  {f : A → B} {g : B → C} {f′ : A′ → B′} {g′ : B′ → C′} →
  pmap (g ∘ f) (g′ ∘ f′) ≣ (pmap g g′ ∘ pmap f f′)
pmap-preserves-∘ (x , y) = refl




