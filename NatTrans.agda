module NatTrans where
open import Data.Maybe hiding ( maybe )
open import Data.List hiding ( map )
open import Data.Product hiding ( map )
open import Function hiding ( id )
open import Relation.Binary.PropositionalEquality

id : {A : Set} → A → A
id x = x

mmap : {A B : Set} (f : A → B) → Maybe A → Maybe B
mmap f (just x) = just (f x)
mmap f nothing = nothing

lmap : {A B : Set} (f : A → B) → List A → List B
lmap f [] = []
lmap f (x ∷ xs) = f x ∷ lmap f xs

pmap : {A B A′ B′ : Set}
  (f : A → B) (g : A′ → B′) → A × A′ → B × B′
pmap f g (x , y) = f x , g y

--------------------------------------------------------------------------------

mmap-preserves-id : {A : Set} (m : Maybe A) →
  mmap id m ≡ id m
mmap-preserves-id (just x) = refl
mmap-preserves-id nothing = refl

mmap-preserves-∘ : {A B C : Set} {f : A → B} {g : B → C} (m : Maybe A) →
  mmap (g ∘ f) m ≡ (mmap g ∘ mmap f) m
mmap-preserves-∘ (just x) = refl
mmap-preserves-∘ nothing = refl

lmap-preserves-id : {A : Set} (xs : List A) →
  lmap id xs ≡ id xs
lmap-preserves-id [] = refl
lmap-preserves-id (x ∷ xs) = cong (_∷_ x) (lmap-preserves-id xs)

lmap-preserves-∘ : {A B C : Set} {f : A → B} {g : B → C} (xs : List A) →
  lmap (g ∘ f) xs ≡ (lmap g ∘ lmap f) xs
lmap-preserves-∘ [] = refl
lmap-preserves-∘ (x ∷ xs) = cong (_∷_ _) (lmap-preserves-∘ xs)

pmap-preserves-id : {A A′ : Set} (xy : A × A′) →
  pmap id id xy ≡ id xy
pmap-preserves-id (x , y) = refl

pmap-preserves-∘ : {A B C A′ B′ C′ : Set}
  {f : A → B} {g : B → C} {f′ : A′ → B′} {g′ : B′ → C′}
  (xy : A × A′) →
  pmap (g ∘ f) (g′ ∘ f′) xy ≡ (pmap g g′ ∘ pmap f f′) xy
pmap-preserves-∘ (x , y) = refl
