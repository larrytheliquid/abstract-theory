module LookupOrn where
open import Data.Bool
open import Data.Nat hiding ( _<_ )
open import Data.Maybe
open import Data.List

isJust : {A : Set} → Maybe A → Bool
isJust (just _) = true
isJust nothing = false

_<_ : ℕ → ℕ → Bool
_ < zero = false
zero < suc _ = true
suc m < suc n = m < n

lookup : {A : Set} → ℕ → List A → Maybe A
lookup _ [] = nothing
lookup zero (x ∷ xs) = just x
lookup (suc n) (x ∷ xs) = lookup n xs

