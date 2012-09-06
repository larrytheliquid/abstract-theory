open import Data.Nat
open import Data.Fin hiding ( _+_ )
open import Data.Product
open import Data.Vec hiding ( sum )
open import Function
open import Relation.Binary.PropositionalEquality
module FunAlgebra where

data Fun : Set where
  fun : (ℕ → ℕ) → Fun

$0α : (ℕ → ℕ) → ℕ
$0α = flip _$_ 0

data IFun : ℕ → Set where
  fun : (f : ℕ → ℕ) → IFun ($0α f)

proj : {n : ℕ} → IFun n → ℕ → ℕ
proj (fun f) = f

ifun : (n : ℕ) → IFun n
ifun n = fun (flip _+_ n)

plus : ℕ → ℕ → ℕ
plus n = proj (ifun n)

