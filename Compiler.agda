open import Data.Nat
open import Data.Product
open import Data.Vec hiding ( sum )
open import Function
open import Relation.Binary.PropositionalEquality
module Compiler where

data Op : ℕ → Set where
  sum product : Op 2
  num : (x : ℕ) → Op 0
Val = ℕ

eval : ∀{n} → Op n → Vec Val n → Val
eval sum (x ∷ y ∷ []) = x + y
eval product (x ∷ y ∷ []) = x * y
eval (num x) [] = x

data Instr : ℕ → Set where
  bop : (f : Val × Val → Val) → Instr 2
  push : (x : Val) → Instr 0

add : Val × Val → Val
add = uncurry _+_

mul : Val × Val → Val
mul = uncurry _*_

compile : ∀{n} → Op n → Instr n
compile sum = bop add
compile product = bop mul
compile (num x) = push x

exec : ∀{m n} → Instr m → Vec Val (m + n) → Vec Val (suc n)
exec (bop f) (x ∷ y ∷ xs) = f (x , y) ∷ xs
exec (push x) xs = x ∷ xs

coh : ∀{m n} → (op : Op m) (xs : Vec Val (m + n)) →
  exec (compile op) xs ≡ eval op (take m xs) ∷ (drop m xs)
coh sum (x ∷ y ∷ xs) = refl
coh product (x ∷ y ∷ xs) = refl
coh (num x) xs = refl