open import Data.Nat
open import Data.Fin hiding ( _+_ )
open import Data.Product
open import Data.Vec hiding ( sum )
open import Function
open import Relation.Binary.PropositionalEquality
module Compiler2 where

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

exec : ∀{m n} → Instr m → Vec Val (m + n) → Vec Val (suc n)
exec (bop f) (x ∷ y ∷ xs) = f (x , y) ∷ xs
exec (push x) xs = x ∷ xs

compile : ∀{n} → Op n → Instr n
compile sum = bop add
compile product = bop mul
compile (num x) = push x

data IInstr : {n : ℕ} (m : ℕ) → Vec Val (m + n) → Vec Val (suc n) → Set where
  bop : ∀{n} →
    (xs : Vec Val (2 + n))
    (f : Val × Val → Val) →
    let x = lookup zero xs
        y = lookup (suc zero) xs
    in IInstr 2 xs (f (x , y) ∷ drop 2 xs)
  push : ∀{n} →
    (xs : Vec Val n)
    (x : Val) →
    IInstr 0 xs (x ∷ xs)

forget : ∀{n m} {xs : Vec Val (m + n)} {ys : Vec Val (suc n)} →
  IInstr m xs ys → Instr m
forget (bop _ f) = bop f
forget (push _ x) = push x

{- Step 1:
coh : ∀{m n} →
  (op : Op m) (xs : Vec Val (m + n)) →
  exec (compile op) xs ≡ eval op (take m xs) ∷ (drop m xs)
-}

{- Step 2:
uprop : ∀{m n} →
  (compile : ∀{n} → Op n → Instr n)
  (op : Op m) (xs : Vec Val (m + n)) →
  exec (compile op) xs ≡ eval op (take m xs) ∷ (drop m xs)
-}

{- Step 3:
choice : ∀{m n} →
  (op : Op m) (xs : Vec Val (m + n)) →
  Σ (Instr m) λ instr →
  exec instr xs ≡ eval op (take m xs) ∷ (drop m xs)
-}

{- Step 4:
ifun : ∀{m n} →
  (op : Op m) (xs : Vec Val (m + n)) →
  IInstr m xs (eval op (take m xs) ∷ (drop m xs))
-}

icompile : ∀{m n} →
  (op : Op m) (xs : Vec Val (m + n)) →
  IInstr m xs (eval op (take m xs) ∷ (drop m xs))
icompile sum (x ∷ y ∷ xs) = bop (x ∷ y ∷ xs) add
icompile product (x ∷ y ∷ xs) = bop (x ∷ y ∷ xs) mul
icompile (num x) xs = push xs x

coh : ∀{m n} →
  (op : Op m) (xs : Vec Val (m + n)) →
  exec (forget $ icompile op xs) xs ≡ eval op (take m xs) ∷ (drop m xs)
coh sum (_ ∷ _ ∷ _) = refl
coh product (_ ∷ _ ∷ _) = refl
coh (num _) _ = refl

----------------------------------------------------------------------

{- Step 2:
uprop :
  (_∙_ : ℕ → (ℕ → ℕ))
  (n : ℕ) →
  n ∙ 0 ≡ n × 0 ∙ n ≡ n
-}

{- Step 3:
choice :
  (n : ℕ) →
  Σ (ℕ → ℕ) λ f →
  f 0 ≡ n
  (flip _$_) 0 n ≡ n
-}

{- Step 4:
ifun : ∀{m n} →
  (x : ℕ) →
  If x
-}

----------------------------------------------------------------------
