open import Data.Nat
import Func
open Func ℕ
module NatFunc where

_[+]_ : Func → Func → Func
_[+]_ g f a = g a + f a


