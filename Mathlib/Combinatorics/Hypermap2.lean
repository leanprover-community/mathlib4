import Mathlib.Data.Fintype.Card

universe u

structure Hypermap (D : Type u) where
  e : D → D
  n : D → D
  f : D → D
  e_n_f_eq : ∀ x, e (n (f x)) = x

namespace Hypermap

variable {D : Type u} [Fintype D]

open Equiv

def ePerm (m : Hypermap D) : Perm D where
  toFun := m.e
  invFun := m.n ∘ m.f
  right_inv := m.e_n_f_eq
  left_inv := Function.RightInverse.leftInverse_of_card_le m.e_n_f_eq (le_refl _)

def fPerm (m : Hypermap D) : Perm D where
  toFun := m.f
  invFun := m.e ∘ m.n
  right_inv := Function.LeftInverse.rightInverse_of_card_le m.e_n_f_eq (le_refl _)
  left_inv := m.e_n_f_eq

def nPerm (m : Hypermap D) : Perm D where
  toFun := m.n
  invFun := m.f ∘ m.e
  right_inv := Function.LeftInverse.rightInverse_of_card_le (fPerm m).right_inv (le_refl _)
  left_inv := Function.RightInverse.leftInverse_of_card_le (ePerm m).left_inv (le_refl _)
