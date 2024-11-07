/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Data.Vector.Basic
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Zify
import Mathlib.Data.Vector.Defs

/-!

https://cstheory.stackexchange.com/questions/31787/embedding-a-language-in-itself

"For larger alphabets this type of argument fails since there are arbitrarily long
square-free words. "

-/

/-- A word `w` is squarefree if it does not contain a nonempty subword `vv`. -/
def squarefree {b:ℕ} (w: List (Fin b)) : Prop :=
  ∀ l:ℕ, l < w.length → ∀ v : Mathlib.Vector (Fin b) l,
  v.1 ≠ List.nil → ¬ List.IsInfix (v.1 ++ v.1) w

/-- A word `w` is cubefree if it does not contain a nonempty subword `vvv`. -/
def cubefree {b:ℕ} (w: List (Fin b)) : Prop :=
  ∀ l:ℕ, l < w.length → ∀ v : Mathlib.Vector (Fin b) l,
  v.1 ≠ List.nil → ¬ List.IsInfix (v.1 ++ v.1 ++ v.1) w


-- instance (b:ℕ) (w : List (Fin b)) : Decidable (squarefree w) := by
--   unfold squarefree
--   exact w.length.decidableBallLT
--     fun n _ => ∀ (v : Mathlib.Vector (Fin b) n), v.1 ≠ [] → ¬v.1 ++ v.1 <:+: w


-- instance (b:ℕ) (w : List (Fin b)) : Decidable (cubefree w) := by
--   unfold cubefree
--   exact
--     w.length.decidableBallLT fun n _ =>
--     ∀ (v : Mathlib.Vector (Fin b) n), v.1 ≠ [] → ¬v.1 ++ v.1 ++ v.1 <:+: w

-- example : ∀ w : Mathlib.Vector (Fin 2) 4, ¬ squarefree w.1 := by decide

/-- A suffix of a squarefree word is itself squarefree. -/
theorem suffix_squarefree (b:ℕ) (u v : List (Fin b)) (h: u <:+ v) (hu : squarefree v) :
    squarefree u := by
  intro lx _ x hx
  obtain ⟨t,ht⟩ := h; intro hc
  have : lx < v.length := calc
        lx  = x.1.length              := x.2.symm
        _   < x.1.length + x.1.length := Nat.lt_add_of_pos_left (List.length_pos.mpr hx)
        _   = (x.1 ++ x.1).length     := (List.length_append x.1 x.1).symm
        _   ≤ u.length                := List.IsInfix.length_le hc
        _   ≤ t.length + u.length     := by linarith
        _   = v.length                := by rw [← List.length_append t u,ht]
  let G := hu lx this x hx; unfold List.IsInfix at G
  let ⟨s₀,hs₀⟩ := hc; let ⟨s₁,hs₁⟩ := hs₀
  have : ∃ s t, s ++ (x.1 ++ x.1) ++ t = v := by use t ++ s₀; use s₁; rw [← ht,← hs₁]; simp
  exact G this

/-- A suffix of a cubefree word is itself cubefree. -/
theorem suffix_cubefree (b:ℕ) (u v : List (Fin b)) (h: u <:+ v) (hu : cubefree v) : cubefree u := by
  intro lx _ x hx hc
  obtain ⟨t,ht⟩ := h
  have : lx < v.length := calc
    lx  = x.1.length                            := x.2.symm
    _   < x.1.length + x.1.length               := Nat.lt_add_of_pos_left (List.length_pos.mpr hx)
    _   ≤ x.1.length + x.1.length + x.1.length  := Nat.le_add_right _ _
    _   = (x.1 ++ x.1).length + x.1.length      := by rw[(List.length_append x.1 x.1).symm]
    _   = (x.1 ++ x.1 ++ x.1).length            := (List.length_append (x.1 ++ x.1) x.1).symm
    _   ≤ u.length                              := List.IsInfix.length_le hc
    _   ≤ t.length + u.length                   := by linarith
    _   = v.length                              := by rw [← List.length_append t u,ht]
  let G := hu lx this x hx; unfold List.IsInfix at G
  let ⟨s₀,hs₀⟩ := hc; let ⟨s₁,hs₁⟩ := hs₀
  have : ∃ s t, s ++ (x.1 ++ x.1 ++ x.1) ++ t = v := by use t ++ s₀; use s₁; rw [← ht,← hs₁]; simp
  exact G this
