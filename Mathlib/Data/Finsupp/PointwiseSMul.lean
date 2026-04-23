/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Set.SMulAntidiagonal
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# Scalar multiplication by finitely supported functions.
Given sets `G` and `P`, with a left-cancellative vector-addition of `G` on `P`, we define an
antidiagonal function that assigns, for any element `a` in `P`, finite subset `s` of `G`, and subset
`t` in `P`, the `Set` of all pairs of an element in `s` and an element in `t` that vector-add to
`a`. When `R` is a ring and `V` is an `R`-module, we obtain a convolution-type action of the ring of
finitely supported `R`-valued functions on `G` on the space of `V`-valued functions on `P`.

## Definitions
* Finsupp.vaddAntidiagonal : The finset of pairs that vector-add to a given element.

-/

@[expose] public section

open Finset Function

noncomputable section

variable {G P F R S U V : Type*}

namespace Finsupp

theorem finite_vaddAntidiagonal [VAdd G P] [IsLeftCancelVAdd G P] [Zero R] [Zero V]
    (f : G →₀ R) (x : P → V) (p : P) :
    Set.Finite (Set.vaddAntidiagonal (SetLike.coe f.support) x.support p) := by
  refine Set.Finite.of_injOn (f := Prod.fst) (t := (SetLike.coe f.support)) ?_ ?_
    f.support.finite_toSet
  · intro _ ⟨h, _⟩
    exact h
  · intro _ ⟨_, _, h13⟩ gh' ⟨_, _, h23⟩ h
    rw [h, ← h23] at h13
    exact Prod.ext h (IsLeftCancelVAdd.left_cancel gh'.1 _ _ h13)

/-- The finset of pairs that vector-add to a given element. -/
def vaddAntidiagonal [VAdd G P] [IsLeftCancelVAdd G P] [Zero R] [Zero V] (f : G →₀ R) (x : P → V)
    (p : P) :
    Finset (G × P) := (finite_vaddAntidiagonal f x p).toFinset

theorem mem_vaddAntidiagonal_iff [VAdd G P] [IsLeftCancelVAdd G P] [Zero R] [Zero V] (f : G →₀ R)
    (x : P → V) (p : P) (gh : G × P) :
    gh ∈ vaddAntidiagonal f x p ↔ f gh.1 ≠ 0 ∧ x gh.2 ≠ 0 ∧ gh.1 +ᵥ gh.2 = p := by
  simp [vaddAntidiagonal]

theorem mem_vaddAntidiagonal_of_addGroup [AddGroup G] [AddAction G P] [Zero R] [Zero V]
    (f : G →₀ R) (x : P → V) (p : P) (gh : G × P) :
    gh ∈ vaddAntidiagonal f x p ↔ f gh.1 ≠ 0 ∧ x gh.2 ≠ 0 ∧ gh.2 = -gh.1 +ᵥ p := by
  rw [mem_vaddAntidiagonal_iff, eq_neg_vadd_iff]

/-- A convolution-type scalar multiplication of finitely supported functions on formal functions. -/
scoped instance [VAdd G P] [IsLeftCancelVAdd G P] [Zero R] [AddCommMonoid V] [SMulWithZero R V] :
    SMul (G →₀ R) (P → V) where
  smul f x p := ∑ G ∈ f.vaddAntidiagonal x p, f G.1 • x G.2

theorem smul_eq [VAdd G P] [IsLeftCancelVAdd G P] [Zero R] [AddCommMonoid V] [SMulWithZero R V]
    (f : G →₀ R) (x : P → V) (p : P) :
    (f • x) p = ∑ G ∈ f.vaddAntidiagonal x p, f G.1 • x G.2 := rfl

theorem smul_apply_addAction [AddGroup G] [AddAction G P] [Zero R] [AddCommMonoid V]
    [SMulWithZero R V] (f : G →₀ R) (x : P → V) (p : P) :
    (f • x) p = ∑ i ∈ f.support, (f i) • x (-i +ᵥ p) := by
  rw [smul_eq, Finset.sum_of_injOn Prod.fst]
  · intro _ h₁ _ h₂ h
    rw [mem_coe, mem_vaddAntidiagonal_of_addGroup] at h₁ h₂
    simp [Prod.ext_iff, h₁.2.2, h₂.2.2, h]
  · intro g hg
    rw [mem_coe, mem_vaddAntidiagonal_iff] at hg
    exact mem_coe.mpr <| mem_support_iff.mpr hg.1
  · intro g hg hgn
    have h : f g = 0 ∨ x (-g +ᵥ p) = 0 := by
      simpa [mem_vaddAntidiagonal_of_addGroup, or_iff_not_imp_left] using hgn
    rcases h with (h | h) <;> simp [h]
  · intro g hg
    rw [mem_vaddAntidiagonal_of_addGroup] at hg
    rw [hg.2.2]

end Finsupp
