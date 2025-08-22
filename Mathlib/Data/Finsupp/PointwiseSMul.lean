/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.AddTorsor
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Set.SMulAntidiagonal

/-!
# Scalar multiplication by finitely supported functions.

Given sets `G` and `P`, with a left-cancellative action of `G` on `P`, we construct, for any element
`a` in `P`, finite subset `s` of `G`, and subset `t` in `P`, the `Set` of all pairs of an element in
`s` and an element in `t` that scalar-multiply to `a`. When `R` is a ring and `V` is an `R`-module,
we obtain an action of the ring of finitely supported `R`-valued functions on `G` on the space of
'V'-valued functions on `P`, when `V` is an `R`-module.

## Definitions

* Finsupp.vaddAntidiagonal :
-/

open Finset Function

noncomputable section

variable {Γ Γ' Γ₁ Γ₂ F R S U V : Type*}

namespace Finsupp

theorem finite_vaddAntidiagonal [VAdd Γ Γ'] [IsLeftCancelVAdd Γ Γ'] [Zero R] [AddCommMonoid V]
    [SMulWithZero R V] [DecidableEq Γ']
    (f : Γ →₀ R) (x : Γ' → V) (g : Γ') :
    Set.Finite (Set.vaddAntidiagonal f.support.toSet x.support g) := by
  refine Set.Finite.of_injOn (f := Prod.fst) (t := f.support.toSet) ?_ ?_ f.support.finite_toSet
  · intro _ ⟨h, _⟩
    exact h
  · intro _ ⟨_, _, h13⟩ gh' ⟨_, _, h23⟩ h
    rw [h, ← h23] at h13
    refine Prod.ext h (IsLeftCancelVAdd.left_cancel gh'.1 _ _ h13)

/-- The finset of pairs that vector-add to a given element. -/
def vaddAntidiagonal [VAdd Γ Γ'] [IsLeftCancelVAdd Γ Γ'] [Zero R] [AddCommMonoid V]
    [SMulWithZero R V] [DecidableEq Γ'] (f : Γ →₀ R) (x : Γ' → V) (g : Γ') :
    Finset (Γ × Γ') := (finite_vaddAntidiagonal f x g).toFinset

theorem mem_vaddAntidiagonal_iff [DecidableEq Γ'] [VAdd Γ Γ'] [IsLeftCancelVAdd Γ Γ'] [Zero R]
    [AddCommMonoid V] [SMulWithZero R V] (f : Γ →₀ R) (x : Γ' → V) (g : Γ') (gh : Γ × Γ') :
    gh ∈ vaddAntidiagonal f x g ↔ f gh.1 ≠ 0 ∧ (x gh.2) ≠ 0 ∧ gh.1 +ᵥ gh.2 = g := by
  simp [vaddAntidiagonal]

scoped instance [VAdd Γ Γ'] [IsLeftCancelVAdd Γ Γ'] [Zero R] [AddCommMonoid V] [SMulWithZero R V]
    [DecidableEq Γ'] :
    SMul (Γ →₀ R) (Γ' → V) where
  smul f x g := ∑ (γ ∈ f.vaddAntidiagonal x g), (f γ.1) • x γ.2

theorem smul_eq [VAdd Γ Γ'] [IsLeftCancelVAdd Γ Γ'] [Zero R] [AddCommMonoid V] [SMulWithZero R V]
    [DecidableEq Γ'] (f : Γ →₀ R) (x : Γ' → V) (g : Γ') :
    (f • x) g = ∑ (γ ∈ f.vaddAntidiagonal x g), (f γ.1) • x γ.2 := rfl

theorem antidiagonal_of_addGroup [AddGroup Γ] [DecidableEq Γ'] [AddAction Γ Γ'] [IsCancelVAdd Γ Γ']
    [Zero R] [AddCommMonoid V] [SMulWithZero R V] (f : Γ →₀ R) (x : Γ' → V) (g : Γ') (gh : Γ × Γ') :
    gh ∈ vaddAntidiagonal f x g ↔ (f gh.1) ≠ 0 ∧ (x gh.2) ≠ 0 ∧ gh.2 = -gh.1 +ᵥ g := by
  rw [mem_vaddAntidiagonal_iff]
  exact and_congr_right' <| and_congr_right' <| vadd_eq_iff_eq_neg_vadd gh.1

theorem smul_apply_addAction [AddGroup Γ] [AddAction Γ Γ'] [Zero R] [AddCommMonoid V]
    [SMulWithZero R V] [DecidableEq Γ'] (f : Γ →₀ R) (x : Γ' → V) (g' : Γ') :
    (f • x) g' = ∑ i ∈ f.support, (f i) • x (-i +ᵥ g') := by
  rw [smul_eq, Finset.sum_of_injOn Prod.fst]
  · intro g₁ hg₁ g₂ hg₂ h
    rw [mem_coe, mem_vaddAntidiagonal_iff] at hg₁ hg₂
    aesop
  · intro g hg
    rw [mem_coe, mem_vaddAntidiagonal_iff] at hg
    exact mem_coe.mpr <| mem_support_iff.mpr hg.1
  · intro g hg hgn
    rw [Set.mem_image, not_exists] at hgn
    have : f g ≠ 0 → x (-g +ᵥ g') = 0 := by simpa [mem_vaddAntidiagonal_iff] using hgn (g, -g +ᵥ g')
    aesop
  · intro g hg
    rw [mem_vaddAntidiagonal_iff] at hg
    aesop

end Finsupp
