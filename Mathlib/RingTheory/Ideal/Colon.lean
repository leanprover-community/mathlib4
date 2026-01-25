/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Ring.Action.Pointwise.Set
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Maps

/-!
# The colon ideal

This file defines `Submodule.colon N P` as the ideal of all elements `r : R` such that `r • P ⊆ N`.
The normal notation for this would be `N : P` which has already been taken by type theory.

-/

@[expose] public section

namespace Submodule

open Pointwise

variable {R M : Type*}

section Semiring

variable [Semiring R] [AddCommMonoid M] [Module R M]
variable {N N₁ N₂ : Submodule R M} {S S₁ S₂ : Set M}

/-- `N.colon P` is the ideal of all elements `r : R` such that `r • P ⊆ N`.
We treat it as an infix in lemma names. -/
def colon (N : Submodule R M) (S : Set M) : Ideal R where
  carrier := {r : R | (r • S : Set M) ⊆ N}
  add_mem' ha hb :=
    (Set.add_smul_subset _ _ _).trans ((Set.add_subset_add ha hb).trans_eq (by simp))
  zero_mem' := (Set.zero_smul_set_subset S).trans (by simp)
  smul_mem' r := by
    simp only [Set.mem_setOf_eq, smul_eq_mul, mul_smul, Set.smul_set_subset_iff]
    intro x hx y hy
    exact N.smul_mem _ (hx hy)

theorem mem_colon {r} : r ∈ N.colon S ↔ ∀ s ∈ S, r • s ∈ N := Set.smul_set_subset_iff

@[simp]
theorem mem_colon_singleton {x : M} {r : R} : r ∈ N.colon {x} ↔ r • x ∈ N := by
  simp [mem_colon, forall_eq]

instance (priority := low) (P : Submodule R M) : (N.colon (P : Set M)).IsTwoSided where
  mul_mem_of_left {r} s hr p hp := by
    obtain ⟨p, hp, rfl⟩ := hp
    exact hr ⟨_, P.smul_mem _ hp, (mul_smul ..).symm⟩

@[simp]
theorem colon_univ {I : Ideal R} [I.IsTwoSided] : I.colon Set.univ = I := by
  simp_rw [SetLike.ext_iff, mem_colon, smul_eq_mul]
  exact fun x ↦ ⟨fun h ↦ mul_one x ▸ h 1 trivial, fun h _ _ ↦ I.mul_mem_right _ h⟩

@[deprecated (since := "2026-01-11")] alias colon_top := colon_univ

@[simp]
theorem bot_colon : colon (⊥ : Submodule R M) (N : Set M) = N.annihilator := by
  ext x
  simp [mem_colon, mem_annihilator]

theorem colon_mono (hn : N₁ ≤ N₂) (hs : S₁ ⊆ S₂) : N₁.colon S₂ ≤ N₂.colon S₁ :=
  fun _ hrns ↦ mem_colon.mpr fun s₁ hs₁ ↦ hn <| (mem_colon).mp hrns s₁ <| hs hs₁

theorem _root_.Ideal.le_colon {I : Ideal R} {S : Set R} [I.IsTwoSided] : I ≤ I.colon S :=
  colon_univ.symm.trans_le (colon_mono le_rfl S.subset_univ)

theorem iInf_colon_iUnion (ι₁ : Sort*) (f : ι₁ → Submodule R M) (ι₂ : Sort*) (g : ι₂ → Set M) :
    (⨅ i, f i).colon (⋃ j, g j) = ⨅ (i) (j), (f i).colon (g j) := by
  aesop (add simp mem_colon)

@[deprecated (since := "2026-01-11")] alias iInf_colon_iSup := iInf_colon_iUnion

/-- If `S ⊆ N₂`, then intersecting with `N₂` does not change the colon ideal. -/
lemma colon_inf_eq_left_of_subset (h : S ⊆ (N₂ : Set M)) : (N₁ ⊓ N₂).colon S = N₁.colon S := by
  aesop (add simp mem_colon)

@[simp]
lemma colon_eq_top_iff_subset (S : Set M) : N.colon S = ⊤ ↔ S ⊆ N := by
  aesop (add simp [mem_colon, Ideal.eq_top_iff_one])

@[simp]
lemma inf_colon : (N₁ ⊓ N₂).colon S = N₁.colon S ⊓ N₂.colon S := by
  aesop (add simp mem_colon)

@[simp]
lemma iInf_colon {ι : Sort*} (f : ι → Submodule R M) : (⨅ i, f i).colon S = ⨅ i, (f i).colon S := by
  aesop (add simp mem_colon)

@[simp]
lemma colon_finsetInf {ι : Type*} (s : Finset ι) (f : ι → Submodule R M) :
    (s.inf f).colon S = s.inf (fun i ↦ (f i).colon S) := by
  aesop (add simp mem_colon)

@[simp]
lemma top_colon : (⊤ : Submodule R M).colon S = ⊤ := by
  aesop (add simp mem_colon)

@[simp]
lemma colon_union : N.colon (S₁ ∪ S₂) = N.colon S₁ ⊓ N.colon S₂ := by
  aesop (add simp mem_colon)

@[simp]
lemma colon_iUnion {ι : Sort*} (f : ι → Set M) : N.colon (⋃ i, f i) = ⨅ i, N.colon (f i) := by
  aesop (add simp mem_colon)

@[simp]
lemma colon_empty : N.colon (∅ : Set M) = ⊤ := by
  aesop (add simp mem_colon)

lemma colon_singleton_zero : N.colon {0} = ⊤ := by
  simp

lemma colon_bot : N.colon ((⊥ : Submodule R M) : Set M) = ⊤ := by
  simp

end Semiring

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {N N' : Submodule R M} {S : Set M}

@[deprecated mem_colon (since := "2026-01-15")]
theorem mem_colon' {r} : r ∈ N.colon S ↔ S ≤ comap (r • (LinearMap.id : M →ₗ[R] M)) N :=
  mem_colon

theorem mem_colon_iff_le {r} : r ∈ N.colon N' ↔ r • N' ≤ N := by
  aesop (add simp SetLike.coe_subset_coe)

/-- A variant for arbitrary sets in commutative semirings -/
theorem bot_colon' : (⊥ : Submodule R M).colon S = (span R S).annihilator := by
  aesop (add simp [mem_colon, mem_annihilator_span])

@[simp]
theorem colon_span : N.colon (span R S) = N.colon S := by
  refine (colon_mono le_rfl subset_span).antisymm fun r h ↦ mem_colon.mpr fun s hs ↦ ?_
  induction hs using Submodule.span_induction with
  | mem => aesop (add simp mem_colon)
  | zero => simp
  | add => aesop
  | smul => simp_all [smul_mem, smul_comm r]

@[simp]
theorem _root_.Ideal.colon_span {I : Ideal R} {S : Set R} : I.colon (Ideal.span S) = I.colon S :=
  Submodule.colon_span

theorem mem_colon_span_singleton {x : M} {r : R} : r ∈ N.colon (span R {x}) ↔ r • x ∈ N := by
  simp

theorem _root_.Ideal.mem_colon_span_singleton {I : Ideal R} {x r : R} :
    r ∈ I.colon (Ideal.span {x}) ↔ r * x ∈ I := by
  simp

end CommSemiring

section Ring

variable [Ring R] [AddCommGroup M] [Module R M]
variable {N P : Submodule R M}

@[simp]
lemma annihilator_map_mkQ_eq_colon : annihilator (P.map N.mkQ) = N.colon (P : Set M) := by
  ext
  rw [mem_annihilator, mem_colon]
  exact ⟨fun H p hp ↦ (Quotient.mk_eq_zero N).1 (H (Quotient.mk p) (mem_map_of_mem hp)),
    fun H _ ⟨p, hp, hpm⟩ ↦ hpm ▸ ((Quotient.mk_eq_zero N).2 <| H p hp)⟩

theorem annihilator_quotient : Module.annihilator R (M ⧸ N) = N.colon Set.univ := by
  ext r
  have htop : (⊤ : Submodule R (M ⧸ N)) = (⊤ : Submodule R M).map N.mkQ := by
    simpa [map_top] using (LinearMap.range_eq_top.mpr (mkQ_surjective N)).symm
  rw [← annihilator_top (R := R) (M := M ⧸ N), htop,
    annihilator_map_mkQ_eq_colon (N := N) (P := ⊤), Submodule.top_coe]

theorem _root_.Ideal.annihilator_quotient {I : Ideal R} [I.IsTwoSided] :
    Module.annihilator R (R ⧸ I) = I := by
  rw [Submodule.annihilator_quotient, colon_univ]

end Ring

end Submodule
