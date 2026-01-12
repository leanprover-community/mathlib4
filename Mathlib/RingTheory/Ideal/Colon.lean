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

/-- `N.colon P` is the ideal of all elements `r : R` such that `r • P ⊆ N`. -/
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
theorem mem_colon_singleton_set {x : M} {r : R} : r ∈ N.colon {x} ↔ r • x ∈ N := by
  simp [mem_colon, forall_eq]

instance (priority := low) (P : Submodule R M) : (N.colon (P : Set M)).IsTwoSided where
  mul_mem_of_left {r} s hr p hp := by
    obtain ⟨p, hp, rfl⟩ := hp
    exact hr ⟨_, P.smul_mem _ hp, (mul_smul ..).symm⟩

@[simp]
theorem colon_univ {I : Ideal R} [I.IsTwoSided] : I.colon (Set.univ : Set R) = I := by
  simp_rw [SetLike.ext_iff, mem_colon, smul_eq_mul]
  exact fun x ↦ ⟨fun h ↦ mul_one x ▸ h 1 trivial, fun h _ _ ↦ I.mul_mem_right _ h⟩

@[deprecated (since := "2026-01-11")] alias colon_top := colon_univ

@[simp]
theorem colon_bot : colon (⊥ : Submodule R M) (N : Set M) = N.annihilator := by
  ext x
  simp [mem_colon, mem_annihilator]

theorem colon_mono (hn : N₁ ≤ N₂) (hs : S₁ ⊆ S₂) : N₁.colon S₂ ≤ N₂.colon S₁ :=
  fun _ hrns ↦ mem_colon.2 fun s₁ hs₁ ↦ hn <| (mem_colon).1 hrns s₁ <| hs hs₁

theorem _root_.Ideal.le_colon {I : Ideal R} {S : Set R} [I.IsTwoSided] :
    I ≤ I.colon S := calc
  I = I.colon (Set.univ : Set R) := colon_univ.symm
  _ ≤ I.colon S := colon_mono (le_refl I) (Set.subset_univ S)

theorem iInf_colon_iUnion (ι₁ : Sort*) (f : ι₁ → Submodule R M) (ι₂ : Sort*) (g : ι₂ → Set M) :
    (⨅ i, f i).colon (⋃ j, g j) = ⨅ (i) (j), (f i).colon (g j) := by
  apply le_antisymm
  · exact le_iInf fun i =>
      le_iInf fun j =>
        colon_mono (iInf_le _ _) (Set.subset_iUnion (fun j => g j) j)
  · intro x hx
    refine mem_colon.2 ?_
    intro m hm
    rcases (Set.mem_iUnion.1 hm) with ⟨j, hm'⟩
    refine (mem_iInf f).2 ?_
    intro i
    have hx_i : x ∈ ⨅ j, (f i).colon (g j) := by
      exact (mem_iInf (p := fun i => ⨅ j, (f i).colon (g j))).1 hx i
    have h : x ∈ (f i).colon (g j) := by
      exact (mem_iInf (p := fun j => (f i).colon (g j))).1 hx_i j
    exact mem_colon.1 h m hm'

@[deprecated (since := "2026-01-11")] alias iInf_colon_iSup := iInf_colon_iUnion

/-- If `S ⊆ N`, then the colon ideal `N.colon S` is the whole ring. -/
lemma colon_eq_top_of_subset (N : Submodule R M) (S : Set M) (h : S ⊆ N) :
    N.colon S = ⊤ := by
  refine top_unique ?_
  intro x _
  refine mem_colon.2 ?_
  intro p h_p
  exact smul_mem N x (h h_p)

/-- If `S ⊆ N₂`, then intersecting with `N₁` does not change the colon ideal. -/
lemma colon_inf_eq_left_of_subset (h : S ⊆ (N₂ : Set M)) : (N₁ ⊓ N₂).colon S = N₁.colon S := calc
  (N₁ ⊓ N₂).colon S = N₁.colon S ⊓ N₂.colon S := by
    simpa [iInf_bool_eq, Set.iUnion_const] using
      (iInf_colon_iUnion (ι₁ := Bool) (f := fun | true => N₁ | false => N₂) (ι₂ := PUnit.{0})
      (g := fun _ => S))
  _ = N₁.colon S ⊓ ⊤ := by rw[colon_eq_top_of_subset N₂ S h]
  _ = N₁.colon S := inf_top_eq (N₁.colon S)

end Semiring

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {N : Submodule R M} (S : Set M)

theorem mem_colon' {r} : r ∈ N.colon S ↔ S ≤ comap (r • (LinearMap.id : M →ₗ[R] M)) N :=
  mem_colon

theorem colon_bot' : colon (⊥ : Submodule R M) S = (Submodule.span R S).annihilator := by
  ext r
  rw [mem_colon, mem_annihilator]
  constructor
  · intro hr m hm
    refine Submodule.span_induction
      (p := fun (x : M) (hx : x ∈ span R S) ↦ r • x = 0) ?_ ?_ ?_ ?_ hm
    · intro s hs
      simpa [Submodule.mem_bot] using hr s hs
    · exact smul_zero r
    · intro _ _ _ _ hrx hry
      rw [smul_add, hrx, hry, zero_add]
    · intro _ _ _ hrx
      rw [smul_smul, mul_comm, ← smul_smul, hrx, smul_zero]
  · intro hr s hs
    simpa [mem_bot] using hr s (mem_span_of_mem hs)

theorem colon_span : N.colon (Submodule.span R S) = N.colon S := by
  ext r
  constructor
  · intro h
    refine mem_colon.mpr ?_
    intro s hs
    exact mem_colon.mp h s (Submodule.subset_span hs)
  · intro h
    refine mem_colon.mpr ?_
    intro s hs
    refine Submodule.span_induction
      (p := fun (x : M) (hx : x ∈ span R S) ↦ r • x ∈ N) ?_ ?_ ?_ ?_ hs
    · intro x hx
      exact mem_colon.mp h x hx
    · simp [smul_zero]
    · intro x y hx hy hrx hry
      simpa [smul_add] using N.add_mem hrx hry
    · intro a x hx hrx
      simpa [smul_comm r a x] using N.smul_mem a hrx

@[simp]
theorem mem_colon_span_singleton {x : M} {r : R} :
    r ∈ N.colon (Submodule.span R {x}) ↔ r • x ∈ N := by
  simp[colon_span (N := N) (S := {x})]

@[deprecated mem_colon_span_singleton "Use `mem_colon_span_singleton` for `Submodule.span R {x}`."
(since := "2025-12-28")]
theorem mem_colon_singleton {x : M} {r : R} : r ∈ N.colon (Submodule.span R {x}) ↔ r • x ∈ N :=
  mem_colon_span_singleton

@[simp]
theorem _root_.Ideal.mem_colon_span_singleton {I : Ideal R} {x r : R} :
    r ∈ I.colon (Ideal.span {x}) ↔ r * x ∈ I := by
  simp only [← Ideal.submodule_span_eq, Submodule.mem_colon_span_singleton, smul_eq_mul]

@[deprecated _root_.Ideal.mem_colon_span_singleton
"Use `Ideal.mem_colon_span_singleton` for `Ideal.span {x}`."
(since := "2025-12-28")]
theorem _root_.Ideal.mem_colon_singleton {I : Ideal R} {x r : R} :
    r ∈ I.colon (Ideal.span {x}) ↔ r * x ∈ I := by
  simp only [← Ideal.submodule_span_eq, Submodule.mem_colon_span_singleton, smul_eq_mul]

end CommSemiring

section Ring

variable [Ring R] [AddCommGroup M] [Module R M]
variable {N P : Submodule R M} {S : Set M}

@[simp]
lemma annihilator_map_mkQ_eq_colon : annihilator (P.map N.mkQ) = N.colon (P : Set M) := by
  ext
  rw [mem_annihilator, mem_colon]
  exact ⟨fun H p hp ↦ (Quotient.mk_eq_zero N).1 (H (Quotient.mk p) (mem_map_of_mem hp)),
    fun H _ ⟨p, hp, hpm⟩ ↦ hpm ▸ ((Quotient.mk_eq_zero N).2 <| H p hp)⟩

theorem annihilator_quotient : Module.annihilator R (M ⧸ N) = N.colon (Set.univ : Set M) := by
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
