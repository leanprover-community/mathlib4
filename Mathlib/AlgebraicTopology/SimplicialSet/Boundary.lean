/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Adam Topaz, Jacob Reinhold
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Subobject.Types

/-!
# The boundary of the standard simplex

We introduce the boundary `∂Δ[n]` of the standard simplex `Δ[n]`.
(These notations become available by doing `open Simplicial`.)

## Future work

There isn't yet a complete API for simplices, boundaries, and horns.
As an example, we should have a function that constructs
from a non-surjective order-preserving function `Fin n → Fin n`
a morphism `Δ[n] ⟶ ∂Δ[n]`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Simplicial Opposite

namespace SSet

/-- The boundary `∂Δ[n]` of the `n`-th standard simplex consists of
all `m`-simplices of `stdSimplex n` that are not surjective
(when viewed as monotone function `m → n`). -/
def boundary (n : ℕ) : (Δ[n] : SSet.{u}).Subcomplex where
  obj _ := setOf (fun s ↦ ¬Function.Surjective (stdSimplex.asOrderHom s))
  map _ _ hs h := hs (Function.Surjective.of_comp h)

/-- The boundary `∂Δ[n]` of the `n`-th standard simplex -/
scoped[Simplicial] notation3 "∂Δ[" n "]" => SSet.boundary n

lemma boundary_eq_iSup (n : ℕ) :
    boundary.{u} n = ⨆ (i : Fin (n + 1)), stdSimplex.face {i}ᶜ := by
  ext
  simp [stdSimplex.face_obj, boundary, Function.Surjective]
  tauto

instance {n : ℕ} : HasDimensionLT (boundary n) n := by
  rw [boundary_eq_iSup, hasDimensionLT_iSup_iff]
  intro i
  exact stdSimplex.hasDimensionLT_face _ _ (by simp [Finset.card_compl])

lemma mem_boundary_iff_notMem_range {n d : ℕ} (s : Δ[n] _⦋d⦌) :
    s ∈ (boundary n).obj _ ↔ ∃ (j : Fin (n + 1)), j ∉ Set.range s := by
  rw [boundary_eq_iSup]
  simp

lemma face_singleton_compl_le_boundary {n : ℕ} (i : Fin (n + 1)) :
    stdSimplex.face.{u} {i}ᶜ ≤ boundary n := by
  rw [boundary_eq_iSup]
  exact le_iSup (fun (i : Fin (n +1)) ↦ stdSimplex.face {i}ᶜ) i

lemma stdSimplex.notMem_boundary (n : ℕ) :
    stdSimplex.objMk (m := op ⦋n⦌) .id ∉ (boundary.{u} n).obj (op ⦋n⦌) := by
  rw [boundary_eq_iSup, Subfunctor.iSup_obj, Set.mem_iUnion, not_exists]
  intro i hi
  simpa using @hi i (by aesop)

lemma boundary_lt_top (n : ℕ) :
    boundary.{u} n < ⊤ :=
  lt_of_le_not_ge (by simp) (fun h ↦ stdSimplex.notMem_boundary n (h _ (by simp)))

lemma boundary_obj_eq_univ (m n : ℕ) (h : m < n := by lia) :
    (boundary.{u} n).obj (op ⦋m⦌) = .univ := by
  ext x
  obtain ⟨f, rfl⟩ := stdSimplex.objEquiv.symm.surjective x
  simp only [Set.mem_univ, iff_true]
  obtain _ | n := n
  · simp at h
  · obtain ⟨i, q, rfl⟩ := SimplexCategory.eq_comp_δ_of_not_surjective f (fun hf ↦ by
      rw [← SimplexCategory.epi_iff_surjective] at hf
      have : n + 1 ≤ m := SimplexCategory.len_le_of_epi f
      lia)
    apply face_singleton_compl_le_boundary i
    rw [stdSimplex.face_singleton_compl, stdSimplex.objEquiv_symm_comp,
      ← Subcomplex.ofSimplex_le_iff]
    apply Subcomplex.ofSimplex_map_le

lemma op_boundary (n : ℕ) :
    ∂Δ[n].op.preimage (stdSimplex.opIso.{u} ⦋n⦌).inv = ∂Δ[n] := by
  ext ⟨⟨d⟩⟩ j
  simp only [Subcomplex.preimage_obj, Set.mem_preimage, stdSimplex.opIso_inv_app_hom_apply,
    Subcomplex.mem_op_obj_iff, mem_boundary_iff_notMem_range, Set.mem_range,
    stdSimplex.opObjEquiv_opObjEquiv_symm_apply, not_exists]
  constructor
  all_goals
  · rintro ⟨k, hk⟩
    exact ⟨k.rev, fun l _ ↦ hk l.rev (by aesop)⟩

namespace stdSimplex

variable {n : ℕ} (A : (Δ[n] : SSet.{u}).Subcomplex)

set_option backward.isDefEq.respectTransparency false in
lemma subcomplex_hasDimensionLT_of_neq_top (h : A ≠ ⊤) :
    HasDimensionLT A n where
  degenerate_eq_top i hi := by
    ext ⟨a, ha⟩
    rw [A.mem_degenerate_iff]
    simp only [Subfunctor.toFunctor_obj, Set.top_eq_univ, Set.mem_univ, iff_true]
    obtain hi | rfl := hi.lt_or_eq
    · simp [Δ[n].degenerate_eq_univ_of_hasDimensionLT (n + 1) i]
    · rw [mem_degenerate_iff_notMem_nonDegenerate, nonDegenerate_top_dim]
      rintro rfl
      exact h (le_antisymm (by simp) (by simpa [← ofSimplex_objEquiv_symm_id]))

set_option backward.isDefEq.respectTransparency false in
lemma le_boundary_iff :
    A ≤ boundary.{u} n ↔ A ≠ ⊤ := by
  refine ⟨fun h ↦ ?_, fun hA ↦ ?_⟩
  · rintro rfl
    exact lt_irrefl _ (lt_of_le_of_lt h (boundary_lt_top n))
  · have := subcomplex_hasDimensionLT_of_neq_top A hA
    rw [Subcomplex.le_iff_contains_nonDegenerate]
    rintro m ⟨x, h₁⟩ h₂
    dsimp at h₂ ⊢
    by_cases! h₃ : m < n
    · simp [boundary_obj_eq_univ m n h₃]
    · simp [← A.mem_nonDegenerate_iff ⟨x, h₂⟩,
        nonDegenerate_eq_empty_of_hasDimensionLT _ _ _ h₃] at h₁

lemma eq_boundary_iff :
    A = boundary n ↔ boundary n ≤ A ∧ A ≠ ⊤ := by
  constructor
  · rintro rfl
    exact ⟨by rfl, (boundary_lt_top n).ne⟩
  · rintro ⟨h₁, h₂⟩
    exact le_antisymm (by rwa [le_boundary_iff]) h₁

end stdSimplex

namespace Subcomplex

/-- If `x : X _⦋n⦌` is missing from `A` and every lower-dimensional simplex lies in `A`,
then `A.preimage (yonedaEquiv.symm x) = ∂Δ[n]`. -/
private lemma preimage_eq_boundary_of_minimal_notMem
    {X : SSet.{u}} {n : ℕ} (A : X.Subcomplex) {x : X _⦋n⦌} (hxA : x ∉ A.obj _)
    (hn : ∀ m < n, ∀ y : X _⦋m⦌, y ∈ A.obj _) :
    A.preimage (yonedaEquiv.symm x) = (∂Δ[n] : (Δ[n] : SSet.{u}).Subcomplex) := by
  rw [stdSimplex.eq_boundary_iff]
  refine ⟨?_, fun heq ↦ hxA ?_⟩
  · rw [Subcomplex.le_iff_contains_nonDegenerate]
    intro d ⟨y, hy⟩ hy'
    have hd : d < n := dim_lt_of_nonDegenerate
      (X := ((∂Δ[n] : (Δ[n] : SSet.{u}).Subcomplex) : SSet.{u}))
      ⟨⟨y, hy'⟩, (Subcomplex.mem_nonDegenerate_iff _ _).2 hy⟩ _
    exact hn d hd ((yonedaEquiv.symm x).app _ y)
  · simpa using heq.symm.le _ (by simp : yonedaEquiv (𝟙 _) ∈ _)

/-- If `A.preimage (yonedaEquiv.symm x) = ∂Δ[n]`, then `x` is non-degenerate. -/
private lemma nonDegenerate_of_preimage_eq_boundary
    {X : SSet.{u}} {n : ℕ} (A : X.Subcomplex) (x : X _⦋n⦌)
    (h : A.preimage (yonedaEquiv.symm x) = ∂Δ[n]) :
    x ∈ X.nonDegenerate n := by
  intro hxd
  rw [SSet.mem_degenerate_iff] at hxd
  obtain ⟨m, hm, f, hf, y, rfl⟩ := hxd
  haveI := hf
  obtain ⟨⟨s, hs⟩⟩ := (isSplitEpi_of_epi f).exists_splitEpi
  -- A section `s : ⦋m⦌ ⟶ ⦋n⦌` of an epi `f : ⦋n⦌ ⟶ ⦋m⦌` with `m < n` cannot be surjective.
  have hs_ns : ¬ Function.Surjective ⇑s.toOrderHom := fun hsurj ↦ by
    haveI : Epi s := SimplexCategory.epi_iff_surjective.mpr hsurj
    exact absurd (SimplexCategory.len_le_of_epi s) (by lia)
  -- Evaluating `X.map f.op y` on the section recovers `y`.
  have hsf : (yonedaEquiv.symm (X.map f.op y)).app (op ⦋m⦌) (stdSimplex.objEquiv.symm s) = y := by
    change X.map s.op (X.map f.op y) = y
    rw [← Functor.map_comp_apply, ← op_comp, hs, op_id, Functor.map_id_apply]
  have hy_in_A : y ∈ A.obj _ := by
    have hs_in : stdSimplex.objEquiv.symm s ∈
        (∂Δ[n] : (Δ[n] : SSet.{u}).Subcomplex).obj (op ⦋m⦌) := hs_ns
    rw [← h] at hs_in
    rwa [Subcomplex.preimage_obj, Set.mem_preimage, hsf] at hs_in
  have hxA : X.map f.op y ∈ A.obj _ := A.map _ hy_in_A
  have hid : yonedaEquiv (𝟙 (Δ[n] : SSet.{u})) ∈
      (A.preimage (yonedaEquiv.symm (X.map f.op y))).obj (op ⦋n⦌) := by
    simp only [Subcomplex.preimage_obj, Set.mem_preimage, yonedaEquiv_symm_app_id]
    exact hxA
  rw [h] at hid
  exact stdSimplex.notMem_boundary n (by simpa using hid)

set_option backward.isDefEq.respectTransparency false in
/-- If the preimage of `A` along the simplex classified by `x : X _⦋n⦌` is `∂Δ[n]`,
then adjoining `x` to `A` is a pushout of `∂Δ[n] ↪ Δ[n]`. -/
lemma boundary.isPushout {X : SSet.{u}} {n : ℕ} (A : X.Subcomplex) (x : X _⦋n⦌)
    (h : A.preimage (yonedaEquiv.symm x) = ∂Δ[n]) :
    IsPushout (A.lift (∂Δ[n].ι ≫ yonedaEquiv.symm x)
        (by simp [Subcomplex.range_comp, Subcomplex.image_le_iff, h]))
      ∂Δ[n].ι (Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ .ofSimplex x))
        (yonedaEquiv.symm ⟨x, Or.inr (Subcomplex.mem_ofSimplex_obj x)⟩) := by
  have hnd : x ∈ X.nonDegenerate n := nonDegenerate_of_preimage_eq_boundary A x h
  set σ : (Δ[n] : SSet.{u}) ⟶ X := yonedaEquiv.symm x
  set A' : X.Subcomplex := A ⊔ .ofSimplex x
  refine IsPushout.of_forall_isPushout_app fun ⟨m⟩ ↦ ?_
  haveI := subtype_val_mono (A.obj ⟨m⟩)
  haveI := subtype_val_mono (A'.obj ⟨m⟩)
  -- Factor through `X.obj m` so the pullback obligation is `h` at `m`.
  refine Types.isPushout_of_isPullback_of_mono (X₅ := X.obj ⟨m⟩)
    (k := ↾Subtype.val) (r' := ↾Subtype.val) (b' := σ.app ⟨m⟩)
      ?_ rfl rfl ?_ ?_
  · exact Types.isPullback_of_eq_setPreimage (σ.app ⟨m⟩) (A.obj ⟨m⟩) (by simp [← h])
  · apply le_antisymm le_top
    rintro ⟨y, hy⟩ _
    simp only [Subfunctor.max_obj, Set.mem_union] at hy
    obtain hy | ⟨z, hz⟩ := hy
    · exact Or.inl ⟨⟨y, hy⟩, rfl⟩
    · exact Or.inr ⟨stdSimplex.objEquiv.symm z.unop, Subtype.ext hz⟩
  -- Off-boundary simplices have epi representing maps, so Eilenberg-Zilber map-uniqueness applies.
  · induction m using SimplexCategory.rec with | _ m
    intro x₃ y₃ hx₃ _ heq
    obtain ⟨φ, rfl⟩ := stdSimplex.objEquiv.symm.surjective x₃
    obtain ⟨ψ, rfl⟩ := stdSimplex.objEquiv.symm.surjective y₃
    have hφs : Function.Surjective ⇑φ.toOrderHom := by
      by_contra h'
      exact hx₃ ⟨⟨stdSimplex.objEquiv.symm φ, h'⟩, rfl⟩
    have hφ : Epi φ := SimplexCategory.epi_iff_surjective.mpr hφs
    obtain rfl := X.unique_nonDegenerate_map _ φ ⟨x, hnd⟩ rfl ψ ⟨x, hnd⟩ heq
    rfl

/-- Every proper subcomplex admits a strict extension exhibited as a pushout of
`∂Δ[n] ↪ Δ[n]` for some `n`. -/
lemma exists_isPushout_of_ne_top {X : SSet.{u}} (A : X.Subcomplex) (hA : A ≠ ⊤) :
    ∃ (B : X.Subcomplex) (lt : A < B) (n : ℕ)
      (t : ((∂Δ[n] : (Δ[n] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ (A : SSet.{u}))
      (b : (Δ[n] : SSet.{u}) ⟶ (B : SSet.{u})),
      IsPushout t (∂Δ[n] : (Δ[n] : SSet.{u}).Subcomplex).ι (Subcomplex.homOfLE lt.le) b := by
  by_contra h
  apply hA
  ext ⟨n⟩ : 2
  simp only [Subfunctor.top_obj, Set.top_eq_univ, Set.eq_univ_iff_forall]
  induction n using SimplexCategory.rec with | _ n
  induction n using Nat.strong_induction_on with | _ n hn
  by_contra! H
  obtain ⟨x, hxA⟩ := H
  apply h
  let A' : X.Subcomplex := A ⊔ .ofSimplex x
  have lt : A < A' := lt_of_le_not_ge le_sup_left
    (fun hAle ↦ hxA (hAle _ (Or.inr (Subcomplex.mem_ofSimplex_obj x))))
  have hpre : A.preimage (yonedaEquiv.symm x) = (∂Δ[n] : (Δ[n] : SSet.{u}).Subcomplex) :=
    preimage_eq_boundary_of_minimal_notMem A hxA hn
  exact ⟨A', lt, n, _, _, boundary.isPushout A x hpre⟩

end Subcomplex

end SSet
