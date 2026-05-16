/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Adam Topaz, Jacob Reinhold
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

import Mathlib.CategoryTheory.Limits.Types.Pushouts

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

/-- A simplex of `Δ[n]` is outside the boundary iff its representing map is epi. -/
lemma stdSimplex.notMem_boundary_iff_epi_objEquiv {n m : ℕ} (x : Δ[n] _⦋m⦌) :
    x ∉ (boundary.{u} n).obj (op ⦋m⦌) ↔ Epi (stdSimplex.objEquiv x) := by
  rw [SimplexCategory.epi_iff_surjective]
  simp only [boundary, Set.mem_setOf_eq, Decidable.not_not]
  rfl

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

@[simp]
lemma boundary_zero : boundary.{u} 0 = ⊥ := by
  ext m x
  simp only [boundary, Nat.reduceAdd, Set.mem_setOf_eq, Subfunctor.bot_obj, Set.bot_eq_empty,
    Set.mem_empty_iff_false, iff_false, Decidable.not_not]
  intro x
  exact ⟨0, by subsingleton⟩

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

namespace boundary

/-- The inclusion of a face of `∂Δ[n]`. -/
def faceι {n : ℕ} (i : Fin (n + 1)) :
    (stdSimplex.face {i}ᶜ : SSet.{u}) ⟶ ∂Δ[n] :=
  Subcomplex.homOfLE (face_singleton_compl_le_boundary i)

instance {n : ℕ} (i : Fin (n + 1)) : Mono (faceι.{u} i) := by
  dsimp [faceι]; infer_instance

@[reassoc (attr := simp)]
lemma faceι_ι {n : ℕ} (i : Fin (n + 2)) :
    faceι i ≫ (boundary.{u} (n + 1)).ι = (stdSimplex.face {i}ᶜ).ι := by
  simp [faceι]

/-- The morphism `Δ[n] ⟶ ∂Δ[n + 1]` corresponding to face
the face `i : Fin (n + 2)`. -/
def ι {n : ℕ} (i : Fin (n + 2)) :
    Δ[n] ⟶ (∂Δ[n + 1] : SSet.{u}) :=
  Subcomplex.lift ((stdSimplex.{u}.map (SimplexCategory.δ i))) (by
    simp only [Subcomplex.range_eq_ofSimplex]
    refine le_trans ?_ (face_singleton_compl_le_boundary i)
    rw [stdSimplex.face_singleton_compl, yonedaEquiv_map])

@[reassoc (attr := simp)]
lemma ι_ι {n : ℕ} (i : Fin (n + 2)) :
    ι.{u} i ≫ ∂Δ[n + 1].ι = stdSimplex.δ i := rfl

@[reassoc (attr := simp)]
lemma faceSingletonComplIso_inv_ι {n : ℕ} (i : Fin (n + 2)) :
    (stdSimplex.faceSingletonComplIso i).inv ≫ ι i = boundary.faceι i := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso i).hom, Iso.hom_inv_id_assoc]
  rfl

instance {n : ℕ} (i : Fin (n + 2)) : Mono (ι.{u} i) := by
  rw [← mono_comp_iff_of_isIso (stdSimplex.faceSingletonComplIso i).inv,
    faceSingletonComplIso_inv_ι]
  infer_instance

instance {n : ℕ} (i : Fin (n + 2)) : Mono (stdSimplex.{u}.δ i) := by
  rw [← ι_ι]
  infer_instance

lemma hom_ext {n : ℕ} {X : SSet.{u}} {f g : (∂Δ[n + 1] : SSet) ⟶ X}
    (h : ∀ (i : Fin (n + 2)), ι i ≫ f = ι i ≫ g) :
    f = g := by
  ext m ⟨x, hx⟩
  simp only [boundary_eq_iSup, stdSimplex.face_singleton_compl, Subfunctor.iSup_obj,
    Set.mem_iUnion, Subcomplex.mem_ofSimplex_obj_iff, op_unop] at hx
  obtain ⟨i, ⟨y, rfl⟩⟩ := hx
  exact ConcreteCategory.congr_hom (congr_app (h i) _) _

@[ext]
lemma hom_ext₀ {X : SSet.{u}} {f g : (∂Δ[0] : SSet) ⟶ X} : f = g := by
  ext _ ⟨x, hx⟩
  simp at hx

/-- The top simplex is not in the boundary. -/
lemma yonedaEquiv_id_notMem (n : ℕ) :
    yonedaEquiv.{u} (𝟙 Δ[n]) ∉ ∂Δ[n].obj _ := by
  simpa only [stdSimplex.objEquiv_yonedaEquiv_id] using stdSimplex.notMem_boundary.{u} n

/-- A codimension-one face lies in the boundary. -/
lemma yonedaEquiv_δ_mem {n : ℕ} (i : Fin (n + 2)) :
    yonedaEquiv (stdSimplex.{u}.δ i) ∈ ∂Δ[n + 1].obj _ := by
  rw [← ι_ι i, ← Subcomplex.yonedaEquiv_coe (boundary.ι.{u} i)]
  exact (yonedaEquiv (ι.{u} i)).property

/-- If `x : X _⦋n⦌` is missing from `A` and every lower-dimensional simplex lies in `A`,
then `A.preimage (yonedaEquiv.symm x) = ∂Δ[n]`. -/
lemma preimage_eq_boundary_of_minimal_notMem
    {X : SSet.{u}} {n : ℕ} (A : X.Subcomplex) {x : X _⦋n⦌} (hxA : x ∉ A.obj _)
    (hn : ∀ m < n, ∀ y : X _⦋m⦌, y ∈ A.obj _) :
    A.preimage (yonedaEquiv.symm x) = ∂Δ[n] := by
  rw [stdSimplex.eq_boundary_iff]
  refine ⟨?_, fun heq ↦ hxA ?_⟩
  · rw [Subcomplex.le_iff_contains_nonDegenerate]
    intro d ⟨y, hy⟩ hy'
    exact hn d (dim_lt_of_nonDegenerate (X := ∂Δ[n]) ⟨⟨y, hy'⟩,
      (Subcomplex.mem_nonDegenerate_iff _ _).2 hy⟩ _) _
  · simpa using heq.symm.le _ (show yonedaEquiv (𝟙 _) ∈ _ by simp)

/-- If `A.preimage (yonedaEquiv.symm x) = ∂Δ[n]`, then `x` is non-degenerate. -/
lemma nonDegenerate_of_preimage_eq_boundary
    {X : SSet.{u}} {n : ℕ} (A : X.Subcomplex) (x : X _⦋n⦌)
    (h : A.preimage (yonedaEquiv.symm x) = ∂Δ[n]) :
    x ∈ X.nonDegenerate n := by
  rw [mem_nonDegenerate_iff_notMem_degenerate]
  intro hx
  obtain _ | n := n
  · simp at hx
  · refine yonedaEquiv_id_notMem.{u} (n + 1) ?_
    rw [← h]
    simp only [degenerate_eq_iUnion_range_σ, Set.mem_iUnion, Set.mem_range] at hx
    obtain ⟨i, y, rfl⟩ := hx
    simp only [Subcomplex.preimage_obj, Set.mem_preimage, yonedaEquiv_symm_app_id]
    apply A.map
    have := yonedaEquiv_δ_mem.{u} i.castSucc
    simp only [← h, Subcomplex.preimage_obj, Set.mem_preimage] at this
    -- TODO: after #38664, express this as Yoneda naturality:
    -- `convert this; rw [← yonedaEquiv_comp, stdSimplex.yonedaEquiv_δ_comp]; simp`.
    change X.δ i.castSucc (X.σ i y) ∈ A.obj _ at this
    simpa using this

/-- If the preimage of `A` along the simplex classified by `x : X _⦋n⦌` is `∂Δ[n]`,
then adjoining `x` to `A` is a pushout of `∂Δ[n] ↪ Δ[n]`. -/
lemma isPushout {X : SSet.{u}} {n : ℕ} (A : X.Subcomplex) (x : X _⦋n⦌)
    (h : A.preimage (yonedaEquiv.symm x) = ∂Δ[n]) :
    IsPushout (A.lift (∂Δ[n].ι ≫ yonedaEquiv.symm x)
        (by simp [Subcomplex.range_comp, Subcomplex.image_le_iff, h]))
      ∂Δ[n].ι (Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ .ofSimplex x))
        (yonedaEquiv.symm ⟨x, Or.inr (Subcomplex.mem_ofSimplex_obj x)⟩) := by
  have hnd : x ∈ X.nonDegenerate n := nonDegenerate_of_preimage_eq_boundary A x h
  set σ : (Δ[n] : SSet.{u}) ⟶ X := yonedaEquiv.symm x
  refine IsPushout.of_forall_isPushout_app fun ⟨m⟩ ↦
    (Types.isPushout_of_isPullback_of_mono
      (k := (Subcomplex.ι _).app _) ?_ rfl rfl ?_ ?_)
  · exact Types.isPullback_of_eq_setPreimage (σ.app ⟨m⟩) (A.obj ⟨m⟩) (by simp [← h])
  · apply le_antisymm le_top
    rintro ⟨y, hy⟩ _
    simp only [Subfunctor.max_obj, Set.mem_union] at hy
    obtain hy | ⟨z, hz⟩ := hy
    · exact Or.inl ⟨⟨y, hy⟩, rfl⟩
    · exact Or.inr ⟨stdSimplex.objEquiv.symm z.unop, Subtype.ext hz⟩
  · induction m using SimplexCategory.rec with | _ m
    intro x₃ y₃ hx₃ _ heq
    obtain ⟨φ, rfl⟩ := stdSimplex.objEquiv.symm.surjective x₃
    obtain ⟨ψ, rfl⟩ := stdSimplex.objEquiv.symm.surjective y₃
    have hφ : Epi φ := (stdSimplex.notMem_boundary_iff_epi_objEquiv
      (stdSimplex.objEquiv.symm φ)).1 (by
        intro hφ_mem
        exact hx₃ ⟨⟨stdSimplex.objEquiv.symm φ, hφ_mem⟩, rfl⟩)
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
  ext ⟨⟨n⟩⟩ : 2
  simp only [Subfunctor.top_obj, Set.top_eq_univ, Set.eq_univ_iff_forall]
  induction n using Nat.strong_induction_on with | _ n hn
  by_contra! H
  obtain ⟨x, hxA⟩ := H
  apply h
  let A' : X.Subcomplex := A ⊔ .ofSimplex x
  have lt : A < A' := lt_of_le_not_ge le_sup_left
    (fun hAle ↦ hxA (hAle _ (Or.inr (Subcomplex.mem_ofSimplex_obj x))))
  have hpre : A.preimage (yonedaEquiv.symm x) = (∂Δ[n] : (Δ[n] : SSet.{u}).Subcomplex) :=
    preimage_eq_boundary_of_minimal_notMem A hxA hn
  exact ⟨A', lt, n, _, _, isPushout A x hpre⟩

end boundary

end SSet
