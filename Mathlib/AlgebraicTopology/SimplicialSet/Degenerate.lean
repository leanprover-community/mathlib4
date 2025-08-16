/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# Degenerate simplices

Given a simplicial set `X` and `n : ℕ`, we define the sets `X.degenerate n`
and `X.nonDegenerate n` of degenerate or non-degenerate simplices of dimension `n`.

## TODO (@joelriou)

* `SSet.exists_nonDegenerate` shows that any `n`-simplex can be written as `X.map f.op y`
  for some epimorphism `f : ⦋n⦌ ⟶ ⦋m⦌` and some non-degenerate simplex `y`.
  Show that `f` and `y` are unique.

-/

universe u

open CategoryTheory Simplicial Limits Opposite

namespace SSet

variable (X : SSet.{u})

/-- An `n`-simplex of a simplicial set `X` is degenerate if it is in the range
of `X.map f.op` for some morphism `f : [n] ⟶ [m]` with `m < n`. -/
def degenerate (n : ℕ) : Set (X _⦋n⦌) :=
  setOf (fun x ↦ ∃ (m : ℕ) (_ : m < n) (f : ⦋n⦌ ⟶ ⦋m⦌),
    x ∈ Set.range (X.map f.op))

/-- The set of `n`-dimensional non-degenerate simplices in a simplicial
set `X` is the complement of `X.degenerate n`. -/
def nonDegenerate (n : ℕ) : Set (X _⦋n⦌) := (X.degenerate n)ᶜ

@[simp]
lemma degenerate_zero : X.degenerate 0 = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨m, hm, _⟩
  simp at hm

@[simp]
lemma nondegenerate_zero : X.nonDegenerate 0 = Set.univ := by
  simp [nonDegenerate]

variable {n : ℕ}

lemma mem_nonDegenerate_iff_notMem_degenerate (x : X _⦋n⦌) :
    x ∈ X.nonDegenerate n ↔ x ∉ X.degenerate n := Iff.rfl

@[deprecated (since := "2025-05-23")]
alias mem_nonDegenerate_iff_not_mem_degenerate := mem_nonDegenerate_iff_notMem_degenerate

lemma mem_degenerate_iff_notMem_nonDegenerate (x : X _⦋n⦌) :
    x ∈ X.degenerate n ↔ x ∉ X.nonDegenerate n := by
  simp [nonDegenerate]

@[deprecated (since := "2025-05-23")]
alias mem_degenerate_iff_not_mem_nonDegenerate := mem_degenerate_iff_notMem_nonDegenerate

lemma σ_mem_degenerate (i : Fin (n + 1)) (x : X _⦋n⦌) :
    X.σ i x ∈ X.degenerate (n + 1) :=
  ⟨n, by omega, SimplexCategory.σ i, Set.mem_range_self x⟩

lemma mem_degenerate_iff (x : X _⦋n⦌) :
    x ∈ X.degenerate n ↔ ∃ (m : ℕ) (_ : m < n) (f : ⦋n⦌ ⟶ ⦋m⦌) (_ : Epi f),
        x ∈ Set.range (X.map f.op) := by
  constructor
  · rintro ⟨m, hm, f, y, hy⟩
    rw [← image.fac f, op_comp] at hy
    have : _ ≤ m := SimplexCategory.len_le_of_mono (image.ι f)
    exact ⟨(image f).len, by omega, factorThruImage f, inferInstance, by aesop⟩
  · rintro ⟨m, hm, f, hf, hx⟩
    exact ⟨m, hm, f, hx⟩

lemma degenerate_eq_iUnion_range_σ :
    X.degenerate (n + 1) = ⋃ (i : Fin (n + 1)), Set.range (X.σ i) := by
  ext x
  constructor
  · intro hx
    rw [mem_degenerate_iff] at hx
    obtain ⟨m, hm, f, hf, y, rfl⟩ := hx
    obtain ⟨i, θ, rfl⟩ := SimplexCategory.eq_σ_comp_of_not_injective f (fun hf ↦ by
      rw [← SimplexCategory.mono_iff_injective] at hf
      have := SimplexCategory.le_of_mono f
      omega)
    aesop
  · intro hx
    simp only [Set.mem_iUnion, Set.mem_range] at hx
    obtain ⟨i, y, rfl⟩ := hx
    apply σ_mem_degenerate

lemma exists_nonDegenerate (x : X _⦋n⦌) :
    ∃ (m : ℕ) (f : ⦋n⦌ ⟶ ⦋m⦌) (_ : Epi f)
      (y : X.nonDegenerate m), x = X.map f.op y := by
  induction n with
  | zero =>
      exact ⟨0, 𝟙 _, inferInstance, ⟨x, by simp⟩, by simp⟩
  | succ n hn =>
      by_cases hx : x ∈ X.nonDegenerate (n + 1)
      · exact ⟨n + 1, 𝟙 _, inferInstance, ⟨x, hx⟩, by simp⟩
      · simp only [← mem_degenerate_iff_notMem_nonDegenerate,
          degenerate_eq_iUnion_range_σ, Set.mem_iUnion, Set.mem_range] at hx
        obtain ⟨i, y, rfl⟩ := hx
        obtain ⟨m, f, hf, z, rfl⟩ := hn y
        exact ⟨_, SimplexCategory.σ i ≫ f, inferInstance, z, by simp; rfl⟩

lemma isIso_of_nonDegenerate (x : X.nonDegenerate n)
    {m : SimplexCategory} (f : ⦋n⦌ ⟶ m) [Epi f]
    (y : X.obj (op m)) (hy : X.map f.op y = x) :
    IsIso f := by
  obtain ⟨x, hx⟩ := x
  induction' m using SimplexCategory.rec with m
  rw [mem_nonDegenerate_iff_notMem_degenerate] at hx
  by_contra!
  refine hx ⟨_, not_le.1 (fun h ↦ this ?_), f, y, hy⟩
  rw [SimplexCategory.isIso_iff_of_epi]
  exact le_antisymm h (SimplexCategory.len_le_of_epi f)

namespace Subcomplex

variable {X} (A : X.Subcomplex)

lemma mem_degenerate_iff {n : ℕ} (x : A.obj (op (.mk n))) :
    x ∈ degenerate A n ↔ x.1 ∈ X.degenerate n := by
  rw [SSet.mem_degenerate_iff, SSet.mem_degenerate_iff]
  constructor
  · rintro ⟨m, hm, f, _, ⟨y, rfl⟩⟩
    exact ⟨m, hm, f, inferInstance, ⟨y.1, rfl⟩⟩
  · obtain ⟨x, hx⟩ := x
    rintro ⟨m, hm, f, _, ⟨y, rfl⟩⟩
    refine ⟨m, hm, f, inferInstance, ⟨⟨y, ?_⟩, rfl⟩⟩
    have := isSplitEpi_of_epi f
    simpa only [Set.mem_preimage, ← op_comp, ← FunctorToTypes.map_comp_apply,
      IsSplitEpi.id, op_id, FunctorToTypes.map_id_apply] using A.map (section_ f).op hx

lemma mem_nonDegenerate_iff {n : ℕ} (x : A.obj (op (.mk n))) :
    x ∈ nonDegenerate A n ↔ x.1 ∈ X.nonDegenerate n := by
  rw [mem_nonDegenerate_iff_notMem_degenerate,
    mem_nonDegenerate_iff_notMem_degenerate, mem_degenerate_iff]

lemma le_iff_contains_nonDegenerate (B : X.Subcomplex) :
    A ≤ B ↔ ∀ (n : ℕ) (x : X.nonDegenerate n), x.1 ∈ A.obj _ → x.1 ∈ B.obj _ := by
  constructor
  · aesop
  · rintro h ⟨n⟩ x hx
    induction' n using SimplexCategory.rec with n
    obtain ⟨m, f, _, ⟨a, ha⟩, ha'⟩ := exists_nonDegenerate A ⟨x, hx⟩
    simp only [Subpresheaf.toPresheaf_obj, Subtype.ext_iff,
      Subpresheaf.toPresheaf_map_coe] at ha'
    subst ha'
    rw [mem_nonDegenerate_iff] at ha
    exact B.map f.op (h _ ⟨_, ha⟩ a.2)

lemma eq_top_iff_contains_nonDegenerate :
    A = ⊤ ↔ ∀ (n : ℕ), X.nonDegenerate n ⊆ A.obj _ := by
  simpa using le_iff_contains_nonDegenerate ⊤ A

lemma degenerate_eq_top_iff (n : ℕ) :
    degenerate A n = ⊤ ↔ (X.degenerate n ⊓ A.obj _) = A.obj _ := by
  constructor
  · intro h
    ext x
    simp only [Set.inf_eq_inter, Set.mem_inter_iff, and_iff_right_iff_imp]
    intro hx
    simp only [← A.mem_degenerate_iff ⟨x, hx⟩, h, Set.top_eq_univ, Set.mem_univ]
  · intro h
    simp only [Set.inf_eq_inter, Set.inter_eq_right] at h
    ext x
    simpa [A.mem_degenerate_iff] using h x.2

variable (X) in
lemma iSup_ofSimplex_nonDegenerate_eq_top :
    ⨆ (x : Σ (p : ℕ), X.nonDegenerate p), ofSimplex x.2.1 = ⊤ := by
  rw [eq_top_iff_contains_nonDegenerate]
  intro n x hx
  simp only [Subpresheaf.iSup_obj, Set.mem_iUnion, Sigma.exists,
    Subtype.exists, exists_prop]
  exact ⟨n, x, hx, mem_ofSimplex_obj x⟩

end Subcomplex


section

variable {X} {Y : SSet.{u}}

lemma degenerate_map {n : ℕ} {x : X _⦋n⦌} (hx : x ∈ X.degenerate n) (f : X ⟶ Y) :
    f.app _ x ∈ Y.degenerate n := by
  obtain ⟨m, hm, g, y, rfl⟩ := hx
  exact ⟨m, hm, g, f.app _ y, by rw [FunctorToTypes.naturality]⟩

lemma degenerate_le_preimage (f : X ⟶ Y) (n : ℕ) :
    X.degenerate n ⊆ Set.preimage (f.app _) (Y.degenerate n) :=
  fun _ hx ↦ degenerate_map hx f

lemma image_degenerate_le (f : X ⟶ Y) (n : ℕ) :
    Set.image (f.app _) (X.degenerate n) ⊆ Y.degenerate n := by
  simpa using degenerate_le_preimage f n

lemma degenerate_iff_of_isIso (f : X ⟶ Y) [IsIso f] {n : ℕ} (x : X _⦋n⦌) :
    f.app _ x ∈ Y.degenerate n ↔ x ∈ X.degenerate n := by
  constructor
  · intro hy
    simpa [← FunctorToTypes.comp] using degenerate_map hy (inv f)
  · exact fun hx ↦ degenerate_map hx f

lemma nonDegenerate_iff_of_isIso (f : X ⟶ Y) [IsIso f] {n : ℕ} (x : X _⦋n⦌) :
    f.app _ x ∈ Y.nonDegenerate n ↔ x ∈ X.nonDegenerate n := by
  simp only [mem_nonDegenerate_iff_notMem_degenerate,
    degenerate_iff_of_isIso]

attribute [local simp] nonDegenerate_iff_of_isIso in
/-- The bijection on nondegenerate simplices induced by an isomorphism
of simplicial sets. -/
@[simps]
def nonDegenerateEquivOfIso (e : X ≅ Y) {n : ℕ} :
    X.nonDegenerate n ≃ Y.nonDegenerate n where
  toFun := fun ⟨x, hx⟩ ↦ ⟨e.hom.app _ x, by aesop⟩
  invFun := fun ⟨y, hy⟩ ↦ ⟨e.inv.app _ y, by aesop⟩
  left_inv _ := by aesop
  right_inv _ := by aesop

end

variable {X} in
lemma degenerate_iff_of_mono {Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (x : X _⦋n⦌) :
    f.app _ x ∈ Y.degenerate n ↔ x ∈ X.degenerate n := by
  rw [← degenerate_iff_of_isIso (Subcomplex.toRange f) x,
    Subcomplex.mem_degenerate_iff]
  simp

variable {X} in
lemma nonDegenerate_iff_of_mono {Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (x : X _⦋n⦌) :
    f.app _ x ∈ Y.nonDegenerate n ↔ x ∈ X.nonDegenerate n := by
  simp only [mem_nonDegenerate_iff_notMem_degenerate, degenerate_iff_of_mono]

end SSet
