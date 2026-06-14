/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Module.SpanRankOperations
public import Mathlib.RingTheory.Regular.RegularSequence

/-!

# Equivalence between two set of minimal generators over local ring

-/

public section

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

variable {F₁ F₂ : Type*} [AddCommGroup F₁] [Module R F₁] [Module.Free R F₁]
  [AddCommGroup F₂] [Module R F₂] [Module.Free R F₂]

open IsLocalRing

variable [IsLocalRing R]
local notation "𝓀" => ResidueField R

lemma LinearMap.baseChange_bijective_of_spanRank_eq [Module.Finite R M]
    (f : F₁ →ₗ[R] M) (surj : Function.Surjective f)
    (hrk1 : Module.rank R F₁ = (⊤ : Submodule R M).spanFinrank) :
    Function.Bijective (f.baseChange 𝓀) := by
  --Module.finrank_eq_spanFinrank_of_free
  sorry

lemma LinearMap.bijective_of_comp_eq_of_spanRank_eq_of_surjective [Module.Finite R M]
    (f : F₁ →ₗ[R] M) (surjf : Function.Surjective f)
    (g : F₂ →ₗ[R] M) (surjg : Function.Surjective g)
    (hrk1 : Module.rank R F₁ = (⊤ : Submodule R M).spanFinrank)
    (hrk2 : Module.rank R F₂ = (⊤ : Submodule R M).spanFinrank)
    (h : F₁ →ₗ[R] F₂) (eq : g.comp h = f) : Function.Bijective h := by
  obtain ⟨e⟩ :=
    nonempty_linearEquiv_of_lift_rank_eq (R := R) (M := F₁) (M' := F₂) (by simp [hrk1, hrk2])
  have : Module.Finite R F₂ := by simp [← Module.rank_lt_aleph0_iff, hrk2]
  apply OrzechProperty.bijective_of_surjective_of_injective _ h e.injective
  have surjb : Function.Surjective (h.baseChange 𝓀) := by
    rw [← Function.Surjective.of_comp_iff' (g.baseChange_bijective_of_spanRank_eq surjg hrk2),
      ← LinearMap.coe_comp, ← LinearMap.baseChange_comp, eq]
    exact baseChange_surjective 𝓀 surjf

  sorry

lemma LinearMap.bijective_of_comp_eq_of_spanRank_eq (N : Submodule R M) (fg : N.FG)
    (f : F₁ →ₗ[R] M) (g : F₂ →ₗ[R] M) (hrf : f.range = N) (hrg : g.range = N)
    (hrk1 : Module.rank R F₁ = N.spanFinrank) (hrk2 : Module.rank R F₂ = N.spanFinrank)
    (h : F₁ →ₗ[R] F₂) (eq : g.comp h = f) : Function.Bijective h := by
  let f' := f.codRestrict N (fun _ ↦ hrf.le (LinearMap.mem_range_self _ _))
  have surjf' : Function.Surjective f' := by
    simp [f', ← LinearMap.range_eq_top, LinearMap.range_codRestrict, hrf]
  let g' := g.codRestrict N (fun _ ↦ hrg.le (LinearMap.mem_range_self _ _))
  have surjg' : Function.Surjective g' := by
    simp [g', ← LinearMap.range_eq_top, LinearMap.range_codRestrict, hrg]
  have : Module.Finite R N := Module.Finite.iff_fg.mpr fg
  apply LinearMap.bijective_of_comp_eq_of_spanRank_eq_of_surjective f' surjf' g' surjg' _ _ h _
  · simp [Submodule.spanFinrank_top, hrk1]
  · simp [Submodule.spanFinrank_top, hrk2]
  · ext x
    exact LinearMap.congr_fun eq x

lemma LinearEquiv.exists_of_length_eq_spanRank (I : Ideal R) (fg : I.FG)
    {l l' : List R} (eq1 : Ideal.ofList l = I) (eq2 : Ideal.ofList l' = I)
    (len1 : l.length = I.spanFinrank) (len2 : l'.length = I.spanFinrank) :
    ∃ e : (Fin l.length → R) ≃ₗ[R] (Fin l'.length → R),
      (Fintype.linearCombination R l'.get).comp e.toLinearMap =
        Fintype.linearCombination R l.get := by
  let f := Fintype.linearCombination R l.get
  let g := Fintype.linearCombination R l'.get
  have r : f.range = g.range := by simp [f, g, eq1, eq2]
  let f' := f.codRestrict g.range (fun _ ↦ r.le (LinearMap.mem_range_self _ _))
  obtain ⟨e, he⟩ := Module.projective_lifting_property _ f' g.surjective_rangeRestrict
  have : g.comp e = f := LinearMap.ext (fun x ↦ Subtype.ext_iff.mp (LinearMap.congr_fun he x))
  have bije := LinearMap.bijective_of_comp_eq_of_spanRank_eq I fg f g
    (by simp [f, eq1]) (by simp [g, eq2]) (by simp [len1]) (by simp [len2]) e this
  use LinearEquiv.ofBijective e bije, this
