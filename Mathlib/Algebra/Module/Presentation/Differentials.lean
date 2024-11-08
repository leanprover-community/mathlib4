/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Module.Presentation.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Kaehler.CotangentComplex
import Mathlib.RingTheory.Presentation

/-!
# Presentation of the module of differentials

Given a presentation of a `R`-algebra `S`, we obtain a presentation
of the `S`-module `Ω[S⁄R]`.

-/
universe w' t w u v

namespace Function.Exact

section

variable {M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
  [AddCommMonoid N₁] [AddCommMonoid N₂] [AddCommMonoid N₃]
  (f : M₁ →+ M₂) (g : M₂ →+ M₃) (f' : N₁ →+ N₂) (g' : N₂ →+ N₃)
  (τ₁ : M₁ →+ N₁) (τ₂ : M₂ →+ N₂) (τ₃ : M₃ →+ N₃)
  (comm₁₂ : f'.comp τ₁ = τ₂.comp f)
  (comm₂₃ : g'.comp τ₂ = τ₃.comp g)
  (h₁ : Function.Surjective τ₁)
  (h₂ : Function.Bijective τ₂)
  (h₃ : Function.Injective τ₃)

include comm₁₂ comm₂₃ h₁ h₂ h₃ in
lemma exact_iff_of_surjective_of_bijective_of_injective :
    Exact f g ↔ Exact f' g' := by
  replace comm₁₂ := DFunLike.congr_fun comm₁₂
  replace comm₂₃ := DFunLike.congr_fun comm₂₃
  dsimp at comm₁₂ comm₂₃
  constructor
  · intro h y₂
    obtain ⟨x₂, rfl⟩ := h₂.2 y₂
    constructor
    · intro hx₂
      obtain ⟨x₁, rfl⟩ := (h x₂).1 (h₃ (by simpa only [map_zero, comm₂₃] using hx₂))
      exact ⟨τ₁ x₁, by simp only [comm₁₂]⟩
    · rintro ⟨y₁, hy₁⟩
      obtain ⟨x₁, rfl⟩ := h₁ y₁
      rw [comm₂₃, (h x₂).2 _, map_zero]
      exact ⟨x₁, h₂.1 (by simpa only [comm₁₂] using hy₁)⟩
  · intro h x₂
    constructor
    · intro hx₂
      obtain ⟨y₁, hy₁⟩ := (h (τ₂ x₂)).1 (by simp only [comm₂₃, hx₂, map_zero])
      obtain ⟨x₁, rfl⟩ := h₁ y₁
      exact ⟨x₁, h₂.1 (by simpa only [comm₁₂] using hy₁)⟩
    · rintro ⟨x₁, rfl⟩
      apply h₃
      simp only [← comm₁₂, ← comm₂₃, h.apply_apply_eq_zero (τ₁ x₁), map_zero]

end

section

variable {R : Type*} [Semiring R]
  {M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
  [AddCommMonoid N₁] [AddCommMonoid N₂] [AddCommMonoid N₃]
  [Module R M₁] [Module R M₂] [Module R M₃]
  [Module R N₁] [Module R N₂] [Module R N₃]
  (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (f' : N₁ →ₗ[R] N₂) (g' : N₂ →ₗ[R] N₃)
  (τ₁ : M₁ →ₗ[R] N₁) (τ₂ : M₂ →ₗ[R] N₂) (τ₃ : M₃ →ₗ[R] N₃)
  (comm₁₂ : f'.comp τ₁ = τ₂.comp f)
  (comm₂₃ : g'.comp τ₂ = τ₃.comp g)
  (h₁ : Function.Surjective τ₁)
  (h₂ : Function.Bijective τ₂)
  (h₃ : Function.Injective τ₃)

include comm₁₂ comm₂₃ h₁ h₂ h₃ in
lemma linearMap_exact_iff_of_surjective_of_bijective_of_injective :
    Exact f g ↔ Exact f' g' :=
  exact_iff_of_surjective_of_bijective_of_injective f.toAddMonoidHom g.toAddMonoidHom
    f'.toAddMonoidHom g'.toAddMonoidHom τ₁.toAddMonoidHom τ₂.toAddMonoidHom τ₃.toAddMonoidHom
    (by ext; apply DFunLike.congr_fun comm₁₂) (by ext; apply DFunLike.congr_fun comm₂₃) h₁ h₂ h₃

end

end Function.Exact

namespace Algebra.Presentation

open KaehlerDifferential

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  (pres : Algebra.Presentation.{t, w} R S)

/-- The shape of the presentation by generators and relations of the `S`-module `Ω[S⁄R]`
that is obtained from a presentation of `S` as a `R`-algebra. -/
@[simps G R]
noncomputable def differentialsRelations : Module.Relations S where
  G := pres.vars
  R := pres.rels
  relation r :=
    Finsupp.mapRange (algebraMap pres.Ring S) (by simp)
      ((mvPolynomialBasis R pres.vars).repr (D _ _ (pres.relation r)))

namespace differentials

/-- Same as `comm₂₃` below, but here we have not yet constructed `differentialsSolution`. -/
lemma comm₂₃' : pres.toKaehler.comp pres.cotangentSpaceBasis.repr.symm.toLinearMap =
    Finsupp.linearCombination S (fun g ↦ D _ _ (pres.val g)) := by
  aesop

noncomputable def hom₁ : (pres.rels →₀ S) →ₗ[S] pres.Cotangent :=
  Finsupp.linearCombination S (fun r ↦ Ideal.toCotangent _ ⟨pres.relation r, by simp⟩)

lemma hom₁_single (r : pres.rels) :
    hom₁ pres (Finsupp.single r 1) = Ideal.toCotangent _ ⟨pres.relation r, by simp⟩ := by
  simp [hom₁]

lemma surjective_hom₁ : Function.Surjective (hom₁ pres) := by
  let φ : (pres.rels →₀ S) →ₗ[pres.Ring] pres.Cotangent :=
    { toFun := hom₁ pres
      map_add' := by simp
      map_smul' := by simp }
  change Function.Surjective φ
  have h₁ := Algebra.Generators.Cotangent.mk_surjective
    (P := pres.toGenerators)
  have h₂ : Submodule.span pres.Ring
    (Set.range (fun r ↦ (⟨pres.relation r, by simp⟩ : pres.ker))) = ⊤ := by
    refine Submodule.map_injective_of_injective (f := Submodule.subtype pres.ker)
      Subtype.coe_injective ?_
    rw [Submodule.map_top, Submodule.range_subtype, Submodule.map_span,
      Submodule.coe_subtype, Ideal.submodule_span_eq]
    simp only [← pres.span_range_relation_eq_ker]
    congr
    aesop
  rw [← LinearMap.range_eq_top] at h₁ ⊢
  rw [← top_le_iff, ← h₁, LinearMap.range_eq_map, ← h₂, Submodule.map_span_le]
  rintro _ ⟨r, rfl⟩
  simp only [LinearMap.mem_range]
  refine ⟨Finsupp.single r 1, ?_⟩
  simp only [LinearMap.coe_mk, AddHom.coe_mk, hom₁_single, φ]
  rfl

lemma comm₁₂_single (r : pres.rels) :
    pres.cotangentComplex (hom₁ pres (Finsupp.single r 1)) =
      pres.cotangentSpaceBasis.repr.symm ((differentialsRelations pres).relation r) := by
  simp only [hom₁, Finsupp.linearCombination_single, one_smul, differentialsRelations,
    Basis.repr_symm_apply]
  erw [Generators.cotangentComplex_mk]
  exact pres.cotangentSpaceBasis.repr.injective (by ext; simp)

lemma comm₁₂ : pres.cotangentComplex.comp (hom₁ pres) =
    pres.cotangentSpaceBasis.repr.symm.comp (differentialsRelations pres).map := by
  ext r
  dsimp
  rw [comm₁₂_single]
  erw [Module.Relations.map_single]

end differentials

open differentials in
/-- The `S`-module `Ω[S⁄R]` contains an obvious solution to the system of linear
equations `pres.differentialsRelations.Solution` when `pres` is a presentation
of `S` as a `R`-algebra. -/
noncomputable def differentialsSolution :
    pres.differentialsRelations.Solution (Ω[S⁄R]) where
  var g := D _ _ (pres.val g)
  linearCombination_var_relation r := by
    simp only [differentialsRelations_G, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, ← comm₂₃', ← comm₁₂_single]
    apply DFunLike.congr_fun (Function.Exact.linearMap_comp_eq_zero
      (pres.exact_cotangentComplex_toKaehler))

namespace differentials

lemma comm₂₃ :
    pres.toKaehler.comp pres.cotangentSpaceBasis.repr.symm.toLinearMap =
      pres.differentialsSolution.π :=
  comm₂₃' pres

end differentials

open differentials in
lemma differentialsSolution_isPresentation :
    pres.differentialsSolution.IsPresentation := by
  rw [Module.Relations.Solution.isPresentation_iff]
  constructor
  · rw [← Module.Relations.Solution.surjective_π_iff_span_eq_top, ← comm₂₃]
    exact Generators.toKaehler_surjective.comp pres.cotangentSpaceBasis.repr.symm.surjective
  · rw [← Module.Relations.range_map]
    exact Function.Exact.linearMap_ker_eq
      ((Function.Exact.linearMap_exact_iff_of_surjective_of_bijective_of_injective
      _ _ _ _ (hom₁ pres)
      pres.cotangentSpaceBasis.repr.symm.toLinearMap .id
      (comm₁₂ pres) (by simpa using comm₂₃ pres) (surjective_hom₁ pres)
        (LinearEquiv.bijective _) (Equiv.refl _).injective).2
        pres.exact_cotangentComplex_toKaehler)

/-- The presentation of the `S`-module `Ω[S⁄R]` deduced from a presentation
of `S` as a `R`-algebra. -/
@[simps!]
noncomputable def differentials : Module.Presentation S (Ω[S⁄R]) where
  toSolution := differentialsSolution pres
  toIsPresentation := pres.differentialsSolution_isPresentation

end Algebra.Presentation
