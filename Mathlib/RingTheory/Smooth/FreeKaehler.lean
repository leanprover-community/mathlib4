/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Smooth.Kaehler
import Mathlib.RingTheory.Smooth.StandardSmooth

/-!
# Standard smooth algebras
-/

universe u v

section

lemma Set.isCompl_iff {α : Type*} (s t : Set α) :
    IsCompl s t ↔ ∀ a, a ∈ s ↔ a ∉ t := by
  simp_rw [← eq_compl_iff_isCompl, Set.ext_iff, mem_compl_iff]

end

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

lemma Algebra.Extension.toKaehler_comp_map {P P' : Extension R S}
    (f : P.Hom P') :
    P'.toKaehler ∘ₗ Extension.CotangentSpace.map f = P.toKaehler := by
  ext x
  simp

@[simp]
lemma Algebra.Extension.toKaehler_map {P P' : Extension R S}
    (f : P.Hom P') (x : P.CotangentSpace) :
    P'.toKaehler (Extension.CotangentSpace.map f x) = P.toKaehler x := by
  simp [← Algebra.Extension.toKaehler_comp_map f]

end

section

variable {R K M P : Type*} [CommRing R] [AddCommGroup K] [AddCommGroup M] [AddCommGroup P]
variable [Module R K] [Module R M] [Module R P]
variable (f : K →ₗ[R] M) (g : M →ₗ[R] P)

section

variable {κ σ : Type*} (b : Basis (κ ⊕ σ) R M)

lemma injective_restrict_aux (hf : Function.Injective f) (hfg : Function.Exact f g)
    (H : LinearIndependent R (fun i ↦ g (b (Sum.inr i)))) :
    Function.Injective
      (Finsupp.lcomapDomain Sum.inl Sum.inl_injective ∘ₗ b.repr.toLinearMap ∘ₗ f) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  have hgfx : g (f x) = 0 := hfg.apply_apply_eq_zero x
  replace hx (i : κ) : (b.repr (f x)) (.inl i) = 0 := by
    rw [LinearMap.mem_ker, Finsupp.ext_iff] at hx
    exact hx i
  suffices h : f x = 0 by
    rw [← LinearMap.ker_eq_bot] at hf
    have : x ∈ LinearMap.ker f := h
    rwa [hf] at this
  generalize f x = q at hx hgfx
  rw [← b.linearCombination_repr q] at hgfx
  rw [Finsupp.linearCombination_apply] at hgfx
  simp only [Finsupp.sum] at hgfx
  simp at hgfx
  rw [← Finset.toLeft_disjSum_toRight (u := (b.repr q).support)] at hgfx
  rw [Finset.sum_disj_sum] at hgfx
  simp [hx] at hgfx
  rw [linearIndependent_iff'] at H
  have := H _ _ hgfx
  rw [b.ext_elem_iff]
  simp [hx]
  intro b
  simp_all only [zero_smul, Finset.sum_const_zero, Finset.mem_toRight, Finsupp.mem_support_iff,
    ne_eq, imp_false, not_not]

lemma surjective_restrict_aux (hfg : Function.Exact f g)
    (H : Submodule.span R (Set.range <| g ∘ b ∘ Sum.inr) = ⊤) :
    Function.Surjective
      (Finsupp.lcomapDomain Sum.inl Sum.inl_injective ∘ₗ b.repr.toLinearMap ∘ₗ f) := by
  intro b
  induction' b using Finsupp.induction_linear with a b ha hb i r
  · use 0
    simp
  · obtain ⟨x, rfl⟩ := ha
    obtain ⟨y, rfl⟩ := hb
    use x + y
    simp
  wlog h : r = 1 generalizing r
  · obtain ⟨x, hx⟩ := this 1 rfl
    use r • x
    simp [hx]
  subst h
  let d := g (b (Sum.inl i))
  have : d ∈ Submodule.span R (Set.range <| g ∘ b ∘ Sum.inr) := by rw [H]; trivial
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at this
  obtain ⟨c, hc⟩ := this
  simp [Finsupp.sum] at hc
  have : b (.inl i) - ∑ j ∈ c.support, c j • b (.inr j) ∈ LinearMap.ker g := by
    simp [hc]
  rw [hfg.linearMap_ker_eq] at this
  obtain ⟨a, ha⟩ := this
  use a
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, ha, map_sub,
    Basis.repr_self, map_sum, map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
  ext j
  simp [Finsupp.lcomapDomain]

end

variable {ι κ σ : Type*} (b : Basis ι R M)
  (u : κ → ι) (hu : Function.Injective u)
  (v : σ → ι) (hv : Function.Injective v)

noncomputable def sumEquiv (huv : IsCompl (Set.range u) (Set.range v)) : σ ⊕ κ ≃ ι :=
  Equiv.ofBijective (Sum.elim v u)
    ⟨hv.sum_elim hu <| by
      intro a b heq
      have : v a ∈ Set.range u ⊓ Set.range v := by
        constructor
        · rw [heq]
          use b
        · use a
      rwa [huv.inf_eq_bot] at this,
    by
      intro i
      have : i ∈ Set.range u ⊔ Set.range v := by
        rw [huv.sup_eq_top]
        trivial
      obtain (⟨i, rfl⟩|⟨i, rfl⟩) := this
      · use Sum.inr i
        simp
      · use Sum.inl i
        simp
    ⟩

@[simp]
lemma sumEquiv_apply (huv : IsCompl (Set.range u) (Set.range v)) (x : σ ⊕ κ) :
    sumEquiv u hu v hv huv x = Sum.elim v u x := rfl

include hu in
lemma injective_restrict (hf : Function.Injective f) (hfg : Function.Exact f g)
    (H : LinearIndependent R (fun i ↦ g (b (u i))))
    (huv : IsCompl (Set.range u) (Set.range v)) :
    Function.Injective
      (Finsupp.lcomapDomain v hv ∘ₗ b.repr.toLinearMap ∘ₗ f) := by
  let b' : Basis (σ ⊕ κ) R M := b.reindex (sumEquiv u hu v hv huv).symm
  have : Finsupp.lcomapDomain v hv ∘ₗ b.repr.toLinearMap ∘ₗ f =
      Finsupp.lcomapDomain Sum.inl Sum.inl_injective ∘ₗ b'.repr.toLinearMap ∘ₗ f := by
    ext x i
    simp [b', Finsupp.lcomapDomain]
  rw [this]
  apply injective_restrict_aux f g _ hf hfg
  have (i) : g (b' (Sum.inr i)) = g (b (u i)) := by simp [b']
  simp_rw [this]
  exact H

include hu in
lemma surjective_restrict (hfg : Function.Exact f g)
    (H : Submodule.span R (Set.range <| g ∘ b ∘ u) = ⊤)
    (huv : IsCompl (Set.range u) (Set.range v)) :
    Function.Surjective
      (Finsupp.lcomapDomain v hv ∘ₗ b.repr.toLinearMap ∘ₗ f) := by
  let b' : Basis (σ ⊕ κ) R M := b.reindex (sumEquiv u hu v hv huv).symm
  have : Finsupp.lcomapDomain v hv ∘ₗ b.repr.toLinearMap ∘ₗ f =
      Finsupp.lcomapDomain Sum.inl Sum.inl_injective ∘ₗ b'.repr.toLinearMap ∘ₗ f := by
    ext x i
    simp [b', Finsupp.lcomapDomain]
  rw [this]
  apply surjective_restrict_aux f g _ hfg
  have : g ∘ b' ∘ Sum.inr = g ∘ b ∘ u := by ext; simp [b']
  simp_rw [this]
  exact H

end

noncomputable section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

namespace Algebra

open KaehlerDifferential MvPolynomial

lemma exists_generators_of_free_kaehlerDifferential [Algebra.FiniteType R S]
    [Module.Free S (Ω[S⁄R])] :
    ∃ (P : Generators.{v} R S) (_ : Finite P.vars) (κ : Type v) (a : κ → P.vars)
      (b : Basis κ S (Ω[S⁄R])),
      ∀ k, b k = P.toExtension.toKaehler (1 ⊗ₜ D _ _ (X (a k))) := by
  haveI : Module.Finite S (Ω[S⁄R]) := inferInstance
  obtain ⟨ι, _, f, hf⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial' (R := R) (S := S)).mp inferInstance
  let P : Generators R S :=
    Generators.ofSurjective (fun i ↦ f (X i)) <| by rwa [aeval_unique f] at hf
  have hfin : Finite P.vars := by
    simp only [P, Generators.ofSurjective_vars]
    infer_instance
  letI : Fintype P.vars := Fintype.ofFinite P.vars
  --use P, hfin
  let I := Module.Free.ChooseBasisIndex S (Ω[S⁄R])
  let b : Basis I S (Ω[S⁄R]) := Module.Free.chooseBasis S (Ω[S⁄R])
  let f := Function.surjInv P.toExtension.toKaehler_surjective
  let bCsp := P.cotangentSpaceBasis
  let coeffs (i : I) : P.vars → S := Finsupp.equivFunOnFinite (bCsp.repr (f (b i)))
  let coeffsp (i : I) : P.vars → P.Ring := P.σ ∘ (coeffs i)
  let t : P.vars ⊕ I → P.Ring :=
    Sum.elim X (fun i ↦ ∑ k : P.vars, coeffsp i k * X k)
  let P' : Generators R S := Generators.ofSurjective
    (vars := P.vars ⊕ I) (aeval P.val ∘ t) sorry
  let hom : P'.Hom P :=
    { val := t
      aeval_val := by intro i; rfl }
  use P', inferInstanceAs (Finite <| P.vars ⊕ I), I, Sum.inr, b
  let r := Extension.CotangentSpace.map hom.toExtensionHom
  intro k
  let foo := r (1 ⊗ₜ[P'.toExtension.Ring] (D R P'.toExtension.Ring) (X (Sum.inr k)))
  have : P.toExtension.toKaehler foo =
      P'.toExtension.toKaehler
        (1 ⊗ₜ[P'.toExtension.Ring] (D R P'.toExtension.Ring) (X (Sum.inr k))) := by
    simp [foo, r, Extension.toKaehler]
    conv_rhs => erw [mapBaseChange_tmul]
    have : (Extension.CotangentSpace.map hom.toExtensionHom) (1 ⊗ₜ[P'.toExtension.Ring]
        (D R P'.toExtension.Ring) (X (Sum.inr k))) =
        1 ⊗ₜ[P.toExtension.Ring]
          (D R P.toExtension.Ring) (hom.toExtensionHom.toAlgHom (X (Sum.inr k))) := by
      apply Algebra.Extension.CotangentSpace.map_tmul
    erw [this]
    conv_lhs => erw [mapBaseChange_tmul]
    simp only [Generators.toExtension_Ring, Generators.toExtension_commRing, map_D,
      Generators.algebraMap_apply, one_smul, aeval_X]
    congr
    erw [Algebra.Extension.Hom.toAlgHom_apply]
    simp
  rw [← this]
  simp only [foo, r]
  rw [Algebra.Extension.CotangentSpace.map_tmul]
  simp
  erw [Algebra.Extension.Hom.toAlgHom_apply]
  simp [t]
  rw [Finset.sum_add_distrib]
  rw [TensorProduct.tmul_add]
  rw [map_add]
  sorry

/-- If `Ω[S⁄R]` has a basis of the form `{d sᵢ}` where `sᵢ : S`, there exist
generators `P` such that `Ω[S⁄R]` is free on `{d xᵢ}` for some of the generators `xᵢ`. -/
lemma exists_generators_of_basis_kaehlerDifferential [Algebra.FiniteType R S]
    {I : Type v} (b : Basis I S (Ω[S⁄R]))
    (hb : Set.range b ⊆ Set.range (D R S)) :
    ∃ (P : Generators.{v} R S) (_ : Finite P.vars) (κ : Type v) (a : κ → P.vars)
      (b : Basis κ S (Ω[S⁄R])),
      Function.Injective a ∧ ∀ k, b k = P.toExtension.toKaehler (1 ⊗ₜ D _ _ (X (a k))) := by
  obtain ⟨ι, _, f, hf⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial' (R := R) (S := S)).mp inferInstance
  let P : Generators R S :=
    Generators.ofSurjective (fun i ↦ f (X i)) <| by rwa [aeval_unique f] at hf
  have hfin : Finite P.vars := by
    simp only [P, Generators.ofSurjective_vars]
    infer_instance
  wlog h : Nontrivial S
  · rw [not_nontrivial_iff_subsingleton] at h
    have : Subsingleton (Ω[S⁄R]) := Module.subsingleton S _
    exact ⟨P, hfin, PEmpty, PEmpty.elim,
      Basis.empty _, Function.injective_of_subsingleton PEmpty.elim, by tauto⟩
  letI : Fintype P.vars := Fintype.ofFinite P.vars
  choose f' hf' using hb
  let f (i : I) : S := f' ⟨i, rfl⟩
  have hf (i : I) : D R S (f i) = b i := by simp [f, hf']
  let g (i : I) : P.Ring := P.σ (f i)
  let t : P.vars ⊕ I → P.Ring := Sum.elim X g
  let P' : Generators R S := Generators.ofSurjective
      (vars := P.vars ⊕ I) (aeval P.val ∘ t) <| by
    intro s
    use rename Sum.inl (P.σ s)
    rw [aeval_rename]
    rw [Function.comp_assoc]
    simp only [Sum.elim_comp_inl, t]
    rw [← aeval_unique]
    simp
  let hom : P'.Hom P :=
    { val := t
      aeval_val := by intro i; rfl }
  haveI : Module.Finite S (Ω[S⁄R]) := inferInstance
  have : Finite I := Module.Finite.finite_basis b
  use P', inferInstanceAs (Finite <| P.vars ⊕ I), I, Sum.inr, b, Sum.inr_injective
  let r := Extension.CotangentSpace.map hom.toExtensionHom
  intro k
  let foo := r (1 ⊗ₜ[P'.toExtension.Ring] (D R P'.toExtension.Ring) (X (Sum.inr k)))
  have : P.toExtension.toKaehler foo =
      P'.toExtension.toKaehler
        (1 ⊗ₜ[P'.toExtension.Ring] (D R P'.toExtension.Ring) (X (Sum.inr k))) := by
    simp [foo, r, Extension.toKaehler]
    conv_rhs => erw [mapBaseChange_tmul]
    have : (Extension.CotangentSpace.map hom.toExtensionHom)
        (1 ⊗ₜ[P'.toExtension.Ring] (D R P'.toExtension.Ring) (X (Sum.inr k))) =
        1 ⊗ₜ[P.toExtension.Ring] (D R P.toExtension.Ring)
          (hom.toExtensionHom.toAlgHom (X (Sum.inr k))) := by
      apply Algebra.Extension.CotangentSpace.map_tmul
    erw [this]
    conv_lhs => erw [mapBaseChange_tmul]
    simp only [Generators.toExtension_Ring, Generators.toExtension_commRing, map_D,
      Generators.algebraMap_apply, one_smul, aeval_X]
    congr
    erw [Algebra.Extension.Hom.toAlgHom_apply]
    simp
  rw [← this]
  simp only [foo, r]
  rw [Algebra.Extension.CotangentSpace.map_tmul]
  simp
  erw [Algebra.Extension.Hom.toAlgHom_apply]
  simp only [Extension.toKaehler, Generators.toExtension_Ring, Generators.toExtension_commRing,
    Generators.toExtension_algebra₂, Generators.Hom.toExtensionHom_toRingHom,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Generators.Hom.toAlgHom_X, Sum.elim_inr, t, g]
  erw [KaehlerDifferential.mapBaseChange_tmul]
  simp only [map_D, Generators.algebraMap_apply, Generators.aeval_val_σ, one_smul]
  rw [hf]

/-- Given generators `R[xᵢ] → S` and an injective map `ι → P.vars`, this is the
composition `I/I² → ⊕ S dxᵢ → ⊕ S dxᵢ` where the second `i` only runs over `ι`. -/
def cotangentRestrict (P : Generators R S) {ι : Type*} (a : ι → P.vars)
    (ha : Function.Injective a) :
    P.toExtension.Cotangent →ₗ[S] (ι →₀ S) :=
  Finsupp.lcomapDomain a ha ∘ₗ P.cotangentSpaceBasis.repr.toLinearMap ∘ₗ
    P.toExtension.cotangentComplex

/-- If `H¹(L_{S/R}) = 0` and `R[xᵢ] → S` are generators indexed by `ι ⊕ κ` such that the images
of `dxₖ` for `k : κ` form a basis of `Ω[S⁄R]`, then the restriction of
`I/I² → ⊕ S dxᵢ` to the direct sum indexed by `i : ι` is an isomorphism. -/
lemma cotangentRestrict_bijective_of_basis_kaehlerDifferential [Subsingleton (H1Cotangent R S)]
    (P : Generators R S) {ι κ : Type*} (u : ι → P.vars) (hu : Function.Injective u)
    (v : κ → P.vars) (hv : Function.Injective v) (huv : IsCompl (Set.range v) (Set.range u))
    (b : Basis κ S (Ω[S⁄R])) (hb : ∀ k, b k = P.toExtension.toKaehler (1 ⊗ₜ D _ _ (X (v k)))) :
    Function.Bijective (cotangentRestrict P u hu) := by
  have hsub : Subsingleton P.toExtension.H1Cotangent := P.equivH1Cotangent.subsingleton
  let bC : Basis P.vars S P.toExtension.CotangentSpace := P.cotangentSpaceBasis
  have heq : P.toExtension.toKaehler ∘ P.cotangentSpaceBasis ∘ v = b := by
    ext i
    simp [hb, P.cotangentSpaceBasis_apply]
  constructor
  · refine injective_restrict P.toExtension.cotangentComplex P.toExtension.toKaehler
      P.cotangentSpaceBasis v hv u hu ?_ P.toExtension.exact_cotangentComplex_toKaehler ?_ huv
    · exact (Extension.subsingleton_h1Cotangent P.toExtension).mp hsub
    · simp_rw [funext_iff, Function.comp_apply] at heq
      simp_rw [heq]
      exact b.linearIndependent
  · refine surjective_restrict P.toExtension.cotangentComplex P.toExtension.toKaehler
      P.cotangentSpaceBasis v hv u hu P.toExtension.exact_cotangentComplex_toKaehler ?_ huv
    · rw [heq]
      exact b.span_eq

lemma Presentation.relation_mem_ker {P : Presentation R S} (r : P.rels) :
    P.relation r ∈ P.ker := by
  rw [← P.span_range_relation_eq_ker]
  apply Ideal.subset_span
  use r

def Generators.append (P : Generators R S) (g : MvPolynomial P.vars R) :
    Generators R S where
  vars := P.vars ⊕ Unit
  val := Sum.elim P.val (fun _ ↦ aeval P.val g)
  σ' := sorry
  aeval_val_σ' := sorry

lemma exists_presentation_of_free [Algebra.FinitePresentation R S]
    (P : Generators R S) {σ : Type*} (b : Basis σ S P.toExtension.Cotangent)
    (u : σ → P.vars) (hu : Function.Injective u) :
    ∃ (val : P.vars ⊕ Unit → S)
      (relation : σ ⊕ Unit → MvPolynomial (P.vars ⊕ Unit) R)
      (hspan : Ideal.span (Set.range relation) = RingHom.ker (aeval val))
      (hcomp : val ∘ Sum.inl = P.val)
      (b : Basis (σ ⊕ Unit) S (Generators.ofSurjective val <| by
          apply Function.Surjective.of_comp (g := MvPolynomial.rename Sum.inl)
          have : ⇑(aeval val) ∘ ⇑(rename Sum.inl) = ⇑(aeval (R := R) (val ∘ Sum.inl)) := by
            ext
            simp [aeval_rename]
          rw [this, hcomp]
          exact P.algebraMap_surjective).toExtension.Cotangent),
      ∀ r, b r = Extension.Cotangent.mk ⟨relation r, sorry⟩ :=
  sorry

lemma PreSubmersivePresentation.jacobian_isUnit_of
    (P : PreSubmersivePresentation R S)
    (b : Basis P.rels S P.toExtension.Cotangent)
    (hb : ∀ r, b r = Extension.Cotangent.mk ⟨P.relation r, P.relation_mem_ker r⟩)
    (h : Function.Bijective (cotangentRestrict P.toGenerators P.map P.map_inj)) :
    IsUnit P.jacobian :=
  sorry

theorem isStandardSmooth_of [Algebra.FinitePresentation R S]
    [Subsingleton (H1Cotangent R S)]
    {I : Type v} (b : Basis I S (Ω[S⁄R])) (hb : Set.range b ⊆ Set.range (D R S)) :
    IsStandardSmooth.{v, v} R S := by
  obtain ⟨P, hfin, κ, v, b, hv, hb⟩ := exists_generators_of_basis_kaehlerDifferential b hb
  let σ : Type v := ((Set.range v)ᶜ : Set P.vars)
  let u : σ → P.vars := Subtype.val
  have huv : IsCompl (Set.range v) (Set.range u) := by
    simp only [u]
    rw [Subtype.range_coe]
    exact isCompl_compl
  have := cotangentRestrict_bijective_of_basis_kaehlerDifferential P u Subtype.val_injective v hv
    huv b hb
  let e := LinearEquiv.ofBijective (cotangentRestrict P u Subtype.val_injective) this
  let bcot' : Basis σ S P.toExtension.Cotangent := Basis.ofRepr e
  obtain ⟨val, relation, hspan, hcomp, bcot, hbcot⟩ :=
    exists_presentation_of_free P bcot' u Subtype.val_injective
  have hsurj : Function.Surjective ⇑(aeval (R := R) val) := by
    apply Function.Surjective.of_comp (g := MvPolynomial.rename Sum.inl)
    have : ⇑(aeval val) ∘ ⇑(rename Sum.inl) = ⇑(aeval (R := R) (val ∘ Sum.inl)) := by
      ext
      simp [aeval_rename]
    rw [this, hcomp]
    exact P.algebraMap_surjective
  let P' : PreSubmersivePresentation R S :=
    { toGenerators := (Generators.ofSurjective val hsurj)
      rels := σ ⊕ Unit
      relation := relation
      span_range_relation_eq_ker := hspan
      map := Sum.map u _root_.id
      map_inj := Sum.map_injective.mpr ⟨Subtype.val_injective, fun _ _ h ↦ h⟩
      relations_finite := inferInstance }
  let hom : P.Hom P'.toGenerators :=
    { val := X ∘ Sum.inl
      aeval_val := fun k ↦ by simp [← hcomp] }
  have heq (k : κ) :
        (1 ⊗ₜ[P'.toExtension.Ring] (D R P'.toExtension.Ring) (X ((Sum.inl ∘ v) k))) =
        Extension.CotangentSpace.map hom.toExtensionHom
          (1 ⊗ₜ[P.toExtension.Ring] (D R P.toExtension.Ring) (X (v k))) := by
    rw [Extension.CotangentSpace.map_tmul, Extension.Hom.toAlgHom_apply]
    rw [Generators.Hom.toExtensionHom_toRingHom]
    simp
  have : P'.IsFinite := ⟨inferInstanceAs <| Finite (P.vars ⊕ Unit), inferInstance⟩
  have hcompl : IsCompl (Set.range (Sum.inl ∘ v)) (Set.range P'.map) := by
    simp only [u, Set.range_comp, Set.isCompl_iff]
    simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, Sum.exists, Sum.map_inl,
      Sum.map_inr, id_eq, not_or, not_exists, Sum.forall, Sum.inl.injEq, reduceCtorEq,
      not_false_eq_true, implies_true, and_true, exists_false, not_true_eq_false, forall_const,
      and_false]
    simp_rw [← Set.mem_range, ← not_exists, ← Set.mem_range]
    rwa [← Set.isCompl_iff]
  have hbij : Function.Bijective (cotangentRestrict P'.toGenerators P'.map P'.map_inj) := by
    apply cotangentRestrict_bijective_of_basis_kaehlerDifferential P'.toGenerators P'.map
      P'.map_inj (Sum.inl ∘ v) (Sum.inl_injective.comp hv) hcompl b
    intro k
    rw [heq, Extension.toKaehler_map, hb]
  use P'
  exact P'.jacobian_isUnit_of bcot hbcot hbij

end Algebra
