/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Smooth.Kaehler
import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Standard smooth algebras
-/

universe t₂ t₁ u v

section

lemma Set.isCompl_iff {α : Type*} (s t : Set α) :
    IsCompl s t ↔ ∀ a, a ∈ s ↔ a ∉ t := by
  simp_rw [← eq_compl_iff_isCompl, Set.ext_iff, mem_compl_iff]

end

lemma LinearMap.isUnit_iff_isUnit_toMatrix {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (f : M →ₗ[R] M)
    {m : Type*} [Fintype m] [DecidableEq m] (b : Basis m R M) :
    IsUnit f ↔ IsUnit (f.toMatrix b b) := by
  simp_rw [isUnit_iff_exists]
  constructor
  · intro ⟨g, hl, hr⟩
    use g.toMatrix b b
    simp [← LinearMap.toMatrix_mul, hl, hr]
  · intro ⟨A, hl, hr⟩
    use Matrix.toLin b b A
    rw [← Matrix.toLin_toMatrix b b f, LinearMap.mul_eq_comp, LinearMap.mul_eq_comp,
      ← Matrix.toLin_mul, ← Matrix.toLin_mul]
    simp [hl, hr, LinearMap.one_eq_id]

lemma LinearMap.isUnit_iff_isUnit_det {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Free R M]
    (f : M →ₗ[R] M) :
    IsUnit f ↔ IsUnit f.det := by
  let b := Module.Free.chooseBasis R M
  rw [LinearMap.isUnit_iff_isUnit_toMatrix f b, ← LinearMap.det_toMatrix b,
    Matrix.isUnit_iff_isUnit_det ((toMatrix b b) f)]

lemma LinearMap.bijective_of_linearIndependent_and_span_eq_top {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (f : M →ₗ[R] N) {ι : Type*}
    (b : Basis ι R M) (hli : LinearIndependent R (f ∘ b))
    (hsp : Submodule.span R (Set.range <| f ∘ b) = ⊤) :
    Function.Bijective f := by
  let b' : Basis ι R N := Basis.mk hli (by rw [hsp])
  let e : M ≃ₗ[R] N := LinearEquiv.ofLinear f (b'.constr R (fun i ↦ b i))
    (by
      refine b'.ext fun i ↦ ?_
      simp only [coe_comp, Function.comp_apply, Basis.constr_basis, id_coe, id_eq]
      simp [b'])
    (by
      refine b.ext fun i ↦ ?_
      have : f (b i) = b' i := by simp [b']
      simp [coe_comp, Function.comp_apply, id_coe, id_eq, this])
  exact e.bijective

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
    rw [map_add]
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

section

open MvPolynomial

/-- Given generators `R[xᵢ] → S` and an injective map `ι → P.vars`, this is the
composition `I/I² → ⊕ S dxᵢ → ⊕ S dxᵢ` where the second `i` only runs over `ι`. -/
def cotangentRestrict (P : Generators R S) {ι : Type*} (a : ι → P.vars)
    (ha : Function.Injective a) :
    P.toExtension.Cotangent →ₗ[S] (ι →₀ S) :=
  Finsupp.lcomapDomain a ha ∘ₗ P.cotangentSpaceBasis.repr.toLinearMap ∘ₗ
    P.toExtension.cotangentComplex

@[simp]
lemma cotangentRestrict_mk (P : Generators R S) {ι : Type*} (a : ι → P.vars)
    (ha : Function.Injective a) (x : P.ker) :
    cotangentRestrict P a ha (Extension.Cotangent.mk x) =
      (fun j ↦ (aeval P.val) <| pderiv (a j) x.val) := by
  ext j
  simp only [cotangentRestrict, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Finsupp.lcomapDomain_apply, Finsupp.comapDomain_apply]
  rw [Extension.cotangentComplex_mk]
  dsimp
  rw [P.cotangentSpaceBasis_repr_tmul, one_mul]

lemma PreSubmersivePresentation.jacobian_eq_det_aevalDifferential
    (P : PreSubmersivePresentation R S) :
    P.jacobian = LinearMap.det P.aevalDifferential := by
  classical
  have : Fintype P.rels := Fintype.ofFinite P.rels
  rw [← LinearMap.det_toMatrix', P.aevalDifferential_toMatrix'_eq_mapMatrix_jacobiMatrix]
  simp [jacobian_eq_jacobiMatrix_det, RingHom.map_det, RingHom.algebraMap_toAlgebra]

lemma PreSubmersivePresentation.isUnit_jacobian_iff_bijective_aevalDifferential
    (P : PreSubmersivePresentation R S) :
    IsUnit P.jacobian ↔ Function.Bijective P.aevalDifferential := by
  rw [P.jacobian_eq_det_aevalDifferential]
  rw [← LinearMap.isUnit_iff_isUnit_det]
  exact Module.End_isUnit_iff P.aevalDifferential

lemma PreSubmersivePresentation.isUnit_jacobian_of_linearIndependent_and_span_eq_top
    (P : PreSubmersivePresentation R S)
    (hli : LinearIndependent S (fun j i : P.rels ↦ aeval P.val <| pderiv (P.map i) (P.relation j)))
    (hsp : Submodule.span S
      (Set.range <| (fun j i : P.rels ↦ aeval P.val <| pderiv (P.map i) (P.relation j))) = ⊤) :
    IsUnit P.jacobian := by
  classical
  rw [PreSubmersivePresentation.isUnit_jacobian_iff_bijective_aevalDifferential]
  apply LinearMap.bijective_of_linearIndependent_and_span_eq_top _ (Pi.basisFun S P.rels)
  · convert hli
    simp
  · convert hsp
    simp

lemma PreSubmersivePresentation.jacobian_isUnit_of
    (P : PreSubmersivePresentation R S)
    (b : Basis P.rels S P.toExtension.Cotangent)
    (hb : ∀ r, b r = Extension.Cotangent.mk ⟨P.relation r, P.relation_mem_ker r⟩)
    (h : Function.Bijective (cotangentRestrict P.toGenerators P.map P.map_inj)) :
    IsUnit P.jacobian := by
  have : (fun j i ↦ (aeval P.val) ((pderiv (P.map i)) (P.relation j))) =
      Finsupp.linearEquivFunOnFinite S S _ ∘
        cotangentRestrict P.toGenerators P.map P.map_inj ∘ ⇑b := by
    ext i j
    simp only [Function.comp_apply, hb, Finsupp.linearEquivFunOnFinite_apply]
    rw [cotangentRestrict_mk]
  apply P.isUnit_jacobian_of_linearIndependent_and_span_eq_top
  · rw [this]
    exact (b.linearIndependent.map' _ (LinearMap.ker_eq_bot_of_injective h.injective)).map' _
      (Finsupp.linearEquivFunOnFinite S S P.rels).ker
  · rw [this]
    rw [Set.range_comp, Set.range_comp, ← Submodule.map_span, ← Submodule.map_span]
    rw [b.span_eq, Submodule.map_top]
    rw [LinearMap.range_eq_top_of_surjective _ h.surjective,
      Submodule.map_top, LinearEquivClass.range]

end

open KaehlerDifferential MvPolynomial

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

lemma aeval_mk_X_eq_mk {σ : Type*} (I : Ideal (MvPolynomial σ R)) :
    aeval (fun i ↦ Ideal.Quotient.mk I (X i)) = Ideal.Quotient.mkₐ _ I := by
  rw [aeval_unique (Ideal.Quotient.mkₐ _ I)]
  rfl

def Generators.naive {σ : Type t₁} {ι : Type t₂} (v : ι → MvPolynomial σ R) :
    Generators.{t₁} R (MvPolynomial σ R ⧸ (Ideal.span <| Set.range v)) where
  vars := σ
  val i := Ideal.Quotient.mk _ (X i)
  σ' := Quotient.out
  aeval_val_σ' x := by
    rw [aeval_mk_X_eq_mk]
    apply Quotient.out_eq

lemma Generators.naive_val {σ ι : Type*} (v : ι → MvPolynomial σ R) (i : σ) :
    (Generators.naive v).val i = Ideal.Quotient.mk _ (X i) :=
  rfl

def Presentation.naive {σ : Type t₁} {ι : Type t₂} (v : ι → MvPolynomial σ R) :
    Presentation.{t₂, t₁} R (MvPolynomial σ R ⧸ (Ideal.span <| Set.range v)) where
  __ := Generators.naive v
  rels := ι
  relation := v
  span_range_relation_eq_ker := by
    show Ideal.span _ = RingHom.ker (aeval <| fun i ↦ Ideal.Quotient.mk _ (X i)).toRingHom
    simp only [AlgHom.toRingHom_eq_coe, aeval_mk_X_eq_mk, Ideal.Quotient.mkₐ_ker]

open _root_.TensorProduct

open Pointwise in
lemma _root_.IsLocalization.Away.of_sub_one_mem_ker {R S T : Type*}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Algebra S T] [IsScalarTower R S T]
    (h₁ : Function.Surjective (algebraMap S T))
    (h₂ : Function.Surjective (algebraMap R S))
    (r : R) (hr : r - 1 ∈ RingHom.ker (algebraMap R T))
    {n : ℕ} (hn : r ^ n • RingHom.ker (algebraMap R T) ≤ RingHom.ker (algebraMap R S)) :
    IsLocalization.Away (algebraMap R S r) T := by
  apply IsLocalization.Away.mk
  · rw [← IsScalarTower.algebraMap_apply]
    have : algebraMap R T r = algebraMap R T 1 := by rwa [← RingHom.sub_mem_ker_iff]
    simp [this]
  · intro t
    use 0
    obtain ⟨s, rfl⟩ := h₁ t
    simp
  · intro x y h
    obtain ⟨a, rfl⟩ := h₂ x
    obtain ⟨b, rfl⟩ := h₂ y
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h
    use n
    rw [← map_pow, ← map_mul, ← map_mul, ← RingHom.sub_mem_ker_iff, ← mul_sub]
    apply hn
    use a - b
    simp [h]

open Pointwise in
lemma _root_.IsLocalization.Away.quotient_of {R : Type*}
    [CommRing R] {I J : Ideal R} [Algebra (R ⧸ I) (R ⧸ J)] [IsScalarTower R (R ⧸ I) (R ⧸ J)]
    (r : R) (hr : r - 1 ∈ J) {n : ℕ} (hn : r ^ n • J ≤ I) :
    IsLocalization.Away (Ideal.Quotient.mk I r) (R ⧸ J) := by
  have : (Ideal.Quotient.mk I) = algebraMap R (R ⧸ I) := rfl
  apply IsLocalization.Away.mk
  · rw [this]
    rw [← IsScalarTower.algebraMap_apply]
    have : Ideal.Quotient.mk J r = Ideal.Quotient.mk J 1 := by
      rwa [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    simp [this]
  · intro s
    use 0
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective s
    use x
    rw [this, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    simp
  · intro a b h
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
    use n
    rw [this, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h
    simp at h
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem] at h
    rw [← map_pow, ← map_mul, ← map_mul]
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← mul_sub]
    apply hn
    use x - y
    simp [h]

lemma _root_.Algebra.Extension.Cotangent.mk_eq_mk_iff_sub_mem {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] {P : Algebra.Extension R S}
    (x y : P.ker) :
    Algebra.Extension.Cotangent.mk x = Algebra.Extension.Cotangent.mk y ↔
      x.val - y.val ∈ P.ker ^ 2 := by
  simp [Extension.Cotangent.ext_iff, Ideal.toCotangent_eq]

lemma exists_presentation_of_free [Algebra.FinitePresentation R S]
    (P : Generators.{t₁} R S) [Finite P.vars] {σ : Type t₂} (b : Basis σ S P.toExtension.Cotangent)
    (u : σ → P.vars) (hu : Function.Injective u) :
    ∃ (P' : Presentation.{t₂, t₁} R S)
      (e₁ : Unit ⊕ P.vars ≃ P'.vars)
      (e₂ : Unit ⊕ σ ≃ P'.rels)
      (b : Basis P'.rels S P'.toExtension.Cotangent),
      P'.val ∘ e₁ ∘ Sum.inr = P.val ∧
      ∀ r, b r = Extension.Cotangent.mk ⟨P'.relation r, P'.relation_mem_ker r⟩ := by
  choose f hf using Extension.Cotangent.mk_surjective (P := P.toExtension)
  choose s hs using P.algebraMap_surjective
  have hf' : Extension.Cotangent.mk (P := P.toExtension) ∘ f ∘ b = b := by
    ext i : 1
    simp only [Function.comp_apply, hf (b i)]
  let v (i : σ) : P.ker := f (b i)
  have hv (i : σ) : Extension.Cotangent.mk (v i) = b i := hf (b i)
  let J : Ideal (MvPolynomial P.vars R) := Ideal.span (Set.range <| Subtype.val ∘ v)
  have hJle : P.ker ≤ P.ker := le_rfl
  have hJ_fg : P.ker.FG := by
    apply FinitePresentation.ker_fG_of_surjective
    apply P.algebraMap_surjective
  have hJ : P.ker ≤ J ⊔ P.ker • P.ker := by
    intro x hx
    have : Extension.Cotangent.mk (P := P.toExtension) ⟨x, hx⟩ ∈
        Submodule.span S (Set.range b) := by
      rw [b.span_eq]
      trivial
    rw [Finsupp.mem_span_range_iff_exists_finsupp] at this
    obtain ⟨c, hc⟩ := this
    have (a : S) (i : σ) : a • b i = Extension.Cotangent.mk (P.σ a • v i) := by
      ext
      simp only [Extension.Cotangent.val_smul, Generators.toExtension_σ, map_smul]
      rw [hv i, Extension.Cotangent.val_smul']
    simp_rw [this] at hc
    rw [← map_finsupp_sum, Eq.comm] at hc
    rw [Algebra.Extension.Cotangent.mk_eq_mk_iff_sub_mem] at hc
    simp only [Finsupp.sum, AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, smul_eq_mul] at hc
    have : x = ∑ x ∈ c.support, P.σ (c x) * v x + (x - ∑ x ∈ c.support, P.σ (c x) * ↑(v x)) := by
      simp
    rw [this]
    apply Submodule.add_mem_sup
    · apply J.sum_mem
      rintro i -
      apply Ideal.mul_mem_left
      apply Ideal.subset_span
      use i
      simp
    · simpa [← pow_two]
  let T := MvPolynomial P.vars R ⧸ J
  have hJ_eq_ker : J = RingHom.ker (algebraMap (MvPolynomial P.vars R) T) := by simp [T]
  let Q₁ : Presentation.{t₂, t₁} R T := Presentation.naive (Subtype.val ∘ v)
  obtain ⟨g, hgmem, hg⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup hJ_fg hJle hJ
  let gbar : T := Ideal.Quotient.mk _ g
  let hom : T →ₐ[R] S := Ideal.Quotient.liftₐ J (aeval P.val) <| by
    intro a ha
    induction' ha using Submodule.span_induction with _ hx _ _ _ _ hx hy _ _ _ h
    · obtain ⟨i, rfl⟩ := hx
      exact (v i).property
    · simp
    · simp [hx, hy]
    · simp [h]
  letI : Algebra T S := hom.toAlgebra
  haveI : IsScalarTower R T S := IsScalarTower.of_algHom hom
  have (x : MvPolynomial P.vars R) (y : T) :
      x • y = algebraMap (MvPolynomial P.vars R) T x * y :=
    rfl
  haveI : IsScalarTower (MvPolynomial P.vars R) T S := by
    constructor
    intro x y z
    rw [Algebra.smul_def]
    rw [Algebra.smul_def]
    rw [Algebra.smul_def]
    rw [this]
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨z, rfl⟩ := P.algebraMap_surjective z
    simp only [map_mul, Generators.algebraMap_apply]
    simp only [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, id.map_eq_id,
      RingHomCompTriple.comp_eq, RingHom.coe_coe, hom]
    rw [Ideal.Quotient.liftₐ_apply]
    rw [Ideal.Quotient.liftₐ_apply]
    simp only [RingHom.coe_comp, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      Function.comp_apply, Ideal.Quotient.lift_mk, RingHom.coe_coe, ← mul_assoc]
  have : IsLocalization.Away gbar S :=
    IsLocalization.Away.of_sub_one_mem_ker
      (by
        apply Function.Surjective.of_comp (g := algebraMap (MvPolynomial P.vars R) T)
        have : ⇑(algebraMap T S) ∘ ⇑(algebraMap (MvPolynomial P.vars R) T) = algebraMap _ S := by
          ext
          simp [← IsScalarTower.algebraMap_apply]
        rw [this]
        apply P.algebraMap_surjective)
      (by simp [T, Ideal.Quotient.mk_surjective])
      g hgmem (n := 1)
      (by simpa [← hJ_eq_ker])
  let equiv1 : S ⊗[T] Q₁.toExtension.Cotangent ≃ₗ[S] P.toExtension.Cotangent := sorry
  let bQ₁ : Basis σ S (S ⊗[T] Q₁.toExtension.Cotangent) := b.map equiv1.symm
  let Q₂ : SubmersivePresentation.{0} T S := SubmersivePresentation.localizationAway S gbar
  let bQ₂ : Basis Unit S Q₂.toExtension.Cotangent := Q₂.basisCotangent
  let P' : Presentation R S := Q₂.toPresentation.comp Q₁
  let b' := Basis.prod bQ₂ bQ₁
  let equiv2 :
      (Q₂.toExtension.Cotangent × S ⊗[T] Q₁.toExtension.Cotangent) ≃ₗ[S] P'.toExtension.Cotangent :=
    sorry
  --let b' : Basis (Unit ⊕ σ) S P'.toExtension.Cotangent := (Basis.prod bQ₂ bQ₁).map equiv2
  use P', Equiv.refl _, Equiv.refl _
  refine ⟨(Basis.prod bQ₂ bQ₁).map equiv2, ?_, ?_⟩
  · ext i
    simp only [Function.comp_apply, P']
    erw [Generators.comp_val]
    simp only [Sum.elim_inr, Function.comp_apply, Q₁]
    erw [Equiv.refl_apply]
    simp only [Sum.elim_inr, Function.comp_apply]
    erw [Generators.naive_val]
    rw [RingHom.algebraMap_toAlgebra]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, J, hom]
    rw [Ideal.Quotient.liftₐ_apply]
    simp
  · rintro (r|r)
    · simp
      sorry
    · sorry

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
  obtain ⟨Q, e₁, e₂, bcot, hcomp, hbcot⟩ :=
    exists_presentation_of_free P bcot' u Subtype.val_injective
  have : Finite Q.rels := Finite.of_equiv _ e₂
  let P' : PreSubmersivePresentation R S :=
    { toPresentation := Q
      map := e₁ ∘ Sum.map _root_.id u ∘ e₂.symm
      map_inj := e₁.injective.comp <|
        (Sum.map_injective.mpr ⟨fun _ _ h ↦ h, Subtype.val_injective⟩).comp e₂.symm.injective
      relations_finite := inferInstance }
  let hom : P.Hom P'.toGenerators :=
    { val := X ∘ e₁ ∘ Sum.inr
      aeval_val := fun k ↦ by simp [← hcomp] }
  have heq (k : κ) :
        (1 ⊗ₜ[P'.toExtension.Ring] (D R P'.toExtension.Ring) (X ((e₁ ∘ Sum.inr ∘ v) k))) =
        Extension.CotangentSpace.map hom.toExtensionHom
          (1 ⊗ₜ[P.toExtension.Ring] (D R P.toExtension.Ring) (X (v k))) := by
    rw [Extension.CotangentSpace.map_tmul, Extension.Hom.toAlgHom_apply]
    rw [Generators.Hom.toExtensionHom_toRingHom]
    simp
  have : Finite P'.vars := Finite.of_equiv _ e₁
  have : P'.IsFinite := ⟨inferInstance, inferInstance⟩
  have hcompl : IsCompl (Set.range (e₁ ∘ Sum.inr ∘ v)) (Set.range P'.map) := by
    simp only [u, Set.range_comp]
    rw [e₁.image_eq_preimage, e₁.image_eq_preimage]
    apply IsCompl.preimage
    simp only [Set.isCompl_iff]
    simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, Equiv.range_eq_univ,
      Set.image_univ, Sum.exists, Sum.map_inl, id_eq, Sum.map_inr, not_or, not_exists, Sum.forall,
      reduceCtorEq, exists_false, not_true_eq_false, forall_const, not_false_eq_true, implies_true,
      and_true, Sum.inr.injEq, true_and]
    simp_rw [← Set.mem_range, ← not_exists, ← Set.mem_range]
    rwa [← Set.isCompl_iff]
  have hbij : Function.Bijective (cotangentRestrict P'.toGenerators P'.map P'.map_inj) := by
    apply cotangentRestrict_bijective_of_basis_kaehlerDifferential P'.toGenerators P'.map
      P'.map_inj (e₁ ∘ Sum.inr ∘ v) (e₁.injective.comp <| Sum.inr_injective.comp hv) hcompl b
    intro k
    rw [heq, Extension.toKaehler_map, hb]
  use P'
  exact P'.jacobian_isUnit_of bcot hbcot hbij

end Algebra
