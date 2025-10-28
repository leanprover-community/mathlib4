/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Extension.Cotangent.LocalizationAway

/-!

-/

open Pointwise MvPolynomial TensorProduct

namespace Algebra.Generators

variable {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S] {σ : Type*}

noncomputable section

variable {ι : Type*} (P : Generators R S ι) {σ : Type*}
  (b : Module.Basis σ S P.toExtension.Cotangent)

/-- An auxiliary structure containing the data to construct the presentation in
`Generators.exists_presentation_of_free`. -/
structure Aux where
  /-- A section of the projection `I → I/I²`. -/
  f : P.toExtension.Cotangent → P.toExtension.ker
  hf : ∀ (b : P.toExtension.Cotangent), Extension.Cotangent.mk (f b) = b
  /-- An element `g` that becomes invertible in `S = R[X₁, ..., Xₙ] / I`. -/
  g : P.Ring
  hgmem : g - 1 ∈ P.ker
  hg : g • P.ker ≤ Ideal.span (Set.range <| Subtype.val ∘ f ∘ b)

namespace Aux

variable {P} {b}
variable (D : Aux P b)

/-- `T = R[X₁, ..., Xₙ] / (b₁, ..., bᵣ)` where the `bᵢ` are lifts of the basis elements
of `I/I²` in `I`. -/
abbrev T :=
  MvPolynomial ι R ⧸ (Ideal.span <| Set.range <| Subtype.val ∘ D.f ∘ b)

/-- The map `R[X₁, ..., Xₙ] → S` factors via `T`, because the `bᵢ` are in `I`. -/
def hom : D.T →ₐ[R] S := Ideal.Quotient.liftₐ _ (aeval P.val) <| by
  simp_rw [← RingHom.mem_ker, ← SetLike.le_def, Ideal.span_le, Set.range_subset_iff]
  intro i
  simpa only [Generators.toExtension_Ring, Generators.toExtension_commRing, Function.comp_apply,
    SetLike.mem_coe, RingHom.mem_ker, ← P.algebraMap_apply] using (D.f _).property

instance : Algebra D.T S := D.hom.toAlgebra
instance [Nontrivial S] : Nontrivial D.T := RingHom.domain_nontrivial (algebraMap D.T S)
instance : IsScalarTower P.Ring D.T S := by
  refine ⟨fun x y z ↦ ?_⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨z, rfl⟩ := P.algebraMap_surjective z
  simp only [Algebra.smul_def, map_mul, Generators.algebraMap_apply, ← mul_assoc]
  rfl

/-- The image of `g : R[X₁, ..., Xₙ]` in `T`. -/
abbrev gbar : D.T := D.g

/-- `S` is the localization of `T` away from `S`. -/
instance : IsLocalization.Away D.gbar S := by
  refine .of_sub_one_mem_ker (n := 1) ?_ ?_ _ D.hgmem (by simpa using D.hg)
  · refine .of_comp (g := algebraMap P.Ring D.T) ?_
    convert P.algebraMap_surjective
    ext x
    exact (IsScalarTower.algebraMap_apply _ D.T S x).symm
  · simp [T, Ideal.Quotient.mk_surjective]

open Classical in
/-- The "naive" presentation of `T = R[X₁, ..., Xₙ] / (b₁, ..., bᵣ)` over `R`.
We make sure the section `T → R[X₁, ..., Xₙ]` maps `-1` to `-1` and `0` to `0`. -/
def presLeft : Presentation R D.T ι σ :=
  .naive (fun x ↦ if x = 0 then 0 else if x = -1 then -1 else
      Function.surjInv Ideal.Quotient.mk_surjective x) fun x ↦ by
    dsimp only; split_ifs
    · next h => subst h; rfl
    · next h => subst h; rfl
    · simp [Function.surjInv_eq]

/-- The `i`-th generator of the kernel `(b₁, ..., bᵣ)` of the naive presentation of `T`. -/
def kerGen (i : σ) : D.presLeft.toExtension.ker :=
  ⟨(D.f (b i)).val, Presentation.mem_ker_naive _ _ i⟩

/-- The identity on `R[X₁, ..., Xₙ]` as a map of presentations of `T` to `S`. -/
def fhom : D.presLeft.Hom P where
  val i := X i
  aeval_val i := by simp [RingHom.algebraMap_toAlgebra, presLeft, hom, T]

@[simp]
lemma toAlgHom_fhom : D.fhom.toAlgHom = AlgHom.id R P.Ring := by
  ext : 1
  simp [fhom]

lemma ker_presLeft_le : D.presLeft.ker ≤ P.ker := by
  intro x hx
  simpa only [toExtension_commRing, toExtension_Ring, RingHom.mem_ker,
    toExtension_algebra₂, algebraMap_apply, Ideal.Quotient.algebraMap_eq,
    map_zero] using (algebraMap D.T S).congr_arg hx

/-- The forward direction of the isomorphism `S ⊗[T] J/J² ≃ₗ[S] I/I²`. -/
def tensorCotangentHom : S ⊗[D.T] D.presLeft.toExtension.Cotangent →ₗ[S] P.toExtension.Cotangent :=
  LinearMap.liftBaseChange _ (Extension.Cotangent.map D.fhom.toExtensionHom)

lemma tensorCotangentHom_tmul (x : D.presLeft.toExtension.ker) :
    D.tensorCotangentHom (1 ⊗ₜ[D.T] Extension.Cotangent.mk x) =
      .mk ⟨x.val, D.ker_presLeft_le x.2⟩ := by
  simp only [tensorCotangentHom, LinearMap.liftBaseChange_tmul, one_smul, presLeft]
  rw [Extension.Cotangent.map_mk]
  congr 2
  rw [Generators.Hom.toExtensionHom_toAlgHom_apply, toAlgHom_fhom]
  simp only [AlgHom.coe_id, id_eq]

/-- The backwards direction of the isomorphism `S ⊗[T] J/J² ≃ₗ[S] I/I²`. -/
def tensorCotangentInv : P.toExtension.Cotangent →ₗ[S] S ⊗[D.T] D.presLeft.toExtension.Cotangent :=
  b.constr S fun i : σ ↦ 1 ⊗ₜ Extension.Cotangent.mk (D.kerGen i)

@[simp]
lemma tensorCotangentInv_apply (i : σ) :
    D.tensorCotangentInv (b i) = 1 ⊗ₜ Extension.Cotangent.mk (D.kerGen i) :=
  Module.Basis.constr_basis _ _ _ _

lemma hspan : Submodule.span D.T
    (Set.range <| fun i ↦ Extension.Cotangent.mk (D.kerGen i)) = ⊤ := by
  refine Extension.Cotangent.span_eq_top_of_span_eq_ker _ ?_
  dsimp only [presLeft, Presentation.naive_toGenerators]
  exact (Generators.ker_naive _ _).symm

/-- The linear isomorphism `S ⊗[T] J/J² ≃ₗ[S] I/I²`. -/
def tensorCotangentEquiv :
    S ⊗[D.T] D.presLeft.toExtension.Cotangent ≃ₗ[S] P.toExtension.Cotangent := by
  refine LinearEquiv.ofLinear D.tensorCotangentHom D.tensorCotangentInv ?_ ?_
  · refine b.ext fun i ↦ ?_
    simpa only [LinearMap.coe_comp, Function.comp_apply, tensorCotangentInv_apply,
      tensorCotangentHom_tmul] using D.hf (b i)
  · ext x
    have : x ∈ Submodule.span D.T (.range <| fun i ↦ Extension.Cotangent.mk (D.kerGen i)) :=
      D.hspan ▸ trivial
    simp only [AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_comp, curry_apply,
      LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply, LinearMap.id_coe,
      id_eq]
    induction this using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [tensorCotangentHom_tmul, kerGen, D.hf]
      simp
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy, tmul_add]
    | smul a x _ hx => simp [hx]

lemma tensorCotangentEquiv_symm_apply (i : σ) :
    D.tensorCotangentEquiv.symm (b i) = 1 ⊗ₜ Extension.Cotangent.mk (D.kerGen i) :=
  D.tensorCotangentInv_apply i

/-- The canonical presentation of `S` as the localization of `T` away from `g`. -/
def presRight : Presentation D.T S Unit Unit :=
  Presentation.localizationAway S D.gbar

/-- The presentation of `S` over `R` obtained from composing the naive presentation of
`T = R[X₁, ..., Xₙ]/(b₁, ..., bᵣ)` with the presentation of the localization away from `g`. -/
def pres : Presentation R S (Unit ⊕ ι) (Unit ⊕ σ) :=
  D.presRight.comp D.presLeft

lemma heq [Nontrivial S] :
    ((Generators.localizationAway _ D.gbar).ofComp D.presLeft.toGenerators).toAlgHom
        (D.pres.relation (Sum.inl ())) = C D.gbar * X () - 1 := by
  have : Nontrivial D.T := inferInstance
  dsimp only [T, Generators.toExtension_Ring, Generators.toExtension_commRing] at this
  classical
  rw [pres, presLeft, presRight, Presentation.relation_comp_localizationAway_inl]
  · exact Generators.toAlgHom_ofComp_localizationAway _ _
  · rw [Presentation.naive, Generators.naive_σ]
    simp
  · rw [Presentation.naive, Generators.naive_σ]
    simp

lemma heq' [Nontrivial S] :
    (Extension.Cotangent.map
      ((Generators.localizationAway S D.gbar).ofComp D.presLeft.toGenerators).toExtensionHom)
      (Extension.Cotangent.mk ⟨D.pres.relation (Sum.inl ()), D.pres.relation_mem_ker _⟩) =
      Generators.cMulXSubOneCotangent S D.gbar := by
  simp_rw [Extension.Cotangent.map_mk, Generators.Hom.toExtensionHom_toAlgHom_apply, D.heq]

/-- The cotangent space of the constructed presentation is isomorphic
to `(g X - 1)/(g X - 1)² × S ⊗[T] J/J²`. -/
def cotangentEquivProd [Nontrivial S] : D.pres.toExtension.Cotangent ≃ₗ[S]
    D.presRight.toExtension.Cotangent × S ⊗[D.T] D.presLeft.toExtension.Cotangent :=
  (D.presLeft.cotangentCompLocalizationAwayEquiv (T := S) D.gbar D.heq') ≪≫ₗ
    LinearEquiv.prodComm _ _ _

lemma cotangentEquivProd_symm_apply [Nontrivial S] (x : D.presRight.toExtension.Cotangent)
      (y : S ⊗[D.T] D.presLeft.toExtension.Cotangent) :
    D.cotangentEquivProd.symm (x, y) =
      (D.presLeft.cotangentCompLocalizationAwayEquiv (T := S) D.gbar D.heq').symm (y, x) :=
  rfl

/-- The basis of `S ⊗[T] J/J²` induced from the basis on `I/I²`. -/
def basisLeft : Module.Basis σ S (S ⊗[D.T] D.presLeft.toExtension.Cotangent) :=
  b.map D.tensorCotangentEquiv.symm

/-- The canonical basis on `(g X - 1)/(g X - 1)²`. -/
def basisRight : Module.Basis Unit S D.presRight.toExtension.Cotangent :=
  Generators.basisCotangentAway S D.gbar

/-- The basis on the cotangent space of the constructed presentation. -/
def basis [Nontrivial S] : Module.Basis (Unit ⊕ σ) S D.pres.toExtension.Cotangent :=
  (Module.Basis.prod D.basisRight D.basisLeft).map D.cotangentEquivProd.symm

lemma basis_inl [Nontrivial S] :
    D.basis (.inl ()) =
      D.cotangentEquivProd.symm (Generators.cMulXSubOneCotangent S D.gbar, 0) := by
  simpa [basis] using Generators.basisCotangentAway_apply _ _

lemma basis_inr [Nontrivial S] (i : σ) :
    D.basis (.inr i) = D.cotangentEquivProd.symm (0, D.basisLeft i) := by
  simp [basis]

lemma pres_val_comp_inr : D.pres.val ∘ Sum.inr = P.val := funext (aeval_X _)

/-- The constructed basis indeed is given by the images of the relations. -/
lemma basis_apply [Nontrivial S] (r : Unit ⊕ σ) :
    D.basis r = Extension.Cotangent.mk ⟨D.pres.relation r, D.pres.relation_mem_ker r⟩ := by
  obtain (r | r) := r
  · rw [basis_inl, cotangentEquivProd_symm_apply]
    exact cotangentCompLocalizationAwayEquiv_symm_inr _ _ _
  · rw [basis_inr, cotangentEquivProd_symm_apply, cotangentCompLocalizationAwayEquiv_symm_inl,
      basisLeft, Module.Basis.map_apply, tensorCotangentEquiv_symm_apply,
      LinearMap.liftBaseChange_tmul, one_smul, Extension.Cotangent.map_mk]
    rfl

end Aux

end

/-- Let `S` be a finitely presented `R`-algebra and suppose `P : R[X] → S` generates `S` with
kernel `I`. If `I/I²` is free, there exists an `R`-presentation `P'` of `S` extending `P` with
kernel `I'`, such that `I'/I'²` is free on the images of the relations of `P'`. -/
@[stacks 07CF]
lemma exists_presentation_of_free [Algebra.FinitePresentation R S]
    {α : Type*} (P : Generators R S α) [Finite α] {σ : Type*}
    (b : Module.Basis σ S P.toExtension.Cotangent) :
    ∃ (P' : Presentation R S (Unit ⊕ α) (Unit ⊕ σ))
      (b : Module.Basis (Unit ⊕ σ) S P'.toExtension.Cotangent),
      P'.val ∘ Sum.inr = P.val ∧
      ∀ r, b r = Extension.Cotangent.mk ⟨P'.relation r, P'.relation_mem_ker r⟩ := by
  cases subsingleton_or_nontrivial S
  · let P' : Presentation R S (Unit ⊕ α) (Unit ⊕ σ) :=
      { toGenerators := .ofSurjective (fun i : Unit ⊕ α ↦ 0) (Function.surjective_to_subsingleton _)
        relation _ := 1
        span_range_relation_eq_ker := by simpa using (RingHom.ker_eq_top_of_subsingleton _).symm }
    have : Subsingleton P'.toExtension.Cotangent := Module.subsingleton S _
    exact ⟨P', default, by subsingleton, by subsingleton⟩
  classical
  choose f hf using Extension.Cotangent.mk_surjective (P := P.toExtension)
  let v (i : σ) : P.ker := f (b i)
  let J : Ideal P.Ring := Ideal.span (Set.range <| Subtype.val ∘ v)
  have hJfg : P.ker.FG := by
    rw [P.ker_eq_ker_aeval_val]
    apply FinitePresentation.ker_fG_of_surjective
    convert P.algebraMap_surjective
    simp [P.algebraMap_eq]
  have hJ : J ≤ P.ker := by simp [J, Ideal.span_le, Set.range_subset_iff]
  suffices hJ : P.ker ≤ J ⊔ P.ker • P.ker by
    obtain ⟨g, hgmem, hg⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup hJfg le_rfl hJ
    let D : Aux P b := { f := f, hf := hf, g := g, hgmem := hgmem, hg := hg }
    exact ⟨D.pres, D.basis, D.pres_val_comp_inr, D.basis_apply⟩
  rw [← Submodule.comap_le_comap_iff_of_le_range (f := P.ker.subtype) (by simp)
    (by simp [Ideal.mul_le_left, hJ]), Submodule.comap_subtype_self,
    Submodule.comap_sup_of_injective P.ker.subtype_injective (by simpa using hJ)
    (by simp [Ideal.mul_le_left]),
    Submodule.comap_smul'' P.ker.subtype_injective (by simp)]
  simp only [Submodule.comap_subtype_self, J]
  rw [← Submodule.coe_subtype, Ideal.span, Submodule.comap_span_range_comp_of_injective
    P.ker.subtype_injective, ← Extension.Cotangent.ker_mk]
  dsimp
  simp only [← LinearMap.map_le_map_iff, Submodule.map_span, ← Set.range_comp,
    Function.comp_def, ← Submodule.restrictScalars_span P.Ring S P.algebraMap_surjective]
  refine le_trans le_top (top_le_iff.mpr ?_)
  rw [Submodule.restrictScalars_eq_top_iff]
  convert b.span_eq
  exact hf _

end Algebra.Generators
