/-
Copyright (c) 2020 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Generators

/-!
# Relation of smoothness and `Ω[S⁄R]`

## Main results

- `Algebra.FormallySmooth.iff_injective_and_projective`:
  Given a formally smooth algebra `P` over `R`, such that the algebra homomorphism `P → S` is
  surjective with kernel `I` (typically a presentation `R[X] → S`),
  then `S` is formally smooth iff `Ω[S/R]` is projective and `I/I² → B ⊗[A] Ω[A⁄R]` is injective.
-
  The first homology of the naive cotangent complex,
  defined as the kernel of `I/I² → S ⊗[R[S]] Ω[R[S]⁄R]` with `0 → I → R[S] → S → 0` being the
  standard presentation.
- `Algebra.FormallySmooth.iff_subsingleton_and_projective`:
  `S` is a formally smooth algebra over `R` iff `H¹(L[S/R]) = 0` and `Ω[S⁄R]` is projective.

## Future project

- Show that being smooth is local on stalks.
- Show that being formally smooth is Zariski-local (very hard).

-/

universe u

open TensorProduct KaehlerDifferential

open Function (Surjective)

variable {R P S : Type u} [CommRing R] [CommRing P] [CommRing S]
variable [Algebra R S] [Algebra R P] [Algebra P S] [IsScalarTower R P S]
variable (hf : Surjective (algebraMap P S)) (hf' : (RingHom.ker (algebraMap P S)) ^ 2 = ⊥)

section ofSection

-- Suppose we have a section (as alghom) of `P →ₐ[R] S`.
variable (g : S →ₐ[R] P) (hg : (IsScalarTower.toAlgHom R P S).comp g = AlgHom.id R S)

/--
Given a surjective algebra hom `f : P →ₐ[R] S` with square-zero kernel `I`,
and a section `g : S →ₐ[R] P` (as an algebra hom),
we get a `R`-derivation `P → I` via `x ↦ x - g (f x)`.
-/
@[simps]
def derivationOfSectionOfKerSqZero : Derivation R P (RingHom.ker (algebraMap P S)) where
  toFun x := ⟨x - g (algebraMap _ _ x), by
    simpa [RingHom.mem_ker, sub_eq_zero] using AlgHom.congr_fun hg.symm (algebraMap _ _ x)⟩
  map_add' x y := by ext; simp only [map_add, AddMemClass.mk_add_mk]; ring
  map_smul' x y := by
    ext
    simp only [Algebra.smul_def, _root_.map_mul, ← IsScalarTower.algebraMap_apply,
      AlgHom.commutes, RingHom.id_apply, Submodule.coe_smul_of_tower]
    ring
  map_one_eq_zero' := by ext; simp
  leibniz' a b := by
    have : (a - g (algebraMap _ _ a)) * (b - g (algebraMap _ _ b)) = 0 := by
      rw [← Ideal.mem_bot, ← hf', pow_two]
      apply Ideal.mul_mem_mul
      · simpa [RingHom.mem_ker, sub_eq_zero] using AlgHom.congr_fun hg.symm (algebraMap P S a)
      · simpa [RingHom.mem_ker, sub_eq_zero] using AlgHom.congr_fun hg.symm (algebraMap P S b)
    ext
    rw [← sub_eq_zero]
    conv_rhs => rw [← neg_zero, ← this]
    simp only [LinearMap.coe_mk, AddHom.coe_mk, map_mul, SetLike.mk_smul_mk, smul_eq_mul,
      AddMemClass.mk_add_mk]
    ring

include hf' hg
lemma isScalarTower_of_section_of_ker_sqZero :
    letI := g.toRingHom.toAlgebra; IsScalarTower P S (RingHom.ker (algebraMap P S)) := by
  letI := g.toRingHom.toAlgebra
  constructor
  intro p s m
  ext
  show g (p • s) * m = p * (g s * m)
  simp only [Algebra.smul_def, _root_.map_mul, mul_assoc, mul_left_comm _ (g s)]
  congr 1
  rw [← sub_eq_zero, ← Ideal.mem_bot, ← hf', pow_two, ← sub_mul]
  refine Ideal.mul_mem_mul ?_ m.2
  simpa [RingHom.mem_ker, sub_eq_zero] using AlgHom.congr_fun hg (algebraMap P S p)

/--
Given a surjective algebra hom `f : P →ₐ[R] S` with square-zero kernel `I`,
and a section `g : S →ₐ[R] P` (as algebra homs),
we get a retraction of the injection `I → S ⊗[P] Ω[P/R]`.
-/
noncomputable
def retractionOfSectionOfKerSqZero : S ⊗[P] Ω[P⁄R] →ₗ[P] RingHom.ker (algebraMap P S) :=
    letI := g.toRingHom.toAlgebra
    haveI := isScalarTower_of_section_of_ker_sqZero hf' g hg
    letI f := (derivationOfSectionOfKerSqZero hf' g hg).liftKaehlerDifferential
    (AlgebraTensorModule.lift ((LinearMap.ringLmapEquivSelf S S _).symm f)).restrictScalars P

@[simp]
lemma retractionOfSectionOfKerSqZero_tmul_D (s : S) (t : P) :
    retractionOfSectionOfKerSqZero hf' g hg (s ⊗ₜ .D _ _ t) =
      g s * t - g s * g (algebraMap _ _ t) := by
  letI := g.toRingHom.toAlgebra
  haveI := isScalarTower_of_section_of_ker_sqZero hf' g hg
  simpa [retractionOfSectionOfKerSqZero] using (mul_sub (g s) t (g (algebraMap P S t)))

lemma retractionOfSectionOfKerSqZero_comp_kerToTensor :
    (retractionOfSectionOfKerSqZero hf' g hg).comp (kerToTensor R P S) = LinearMap.id := by
  ext x; simp [RingHom.mem_ker.mp x.2]

end ofSection

section ofRetraction

variable (l : S ⊗[P] Ω[P⁄R] →ₗ[P] RingHom.ker (algebraMap P S))
variable (hl : l.comp (kerToTensor R P S) = LinearMap.id)

-- suppose we have a (set-theoretic) section
variable (σ : S → P) (hσ : ∀ x, algebraMap P S (σ x) = x)

-- This is just an auxiliary lemma
-- so we ignore the fact that some typeclass assumptions weren't used.
set_option linter.unusedSectionVars false in
include hl in
lemma sectionOfRetractionKerToTensorAux_prop (x y) (h : algebraMap P S x = algebraMap P S y) :
    x - l (1 ⊗ₜ .D _ _ x) = y - l (1 ⊗ₜ .D _ _ y) := by
  rw [sub_eq_iff_eq_add, sub_add_comm, ← sub_eq_iff_eq_add, ← Submodule.coe_sub,
    ← map_sub, ← tmul_sub, ← map_sub]
  exact congr_arg Subtype.val (LinearMap.congr_fun hl.symm ⟨x - y, by simp [RingHom.mem_ker, h]⟩)

/--
Given a surjective algebra hom `f : P →ₐ[R] S` with square-zero kernel `I`,
and `σ` be an arbitrary (set-theoretic) section of `f`.
Suppose we have a retraction `l` of the injection `l : I →ₗ[P] S ⊗[P] Ω[P/R]`, then
`x ↦ σ x - l (1 ⊗ D x)` is an algebra homomorphism and a section to `f`.
-/
noncomputable
def sectionOfRetractionKerToTensorAux : S →ₐ[R] P where
  toFun x := σ x - l (1 ⊗ₜ .D _ _ (σ x))
  map_one' := by simp [sectionOfRetractionKerToTensorAux_prop l hl (σ 1) 1 (by simp [hσ])]
  map_mul' a b := by
    have (x y) : (l x).1 * (l y).1 = 0 := by
      rw [← Ideal.mem_bot, ← hf', pow_two]; exact Ideal.mul_mem_mul (l x).2 (l y).2
    simp only [sectionOfRetractionKerToTensorAux_prop l hl (σ (a * b)) (σ a * σ b) (by simp [hσ]),
      Derivation.leibniz, tmul_add, tmul_smul, map_add, map_smul, Submodule.coe_add,
      SetLike.val_smul, smul_eq_mul, mul_sub, sub_mul, this, sub_zero]
    ring
  map_add' a b := by
    simp only [sectionOfRetractionKerToTensorAux_prop l hl (σ (a + b)) (σ a + σ b) (by simp [hσ]),
      map_add, tmul_add, Submodule.coe_add, add_sub_add_comm]
  map_zero' := by simp [sectionOfRetractionKerToTensorAux_prop l hl (σ 0) 0 (by simp [hσ])]
  commutes' r := by
    simp [sectionOfRetractionKerToTensorAux_prop l hl
      (σ (algebraMap R S r)) (algebraMap R P r) (by simp [hσ, ← IsScalarTower.algebraMap_apply])]

lemma sectionOfRetractionKerToTensorAux_algebraMap (x : P) :
    sectionOfRetractionKerToTensorAux hf' l hl σ hσ (algebraMap P S x) = x - l (1 ⊗ₜ .D _ _ x) :=
  sectionOfRetractionKerToTensorAux_prop l hl _ x (by simp [hσ])

noncomputable def sectionOfRetractionKerToTensor : S →ₐ[R] P :=
  sectionOfRetractionKerToTensorAux hf' l hl _ (fun x ↦ (hf x).choose_spec)

@[simp]
lemma sectionOfRetractionKerToTensor_algebraMap (x : P) :
    sectionOfRetractionKerToTensor hf hf' l hl (algebraMap P S x) = x - l (1 ⊗ₜ .D _ _ x) :=
  sectionOfRetractionKerToTensorAux_algebraMap hf' l hl _ _ x

@[simp]
lemma toAlgHom_comp_sectionOfRetractionKerToTensor :
    (IsScalarTower.toAlgHom R P S).comp
      (sectionOfRetractionKerToTensor hf hf' l hl) = AlgHom.id _ _ := by
  ext x
  obtain ⟨x, rfl⟩ := hf x
  simp [RingHom.mem_ker.mp]

end ofRetraction

/--
Given a surjective algebra hom `f : P →ₐ[R] S` with square-zero kernel `I`,
there is a one-to-one correspondance between algebra homomorphism sections of `f`,
and `P`-linear retractions to `I →ₗ[P] S ⊗[P] Ω[P/R]`.
-/
noncomputable
def retractionEquivSectionKerToTensor :
    { l // l ∘ₗ (kerToTensor R P S) = LinearMap.id } ≃
      { g // (IsScalarTower.toAlgHom R P S).comp g = AlgHom.id R S } where
  toFun l := ⟨_, toAlgHom_comp_sectionOfRetractionKerToTensor hf hf' _ l.2⟩
  invFun g := ⟨_, retractionOfSectionOfKerSqZero_comp_kerToTensor hf' _ g.2⟩
  left_inv l := by
    ext s p
    obtain ⟨s, rfl⟩ := hf s
    have (x y) : (l.1 x).1 * (l.1 y).1 = 0 := by
      rw [← Ideal.mem_bot, ← hf', pow_two]; exact Ideal.mul_mem_mul (l.1 x).2 (l.1 y).2
    simp only [AlgebraTensorModule.curry_apply,
      Derivation.coe_comp, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Derivation.coeFn_coe,
      Function.comp_apply, curry_apply, retractionOfSectionOfKerSqZero_tmul_D,
      sectionOfRetractionKerToTensor_algebraMap, ← mul_sub, sub_sub_cancel]
    rw [sub_mul]
    simp only [this, Algebra.algebraMap_eq_smul_one, ← smul_tmul', LinearMapClass.map_smul,
      SetLike.val_smul, smul_eq_mul, sub_zero]
  right_inv g := by ext s; obtain ⟨s, rfl⟩ := hf s; simp

attribute [local instance 99999] IsScalarTower.right

local instance Algebra.kerSquareLift : Algebra (P ⧸ (RingHom.ker (algebraMap P S) ^ 2)) S :=
  (Algebra.ofId P S).kerSquareLift.toAlgebra

instance : IsScalarTower R (P ⧸ (RingHom.ker (algebraMap P S) ^ 2)) S :=
  IsScalarTower.of_algebraMap_eq'
    (IsScalarTower.toAlgHom R P S).kerSquareLift.comp_algebraMap.symm

variable (R P S) in
noncomputable
def derivationQuotKerSq :
    Derivation R (P ⧸ (RingHom.ker (algebraMap P S) ^ 2)) (S ⊗[P] Ω[P⁄R]) := by
  letI := Submodule.liftQ ((RingHom.ker (algebraMap P S) ^ 2).restrictScalars R)
    (((mk P S _ 1).restrictScalars R).comp (KaehlerDifferential.D R P).toLinearMap)
  refine ⟨this ?_, ?_, ?_⟩
  · rintro x hx
    simp only [Submodule.restrictScalars_mem, pow_two] at hx
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
      Derivation.coeFn_coe, Function.comp_apply, mk_apply]
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro x hx y hy
      simp only [smul_eq_mul, Derivation.leibniz, tmul_add, ← smul_tmul, Algebra.smul_def,
        mul_one, RingHom.mem_ker.mp hx, RingHom.mem_ker.mp hy, zero_tmul, zero_add]
    · intro x y hx hy; simp only [map_add, hx, hy, tmul_add, zero_add]
  · show (1 : S) ⊗ₜ[P] KaehlerDifferential.D R P 1 = 0; simp
  · intro a b
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    show (1 : S) ⊗ₜ[P] KaehlerDifferential.D R P (a * b) =
      Ideal.Quotient.mk _ a • ((1 : S) ⊗ₜ[P] KaehlerDifferential.D R P b) +
      Ideal.Quotient.mk _ b • ((1 : S) ⊗ₜ[P] KaehlerDifferential.D R P a)
    simp only [← Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_smul,
      Derivation.leibniz, tmul_add, tmul_smul]

@[simp]
lemma derivationQuotKerSq_mk (x) :
    derivationQuotKerSq R P S (Ideal.Quotient.mk _ x) = 1 ⊗ₜ .D R P x := rfl

variable (R P S) in
noncomputable
def tensorKaehlerQuotKerSqEquiv :
    S ⊗[P ⧸ (RingHom.ker (algebraMap P S) ^ 2)] Ω[(P ⧸ (RingHom.ker (algebraMap P S) ^ 2))⁄R]
      ≃ₗ[S] S ⊗[P] Ω[P⁄R] := by
  letI f₁ := (derivationQuotKerSq R P S).liftKaehlerDifferential
  letI f₂ := AlgebraTensorModule.lift ((LinearMap.ringLmapEquivSelf S S _).symm f₁)
  letI f₃ := KaehlerDifferential.map R R P (P ⧸ (RingHom.ker (algebraMap P S) ^ 2))
  letI f₄ := ((mk (P ⧸ RingHom.ker (algebraMap P S) ^ 2) S _ 1).restrictScalars P).comp f₃
  letI f₅ := AlgebraTensorModule.lift ((LinearMap.ringLmapEquivSelf S S _).symm f₄)
  refine { __ := f₂, invFun := f₅, left_inv := ?_, right_inv := ?_ }
  · suffices f₅.comp f₂ = LinearMap.id from LinearMap.congr_fun this
    ext a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    simp [f₁, f₂, f₃, f₄, f₅]
  · suffices f₂.comp f₅ = LinearMap.id from LinearMap.congr_fun this
    ext a
    simp [f₁, f₂, f₃, f₄, f₅]

@[simp]
lemma tensorKaehlerQuotKerSqEquiv_tmul_D (s t) :
    tensorKaehlerQuotKerSqEquiv R P S (s ⊗ₜ .D _ _ (Ideal.Quotient.mk _ t)) = s ⊗ₜ .D _ _ t := by
  show s • (derivationQuotKerSq R P S).liftKaehlerDifferential (.D _ _ (Ideal.Quotient.mk _ t)) = _
  simp [smul_tmul']

@[simp]
lemma tensorKaehlerQuotKerSqEquiv_symm_tmul_D (s t) :
    (tensorKaehlerQuotKerSqEquiv R P S).symm (s ⊗ₜ .D _ _ t) =
      s ⊗ₜ .D _ _ (Ideal.Quotient.mk _ t) := by
  apply (tensorKaehlerQuotKerSqEquiv R P S).injective
  simp

noncomputable
def retractionEquivSectionKerCotangentToTensor :
    { l // l ∘ₗ (kerCotangentToTensor R P S) = LinearMap.id } ≃
      { g // (IsScalarTower.toAlgHom R P S).kerSquareLift.comp g = AlgHom.id R S } := by
  let P' := P ⧸ (RingHom.ker (algebraMap P S) ^ 2)
  have h₁ : Surjective (algebraMap P' S) := Function.Surjective.of_comp (g := algebraMap P P') hf
  have h₂ : RingHom.ker (algebraMap P' S) ^ 2 = ⊥ := by
    rw [RingHom.algebraMap_toAlgebra, AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square]
  let e₁ : (RingHom.ker (algebraMap P S)).Cotangent ≃ₗ[P] (RingHom.ker (algebraMap P' S)) := by
    refine (Ideal.cotangentEquivIdeal _).trans ((LinearEquiv.ofEq _ _
      (IsScalarTower.toAlgHom R P S).ker_kerSquareLift.symm).restrictScalars P)
  let e₂ : S ⊗[P'] Ω[P'⁄R] ≃ₗ[P] S ⊗[P] Ω[P⁄R] :=
    (tensorKaehlerQuotKerSqEquiv R P S).restrictScalars P
  have H : kerCotangentToTensor R P S =
      e₂.toLinearMap ∘ₗ (kerToTensor R P' S ).restrictScalars P ∘ₗ e₁.toLinearMap := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ x
    exact (tensorKaehlerQuotKerSqEquiv_tmul_D 1 x.1).symm
  refine Equiv.trans ?_ (retractionEquivSectionKerToTensor (R := R) h₁ h₂)
  refine ⟨fun ⟨l, hl⟩ ↦ ⟨⟨(e₁.toLinearMap ∘ₗ l ∘ₗ e₂.toLinearMap).toAddMonoidHom, ?_⟩, ?_⟩,
    fun ⟨l, hl⟩ ↦ ⟨e₁.symm.toLinearMap ∘ₗ l.restrictScalars P ∘ₗ e₂.symm.toLinearMap, ?_⟩, ?_, ?_⟩
  · rintro x y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [← Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_smul]
    exact (e₁.toLinearMap ∘ₗ l ∘ₗ e₂.toLinearMap).map_smul x y
  · ext1 x
    rw [H] at hl
    obtain ⟨x, rfl⟩ := e₁.surjective x
    exact DFunLike.congr_arg e₁ (LinearMap.congr_fun hl x)
  · ext x
    rw [H]
    apply e₁.injective
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars,
      Function.comp_apply, LinearEquiv.symm_apply_apply, LinearMap.id_coe, id_eq,
      LinearEquiv.apply_symm_apply]
    exact LinearMap.congr_fun hl (e₁ x)
  · intro f
    ext x
    simp only [AlgebraTensorModule.curry_apply, Derivation.coe_comp, LinearMap.coe_comp,
      LinearMap.coe_restrictScalars, Derivation.coeFn_coe, Function.comp_apply, curry_apply,
      LinearEquiv.coe_coe, LinearMap.coe_mk, AddHom.coe_coe, LinearMap.toAddMonoidHom_coe,
      LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  · intro f
    ext x
    simp only [AlgebraTensorModule.curry_apply, Derivation.coe_comp, LinearMap.coe_comp,
      LinearMap.coe_restrictScalars, Derivation.coeFn_coe, Function.comp_apply, curry_apply,
      LinearMap.coe_mk, AddHom.coe_coe, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

include hf in
theorem range_kerCotangentToTensor :
    LinearMap.range (kerCotangentToTensor R P S) =
      (LinearMap.ker (KaehlerDifferential.mapBaseChange R P S)).restrictScalars P := by
  classical
  ext x
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ x
    simp [kerCotangentToTensor_toCotangent, RingHom.mem_ker.mp x.2]
  · intro hx
    obtain ⟨x, rfl⟩ := LinearMap.rTensor_surjective (Ω[P⁄R]) (g := Algebra.linearMap P S) hf x
    obtain ⟨x, rfl⟩ := (TensorProduct.lid _ _).symm.surjective x
    replace hx : x ∈ LinearMap.ker (KaehlerDifferential.map R R P S) := by simpa using hx
    rw [KaehlerDifferential.ker_map_of_surjective _ _ _ hf] at hx
    obtain ⟨x, hx, rfl⟩ := hx
    simp only [lid_symm_apply, LinearMap.rTensor_tmul, Algebra.linearMap_apply, _root_.map_one]
    rw [← Finsupp.sum_single x, Finsupp.sum, ← Finset.sum_fiberwise_of_maps_to
      (fun _ ↦ Finset.mem_image_of_mem (algebraMap P S))]
    simp only [Function.comp_apply, map_sum (s := x.support.image (algebraMap P S)), tmul_sum]
    apply sum_mem
    intro c _
    simp only [Finset.filter_congr_decidable, TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul,
      AlgHom.toLinearMap_apply, _root_.map_one, LinearMap.mem_range]
    simp only [map_sum, Finsupp.linearCombination_single]
    have : (x.support.filter (algebraMap P S · = c)).sum x ∈ RingHom.ker (algebraMap P S) := by
      simpa [Finsupp.mapDomain, Finsupp.sum, Finsupp.finset_sum_apply, RingHom.mem_ker,
        Finsupp.single_apply, ← Finset.sum_filter] using DFunLike.congr_fun hx c
    obtain ⟨a, ha⟩ := hf c
    use (x.support.filter (algebraMap P S · = c)).attach.sum
        fun i ↦ x i • Ideal.toCotangent _ ⟨i - a, ?_⟩; swap
    · have : x i ≠ 0 ∧ algebraMap P S i = c := by simpa [-Finset.coe_mem] using i.2
      simp [RingHom.mem_ker, ha, this.2]
    · simp only [map_sum, LinearMapClass.map_smul, kerCotangentToTensor_toCotangent, map_sub]
      simp_rw [← TensorProduct.tmul_smul]
      simp only [smul_sub, TensorProduct.tmul_sub, Finset.sum_sub_distrib, ← TensorProduct.tmul_sum,
        ← Finset.sum_smul, Finset.sum_attach, sub_eq_self,
        Finset.sum_attach (f := fun i ↦ x i • KaehlerDifferential.D R P i)]
      rw [← TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, RingHom.mem_ker.mp this,
        TensorProduct.zero_tmul]

variable [Algebra.FormallySmooth R P]

include hf in
theorem Algebra.FormallySmooth.iff_split_injection :
    Algebra.FormallySmooth R S ↔ ∃ l, l ∘ₗ (kerCotangentToTensor R P S) = LinearMap.id := by
  have := (retractionEquivSectionKerCotangentToTensor (R := R) hf).nonempty_congr
  simp only [nonempty_subtype] at this
  rw [this, ← Algebra.FormallySmooth.iff_split_surjection _ hf]

attribute [local instance 99999] KaehlerDifferential.module'

@[simps!]
def LinearMap.restrictScalarsEquiv {R S M N} [CommSemiring R] [Semiring S] [AddCommMonoid M]
    [AddCommMonoid N] [Algebra R S] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module R N] [Module S N] [IsScalarTower R S N]
    (h : Function.Surjective (algebraMap R S)) : (M →ₗ[S] N) ≃ₗ[R] (M →ₗ[R] N) where
  toFun := restrictScalars R
  map_add' f g := rfl
  map_smul' r f := rfl
  invFun f := ⟨f.toAddMonoidHom, h.forall.mpr (by simp)⟩
  left_inv f := rfl
  right_inv f := rfl

include hf in
theorem Algebra.FormallySmooth.iff_injective_and_split :
    Algebra.FormallySmooth R S ↔ Function.Injective (kerCotangentToTensor R P S) ∧
      ∃ l, (KaehlerDifferential.mapBaseChange R P S) ∘ₗ l = LinearMap.id := by
  rw [Algebra.FormallySmooth.iff_split_injection hf]
  refine (and_iff_right (KaehlerDifferential.mapBaseChange_surjective R _ _ hf)).symm.trans ?_
  refine Iff.trans (((exact_kerCotangentToTensor_mapBaseChange R _ _ hf).split_tfae'
    (g := (KaehlerDifferential.mapBaseChange R P S).restrictScalars P)).out 1 0)
    (and_congr Iff.rfl ?_)
  rw [(LinearMap.restrictScalarsEquiv hf).surjective.exists]
  simp only [LinearMap.ext_iff, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
    Function.comp_apply, LinearMap.restrictScalarsEquiv_apply_apply, LinearMap.id_coe, id_eq]

/-- An auxiliary lemma strictly weaker than the unprimed version. Use that instead. -/
theorem Algebra.FormallySmooth.iff_injective_and_projective' :
    letI : Algebra (MvPolynomial S R) S := (MvPolynomial.aeval _root_.id).toAlgebra
    Algebra.FormallySmooth R S ↔
        Function.Injective (kerCotangentToTensor R (MvPolynomial S R) S) ∧
        Module.Projective S (Ω[S⁄R]) := by
  letI : Algebra (MvPolynomial S R) S := (MvPolynomial.aeval _root_.id).toAlgebra
  have : Function.Surjective (algebraMap (MvPolynomial S R) S) :=
    fun x ↦ ⟨.X x, MvPolynomial.aeval_X _ _⟩
  rw [Algebra.FormallySmooth.iff_injective_and_split this,
    ← Module.Projective.iff_split_of_projective]
  exact KaehlerDifferential.mapBaseChange_surjective _ _ _ this

instance : Module.Projective P (Ω[P⁄R]) :=
  (Algebra.FormallySmooth.iff_injective_and_projective'.mp ‹_›).2

include hf in
/-- Given a formally smooth algebra `P` over `R`, such that the algebra homomorphism `P → S` is
surjective with kernel `I` (typically a presentation `R[X] → S`),
then `S` is formally smooth iff `Ω[S/R]` is projective and `I/I² → B ⊗[A] Ω[A⁄R]` is injective.
-/
theorem Algebra.FormallySmooth.iff_injective_and_projective :
    Algebra.FormallySmooth R S ↔
        Function.Injective (kerCotangentToTensor R P S) ∧ Module.Projective S (Ω[S⁄R]) := by
  rw [Algebra.FormallySmooth.iff_injective_and_split hf,
    ← Module.Projective.iff_split_of_projective]
  exact KaehlerDifferential.mapBaseChange_surjective _ _ _ hf

open MvPolynomial

section H1Cotangent

namespace Algebra

namespace Generators

variable (P : Generators R S) in
/--
The first homology of the naive cotangent complex of `S` over `R`,
induced by a given presentation `0 → I → P → R → 0`,
defined as the kernel of `I/I² → S ⊗[P] Ω[P⁄R]`.
TODO: show that this does not depend on the preseentation chosen.
-/
noncomputable
def H1Cotangent : Type _ := LinearMap.ker (kerCotangentToTensor R P.Ring S)

variable {P : Generators R S}

noncomputable
instance : AddCommGroup P.H1Cotangent := by delta H1Cotangent; infer_instance

noncomputable
instance : Module P.Ring P.H1Cotangent := by delta H1Cotangent; infer_instance

lemma Ideal.Cotangent.smul_eq_zero_of_mem {R} [CommRing R] {I : Ideal R}
    {x} (hx : x ∈ I) (m : I.Cotangent) : x • m = 0 := by
  obtain ⟨m, rfl⟩ := Ideal.toCotangent_surjective _ m
  rw [← map_smul, Ideal.toCotangent_eq_zero, pow_two]
  exact Ideal.mul_mem_mul hx m.2

lemma H1Cotangent.smul_eq_of_map_eq (r₁ r₂ : P.Ring) (x : P.H1Cotangent)
    (e : algebraMap _ S r₁ = algebraMap _ S r₂) : r₁ • x = r₂ • x := by
  apply Subtype.ext
  rw [Submodule.coe_smul, Submodule.coe_smul, ← sub_eq_zero, ← sub_smul,
    Ideal.Cotangent.smul_eq_zero_of_mem]
  rwa [RingHom.mem_ker, map_sub, sub_eq_zero]

noncomputable
instance H1Cotangent.module : Module S P.H1Cotangent where
  smul s x := P.σ s • x
  smul_add r x y := smul_add (P.σ r) x y
  smul_zero r := smul_zero (P.σ r)
  zero_smul x := (smul_eq_of_map_eq (P.σ 0) 0 x (by simp)).trans (zero_smul _ x)
  one_smul x := (smul_eq_of_map_eq (P.σ 1) 1 x (by simp)).trans (one_smul _ x)
  add_smul r s x :=
    (smul_eq_of_map_eq (P.σ (r + s)) (P.σ r + P.σ s) x (by simp)).trans (add_smul _ _ _)
  mul_smul r s x :=
    (smul_eq_of_map_eq (P.σ (r * s)) (P.σ r * P.σ s) x (by simp)).trans (mul_smul _ _ _)

lemma H1Cotangent.σ_smul (r : S) (x : P.H1Cotangent) :
    P.σ r • x = r • x := rfl

instance H1Cotangent.isScalarTower : IsScalarTower P.Ring S P.H1Cotangent where
  smul_assoc r s x :=
    (smul_eq_of_map_eq (P.σ (r • s)) (r * P.σ s) x
      (by simp [Algebra.smul_def])).trans (mul_smul _ _ _)

lemma subsingleton_h1Cotangent (P : Generators R S) :
    Subsingleton P.H1Cotangent ↔ Function.Injective (kerCotangentToTensor R P.Ring S) := by
  delta H1Cotangent
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff, subsingleton_iff_forall_eq 0, Subtype.forall']
  simp only [Subtype.ext_iff, Submodule.coe_zero]

end Generators

end Algebra

end H1Cotangent

variable (R S) in
/--
This is the first homology of the naive cotangent complex,
defined as the kernel of `I/I² → S ⊗[R[S]] Ω[R[S]⁄R]` with `0 → I → R[S] → S → 0` being the
standard presentation.
-/
abbrev Algebra.H1Cotangent : Type _ := (Generators.self R S).H1Cotangent

/-- `S` is a formally smooth algebra over `R` iff `H¹(L[S/R]) = 0` and `Ω[S⁄R]` is projective. -/
theorem Algebra.FormallySmooth.iff_of_generators (P : Generators.{u} R S) :
    Algebra.FormallySmooth R S ↔ Subsingleton P.H1Cotangent ∧ Module.Projective S (Ω[S⁄R]) := by
  rw [P.subsingleton_h1Cotangent,
    ← @Algebra.FormallySmooth.iff_injective_and_projective R P.Ring S]
  exact P.algebraMap_surjective

/-- `S` is a formally smooth algebra over `R` iff `H¹(L[S/R]) = 0` and `Ω[S⁄R]` is projective. -/
theorem Algebra.FormallySmooth.iff_subsingleton_and_projective :
    Algebra.FormallySmooth R S ↔ Subsingleton (H1Cotangent R S) ∧ Module.Projective S (Ω[S⁄R]) :=
  Algebra.FormallySmooth.iff_of_generators _
