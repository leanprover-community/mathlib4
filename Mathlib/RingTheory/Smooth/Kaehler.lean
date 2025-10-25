/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.Tactic.StacksAttribute

/-!
# Relation of smoothness and `Ω[S⁄R]`

## Main results

- `retractionKerToTensorEquivSection`:
  Given a surjective algebra homomorphism `f : P →ₐ[R] S` with square-zero kernel `I`,
  there is a one-to-one correspondence between `P`-linear retractions of `I →ₗ[P] S ⊗[P] Ω[P/R]`
  and algebra homomorphism sections of `f`.
- `retractionKerCotangentToTensorEquivSection`:
  Given a surjective algebra homomorphism `f : P →ₐ[R] S` with kernel `I`,
  there is a one-to-one correspondence between `P`-linear retractions of `I/I² →ₗ[P] S ⊗[P] Ω[P/R]`
  and algebra homomorphism sections of `f‾ : P/I² → S`.
- `Algebra.FormallySmooth.iff_split_injection`:
  Given a formally smooth `R`-algebra `P` and a surjective algebra homomorphism `f : P →ₐ[R] S`
  with kernel `I` (typically a presentation `R[X] → S`),
  `S` is formally smooth iff the `P`-linear map `I/I² → S ⊗[P] Ω[P⁄R]` is split injective.
- `Algebra.FormallySmooth.iff_injective_and_projective`:
  Given a formally smooth `R`-algebra `P` and a surjective algebra homomorphism `f : P →ₐ[R] S`
  with kernel `I` (typically a presentation `R[X] → S`),
  then `S` is formally smooth iff `Ω[S/R]` is projective and `I/I² → S ⊗[P] Ω[P⁄R]` is injective.
- `Algebra.FormallySmooth.iff_subsingleton_and_projective`:
  An algebra is formally smooth if and only if `H¹(L_{R/S}) = 0` and `Ω_{S/R}` is projective.
- `Algebra.Extension.equivH1CotangentOfFormallySmooth`:
  Any formally smooth extension can be used to calculate `H¹(L_{S/R})`.

## Future projects

- Show that being smooth is local on stalks.
- Show that being formally smooth is Zariski-local (very hard).

## References

- https://stacks.math.columbia.edu/tag/00TH
- [B. Iversen, *Generic Local Structure of the Morphisms in Commutative Algebra*][iversen]


-/

universe u

open TensorProduct KaehlerDifferential

open Function (Surjective)

variable {R P S : Type u} [CommRing R] [CommRing P] [CommRing S]
variable [Algebra R P] [Algebra P S]

section ofSection

variable [Algebra R S] [IsScalarTower R P S]
-- Suppose we have a section (as an algebra homomorphism) of `P →ₐ[R] S`.
variable (g : S →ₐ[R] P)

/--
Given a surjective algebra homomorphism `f : P →ₐ[R] S` with square-zero kernel `I`,
and a section `g : S →ₐ[R] P` (as an algebra homomorphism),
we get an `R`-derivation `P → I` via `x ↦ x - g (f x)`.
-/
@[simps]
def derivationOfSectionOfKerSqZero (f : P →ₐ[R] S) (hf' : (RingHom.ker f) ^ 2 = ⊥) (g : S →ₐ[R] P)
    (hg : f.comp g = AlgHom.id R S) : Derivation R P (RingHom.ker f) where
  toFun x := ⟨x - g (f x), by
    simpa [RingHom.mem_ker, sub_eq_zero] using AlgHom.congr_fun hg.symm (f x)⟩
  map_add' x y := by simp only [map_add, AddMemClass.mk_add_mk, Subtype.mk.injEq]; ring
  map_smul' x y := by
    ext
    simp only [Algebra.smul_def, map_mul, AlgHom.commutes,
      RingHom.id_apply, Submodule.coe_smul_of_tower]
    ring
  map_one_eq_zero' := by simp only [LinearMap.coe_mk, AddHom.coe_mk, map_one, sub_self,
    Submodule.mk_eq_zero]
  leibniz' a b := by
    have : (a - g (f a)) * (b - g (f b)) = 0 := by
      rw [← Ideal.mem_bot, ← hf', pow_two]
      apply Ideal.mul_mem_mul
      · simpa [RingHom.mem_ker, sub_eq_zero] using AlgHom.congr_fun hg.symm (f a)
      · simpa [RingHom.mem_ker, sub_eq_zero] using AlgHom.congr_fun hg.symm (f b)
    ext
    rw [← sub_eq_zero]
    conv_rhs => rw [← neg_zero, ← this]
    simp only [LinearMap.coe_mk, AddHom.coe_mk, map_mul, SetLike.mk_smul_mk, smul_eq_mul, mul_sub,
      AddMemClass.mk_add_mk, sub_mul, neg_sub]
    ring

variable (hf' : (RingHom.ker (algebraMap P S)) ^ 2 = ⊥)
  (hg : (IsScalarTower.toAlgHom R P S).comp g = AlgHom.id R S)
include hf' hg

lemma isScalarTower_of_section_of_ker_sqZero :
    letI := g.toRingHom.toAlgebra; IsScalarTower P S (RingHom.ker (algebraMap P S)) := by
  letI := g.toRingHom.toAlgebra
  constructor
  intro p s m
  ext
  change g (p • s) * m = p * (g s * m)
  simp only [Algebra.smul_def, map_mul, mul_assoc, mul_left_comm _ (g s)]
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
  haveI := isScalarTower_of_section_of_ker_sqZero g hf' hg
  letI f : _ →ₗ[P] RingHom.ker (algebraMap P S) := (derivationOfSectionOfKerSqZero
    (IsScalarTower.toAlgHom R P S) hf' g hg).liftKaehlerDifferential
  (f.liftBaseChange S).restrictScalars P

@[simp]
lemma retractionOfSectionOfKerSqZero_tmul_D (s : S) (t : P) :
    retractionOfSectionOfKerSqZero g hf' hg (s ⊗ₜ .D _ _ t) =
      g s * t - g s * g (algebraMap _ _ t) := by
  letI := g.toRingHom.toAlgebra
  haveI := isScalarTower_of_section_of_ker_sqZero g hf' hg
  simp only [retractionOfSectionOfKerSqZero, AlgHom.toRingHom_eq_coe, LinearMap.coe_restrictScalars,
    LinearMap.liftBaseChange_tmul, SetLike.val_smul_of_tower]
  -- The issue is a mismatch between `RingHom.ker (algebraMap P S)` and
  -- `RingHom.ker (IsScalarTower.toAlgHom R P S)`, but `rw` and `simp` can't rewrite it away...
  erw [Derivation.liftKaehlerDifferential_comp_D]
  exact mul_sub (g s) t (g (algebraMap P S t))

lemma retractionOfSectionOfKerSqZero_comp_kerToTensor :
    (retractionOfSectionOfKerSqZero g hf' hg).comp (kerToTensor R P S) = LinearMap.id := by
  ext x; simp [RingHom.mem_ker.mp x.2]

end ofSection

section ofRetraction

variable (l : S ⊗[P] Ω[P⁄R] →ₗ[P] RingHom.ker (algebraMap P S))
variable (hl : l.comp (kerToTensor R P S) = LinearMap.id)
include hl

-- suppose we have a (set-theoretic) section
variable (σ : S → P) (hσ : ∀ x, algebraMap P S (σ x) = x)

lemma sectionOfRetractionKerToTensorAux_prop (x y) (h : algebraMap P S x = algebraMap P S y) :
    x - l (1 ⊗ₜ .D _ _ x) = y - l (1 ⊗ₜ .D _ _ y) := by
  rw [sub_eq_iff_eq_add, sub_add_comm, ← sub_eq_iff_eq_add, ← Submodule.coe_sub,
    ← map_sub, ← tmul_sub, ← map_sub]
  exact congr_arg Subtype.val (LinearMap.congr_fun hl.symm ⟨x - y, by simp [RingHom.mem_ker, h]⟩)

variable [Algebra R S] [IsScalarTower R P S]
variable (hf' : (RingHom.ker (algebraMap P S)) ^ 2 = ⊥)
include hf'

/--
Given a surjective algebra homomorphism `f : P →ₐ[R] S` with square-zero kernel `I`.
Let `σ` be an arbitrary (set-theoretic) section of `f`.
Suppose we have a retraction `l` of the injection `I →ₗ[P] S ⊗[P] Ω[P/R]`, then
`x ↦ σ x - l (1 ⊗ D (σ x))` is an algebra homomorphism and a section to `f`.
-/
noncomputable
def sectionOfRetractionKerToTensorAux : S →ₐ[R] P where
  toFun x := σ x - l (1 ⊗ₜ .D _ _ (σ x))
  map_one' := by simp [sectionOfRetractionKerToTensorAux_prop l hl (σ 1) 1 (by simp [hσ])]
  map_mul' a b := by
    have (x y : _) : (l x).1 * (l y).1 = 0 := by
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
    sectionOfRetractionKerToTensorAux l hl σ hσ hf' (algebraMap P S x) = x - l (1 ⊗ₜ .D _ _ x) :=
  sectionOfRetractionKerToTensorAux_prop l hl _ x (by simp [hσ])

variable (hf : Surjective (algebraMap P S))
include hf

lemma toAlgHom_comp_sectionOfRetractionKerToTensorAux :
    (IsScalarTower.toAlgHom R P S).comp
      (sectionOfRetractionKerToTensorAux l hl σ hσ hf') = AlgHom.id _ _ := by
  ext x
  obtain ⟨x, rfl⟩ := hf x
  simp [sectionOfRetractionKerToTensorAux_algebraMap, RingHom.mem_ker.mp]

/--
Given a surjective algebra homomorphism `f : P →ₐ[R] S` with square-zero kernel `I`.
Suppose we have a retraction `l` of the injection `I →ₗ[P] S ⊗[P] Ω[P/R]`, then
`x ↦ σ x - l (1 ⊗ D (σ x))` is an algebra homomorphism and a section to `f`,
where `σ` is an arbitrary (set-theoretic) section of `f`
-/
noncomputable def sectionOfRetractionKerToTensor : S →ₐ[R] P :=
  sectionOfRetractionKerToTensorAux l hl _ (fun x ↦ (hf x).choose_spec) hf'

@[simp]
lemma sectionOfRetractionKerToTensor_algebraMap (x : P) :
    sectionOfRetractionKerToTensor l hl hf' hf (algebraMap P S x) = x - l (1 ⊗ₜ .D _ _ x) :=
  sectionOfRetractionKerToTensorAux_algebraMap l hl _ _ hf' x

@[simp]
lemma toAlgHom_comp_sectionOfRetractionKerToTensor :
    (IsScalarTower.toAlgHom R P S).comp
      (sectionOfRetractionKerToTensor l hl hf' hf) = AlgHom.id _ _ :=
  toAlgHom_comp_sectionOfRetractionKerToTensorAux (hf := hf) ..

end ofRetraction

variable [Algebra R S] [IsScalarTower R P S]
variable (hf' : (RingHom.ker (algebraMap P S)) ^ 2 = ⊥) (hf : Surjective (algebraMap P S))

/--
Given a surjective algebra homomorphism `f : P →ₐ[R] S` with square-zero kernel `I`,
there is a one-to-one correspondence between `P`-linear retractions of `I →ₗ[P] S ⊗[P] Ω[P/R]`
and algebra homomorphism sections of `f`.
-/
noncomputable
def retractionKerToTensorEquivSection :
    { l // l ∘ₗ (kerToTensor R P S) = LinearMap.id } ≃
      { g // (IsScalarTower.toAlgHom R P S).comp g = AlgHom.id R S } where
  toFun l := ⟨_, toAlgHom_comp_sectionOfRetractionKerToTensor _ l.2 hf' hf⟩
  invFun g := ⟨_, retractionOfSectionOfKerSqZero_comp_kerToTensor _ hf' g.2⟩
  left_inv l := by
    ext s p
    obtain ⟨s, rfl⟩ := hf s
    have (x y : _) : (l.1 x).1 * (l.1 y).1 = 0 := by
      rw [← Ideal.mem_bot, ← hf', pow_two]; exact Ideal.mul_mem_mul (l.1 x).2 (l.1 y).2
    simp only [AlgebraTensorModule.curry_apply,
      Derivation.coe_comp, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Derivation.coeFn_coe,
      Function.comp_apply, curry_apply, retractionOfSectionOfKerSqZero_tmul_D,
      sectionOfRetractionKerToTensor_algebraMap, ← mul_sub, sub_sub_cancel]
    rw [sub_mul]
    simp only [this, Algebra.algebraMap_eq_smul_one, ← smul_tmul', LinearMapClass.map_smul,
      SetLike.val_smul, smul_eq_mul, sub_zero]
  right_inv g := by ext s; obtain ⟨s, rfl⟩ := hf s; simp

variable (R P S) in
/--
Given a tower of algebras `S/P/R`, with `I = ker(P → S)`,
this is the `R`-derivative `P/I² → S ⊗[P] Ω[P⁄R]` given by `[x] ↦ 1 ⊗ D x`.
-/
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
  · change (1 : S) ⊗ₜ[P] KaehlerDifferential.D R P 1 = 0; simp
  · intro a b
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    change (1 : S) ⊗ₜ[P] KaehlerDifferential.D R P (a * b) =
      Ideal.Quotient.mk _ a • ((1 : S) ⊗ₜ[P] KaehlerDifferential.D R P b) +
      Ideal.Quotient.mk _ b • ((1 : S) ⊗ₜ[P] KaehlerDifferential.D R P a)
    simp only [← Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_smul,
      Derivation.leibniz, tmul_add, tmul_smul]

@[simp]
lemma derivationQuotKerSq_mk (x : P) :
    derivationQuotKerSq R P S x = 1 ⊗ₜ .D R P x := rfl

variable (R P S) in
/--
Given a tower of algebras `S/P/R`, with `I = ker(P → S)` and `Q := P/I²`,
there is an isomorphism of `S`-modules `S ⊗[Q] Ω[Q/R] ≃ S ⊗[P] Ω[P/R]`.
-/
noncomputable
def tensorKaehlerQuotKerSqEquiv :
    S ⊗[P ⧸ (RingHom.ker (algebraMap P S) ^ 2)] Ω[(P ⧸ (RingHom.ker (algebraMap P S) ^ 2))⁄R] ≃ₗ[S]
      S ⊗[P] Ω[P⁄R] :=
  letI f₁ := (derivationQuotKerSq R P S).liftKaehlerDifferential
  letI f₂ := AlgebraTensorModule.lift ((LinearMap.ringLmapEquivSelf S S _).symm f₁)
  letI f₃ := KaehlerDifferential.map R R P (P ⧸ (RingHom.ker (algebraMap P S) ^ 2))
  letI f₄ := ((mk (P ⧸ RingHom.ker (algebraMap P S) ^ 2) S _ 1).restrictScalars P).comp f₃
  letI f₅ := AlgebraTensorModule.lift ((LinearMap.ringLmapEquivSelf S S _).symm f₄)
  { __ := f₂
    invFun := f₅
    left_inv := by
      suffices f₅.comp f₂ = LinearMap.id from LinearMap.congr_fun this
      ext a
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      simp [f₁, f₂, f₃, f₄, f₅]
    right_inv := by
      suffices f₂.comp f₅ = LinearMap.id from LinearMap.congr_fun this
      ext a
      simp [f₁, f₂, f₃, f₄, f₅] }

@[simp]
lemma tensorKaehlerQuotKerSqEquiv_tmul_D (s t) :
    tensorKaehlerQuotKerSqEquiv R P S (s ⊗ₜ .D _ _ (Ideal.Quotient.mk _ t)) = s ⊗ₜ .D _ _ t := by
  change s • (derivationQuotKerSq R P S).liftKaehlerDifferential
    (.D _ _ (Ideal.Quotient.mk _ t)) = _
  simp [smul_tmul']

@[simp]
lemma tensorKaehlerQuotKerSqEquiv_symm_tmul_D (s t) :
    (tensorKaehlerQuotKerSqEquiv R P S).symm (s ⊗ₜ .D _ _ t) =
      s ⊗ₜ .D _ _ (Ideal.Quotient.mk _ t) := by
  apply (tensorKaehlerQuotKerSqEquiv R P S).injective
  simp

/--
Given a surjective algebra homomorphism `f : P →ₐ[R] S` with kernel `I`,
there is a one-to-one correspondence between `P`-linear retractions of `I/I² →ₗ[P] S ⊗[P] Ω[P/R]`
and algebra homomorphism sections of `f‾ : P/I² → S`.
-/
noncomputable
def retractionKerCotangentToTensorEquivSection :
    { l // l ∘ₗ (kerCotangentToTensor R P S) = LinearMap.id } ≃
      { g // (IsScalarTower.toAlgHom R P S).kerSquareLift.comp g = AlgHom.id R S } := by
  let P' := P ⧸ (RingHom.ker (algebraMap P S) ^ 2)
  have h₁ : Surjective (algebraMap P' S) := Function.Surjective.of_comp (g := algebraMap P P') hf
  have h₂ : RingHom.ker (algebraMap P' S) ^ 2 = ⊥ := by
    rw [RingHom.algebraMap_toAlgebra, AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square]
  let e₁ : (RingHom.ker (algebraMap P S)).Cotangent ≃ₗ[P] (RingHom.ker (algebraMap P' S)) :=
    (Ideal.cotangentEquivIdeal _).trans ((LinearEquiv.ofEq _ _
      (IsScalarTower.toAlgHom R P S).ker_kerSquareLift.symm).restrictScalars P)
  let e₂ : S ⊗[P'] Ω[P'⁄R] ≃ₗ[P] S ⊗[P] Ω[P⁄R] :=
    (tensorKaehlerQuotKerSqEquiv R P S).restrictScalars P
  have H : kerCotangentToTensor R P S =
      e₂.toLinearMap ∘ₗ (kerToTensor R P' S).restrictScalars P ∘ₗ e₁.toLinearMap := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ x
    exact (tensorKaehlerQuotKerSqEquiv_tmul_D 1 x.1).symm
  refine Equiv.trans ?_ (retractionKerToTensorEquivSection (R := R) h₂ h₁)
  refine ⟨fun ⟨l, hl⟩ ↦ ⟨⟨e₁.toLinearMap ∘ₗ l ∘ₗ e₂.toLinearMap, ?_⟩, ?_⟩,
    fun ⟨l, hl⟩ ↦ ⟨e₁.symm.toLinearMap ∘ₗ l.restrictScalars P ∘ₗ e₂.symm.toLinearMap, ?_⟩, ?_, ?_⟩
  · rintro x y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [P', ← Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_smul]
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
      LinearEquiv.coe_coe, LinearMap.coe_mk, AddHom.coe_coe,
      LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  · intro f
    ext x
    simp only [AlgebraTensorModule.curry_apply, Derivation.coe_comp, LinearMap.coe_comp,
      LinearMap.coe_restrictScalars, Derivation.coeFn_coe, Function.comp_apply, curry_apply,
      LinearMap.coe_mk, AddHom.coe_coe, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

variable [Algebra.FormallySmooth R P]

include hf in
/--
Given a formally smooth `R`-algebra `P` and a surjective algebra homomorphism `f : P →ₐ[R] S`
with kernel `I` (typically a presentation `R[X] → S`),
`S` is formally smooth iff the `P`-linear map `I/I² → S ⊗[P] Ω[P⁄R]` is split injective.
Also see `Algebra.Extension.formallySmooth_iff_split_injection`
for the version in terms of `Extension`.
-/
@[stacks 031I]
theorem Algebra.FormallySmooth.iff_split_injection :
    Algebra.FormallySmooth R S ↔ ∃ l, l ∘ₗ (kerCotangentToTensor R P S) = LinearMap.id := by
  have := (retractionKerCotangentToTensorEquivSection (R := R) hf).nonempty_congr
  simp only [nonempty_subtype] at this
  rw [this, ← Algebra.FormallySmooth.iff_split_surjection _ hf]

/--
Given a formally smooth `R`-algebra `P` and a surjective algebra homomorphism `f : P →ₐ[R] S`
with kernel `I` (typically a presentation `R[X] → S`),
`S` is formally smooth iff the `P`-linear map `I/I² → S ⊗[P] Ω[P⁄R]` is split injective.
-/
@[stacks 031I]
theorem Algebra.Extension.formallySmooth_iff_split_injection
    (P : Algebra.Extension.{u} R S) [FormallySmooth R P.Ring] :
    Algebra.FormallySmooth R S ↔ ∃ l, l ∘ₗ P.cotangentComplex = LinearMap.id := by
  refine (Algebra.FormallySmooth.iff_split_injection P.algebraMap_surjective).trans ?_
  let e : P.ker.Cotangent ≃ₗ[P.Ring] P.Cotangent :=
    { __ := AddEquiv.refl _, map_smul' r m := by ext1; simp; rfl }
  constructor
  · intro ⟨l, hl⟩
    exact ⟨(e.comp l).extendScalarsOfSurjective P.algebraMap_surjective,
      LinearMap.ext (DFunLike.congr_fun hl : _)⟩
  · intro ⟨l, hl⟩
    exact ⟨e.symm.toLinearMap ∘ₗ l.restrictScalars P.Ring,
      LinearMap.ext (DFunLike.congr_fun hl : _)⟩

include hf in
/--
Given a formally smooth `R`-algebra `P` and a surjective algebra homomorphism `f : P →ₐ[R] S`
with kernel `I` (typically a presentation `R[X] → S`),
then `S` is formally smooth iff `I/I² → S ⊗[P] Ω[S⁄R]` is injective and
`S ⊗[P] Ω[P⁄R] → Ω[S⁄R]` is split surjective.
-/
theorem Algebra.FormallySmooth.iff_injective_and_split :
    Algebra.FormallySmooth R S ↔ Function.Injective (kerCotangentToTensor R P S) ∧
      ∃ l, (KaehlerDifferential.mapBaseChange R P S) ∘ₗ l = LinearMap.id := by
  rw [Algebra.FormallySmooth.iff_split_injection hf]
  refine (and_iff_right (KaehlerDifferential.mapBaseChange_surjective R _ _ hf)).symm.trans ?_
  refine Iff.trans (((exact_kerCotangentToTensor_mapBaseChange R _ _ hf).split_tfae'
    (g := (KaehlerDifferential.mapBaseChange R P S).restrictScalars P)).out 1 0)
    (and_congr Iff.rfl ?_)
  rw [(LinearMap.extendScalarsOfSurjectiveEquiv hf).surjective.exists]
  simp only [LinearMap.ext_iff, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
    Function.comp_apply, LinearMap.extendScalarsOfSurjective_apply, LinearMap.id_coe, id_eq]

private theorem Algebra.FormallySmooth.iff_injective_and_projective' :
    letI : Algebra (MvPolynomial S R) S := (MvPolynomial.aeval _root_.id).toAlgebra
    Algebra.FormallySmooth R S ↔
        Function.Injective (kerCotangentToTensor R (MvPolynomial S R) S) ∧
        Module.Projective S Ω[S⁄R] := by
  letI : Algebra (MvPolynomial S R) S := (MvPolynomial.aeval _root_.id).toAlgebra
  have : Function.Surjective (algebraMap (MvPolynomial S R) S) :=
    fun x ↦ ⟨.X x, MvPolynomial.aeval_X _ _⟩
  rw [Algebra.FormallySmooth.iff_injective_and_split this,
    ← Module.Projective.iff_split_of_projective]
  exact KaehlerDifferential.mapBaseChange_surjective _ _ _ this

instance : Module.Projective P Ω[P⁄R] :=
  (Algebra.FormallySmooth.iff_injective_and_projective'.mp ‹_›).2

include hf in
/--
Given a formally smooth `R`-algebra `P` and a surjective algebra homomorphism `f : P →ₐ[R] S`
with kernel `I` (typically a presentation `R[X] → S`),
then `S` is formally smooth iff `I/I² → S ⊗[P] Ω[P⁄R]` is injective and `Ω[S/R]` is projective.
-/
theorem Algebra.FormallySmooth.iff_injective_and_projective :
    Algebra.FormallySmooth R S ↔
        Function.Injective (kerCotangentToTensor R P S) ∧ Module.Projective S Ω[S⁄R] := by
  rw [Algebra.FormallySmooth.iff_injective_and_split hf,
    ← Module.Projective.iff_split_of_projective]
  exact KaehlerDifferential.mapBaseChange_surjective _ _ _ hf

/--
An algebra is formally smooth if and only if `H¹(L_{R/S}) = 0` and `Ω_{S/R}` is projective.
-/
@[stacks 031J]
theorem Algebra.FormallySmooth.iff_subsingleton_and_projective :
    Algebra.FormallySmooth R S ↔
        Subsingleton (Algebra.H1Cotangent R S) ∧ Module.Projective S Ω[S⁄R] := by
  refine (Algebra.FormallySmooth.iff_injective_and_projective
    (Generators.self R S).algebraMap_surjective).trans (and_congr ?_ Iff.rfl)
  change Function.Injective (Generators.self R S).toExtension.cotangentComplex ↔ _
  rw [← LinearMap.ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot]
  simp [H1Cotangent, Extension.H1Cotangent]

instance [Algebra.FormallySmooth R S] : Subsingleton (Algebra.H1Cotangent R S) :=
  (Algebra.FormallySmooth.iff_subsingleton_and_projective.mp ‹_›).1

namespace Algebra.Extension

lemma CotangentSpace.map_toInfinitesimal_bijective (P : Extension.{u} R S) :
    Function.Bijective (CotangentSpace.map P.toInfinitesimal) := by
  suffices CotangentSpace.map P.toInfinitesimal =
      (tensorKaehlerQuotKerSqEquiv _ _ _).symm.toLinearMap by
    rw [this]; exact(tensorKaehlerQuotKerSqEquiv _ _ _).symm.bijective
  letI : Algebra P.Ring P.infinitesimal.Ring := inferInstanceAs (Algebra P.Ring (P.Ring ⧸ _))
  have : IsScalarTower P.Ring P.infinitesimal.Ring S := .of_algebraMap_eq' rfl
  apply LinearMap.restrictScalars_injective P.Ring
  ext x a
  dsimp
  simp only [map_tmul, algebraMap_self, RingHom.id_apply, Hom.toAlgHom_apply]
  exact (tensorKaehlerQuotKerSqEquiv_symm_tmul_D _ _).symm

lemma Cotangent.map_toInfinitesimal_bijective (P : Extension.{u} R S) :
    Function.Bijective (Cotangent.map P.toInfinitesimal) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
    have hx : x.1 ∈ P.ker ^ 2 := by
      apply_fun Cotangent.val at hx
      simp only [map_mk, Hom.toAlgHom_apply, val_mk, val_zero, Ideal.toCotangent_eq_zero,
        Extension.ker_infinitesimal] at hx
      rw [Ideal.cotangentIdeal_square] at hx
      simpa only [toInfinitesimal, Ideal.mem_bot, infinitesimal,
        Ideal.Quotient.eq_zero_iff_mem] using hx
    ext
    simpa [Ideal.toCotangent_eq_zero]
  · intro x
    obtain ⟨⟨x, hx⟩, rfl⟩ := Cotangent.mk_surjective x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [ker_infinitesimal, Ideal.mk_mem_cotangentIdeal] at hx
    exact ⟨.mk ⟨x, hx⟩, rfl⟩

lemma H1Cotangent.map_toInfinitesimal_bijective (P : Extension.{u} R S) :
    Function.Bijective (H1Cotangent.map P.toInfinitesimal) := by
  constructor
  · intro x y e
    ext1
    exact (Cotangent.map_toInfinitesimal_bijective P).1 (congr_arg Subtype.val e)
  · intro ⟨x, hx⟩
    obtain ⟨x, rfl⟩ := (Cotangent.map_toInfinitesimal_bijective P).2 x
    refine ⟨⟨x, ?_⟩, rfl⟩
    simpa [← CotangentSpace.map_cotangentComplex,
      map_eq_zero_iff _ (CotangentSpace.map_toInfinitesimal_bijective P).injective] using hx

/--
Given extensions `0 → I₁ → P₁ → S → 0` and `0 → I₂ → P₂ → S → 0` with `P₁` formally smooth,
this is an arbitrarily chosen map `P₁/I₁² → P₂/I₂²` of extensions.
-/
noncomputable
def homInfinitesimal (P₁ P₂ : Extension R S) [FormallySmooth R P₁.Ring] :
    P₁.infinitesimal.Hom P₂.infinitesimal :=
  letI lift : P₁.Ring →ₐ[R] P₂.infinitesimal.Ring := FormallySmooth.liftOfSurjective
    (IsScalarTower.toAlgHom R P₁.Ring S)
    (IsScalarTower.toAlgHom R P₂.infinitesimal.Ring S)
    P₂.infinitesimal.algebraMap_surjective
    ⟨2, show P₂.infinitesimal.ker ^ 2 = ⊥ by
      rw [ker_infinitesimal]; exact Ideal.cotangentIdeal_square _⟩
  { toRingHom := (Ideal.Quotient.liftₐ (P₁.ker ^ 2) lift (by
        change P₁.ker ^ 2 ≤ RingHom.ker lift
        rw [pow_two, Ideal.mul_le]
        have : ∀ r ∈ P₁.ker, lift r ∈ P₂.infinitesimal.ker :=
          fun r hr ↦ (FormallySmooth.liftOfSurjective_apply _
            (IsScalarTower.toAlgHom R P₂.infinitesimal.Ring S) _ _ r).trans hr
        intro r hr s hs
        rw [RingHom.mem_ker, map_mul, ← Ideal.mem_bot, ← P₂.ker.cotangentIdeal_square,
          ← ker_infinitesimal, pow_two]
        exact Ideal.mul_mem_mul (this r hr) (this s hs))).toRingHom
    toRingHom_algebraMap := by simp
    algebraMap_toRingHom x := by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact FormallySmooth.liftOfSurjective_apply _
            (IsScalarTower.toAlgHom R P₂.infinitesimal.Ring S) _ _ x }

/-- Formally smooth extensions have isomorphic `H¹(L_P)`. -/
noncomputable
def H1Cotangent.equivOfFormallySmooth (P₁ P₂ : Extension R S)
    [FormallySmooth R P₁.Ring] [FormallySmooth R P₂.Ring] :
    P₁.H1Cotangent ≃ₗ[S] P₂.H1Cotangent :=
  .ofBijective _ (H1Cotangent.map_toInfinitesimal_bijective P₁) ≪≫ₗ
    H1Cotangent.equiv (Extension.homInfinitesimal _ _) (Extension.homInfinitesimal _ _)
    ≪≫ₗ .symm (.ofBijective _ (H1Cotangent.map_toInfinitesimal_bijective P₂))

lemma H1Cotangent.equivOfFormallySmooth_toLinearMap {P₁ P₂ : Extension R S} (f : P₁.Hom P₂)
    [FormallySmooth R P₁.Ring] [FormallySmooth R P₂.Ring] :
    (H1Cotangent.equivOfFormallySmooth P₁ P₂).toLinearMap = map f := by
  ext1 x
  refine (LinearEquiv.symm_apply_eq _).mpr ?_
  change ((map (P₁.homInfinitesimal P₂)).restrictScalars S ∘ₗ map P₁.toInfinitesimal) x =
    ((map P₂.toInfinitesimal).restrictScalars S ∘ₗ map f) x
  rw [← map_comp, ← map_comp, map_eq]

lemma H1Cotangent.equivOfFormallySmooth_apply {P₁ P₂ : Extension R S} (f : P₁.Hom P₂)
    [FormallySmooth R P₁.Ring] [FormallySmooth R P₂.Ring] (x) :
    H1Cotangent.equivOfFormallySmooth P₁ P₂ x = map f x := by
  rw [← equivOfFormallySmooth_toLinearMap]; rfl

lemma H1Cotangent.equivOfFormallySmooth_symm (P₁ P₂ : Extension R S)
    [FormallySmooth R P₁.Ring] [FormallySmooth R P₂.Ring] :
    (equivOfFormallySmooth P₁ P₂).symm = equivOfFormallySmooth P₂ P₁ := rfl

/-- Any formally smooth extension can be used to calculate `H¹(L_{S/R})`. -/
noncomputable
def equivH1CotangentOfFormallySmooth (P : Extension R S) [FormallySmooth R P.Ring] :
    P.H1Cotangent ≃ₗ[S] H1Cotangent R S :=
  have : FormallySmooth R (Generators.self R S).toExtension.Ring :=
    inferInstanceAs (FormallySmooth R (MvPolynomial _ _))
  H1Cotangent.equivOfFormallySmooth _ _

end Algebra.Extension
