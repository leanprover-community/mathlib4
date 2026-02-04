/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Geometry.Manifold.RegularValueTheorem
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Geometry.Manifold.Sheaf.LocallyRingedSpace

/-! # Analytification of a standard smooth algebra as a manifold

to be written!
-/

universe u

public section

open scoped ContDiff
open Manifold Topology Function Set

section

noncomputable
def Module.End.funMap {ι : Type*} {R S : Type*} [CommRing R] [CommRing S]
    (f : R → S) [Fintype ι] [DecidableEq ι]
    (l : Module.End R (ι → R)) : Module.End S (ι → S) :=
  (l.toMatrix'.map f).toLin'

noncomputable
def Module.End.funMapHom {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    Module.End R (ι → R) →+* Module.End S (ι → S) :=
  (Matrix.toLinAlgEquiv (Pi.basisFun _ _)).toRingHom.comp <|
    f.mapMatrix.comp (LinearMap.toMatrixAlgEquiv (Pi.basisFun _ _)).toRingHom

@[simp]
lemma Module.End.funMapHom_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (l : Module.End R (ι → R)) :
    Module.End.funMapHom f l = l.funMap f := by
  rfl

@[simp]
lemma Module.End.funMap_single {ι : Type*} {R S : Type*} [CommRing R] [CommRing S]
    (f : R → S) [Fintype ι] [DecidableEq ι]
    (l : Module.End R (ι → R)) (i : ι) (x : S) :
    l.funMap f (Pi.single i x) = x • (f ∘ l (Pi.single i 1)) := by
  ext
  rw [← Pi.basisFun_apply, ← mul_one x, ← smul_eq_mul, Pi.single_smul]
  simp [funMap, ← Pi.single_apply]

lemma Function.Injective.extend_single_zero {α β γ : Type*} [DecidableEq α] [DecidableEq β] [Zero γ]
    (f : α → β) (hf : Function.Injective f) (a : α) (x : γ) :
    Function.extend f (Pi.single a x) 0 = Pi.single (f a) x := by
  ext j
  by_cases h : j ∈ Set.range f
  · obtain ⟨i, rfl⟩ := h
    simp [hf.extend_apply, Pi.single_apply, hf.eq_iff]
  · rw [Function.extend_apply' _ _ _ h, Pi.single_apply]
    simp
    grind

-- less universe restrictions
@[expose, simps]
noncomputable def Function.ExtendByZero.linearMap' (R : Type*) [Semiring R]
    {ι η : Type*} (s : ι → η) :
    (ι → R) →ₗ[R] η → R :=
  { Function.ExtendByZero.hom R s with
    toFun := fun f => Function.extend s f 0
    map_smul' := fun r f => by simpa using Function.extend_smul r s f 0 }

end

@[simp]
lemma fderiv_apply {ι : Type*} [Fintype ι]
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] (x : ι → 𝕜) (i : ι) :
    fderiv 𝕜 (fun x : ι → 𝕜 => x i) x = ContinuousLinearMap.proj i :=
  (ContinuousLinearMap.proj (R := 𝕜) i).fderiv (x := x)

@[fun_prop]
lemma MvPolynomial.contDiff {ι : Type*} [Fintype ι]
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] (p : MvPolynomial ι 𝕜) :
    ContDiff 𝕜 ω (p.eval ·) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p j hp => simpa using hp.mul (contDiff_apply 𝕜 𝕜 j)

@[fun_prop]
lemma MvPolynomial.differentiable {ι : Type*} [Fintype ι]
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] (p : MvPolynomial ι 𝕜) :
    Differentiable 𝕜 (p.eval ·) :=
  p.contDiff.differentiable (by simp)

lemma MvPolynomial.eval_pderiv_eq_fderiv_aeval {ι : Type*} [DecidableEq ι] [Fintype ι]
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] (p : MvPolynomial ι 𝕜) (i : ι) (x : ι → 𝕜) :
    (p.pderiv i).eval x = fderiv 𝕜 (p.eval ·) x (Pi.single i 1) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp
  | add p q hp hq =>
    simp only [map_add]
    rw [fderiv_fun_add (by fun_prop) (by fun_prop)]
    simp [hp, hq]
  | mul_X p j hp =>
    simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, eval_X]
    rw [fderiv_fun_mul (by fun_prop) (by fun_prop)]
    simp [hp, Pi.single_apply]

namespace Algebra

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {R : Type u} [CommRing R] [Algebra 𝕜 R]
variable {S : Type*} [CommRing S] [Algebra R S]
variable {T : Type*} [CommRing T] [Algebra R T]
variable {ι σ : Type u}

namespace Presentation

section Algebra

variable (P : Presentation R S ι σ)

/--
The polynomial function `(ι → R) → (σ → R)` given by evaluating the relations:
`x = (xᵢ)ᵢ ↦ ((P.relation r)(x))ᵣ`
-/
def evaluation (P : Presentation R S ι σ) (x : (ι → R)) (r : σ) : R :=
  (P.relation r).eval x

def evaluation' (P : Presentation R S ι σ) (x : (ι → R)) : σ → R :=
  fun r ↦ (P.relation r).eval x

end Algebra

end Presentation

namespace PreSubmersivePresentation

section Algebra

variable [Finite σ]
variable (P : PreSubmersivePresentation R S ι σ)

noncomputable
def aevalDifferential' (x : ι → T) : (σ → T) →ₗ[T] (σ → T) :=
  (Pi.basisFun T σ).constr T fun i j ↦
    MvPolynomial.aeval x (MvPolynomial.pderiv (P.map i) (P.relation j))

@[simp]
lemma aevalDifferential'_single [DecidableEq σ] (x : ι → T) (i j : σ) :
    P.aevalDifferential' x (Pi.single i 1) j = ((P.relation j).pderiv (P.map i)).aeval x := by
  simp [← Pi.basisFun_apply, aevalDifferential']

lemma aevalDifferential'_comp [Fintype σ] [DecidableEq σ] {A : Type*} [CommRing A]
    [Algebra R A] (f : T →ₐ[R] A) (x : ι → T) :
    P.aevalDifferential' (f ∘ x) = Module.End.funMap f (P.aevalDifferential' x) := by
  refine (Pi.basisFun A σ).ext fun i ↦ ?_
  simp [aevalDifferential', MvPolynomial.comp_aeval_apply, Function.comp_def]

end Algebra

section Analysis

variable (P : PreSubmersivePresentation 𝕜 R ι σ) [Fintype ι] [Fintype σ]

lemma fderiv_evaluation (x : ι → 𝕜) :
     (fderiv 𝕜 P.evaluation x).toLinearMap ∘ₗ Function.ExtendByZero.linearMap' _ P.map =
      P.aevalDifferential' x := by
  classical
  apply (Pi.basisFun 𝕜 σ).ext fun i ↦ ?_
  dsimp [ExtendByZero.linearMap']
  simp only [Pi.basisFun_apply, aevalDifferential', MvPolynomial.aeval_eq_eval,
    MvPolynomial.eval_pderiv_eq_fderiv_aeval, Module.Basis.constr_apply_fintype,
    Pi.basisFun_equivFun, LinearEquiv.refl_apply, Fintype.sum_single_smul, one_smul,
    P.map_inj.extend_single_zero]
  unfold Presentation.evaluation
  ext a
  rw [← ContinuousLinearMap.proj_apply (R := 𝕜)
    (b := (fderiv 𝕜 (fun x r ↦ (MvPolynomial.eval x) (P.relation r)) x) (Pi.single (P.map i) 1))]
  rw [← (ContinuousLinearMap.proj (φ := fun _ ↦ 𝕜) (R := 𝕜) a).fderiv,
    ← ContinuousLinearMap.comp_apply, ← fderiv_comp _ (by fun_prop) (by fun_prop),
    Function.comp_def]
  dsimp

lemma contMDiff_evaluation : ContMDiff 𝓘(𝕜, ι → 𝕜) 𝓘(𝕜, σ → 𝕜) ω P.evaluation := by
  rw [contMDiff_iff_contDiff]
  unfold Presentation.evaluation
  fun_prop

end Analysis

end PreSubmersivePresentation

namespace SubmersivePresentation

section Algebra

variable [Finite σ] (P : SubmersivePresentation R S ι σ)

lemma aevalDifferential'_bijective {x : ι → R} (hx : P.evaluation x = 0) :
    Function.Bijective (P.aevalDifferential' x) := by
  classical
  cases nonempty_fintype σ
  rw [← Module.End.isUnit_iff, ← LinearMap.isUnit_toMatrix'_iff]
  let f : S →ₐ[R] R :=
    (Ideal.Quotient.liftₐ _ (MvPolynomial.aeval x) <| by
      simp_rw [← RingHom.mem_ker, ← SetLike.le_def]
      rw [← P.span_range_relation_eq_ker, Ideal.span_le, Set.range_subset_iff]
      intro i
      exact congr($(hx) i)).comp
    (P.quotientEquiv.symm.toAlgHom.restrictScalars R)
  have (i : ι) : P.quotientEquiv.symm (P.val i) = Ideal.Quotient.mk _ (MvPolynomial.X i) := by
    simp [← P.quotientEquiv.injective.eq_iff]
  have hx : x = f ∘ P.val := by ext; simp [f, -Presentation.quotientEquiv_symm, this]
  have heq (i : σ) : Pi.single i 1 = f.toRingHom ∘ Pi.single i 1 := by ext; simp [Pi.single_apply]
  -- TODO: remove the `transpose` when mathlib's `aevalDifferential` is fixed
  have : LinearMap.toMatrix' (P.aevalDifferential' x) =
      f.mapMatrix P.aevalDifferential.toMatrix'.transpose := by
    refine Matrix.ext_of_mulVec_single fun i ↦ ?_
    ext j
    conv_rhs => rw [heq]
    rw [LinearMap.toMatrix'_mulVec, AlgHom.mapMatrix_apply, ← AlgHom.coe_toRingHom,
      ← AlgHom.toRingHom_eq_coe, ← f.map_mulVec _ (Pi.single i 1) j]
    simp [← Pi.single_apply, P.aevalDifferential_single, hx, Function.comp_def]
  rw [this]
  refine IsUnit.map _ ?_
  simpa [Module.End.isUnit_iff, ← P.isUnit_jacobian_iff_aevalDifferential_bijective] using
    P.jacobian_isUnit

end Algebra

section Analysis

variable [Fintype ι] [Fintype σ] (P : SubmersivePresentation 𝕜 R ι σ)

variable [CompleteSpace 𝕜]

/-- The evaluation `(ι → 𝕜) → (σ → 𝕜)` given by evaluating the defining equations of `P`
has regular value `0`. -/
lemma isRegularValue_zero : IsRegularValue 𝓘(𝕜, ι → 𝕜) 𝓘(𝕜, σ → 𝕜) P.evaluation 0 := by
  intro x hx
  dsimp only [IsRegularPoint]
  refine .of_surjective_of_finiteDimensional ?_
  suffices h : Function.Surjective (P.aevalDifferential' x) by
    rw [← P.fderiv_evaluation x] at h
    apply Function.Surjective.of_comp
    exact h
  exact (P.aevalDifferential'_bijective hx).surjective

@[expose]
def manifold : Type u :=
  P.isRegularValue_zero.Preimage
  deriving TopologicalSpace

instance : ChartedSpace P.isRegularValue_zero.modelSpace' P.manifold :=
  inferInstanceAs <| ChartedSpace P.isRegularValue_zero.modelSpace' P.isRegularValue_zero.Preimage

instance : IsManifold 𝓘(𝕜, P.isRegularValue_zero.modelSpace') ω P.manifold :=
  inferInstanceAs <|
    IsManifold 𝓘(𝕜, P.isRegularValue_zero.modelSpace') ω P.isRegularValue_zero.Preimage

def manifoldι : P.manifold → (ι → 𝕜) :=
  P.isRegularValue_zero.inclusion

lemma isSmoothEmbedding_manifoldι :
    IsSmoothEmbedding 𝓘(𝕜, P.isRegularValue_zero.modelSpace') 𝓘(𝕜, ι → 𝕜) ω P.manifoldι :=
  P.isRegularValue_zero.foo

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] (IM : ModelWithCorners 𝕜 EM HM)
  {M : Type u} [TopologicalSpace M] [ChartedSpace HM M]

open AlgebraicGeometry CategoryTheory Limits IsManifold

def manifoldEquivAlgHom : P.manifold ≃ (R →ₐ[𝕜] 𝕜) :=
  sorry

def toSpec (x : P.manifold) : Spec (.of R) :=
  ⟨Ideal.map (MvPolynomial.aeval (R := 𝕜) P.val)
    (Ideal.span <| Set.range <| fun i : ι ↦ MvPolynomial.X i - (MvPolynomial.C (x.1 i))),
    sorry⟩

/-- `P.manifold` is the analytification of `Spec R`. -/
theorem exists_toSpec_comp_eq
    (f : locallyRingedSpace IM M ⟶ Scheme.forgetToLocallyRingedSpace.obj (Spec (.of R))) :
    ∃ (g : M → P.manifold),
      ContMDiff IM 𝓘(𝕜, P.isRegularValue_zero.modelSpace') ω g ∧
        P.toSpec ∘ g = (LocallyRingedSpace.forgetToTop.map f).hom.1 := by
  sorry

end Analysis

end SubmersivePresentation

end Algebra
