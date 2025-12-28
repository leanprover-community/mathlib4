/-
Copyright (c) 2025 Gregory Wickham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Wickham
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.GNSConstruction.Defs
public import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# The *-homomorphism of the GNS construction

In this file we define the unital ⋆-homomorphism from our C⋆-algebra `A` into the Hilbert space
`f.GNS_HilbertSpace` that is constructed in Mathlib.Analysis.CStarAlgebra.GNSConstruction.Defs.

## Main results

- `f.π` : The unital *-homomorphism from `A` into the bounded linear operators on
  `f.GNS_HilbertSpace`.

## References

Most of this work follows from private course notes prepared by Professor Konrad Aguilar at Pomona
College.

For another, similar approach, see "A Primer on Spectral Theory" by Bernard Aupetit, the other main
refence used here.
-/
@[expose] public section
open scoped ComplexOrder
open Complex
open ContinuousLinearMap
open UniformSpace
open UniformSpace.Completion

variable {A : Type*} [CStarAlgebra A] [PartialOrder A]
variable (f : A →ₚ[ℂ] ℂ)

namespace PositiveLinearMap

variable (a : A)

@[simp]
lemma ofTo : f.ofGNS (f.toGNS a) = a := by rfl

@[simp]
lemma toOf : f.toGNS (f.ofGNS a) = a := by rfl

variable [StarOrderedRing A]

@[coe]
def PLF.toCLM : A →L[ℂ] ℂ where
  toFun := f
  map_add' := by simp
  map_smul' := by simp
-- why can't we set by simp as default method to synthesize these fields?

instance : Coe (A →ₚ[ℂ] ℂ) (A →L[ℂ] ℂ) where
  coe f := PLF.toCLM f

noncomputable
instance : Norm (A →ₚ[ℂ] ℂ) where
  norm f := ‖(f : A →L[ℂ] ℂ)‖

-- figure out approximate unit stuff later
-- How do I get Aguilar 9.0.17

/--
This positive linear functional simply helps with some of the below proofs. There should be no
reason to reference it outside of this file.
-/
def g (b : A) : A →ₚ[ℂ] ℂ where
  toFun x := f (star b * x * b)
  map_add' x y := by rw [mul_add, add_mul, map_add]
  map_smul' m x := by
    have : (star b * m • x * b) = (m • (star b * x * b)) := by noncomm_ring
    rw [this]; simp
  monotone' := by
    unfold Monotone
    intro y z hyz
    apply le_neg_add_iff_le.mp
    obtain ⟨q, hq⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (sub_nonneg_of_le hyz)
    rw [add_comm, ← sub_eq_add_neg, ← map_sub, mul_assoc, mul_assoc,
      ← mul_sub (star b) (z * b) (y * b), ← sub_mul, ← mul_assoc,
      hq, ← mul_assoc, mul_assoc (star b * star q), ← star_mul]
    exact f.map_nonneg (star_mul_self_nonneg (q * b))

@[simp]
lemma g_apply (x b : A) : f (star b * x * b) = (f.g b) x := by rfl

lemma re_of_star_mul_self (a : A) : (f (star a * a)).re = f (star a * a) := by
  have := conj_eq_iff_re.mp (map_isSelfAdjoint f ((star a) * star (star a))
    (IsSelfAdjoint.mul_star_self (star a)))
  rwa [star_star] at this

noncomputable
def const_mul_GNS : f.GNS →L[ℂ] f.GNS := by
  refine LinearMap.mkContinuous
    ((f.toGNS).comp (((LinearMap.mul (A := A) (R := ℂ) a)).comp (f.ofGNS).toLinearMap)) (‖a‖) ?_
  intro x
  simp only [GNS_norm_def]
  have move_const : ‖a‖ = √((‖a‖) ^ 2) := by simp_all only [norm_nonneg, Real.sqrt_sq]
  have normSq_nonneg : 0 ≤ (‖a‖) ^ 2 := pow_two_nonneg ‖a‖
  have : 0 ≤ star (f.ofGNS x) * f.ofGNS x := star_mul_self_nonneg (f.ofGNS x)
  have : 0 ≤ (f (star (f.ofGNS x) * f.ofGNS x)) := PositiveLinearMap.map_nonneg f this
  have : (0 : ℂ) ≤ (f (star (f.ofGNS x) * f.ofGNS x)).re := by
    rw [f.re_of_star_mul_self]; simp_all
  have : 0 ≤ (f (star (f.ofGNS x) * f.ofGNS x)).re := by simp_all
  have : 0 ≤ (‖a‖) ^ 2 * (f (star (f.ofGNS x) * f.ofGNS x)).re := mul_nonneg normSq_nonneg this
  rw [move_const, ← Real.sqrt_mul']; swap
  · assumption
  apply (Real.sqrt_le_sqrt_iff this).mpr
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.mul_apply_apply, ofTo, star_mul]
  nth_rw 1 [← mul_assoc]
  nth_rw 2 [mul_assoc]
  rw [f.g_apply (star a * a) (f.ofGNS x)]
  suffices ((f.g (f.ofGNS x)) (star a * a)).re ≤
      ‖a‖ ^ 2 * (f (star (f.ofGNS x) * 1 * f.ofGNS x)).re by
    simp at this
    assumption
  rw [f.g_apply (1) (f.ofGNS x)]
  have staraaPos := (mul_star_self_nonneg (star a : A))
  rw [star_star] at staraaPos
  have opNorm_leq_one :=
    PositiveLinearMap.norm_apply_le_of_nonneg (f.g (f.ofGNS x)) (star a * a) staraaPos
  rw [CStarRing.norm_star_mul_self, ← pow_two] at opNorm_leq_one
  have main : ‖(f.g (f.ofGNS x)) (star a * a)‖ ≤ ‖f.g (f.ofGNS x)‖ * ‖star a * a‖ :=
    le_opNorm ((f.g (f.ofGNS x)) : A →L[ℂ] ℂ) (star a * a)
  have re_eq_self := (f.g (f.ofGNS x)).re_of_star_mul_self a
  have : 0 ≤ (star a * a) := star_mul_self_nonneg a
  have : 0 ≤ (f.g (f.ofGNS x)) (star a * a) := PositiveLinearMap.map_nonneg (f.g (f.ofGNS x)) this
  have : ‖(f.g (f.ofGNS x)) (star a * a)‖ = ((f.g (f.ofGNS x)) (star a * a)).re := by
    suffices (‖(f.g (f.ofGNS x)) (star a * a)‖ : ℂ) = (((f.g (f.ofGNS x)) (star a * a)).re : ℂ) by
      norm_cast at this
    rw [re_eq_self]
    exact norm_of_nonneg' this
  rw [← this, mul_comm]
  have : 0 ≤ (f.g (f.ofGNS x)) 1 := PositiveLinearMap.map_nonneg (f.g (f.ofGNS x)) (zero_le_one' A)
  have : ((f.g (f.ofGNS x)) 1).re = ‖(f.g (f.ofGNS x)) 1‖ := re_eq_norm.mpr this
  rwa [this]

noncomputable
def A_mul_GNS : A →ₗ[ℂ] f.GNS →L[ℂ] f.GNS where
  toFun a := f.const_mul_GNS a
  map_add' x y := by
    ext b
    dsimp [const_mul_GNS]
    rw [← map_add, add_mul]
  map_smul' c x := by
    ext b
    simp only [RingHom.id_apply, coe_smul', Pi.smul_apply, const_mul_GNS]
    rw [← map_smul]
    simp

noncomputable
def A_mul_Quot : f.GNS_Quotient →L[ℂ] f.GNS_Quotient :=
  (SeparationQuotient.mkCLM (M := f.GNS) (R := ℂ)).comp ((f.A_mul_GNS a).comp
    (SeparationQuotient.outCLM (E := f.GNS) (K := ℂ)))

@[simp]
lemma A_mul_Quot_from_Completion (b : f.GNS_Quotient) :
  Completion.map ⇑(f.A_mul_Quot a) ↑b = (f.A_mul_Quot a) b := by
    simp [map_coe (ContinuousLinearMap.uniformContinuous (f.A_mul_Quot a))]

noncomputable
def π_ofA (a : A) : f.GNS_HilbertSpace →L[ℂ] f.GNS_HilbertSpace where
  toFun := Completion.map (f.A_mul_Quot a)
  map_add' x y := by
    induction x using Completion.induction_on with
    | hp => exact (isClosed_eq ((continuous_map).comp (by continuity))
        (Continuous.add (continuous_map) (continuous_const)))
    | ih x
    induction y using Completion.induction_on with
    | hp => exact (isClosed_eq ((continuous_map).comp (by continuity))
        (Continuous.add (continuous_const) (continuous_map)))
    | ih y
    rw [← Completion.coe_add]
    simp only [A_mul_Quot_from_Completion, map_add]
    rw [Completion.coe_add]
  map_smul' x y := by
    induction y using Completion.induction_on with
    | hp => exact (isClosed_eq ((continuous_map).comp (continuous_const_smul x))
        (Continuous.smul (continuous_const) (continuous_map)))
    | ih y
    rw [← Completion.coe_smul, A_mul_Quot_from_Completion]
    simp
  cont := continuous_map

@[simp]
lemma A_mul_GNS_prod_eq_comp (a b : A) :
    f.A_mul_GNS (a * b) = f.A_mul_GNS (a) ∘ f.A_mul_GNS (b) := by
  ext c
  simp only [Function.comp_apply]
  dsimp [A_mul_GNS, const_mul_GNS]
  simp_all only [ofTo, EmbeddingLike.apply_eq_iff_eq]
  rw [mul_assoc]

@[simp]
theorem Quot_to_SepQuot (c : f.GNS) :
  (Quot.mk (⇑(inseparableSetoid f.GNS)) c) = SeparationQuotient.mk c := by rfl

open SeparationQuotient
theorem Inseparable.outCLM_comp_mkCLM (c : f.GNS) :
  Inseparable ((outCLM ℂ f.GNS) (mkCLM ℂ f.GNS c)) c := by
  have h3 : SeparationQuotient.mk ((outCLM ℂ f.GNS) ((mkCLM ℂ f.GNS) c)) = ((mkCLM ℂ f.GNS) c) := by
    simp
  exact mk_eq_mk.mp h3

lemma mk_eq_mkCLM (c : f.GNS) :
    (SeparationQuotient.mk c) = (SeparationQuotient.mkCLM (R := ℂ) (M := f.GNS) c) := by simp

lemma move_Continuous (c : f.GNS) {h : f.GNS → f.GNS} (hyp : Continuous h) :
  Inseparable (h ((outCLM ℂ f.GNS) ((mkCLM ℂ f.GNS) c)))
    ((outCLM ℂ f.GNS) ((mkCLM ℂ f.GNS) (h c))) :=
  Inseparable.trans
    (Inseparable.map (Inseparable.outCLM_comp_mkCLM f c) (by continuity))
    (Inseparable.symm (Inseparable.outCLM_comp_mkCLM f (h c)))

lemma move_A_mul_GNS (c : f.GNS) (b : A) :
  Inseparable ((f.A_mul_GNS b) ((outCLM ℂ f.GNS) ((mkCLM ℂ f.GNS) c)))
    ((outCLM ℂ f.GNS) ((mkCLM ℂ f.GNS) ((f.A_mul_GNS b) c))) :=
  f.move_Continuous c (h := f.A_mul_GNS b) (by continuity)

lemma A_mul_Quot_of_mk_to_mk (x : f.GNS) :
  ((f.A_mul_Quot a) (SeparationQuotient.mk x))
    = SeparationQuotient.mk ((f.A_mul_GNS a) x) := by
  dsimp [A_mul_Quot]
  simp_all only [mk_eq_mk]
  rw [mk_eq_mkCLM]
  exact Inseparable.map (f := f.A_mul_GNS a) (Inseparable.outCLM_comp_mkCLM f x) (by continuity)

noncomputable
def π : StarAlgHom ℂ A (f.GNS_HilbertSpace →L[ℂ] f.GNS_HilbertSpace) where
  toFun := f.π_ofA
  map_one' := by
    ext b
    dsimp [π_ofA]
    induction b using Completion.induction_on with
    | hp => exact (isClosed_eq (by continuity) (by continuity))
    | ih b
    simp_all only [A_mul_Quot_from_Completion, Completion.coe_inj]
    dsimp [A_mul_Quot, A_mul_GNS, const_mul_GNS]
    simp_all
  map_mul' a b := by
    ext c
    simp only [π_ofA, coe_mk', LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.coe_mul,
      Function.comp_apply]
    induction c using Completion.induction_on with
      | hp => exact (isClosed_eq (by continuity)
            (ContinuousLinearMap.continuous ((f.π_ofA a).comp (f.π_ofA b))))
      | ih c
    simp only [A_mul_Quot_from_Completion, Completion.coe_inj]
    dsimp [A_mul_Quot]
    simp_all only [A_mul_GNS_prod_eq_comp, Function.comp_apply]
    induction c using Quot.induction_on
    simp_all only [Quot_to_SepQuot, mk_eq_mk]
    exact Inseparable.map (Inseparable.symm
      (Inseparable.outCLM_comp_mkCLM f ((f.A_mul_GNS b) ((outCLM ℂ f.GNS) ((mkCLM ℂ f.GNS) _)))))
      (f := (f.A_mul_GNS a)) (by continuity)
  map_zero' := by
    ext b
    dsimp [π_ofA]
    induction b using Completion.induction_on with
    | hp => exact (isClosed_eq (by continuity) (by continuity))
    | ih b
    simp_all only [A_mul_Quot_from_Completion]
    dsimp [A_mul_Quot, A_mul_GNS, const_mul_GNS]
    simp_all
  map_add' x y := by
    ext c
    simp only [π_ofA, coe_mk', LinearMap.coe_mk, AddHom.coe_mk, add_apply]
    induction c using Completion.induction_on with
      | hp => exact (isClosed_eq (by continuity) (by continuity))
      | ih c
    simp only [A_mul_Quot_from_Completion]
    dsimp [A_mul_Quot]
    simp_all only [_root_.map_add, add_apply, mk_add]
    rw [mk_eq_mkCLM, mk_eq_mkCLM]
    norm_cast
  commutes' r := by
    simp only [← RingHom.smulOneHom_eq_algebraMap, RingHom.smulOneHom_apply, π_ofA]
    congr
    ext c
    simp [A_mul_Quot, A_mul_GNS, const_mul_GNS]
  map_star' a := by
    refine (eq_adjoint_iff (π_ofA f (star a)) (π_ofA f a)).mpr ?_
    intro x y
    induction x using Completion.induction_on with
    | hp => exact (isClosed_eq (by continuity)
      (Continuous.inner (continuous_id) (continuous_const)))
    | ih x
    induction x using Quot.induction_on
    induction y using Completion.induction_on with
    | hp => exact (isClosed_eq (Continuous.inner (continuous_const) (continuous_id))
        (Continuous.inner (by continuity) (by continuity)))
    | ih y
    induction y using Quot.induction_on
    simp only [Quot_to_SepQuot, π_ofA, coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
      A_mul_Quot_from_Completion, inner_coe]
    rw [A_mul_Quot_of_mk_to_mk, A_mul_Quot_of_mk_to_mk]
    simp only [inner_mk_mk]
    dsimp [A_mul_GNS, const_mul_GNS]
    rw [GNS_inner_def, GNS_inner_def]
    simp_all only [ofTo, star_mul, star_star]
    congr 1
    group

end PositiveLinearMap
