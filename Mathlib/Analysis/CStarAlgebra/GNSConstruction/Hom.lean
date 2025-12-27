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

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)

namespace PositiveLinearMap

noncomputable instance : NormedSpace ℂ f.GNS :=
  InnerProductSpace.Core.toNormedSpace (c := f.preInnerProdSpace)

variable (a : A)

lemma fprop (a : A) : ‖f a‖ ≤ ‖f‖ * ‖a‖ := le_opNorm (f : A →L[ℂ] ℂ) a


@[simp]
lemma ofTo : f.ofGNS (f.toGNS a) = a := by rfl


@[simp]
lemma toOf : f.toGNS (f.ofGNS a) = a := by rfl

/--
This positive linear functional simply helps with some of the below proofs. There should be no
reason to reference it outside of this file.
-/
def g (b : A) : A →ₚ[ℂ] ℂ where
  toFun x := f (star b * x * b)
  map_add' x y := by rw [mul_add, add_mul, map_add]
  map_smul' m x := by simp
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
lemma g_apply (x b : A):
  f (star b * x * b) = (f.g b) x := by rfl

noncomputable
def const_mul_GNS_nonCont : f.GNS →ₗ[ℂ] f.GNS where
  toFun b := f.toGNS ((ContinuousLinearMap.mul (R := A) (𝕜 := ℂ) a) (f.ofGNS b))
  map_add' x y := by simp [map_add]
  map_smul' c x := by simp_all

-- maybe I should bound it using the unit ball method instead. Re-work later if possible
noncomputable
def const_mul_GNS : f.GNS →L[ℂ] f.GNS := by
  refine LinearMap.mkContinuous (f.const_mul_GNS_nonCont a) (‖a‖) ?_
  intro x
  simp only [GNS_norm_def]
  have move_const : ‖a‖ = √((‖a‖) ^ 2) := by simp_all only [norm_nonneg, Real.sqrt_sq]
  have : 0 ≤ (‖a‖) ^ 2 := by exact pow_two_nonneg ‖a‖
  have : 0 ≤ star (f.ofGNS x) * f.ofGNS x := by exact star_mul_self_nonneg (f.ofGNS x)
  have : 0 ≤ (f (star (f.ofGNS x) * f.ofGNS x)) := by exact PositiveLinearMap.map_nonneg f this
  have : (0 : ℂ) ≤ (f (star (f.ofGNS x) * f.ofGNS x)).re := by
    rw [f.re_of_star_mul_self]; simp_all
  have : 0 ≤ (f (star (f.ofGNS x) * f.ofGNS x)).re := by simp_all
  have : 0 ≤ (‖a‖) ^ 2 * (f (star (f.ofGNS x) * f.ofGNS x)).re := by
    (expose_names; exact mul_nonneg this_1 this)
  rw [move_const, ← Real.sqrt_mul']
  · apply (Real.sqrt_le_sqrt_iff this).mpr
    dsimp [const_mul_GNS_nonCont]
    simp only [ofTo, star_mul]
    nth_rw 1 [← mul_assoc]
    nth_rw 2 [mul_assoc]
    rw [f.g_apply (star a * a) (f.ofGNS x)]
    suffices ((f.g (f.ofGNS x)) (star a * a)).re ≤
        ‖a‖ ^ 2 * (f (star (f.ofGNS x) * 1 * f.ofGNS x)).re by
      simp at this
      assumption
    rw [f.g_apply (1) (f.ofGNS x)]
    rw [← opNorm_eq_of_one, pow_two, ← CStarRing.norm_star_mul_self]
    have main := fprop ((f.g (f.ofGNS x))) (star a * a)
    have re_eq_self := re_of_self_star_self ((f.g (f.ofGNS x))) (star a)
    simp only [star_star] at re_eq_self
    have : 0 ≤ (star a * a) := by exact star_mul_self_nonneg a
    have : 0 ≤ (f.g (f.ofGNS x)) (star a * a) := PositiveLinearMap.map_nonneg (f.g (f.ofGNS x)) this
    have : ‖(f.g (f.ofGNS x)) (star a * a)‖ = ((f.g (f.ofGNS x)) (star a * a)).re := by
      suffices (‖(f.g (f.ofGNS x)) (star a * a)‖ : ℂ) = (((f.g (f.ofGNS x)) (star a * a)).re : ℂ) by
        norm_cast at this
      rw [re_eq_self]
      exact norm_of_nonneg' this
    rw [← this, mul_comm]
    have : (‖f.g (f.ofGNS x)‖ : ℂ).re = ‖f.g (f.ofGNS x)‖ := by simp
    rwa [this]
  assumption

noncomputable
def A_mul_GNS : A →ₗ[ℂ] f.GNS →L[ℂ] f.GNS where
  toFun a := f.const_mul_GNS a
  map_add' x y := by
    ext b
    dsimp [const_mul_GNS, const_mul_GNS_nonCont]
    rw [← map_add, add_mul]
  map_smul' c x := by
    ext b
    simp_all only [RingHom.id_apply, coe_smul', Pi.smul_apply]
    dsimp [const_mul_GNS, const_mul_GNS_nonCont]
    rw [← map_smul]
    simp

@[continuity]
lemma A_mul_GNS_cont (a : A) : Continuous (f.A_mul_GNS a) := by
  exact ContinuousLinearMap.continuous (f.A_mul_GNS a)

noncomputable
def constA_mul_Quot_toQuot : f.GNS_Quotient →L[ℂ] f.GNS_Quotient where
  toFun := (SeparationQuotient.mkCLM (M := f.GNS) (R := ℂ)) ∘ (f.A_mul_GNS a) ∘
      (SeparationQuotient.outCLM (E := f.GNS) (K := ℂ))
  map_add' := by simp_all
  map_smul' := by simp_all

@[simp]
lemma π_completion_onQuot_equiv (b : f.GNS_Quotient) :
  Completion.map ⇑(f.constA_mul_Quot_toQuot a) ↑b = (f.constA_mul_Quot_toQuot a) b := by
    simp [map_coe (ContinuousLinearMap.uniformContinuous (f.constA_mul_Quot_toQuot a))]

noncomputable
def π_ofA (a : A) : f.GNS_HilbertSpace →L[ℂ] f.GNS_HilbertSpace where
  toFun := Completion.map (f.constA_mul_Quot_toQuot a)
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
    simp only [π_completion_onQuot_equiv, map_add]
    rw [Completion.coe_add]
  map_smul' x y := by
    induction y using Completion.induction_on with
    | hp => exact (isClosed_eq ((continuous_map).comp (continuous_const_smul x))
        (Continuous.smul (continuous_const) (continuous_map)))
    | ih y
    rw [← Completion.coe_smul, π_completion_onQuot_equiv]
    simp
  cont := continuous_map


@[simp]
lemma A_mul_GNS_mult (a b : A) : f.A_mul_GNS (a * b) = f.A_mul_GNS (a) ∘ f.A_mul_GNS (b) := by
  ext c
  simp only [Function.comp_apply]
  dsimp [A_mul_GNS, const_mul_GNS, const_mul_GNS_nonCont]
  simp_all only [ofTo, EmbeddingLike.apply_eq_iff_eq]
  rw [mul_assoc]

example (b : A) (c : f.GNS) : ((f.constA_mul_Quot_toQuot b) (SeparationQuotient.mk c)) =
    SeparationQuotient.mk ((f.A_mul_GNS b) c) := by
  dsimp [constA_mul_Quot_toQuot]
  sorry

@[simp]
theorem quot_sepQuot (c : f.GNS) :
  (Quot.mk (⇑(inseparableSetoid f.GNS)) c) = SeparationQuotient.mk c := by rfl

open SeparationQuotient
theorem out_comp_mk (c : f.GNS) :
  Inseparable ((outCLM ℂ f.GNS) (mkCLM ℂ f.GNS c))
    c := by
  -- apply mk to both sides
  have h1 : Inseparable c c := by exact mk_eq_mk.mp rfl
  have h2 := Inseparable.map h1 (f := mkCLM (M := f.GNS) (R := ℂ)) (by continuity)
  have h3 : ((mkCLM ℂ f.GNS) c) =
    SeparationQuotient.mk ((outCLM ℂ f.GNS)
      ((mkCLM ℂ f.GNS) c)) := by
    simp
  rw [h3] at h2
  nth_rw 1 [mkCLM_apply,mk_outCLM] at h2
  exact mk_eq_mk.mp (id (Eq.symm h3))

variable [StarOrderedRing A]

#check f.out_comp_mk

lemma mk_to_mkCLM (c : f.GNS) :
    (SeparationQuotient.mk c) = (SeparationQuotient.mkCLM (R := ℂ) (M := f.GNS) c) := by
  simp

lemma move_func (c : f.GNS) (b : A) :
  Inseparable ((f.A_mul_GNS b) ((outCLM ℂ f.GNS) ((mkCLM ℂ f.GNS) c)))
    ((outCLM ℂ f.GNS) ((mkCLM ℂ f.GNS) ((f.A_mul_GNS b) c))) := by
  -- Inseparability should be transitive
  -- show both sides are inseparable from flat function times thing
  #check Inseparable.trans
  have h1 : Inseparable
    ((outCLM ℂ f.GNS) ((mkCLM ℂ f.GNS) ((f.A_mul_GNS b) c)))
    ((f.A_mul_GNS b) c) := by exact out_comp_mk f ((f.A_mul_GNS b) c)
  have h2 : Inseparable
    c
    ((outCLM ℂ f.GNS) ((mkCLM ℂ f.GNS) c)) := by exact Inseparable.symm (out_comp_mk f c)
  -- apply the function to h2
  have h3 := Inseparable.map h2 (f := (f.A_mul_GNS b)) (by continuity)
  exact Inseparable.trans (id (Inseparable.symm h3)) (id (Inseparable.symm h1))

lemma map_mul (a b : A) : f.π_ofA (a * b) = f.π_ofA a * f.π_ofA b := by
  ext c
  simp only [π_ofA, coe_mk', LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.coe_mul,
    Function.comp_apply]
  induction c using Completion.induction_on with
    | hp => exact (isClosed_eq (by continuity)
          (ContinuousLinearMap.continuous ((f.π_ofA a).comp (f.π_ofA b))))
    | ih c
  simp only [π_completion_onQuot_equiv, Completion.coe_inj]

  dsimp [constA_mul_Quot_toQuot]
  simp_all only [A_mul_GNS_mult, Function.comp_apply]--, SeparationQuotient.mk_eq_mk]
  induction c using Quot.induction_on
  rename_i c
  simp only [quot_sepQuot, mk_to_mkCLM]
  simp_all only [mkCLM_apply, mk_eq_mk]
  rw [mk_to_mkCLM, mk_to_mkCLM]
  -- think out on paper, use awkward transitives
  suffices
    Inseparable
      (((f.A_mul_GNS b) ((outCLM ℂ f.GNS) ((mkCLM ℂ f.GNS) c))))
      (((outCLM ℂ f.GNS) ((mkCLM ℂ f.GNS)
        ((f.A_mul_GNS b) ((outCLM ℂ f.GNS) ((mkCLM ℂ f.GNS) c)))))) by
    sorry -- use Inseparable.map
  -- direct transtiives here should suffice
  sorry

noncomputable
def π : StarAlgHom ℂ A (f.GNS_HilbertSpace →L[ℂ] f.GNS_HilbertSpace) where
  toFun := f.π_ofA
  map_one' := by
    ext b
    dsimp [π_ofA]
    induction b using Completion.induction_on with
    | hp => exact (isClosed_eq (by continuity) (by continuity))
    | ih b
    simp_all only [π_completion_onQuot_equiv, Completion.coe_inj]
    dsimp [constA_mul_Quot_toQuot, A_mul_GNS, const_mul_GNS, const_mul_GNS_nonCont]
    simp_all
  map_mul' := map_mul
  map_zero' := by
    ext b
    dsimp [π_ofA]
    induction b using Completion.induction_on with
    | hp => exact (isClosed_eq (by continuity) (by continuity))
    | ih b
    simp_all only [π_completion_onQuot_equiv]
    dsimp [constA_mul_Quot_toQuot, A_mul_GNS, const_mul_GNS, const_mul_GNS_nonCont]
    simp_all
  map_add' x y := sorry
  commutes' r := sorry
  map_star' a := sorry


end PositiveLinearMap

/-

example (b : A) (c : f.GNS_Quotient) :
    ((f.A_mul_GNS b) ((SeparationQuotient.outCLM ℂ f.GNS) c)) =
    ((SeparationQuotient.outCLM ℂ f.GNS) ((f.A_mul_GNS b) c)) := by

  sorry

example (c : f.GNS_Quotient) (b : A) : ((f.A_mul_GNS b) ((SeparationQuotient.outCLM ℂ f.GNS) c)) =
    (SeparationQuotient.outCLM ℂ f.GNS) ((f.constA_mul_Quot_toQuot b) c) := by
  dsimp [constA_mul_Quot_toQuot]
  dsimp [SeparationQuotient.outCLM]
  dsimp [SeparationQuotient.mk]


lemma constA_mul_Quot_toQuot_mult (a b : A) :
  f.constA_mul_Quot_toQuot (a * b) = f.constA_mul_Quot_toQuot (a) ∘ f.constA_mul_Quot_toQuot (b) := by
  ext c
  dsimp [constA_mul_Quot_toQuot]
  rw [A_mul_GNS_mult]
  simp_all
  congr 2

  simp only [Function.comp_apply]
  dsimp [constA_mul_Quot_toQuot]
  simp_all only [A_mul_GNS_mult, Function.comp_apply, SeparationQuotient.mk_eq_mk]
  set pt := ((SeparationQuotient.outCLM ℂ f.GNS) c)
  set result := (f.A_mul_GNS b) pt
  suffices Inseparable
    result (((SeparationQuotient.outCLM ℂ f.GNS) (SeparationQuotient.mk result))) by
    refine Inseparable.map_of_continuousAt this ?_ ?_
    · exact map_continuousAt (f.A_mul_GNS a) result
    exact
      map_continuousAt (f.A_mul_GNS a)
        ((SeparationQuotient.outCLM ℂ f.GNS) (SeparationQuotient.mk result))
  --by_contra
  dsimp [Inseparable]




  /-  have result_self_insep : Inseparable
    (((SeparationQuotient.outCLM ℂ f.GNS) (SeparationQuotient.mk result)))
    (((SeparationQuotient.outCLM ℂ f.GNS) (SeparationQuotient.mk result))) := by exact SeparationQuotient.mk_eq_mk.mp rfl
  #check SeparationQuotient.mkCLM (M := f.GNS) (R := ℂ)
  have : ContinuousAt (⇑(SeparationQuotient.mkCLM ℂ f.GNS)) (((SeparationQuotient.outCLM ℂ f.GNS) (SeparationQuotient.mk result))) := by
    exact map_continuousAt (SeparationQuotient.mkCLM ℂ f.GNS) (((SeparationQuotient.outCLM ℂ f.GNS) (SeparationQuotient.mk result)))
  have := Inseparable.map_of_continuousAt result_self_insep (f := SeparationQuotient.mkCLM (M := f.GNS) (R := ℂ))
    this this
  nth_rw 1 [SeparationQuotient.mkCLM_apply, SeparationQuotient.mk_outCLM] at this
  rw [SeparationQuotient.mkCLM_apply] at this
  -- something something continuity at this to get goal
  -/



  -- maybe apply mk to both sides?




  sorry
-/
