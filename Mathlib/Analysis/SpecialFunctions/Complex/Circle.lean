/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Topology.Covering.AddCircle

/-!
# Maps on the unit circle

In this file we prove some basic lemmas about `Circle.exp` and the restriction of `Complex.arg`
to the unit circle. These two maps define a partial equivalence between `Circle` and `ℝ`, see
`Circle.argPartialEquiv` and `Circle.argEquiv`, that sends the whole circle to `(-π, π]`.
-/

@[expose] public section


open Complex Function Set

open Real

namespace Circle

theorem injective_arg : Injective fun z : Circle => arg z := fun z w h =>
  Subtype.ext <| ext_norm_arg (z.norm_coe.trans w.norm_coe.symm) h

@[simp]
theorem arg_eq_arg {z w : Circle} : arg z = arg w ↔ z = w :=
  injective_arg.eq_iff

theorem arg_exp {x : ℝ} (h₁ : -π < x) (h₂ : x ≤ π) : arg (exp x) = x := by
  rw [coe_exp, exp_mul_I, arg_cos_add_sin_mul_I ⟨h₁, h₂⟩]

@[simp]
theorem exp_arg (z : Circle) : exp (arg z) = z :=
  injective_arg <| arg_exp (neg_pi_lt_arg _) (arg_le_pi _)

/-- `Complex.arg ∘ (↑)` and `Circle.exp` define a partial equivalence between `Circle` and `ℝ`
with `source = Set.univ` and `target = Set.Ioc (-π) π`. -/
@[simps -fullyApplied]
noncomputable def argPartialEquiv : PartialEquiv Circle ℝ where
  toFun := arg ∘ (↑)
  invFun := exp
  source := univ
  target := Ioc (-π) π
  map_source' _ _ := ⟨neg_pi_lt_arg _, arg_le_pi _⟩
  map_target' := mapsTo_univ _ _
  left_inv' z _ := exp_arg z
  right_inv' _ hx := arg_exp hx.1 hx.2

/-- `Complex.arg` and `Circle.exp ∘ (↑)` define an equivalence between `Circle` and `(-π, π]`. -/
@[simps -fullyApplied]
noncomputable def argEquiv : Circle ≃ Ioc (-π) π where
  toFun z := ⟨arg z, neg_pi_lt_arg _, arg_le_pi _⟩
  invFun := exp ∘ (↑)
  left_inv _ := argPartialEquiv.left_inv trivial
  right_inv x := Subtype.ext <| argPartialEquiv.right_inv x.2

lemma leftInverse_exp_arg : LeftInverse exp (arg ∘ (↑)) := exp_arg
lemma invOn_arg_exp : InvOn (arg ∘ (↑)) exp (Ioc (-π) π) univ := argPartialEquiv.symm.invOn
lemma surjOn_exp_neg_pi_pi : SurjOn exp (Ioc (-π) π) univ := argPartialEquiv.symm.surjOn

lemma exp_eq_exp {x y : ℝ} : exp x = exp y ↔ ∃ m : ℤ, x = y + m * (2 * π) := by
  rw [Subtype.ext_iff, coe_exp, coe_exp, exp_eq_exp_iff_exists_int]
  refine exists_congr fun n => ?_
  rw [← mul_assoc, ← add_mul, mul_left_inj' I_ne_zero]
  norm_cast

lemma periodic_exp : Periodic exp (2 * π) := fun z ↦ exp_eq_exp.2 ⟨1, by rw [Int.cast_one, one_mul]⟩

@[simp] lemma exp_two_pi : exp (2 * π) = 1 := periodic_exp.eq.trans exp_zero

lemma exp_int_mul_two_pi (n : ℤ) : exp (n * (2 * π)) = 1 :=
  ext <| by simpa [mul_assoc] using Complex.exp_int_mul_two_pi_mul_I n

lemma exp_two_pi_mul_int (n : ℤ) : exp (2 * π * n) = 1 := by
  simpa only [mul_comm] using exp_int_mul_two_pi n

lemma exp_eq_one {r : ℝ} : exp r = 1 ↔ ∃ n : ℤ, r = n * (2 * π) := by
  simp [Circle.ext_iff, Complex.exp_eq_one_iff, ← mul_assoc, Complex.I_ne_zero,
    ← Complex.ofReal_inj]

lemma exp_inj {r s : ℝ} : exp r = exp s ↔ r ≡ s [PMOD (2 * π)] := by
  simp [AddCommGroup.modEq_iff_zsmul', ← exp_eq_one, div_eq_one, eq_comm (a := exp r)]

lemma exp_sub_two_pi (x : ℝ) : exp (x - 2 * π) = exp x := periodic_exp.sub_eq x
lemma exp_add_two_pi (x : ℝ) : exp (x + 2 * π) = exp x := periodic_exp x

end Circle

namespace Real.Angle

/-- `Circle.exp`, applied to a `Real.Angle`. -/
noncomputable def toCircle (θ : Angle) : Circle := Circle.periodic_exp.lift θ

@[simp] lemma toCircle_coe (x : ℝ) : toCircle x = .exp x := rfl

lemma coe_toCircle (θ : Angle) : (θ.toCircle : ℂ) = θ.cos + θ.sin * I := by
  induction θ using Real.Angle.induction_on
  simp [exp_mul_I]

@[simp] lemma toCircle_zero : toCircle 0 = 1 := by rw [← coe_zero, toCircle_coe, Circle.exp_zero]

@[simp] lemma toCircle_neg (θ : Angle) : toCircle (-θ) = (toCircle θ)⁻¹ := by
  induction θ using Real.Angle.induction_on
  simp_rw [← coe_neg, toCircle_coe, Circle.exp_neg]

@[simp] lemma toCircle_add (θ₁ θ₂ : Angle) : toCircle (θ₁ + θ₂) = toCircle θ₁ * toCircle θ₂ := by
  induction θ₁ using Real.Angle.induction_on
  induction θ₂ using Real.Angle.induction_on
  exact Circle.exp_add _ _

@[simp] lemma arg_toCircle (θ : Real.Angle) : (arg θ.toCircle : Angle) = θ := by
  induction θ using Real.Angle.induction_on
  rw [toCircle_coe, Circle.coe_exp, exp_mul_I, ← ofReal_cos, ← ofReal_sin, ←
    Real.Angle.cos_coe, ← Real.Angle.sin_coe, arg_cos_add_sin_mul_I_coe_angle]

end Real.Angle

namespace AddCircle

variable {T : ℝ}

/-! ### Map from `AddCircle` to `Circle` -/

theorem scaled_exp_map_periodic : Function.Periodic (fun x => Circle.exp (2 * π / T * x)) T := by
  -- The case T = 0 is not interesting, but it is true, so we prove it to save hypotheses
  rcases eq_or_ne T 0 with (rfl | hT)
  · simp
  · intro x; simp_rw [mul_add]; rw [div_mul_cancel₀ _ hT, Circle.periodic_exp]

/-- The canonical map `fun x => exp (2 π i x / T)` from `ℝ / ℤ • T` to the unit circle in `ℂ`.
If `T = 0` we understand this as the constant function 1. -/
noncomputable def toCircle : AddCircle T → Circle :=
  (@scaled_exp_map_periodic T).lift

theorem toCircle_apply_mk (x : ℝ) : @toCircle T x = Circle.exp (2 * π / T * x) :=
  rfl

theorem toCircle_add (x y : AddCircle T) : toCircle (x + y) = toCircle x * toCircle y := by
  induction x using QuotientAddGroup.induction_on
  induction y using QuotientAddGroup.induction_on
  simp_rw [← coe_add, toCircle_apply_mk, mul_add, Circle.exp_add]

@[simp] lemma toCircle_zero : toCircle (0 : AddCircle T) = 1 := by
  rw [← QuotientAddGroup.mk_zero, toCircle_apply_mk, mul_zero, Circle.exp_zero]

theorem toCircle_neg (x : AddCircle T) : toCircle (-x) = (toCircle x)⁻¹ :=
  (mul_left_inj (toCircle x)).mp <| by simp [← toCircle_add]

theorem toCircle_nsmul (x : AddCircle T) (n : ℕ) : toCircle (n • x) = toCircle x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, toCircle_add, ih, pow_succ]

theorem toCircle_zsmul (x : AddCircle T) (n : ℤ) : toCircle (n • x) = toCircle x ^ n := by
  cases n <;> simp [toCircle_nsmul, toCircle_neg]

theorem continuous_toCircle : Continuous (@toCircle T) :=
  continuous_coinduced_dom.mpr (Circle.exp.continuous.comp <| by fun_prop)

theorem injective_toCircle (hT : T ≠ 0) : Function.Injective (@toCircle T) := by
  intro a b h
  induction a using QuotientAddGroup.induction_on
  induction b using QuotientAddGroup.induction_on
  simp_rw [toCircle_apply_mk] at h
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h.symm
  rw [QuotientAddGroup.eq]; simp_rw [AddSubgroup.mem_zmultiples_iff, zsmul_eq_mul]
  use m
  field_simp at hm
  linarith

/-- The homeomorphism between `AddCircle (2 * π)` and `Circle`. -/
@[simps] noncomputable def homeomorphCircle' : AddCircle (2 * π) ≃ₜ Circle where
  toFun := Angle.toCircle
  invFun := fun x ↦ arg x
  left_inv := Angle.arg_toCircle
  right_inv := Circle.exp_arg
  continuous_toFun := continuous_coinduced_dom.mpr Circle.exp.continuous
  continuous_invFun := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (continuousAt_arg_coe_angle x.coe_ne_zero).comp continuousAt_subtype_val

theorem homeomorphCircle'_apply_mk (x : ℝ) : homeomorphCircle' x = Circle.exp x := rfl

/-- The homeomorphism between `AddCircle` and `Circle`. -/
noncomputable def homeomorphCircle (hT : T ≠ 0) : AddCircle T ≃ₜ Circle :=
  (homeomorphAddCircle T (2 * π) hT (by positivity)).trans homeomorphCircle'

theorem homeomorphCircle_apply (hT : T ≠ 0) (x : AddCircle T) :
    homeomorphCircle hT x = toCircle x := by
  cases x using QuotientAddGroup.induction_on
  rw [homeomorphCircle, Homeomorph.trans_apply,
    homeomorphAddCircle_apply_mk, homeomorphCircle'_apply_mk, toCircle_apply_mk]
  ring_nf

end AddCircle

open AddCircle

theorem Circle.isAddQuotientCoveringMap_exp :
    IsAddQuotientCoveringMap exp (AddSubgroup.zmultiples (2 * Real.pi)) := by
  convert (isAddQuotientCoveringMap_coe _).homeomorph_comp (homeomorphCircle _)
  on_goal 2 => simp
  ext; simp [homeomorphCircle_apply, toCircle]

theorem Circle.isCoveringMap_exp : IsCoveringMap exp := isAddQuotientCoveringMap_exp.isCoveringMap

lemma isLocalHomeomorph_circleExp : IsLocalHomeomorph Circle.exp :=
  Circle.isCoveringMap_exp.isLocalHomeomorph

/- TODO: this generalizes to a large class of groups, but requires an open mapping theorem for
topological groups to show the `n`th power map is open (see https://www.mathematik.tu-darmstadt.de/media/mathematik/forschung/preprint/preprints/2480.pdf
and https://www.math.uwaterloo.ca/~cgodsil/pdfs/topology/topgr.pdf), and discreteness of the
kernel (see https://gemini.google.com/share/6e9ab4abcb95). -/
theorem Circle.isQuotientCoveringMap_zpow (n : ℤ) [NeZero n] :
    IsQuotientCoveringMap (· ^ n : Circle → _) (zpowGroupHom (α := Circle) n).ker := by
  have hn : IsUnit (n : ℝ) := by simpa using NeZero.ne n
  let e := AddCircle.homeomorphCircle one_ne_zero
  refine Topology.IsQuotientMap.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom
    (f := zpowGroupHom (α := Circle) n) ?_ (Set.Finite.isDiscrete <| .of_preimage ?_ e.surjective)
  · refine .of_comp e.continuous (continuous_zpow n) ?_
    convert e.isQuotientMap.comp <| IsUnit.isQuotientMap_zsmul (M := ℝ)
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) isQuotientMap_quotient_mk' n hn
    ext; simp [zpowGroupHom, e, homeomorphCircle_apply, toCircle_zsmul]
  · convert finite_torsion_of_isSMulRegular_int (1 : ℝ) n fun _ ↦ by simp [NeZero.ne]
    ext
    simp [e, homeomorphCircle_apply, ← toCircle_zsmul, ← (injective_toCircle one_ne_zero).eq_iff]

theorem Circle.isQuotientCoveringMap_npow (n : ℕ) [NeZero n] :
    IsQuotientCoveringMap (· ^ n : Circle → _) (powMonoidHom (α := Circle) n).ker :=
  isQuotientCoveringMap_zpow n
