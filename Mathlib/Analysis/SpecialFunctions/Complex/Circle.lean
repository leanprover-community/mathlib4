/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.IsLocalHomeomorph

#align_import analysis.special_functions.complex.circle from "leanprover-community/mathlib"@"f333194f5ecd1482191452c5ea60b37d4d6afa08"

/-!
# Maps on the unit circle

In this file we prove some basic lemmas about `expMapCircle` and the restriction of `Complex.arg`
to the unit circle. These two maps define a partial equivalence between `circle` and `ℝ`, see
`circle.argPartialEquiv` and `circle.argEquiv`, that sends the whole circle to `(-π, π]`.
-/


open Complex Function Set

open Real

namespace circle

theorem injective_arg : Injective fun z : circle => arg z := fun z w h =>
  Subtype.ext <| ext_abs_arg ((abs_coe_circle z).trans (abs_coe_circle w).symm) h
#align circle.injective_arg circle.injective_arg

@[simp]
theorem arg_eq_arg {z w : circle} : arg z = arg w ↔ z = w :=
  injective_arg.eq_iff
#align circle.arg_eq_arg circle.arg_eq_arg

end circle

theorem arg_expMapCircle {x : ℝ} (h₁ : -π < x) (h₂ : x ≤ π) : arg (expMapCircle x) = x := by
  rw [expMapCircle_apply, exp_mul_I, arg_cos_add_sin_mul_I ⟨h₁, h₂⟩]
#align arg_exp_map_circle arg_expMapCircle

@[simp]
theorem expMapCircle_arg (z : circle) : expMapCircle (arg z) = z :=
  circle.injective_arg <| arg_expMapCircle (neg_pi_lt_arg _) (arg_le_pi _)
#align exp_map_circle_arg expMapCircle_arg

namespace circle

/-- `Complex.arg ∘ (↑)` and `expMapCircle` define a partial equivalence between `circle` and `ℝ`
with `source = Set.univ` and `target = Set.Ioc (-π) π`. -/
@[simps (config := .asFn)]
noncomputable def argPartialEquiv : PartialEquiv circle ℝ where
  toFun := arg ∘ (↑)
  invFun := expMapCircle
  source := univ
  target := Ioc (-π) π
  map_source' _ _ := ⟨neg_pi_lt_arg _, arg_le_pi _⟩
  map_target' := mapsTo_univ _ _
  left_inv' z _ := expMapCircle_arg z
  right_inv' _ hx := arg_expMapCircle hx.1 hx.2
#align circle.arg_local_equiv circle.argPartialEquiv

/-- `Complex.arg` and `expMapCircle` define an equivalence between `circle` and `(-π, π]`. -/
@[simps (config := .asFn)]
noncomputable def argEquiv : circle ≃ Ioc (-π) π where
  toFun z := ⟨arg z, neg_pi_lt_arg _, arg_le_pi _⟩
  invFun := expMapCircle ∘ (↑)
  left_inv _ := argPartialEquiv.left_inv trivial
  right_inv x := Subtype.ext <| argPartialEquiv.right_inv x.2
#align circle.arg_equiv circle.argEquiv

end circle

theorem leftInverse_expMapCircle_arg : LeftInverse expMapCircle (arg ∘ (↑)) :=
  expMapCircle_arg
#align left_inverse_exp_map_circle_arg leftInverse_expMapCircle_arg

theorem invOn_arg_expMapCircle : InvOn (arg ∘ (↑)) expMapCircle (Ioc (-π) π) univ :=
  circle.argPartialEquiv.symm.invOn
#align inv_on_arg_exp_map_circle invOn_arg_expMapCircle

theorem surjOn_expMapCircle_neg_pi_pi : SurjOn expMapCircle (Ioc (-π) π) univ :=
  circle.argPartialEquiv.symm.surjOn
#align surj_on_exp_map_circle_neg_pi_pi surjOn_expMapCircle_neg_pi_pi

theorem expMapCircle_eq_expMapCircle {x y : ℝ} :
    expMapCircle x = expMapCircle y ↔ ∃ m : ℤ, x = y + m * (2 * π) := by
  rw [Subtype.ext_iff, expMapCircle_apply, expMapCircle_apply, exp_eq_exp_iff_exists_int]
  refine' exists_congr fun n => _
  rw [← mul_assoc, ← add_mul, mul_left_inj' I_ne_zero]
  norm_cast
#align exp_map_circle_eq_exp_map_circle expMapCircle_eq_expMapCircle

theorem periodic_expMapCircle : Periodic expMapCircle (2 * π) := fun z =>
  expMapCircle_eq_expMapCircle.2 ⟨1, by rw [Int.cast_one, one_mul]⟩
#align periodic_exp_map_circle periodic_expMapCircle

@[simp]
theorem expMapCircle_two_pi : expMapCircle (2 * π) = 1 :=
  periodic_expMapCircle.eq.trans expMapCircle_zero
#align exp_map_circle_two_pi expMapCircle_two_pi

theorem expMapCircle_sub_two_pi (x : ℝ) : expMapCircle (x - 2 * π) = expMapCircle x :=
  periodic_expMapCircle.sub_eq x
#align exp_map_circle_sub_two_pi expMapCircle_sub_two_pi

theorem expMapCircle_add_two_pi (x : ℝ) : expMapCircle (x + 2 * π) = expMapCircle x :=
  periodic_expMapCircle x
#align exp_map_circle_add_two_pi expMapCircle_add_two_pi

/-- `expMapCircle`, applied to a `Real.Angle`. -/
noncomputable def Real.Angle.expMapCircle (θ : Real.Angle) : circle :=
  periodic_expMapCircle.lift θ
#align real.angle.exp_map_circle Real.Angle.expMapCircle

@[simp]
theorem Real.Angle.expMapCircle_coe (x : ℝ) : Real.Angle.expMapCircle x = _root_.expMapCircle x :=
  rfl
#align real.angle.exp_map_circle_coe Real.Angle.expMapCircle_coe

theorem Real.Angle.coe_expMapCircle (θ : Real.Angle) :
    (θ.expMapCircle : ℂ) = θ.cos + θ.sin * I := by
  induction θ using Real.Angle.induction_on
  simp [Complex.exp_mul_I]
#align real.angle.coe_exp_map_circle Real.Angle.coe_expMapCircle

@[simp]
theorem Real.Angle.expMapCircle_zero : Real.Angle.expMapCircle 0 = 1 := by
  rw [← Real.Angle.coe_zero, Real.Angle.expMapCircle_coe, _root_.expMapCircle_zero]
#align real.angle.exp_map_circle_zero Real.Angle.expMapCircle_zero

@[simp]
theorem Real.Angle.expMapCircle_neg (θ : Real.Angle) :
    Real.Angle.expMapCircle (-θ) = (Real.Angle.expMapCircle θ)⁻¹ := by
  induction θ using Real.Angle.induction_on
  simp_rw [← Real.Angle.coe_neg, Real.Angle.expMapCircle_coe, _root_.expMapCircle_neg]
#align real.angle.exp_map_circle_neg Real.Angle.expMapCircle_neg

@[simp]
theorem Real.Angle.expMapCircle_add (θ₁ θ₂ : Real.Angle) : Real.Angle.expMapCircle (θ₁ + θ₂) =
    Real.Angle.expMapCircle θ₁ * Real.Angle.expMapCircle θ₂ := by
  induction θ₁ using Real.Angle.induction_on
  induction θ₂ using Real.Angle.induction_on
  exact _root_.expMapCircle_add _ _
#align real.angle.exp_map_circle_add Real.Angle.expMapCircle_add

@[simp]
theorem Real.Angle.arg_expMapCircle (θ : Real.Angle) :
    (arg (Real.Angle.expMapCircle θ) : Real.Angle) = θ := by
  induction θ using Real.Angle.induction_on
  rw [Real.Angle.expMapCircle_coe, expMapCircle_apply, exp_mul_I, ← ofReal_cos, ← ofReal_sin, ←
    Real.Angle.cos_coe, ← Real.Angle.sin_coe, arg_cos_add_sin_mul_I_coe_angle]
#align real.angle.arg_exp_map_circle Real.Angle.arg_expMapCircle

lemma isLocalHomeomorph_expMapCircle : IsLocalHomeomorph expMapCircle := by
  have fund : ∀ x : circle, Complex.arg x = Real.pi ↔ x = expMapCircle Real.pi := by
    rintro ⟨x, hx⟩
    rw [mem_circle_iff_normSq, Complex.normSq_apply] at hx
    rw [Complex.arg_eq_pi_iff, Subtype.ext_iff, expMapCircle_apply, Complex.exp_pi_mul_I,
        Complex.ext_iff, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im, neg_zero]
    rw [and_congr_left_iff]
    simp only
    intro hx'
    rw [hx', mul_zero, add_zero, ← sq, sq_eq_one_iff] at hx
    rcases hx with hx | hx <;> rw [hx] <;> norm_num
  let e1 : PartialHomeomorph ℝ circle :=
  { toFun := expMapCircle
    invFun := Complex.arg ∘ Subtype.val
    source := Set.Ioo (-Real.pi) Real.pi
    target := {expMapCircle Real.pi}ᶜ
    map_source' := by
      intro x hx hx'
      rw [Set.mem_singleton_iff] at hx'
      replace hx' := congrArg (Complex.arg ∘ Subtype.val) hx'
      simp only [Function.comp_apply] at hx'
      rw [arg_expMapCircle hx.1 hx.2.le] at hx'
      rw [arg_expMapCircle (neg_lt_self Real.pi_pos) le_rfl] at hx'
      rw [hx'] at hx
      exact lt_irrefl Real.pi hx.2
    map_target' := by
      intro x hx
      have key := Complex.arg_mem_Ioc x
      exact ⟨key.1, lt_of_le_of_ne key.2 (hx ∘ (fund x).mp)⟩
    left_inv' := fun x hx ↦ arg_expMapCircle hx.1 hx.2.le
    right_inv' := fun x _ ↦ expMapCircle_arg x
    open_source := isOpen_Ioo
    open_target := isOpen_compl_singleton
    continuousOn_toFun := Continuous.continuousOn $ by continuity
    continuousOn_invFun := by
      refine' (ContinuousAt.continuousOn fun _ ↦ Complex.continuousAt_arg).comp
        (Continuous.continuousOn $ by continuity) _
      simp only
      intro x hx
      contrapose! hx
      rw [Set.not_mem_compl_iff, Set.mem_singleton_iff, ← fund, Complex.arg_eq_pi_iff]
      rw [Complex.slitPlane, Set.mem_setOf_eq, not_or, not_lt, not_ne_iff] at hx
      refine' ⟨lt_of_le_of_ne hx.1 _, hx.2⟩
      intro hx'
      have hx'' := x.2
      rw [mem_circle_iff_normSq, Complex.normSq_apply, hx', hx.2, mul_zero, add_zero] at hx''
      exact zero_ne_one hx'' }
  intro t
  let e2 : PartialHomeomorph ℝ ℝ :=
  { toFun := fun s ↦ s - t
    invFun := fun s ↦ s + t
    source := Set.Ioo (t - Real.pi) (t + Real.pi)
    target := Set.Ioo (-Real.pi) Real.pi
    map_source' := by
      intro x hx
      rw [Set.mem_Ioo, sub_lt_iff_lt_add'] at hx ⊢
      rwa [neg_lt_sub_iff_lt_add]
    map_target' := by
      intro x hx
      rw [Set.mem_Ioo] at hx ⊢
      rwa [← neg_add_eq_sub, add_lt_add_iff_right, add_comm, add_lt_add_iff_right]
    left_inv' := fun x _ ↦ sub_add_cancel x t
    right_inv' := fun x _ ↦ add_sub_cancel x t
    open_source := isOpen_Ioo
    open_target := isOpen_Ioo
    continuousOn_toFun := Continuous.continuousOn $ by continuity
    continuousOn_invFun := Continuous.continuousOn $ by continuity }
  let e3 : PartialHomeomorph circle circle :=
  { toFun := fun s ↦ s * expMapCircle t
    invFun := fun s ↦ s / expMapCircle t
    source := {expMapCircle Real.pi}ᶜ
    target := {expMapCircle (Real.pi + t)}ᶜ
    map_source' := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
      rwa [← eq_div_iff_mul_eq', ← expMapCircle_sub, add_sub_cancel]
    map_target' := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
      rwa [div_eq_iff_eq_mul, ← expMapCircle_add]
    left_inv' := fun x _ ↦ mul_div_cancel'' x (expMapCircle t)
    right_inv' := fun x _ ↦ div_mul_cancel' x (expMapCircle t)
    open_source := isOpen_compl_singleton
    open_target := isOpen_compl_singleton
    continuousOn_toFun := Continuous.continuousOn $ by continuity
    continuousOn_invFun := Continuous.continuousOn $ by continuity }
  let e4 : PartialHomeomorph ℝ circle := e2.trans' (e1.trans' e3 rfl) rfl
  refine' ⟨e4, ⟨sub_lt_self t Real.pi_pos, lt_add_of_pos_right t Real.pi_pos⟩, _⟩
  ext x
  simp only [e4, e1, e3, e2]
  simp only [expMapCircle_apply, expMapCircle_add, PartialHomeomorph.trans'_apply,
    PartialHomeomorph.mk_coe, expMapCircle_sub, div_mul_cancel']
