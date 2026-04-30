/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Analysis.Convex.PathConnected

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

@[simp]
theorem arg_eq_zero {z : Circle} : arg z = 0 ↔ z = 1 := by
  simpa using arg_eq_arg (w := 1)

theorem arg_exp {x : ℝ} (h₁ : -π < x) (h₂ : x ≤ π) : arg (exp x) = x := by
  rw [coe_exp, exp_mul_I, arg_cos_add_sin_mul_I ⟨h₁, h₂⟩]

@[simp]
theorem exp_arg (z : Circle) : exp (arg z) = z :=
  injective_arg <| arg_exp (neg_pi_lt_arg _) (arg_le_pi _)

/-- The image under `Circle.exp` of the interval of angles `(-r, r)`. -/
def centeredArc (r : ℝ) : Set Circle :=
  exp '' {x | |x| < r}

theorem mem_centeredArc {r : ℝ} (hr : r ≤ π) {z : Circle} :
    z ∈ centeredArc r ↔ |arg z| < r := by
  refine ⟨?_, fun hz ↦ ⟨arg z, hz, exp_arg z⟩⟩
  rintro ⟨t, ht, rfl⟩
  have htπ : |t| < π := ht.trans_le hr
  rwa [arg_exp (neg_lt_of_abs_lt htπ) (lt_of_abs_lt htπ).le]

/-- If all positive powers of a point on the circle lie in the right half centered arc,
then the point is `1`. -/
theorem eq_one_of_forall_pow_mem_centeredArc_pi_div_two {z : Circle}
    (hz : ∀ n > 0, z ^ n ∈ centeredArc (π / 2)) : z = 1 := by
  have exists_pos_cos_mul_nonpos_of_pos :
      ∀ {θ : ℝ}, 0 < θ → θ ≤ π → ∃ n > (0 : ℕ), Real.cos ((n : ℝ) * θ) ≤ 0 := by
    intro θ hθ0 hθπ
    refine ⟨⌈π / 2 / θ⌉₊, by positivity, cos_nonpos_of_pi_div_two_le_of_le ?_ ?_⟩
    · grw [← Nat.le_ceil]
      simp [hθ0.ne']
    · grw [Nat.ceil_lt_add_one (by positivity), add_one_mul]
      simpa [hθ0.ne', add_comm]
  have exists_pos_cos_mul_nonpos :
      ∀ {θ : ℝ}, -π < θ → θ ≤ π → θ ≠ 0 →
        ∃ n > (0 : ℕ), Real.cos ((n : ℝ) * θ) ≤ 0 := by
    intro θ hθ₁ hθ₂ hθ
    obtain (_hθ | hθ) := hθ.lt_or_gt
    · simpa using exists_pos_cos_mul_nonpos_of_pos (θ := -θ) (by linarith) (by linarith)
    · exact exists_pos_cos_mul_nonpos_of_pos hθ hθ₂
  rw [← arg_eq_zero]
  by_contra hθ
  obtain ⟨n, hn, hcos⟩ := exists_pos_cos_mul_nonpos (neg_pi_lt_arg _) (arg_le_pi _) hθ
  have hzarg : |arg (z ^ n)| < π / 2 :=
    (mem_centeredArc (z := z ^ n) (by linarith [pi_pos])).1 (hz n hn)
  have hpow : exp ((n : ℝ) * arg z) = exp (arg (z ^ n)) := by
    rw [exp_natCast_mul, exp_arg]
    exact (exp_arg (z ^ n)).symm
  have : Real.cos ((n : ℝ) * arg z) = Real.cos (arg (z ^ n)) :=
    cos_eq_cos_of_exp_eq_exp hpow
  have hzargIoo : arg (z ^ n) ∈ Set.Ioo (-(π / 2)) (π / 2) := by
    simpa [Set.mem_Ioo] using abs_lt.mp hzarg
  linarith [cos_pos_of_mem_Ioo hzargIoo]

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

set_option backward.isDefEq.respectTransparency false in
lemma exp_eq_exp {x y : ℝ} : exp x = exp y ↔ ∃ m : ℤ, x = y + m * (2 * π) := by
  rw [Subtype.ext_iff, coe_exp, coe_exp, exp_eq_exp_iff_exists_int]
  refine exists_congr fun n => ?_
  rw [← mul_assoc, ← add_mul, mul_left_inj' I_ne_zero]
  norm_cast

lemma periodic_exp : Periodic exp (2 * π) := fun z ↦ exp_eq_exp.2 ⟨1, by rw [Int.cast_one, one_mul]⟩

@[simp] lemma exp_two_pi : exp (2 * π) = 1 := periodic_exp.eq.trans exp_zero

lemma exp_int_mul_two_pi (n : ℤ) : exp (n * (2 * π)) = 1 :=
  ext <| by simp

lemma exp_two_pi_mul_int (n : ℤ) : exp (2 * π * n) = 1 := by
  simpa only [mul_comm] using exp_int_mul_two_pi n

lemma exp_eq_one {r : ℝ} : exp r = 1 ↔ ∃ n : ℤ, r = n * (2 * π) := by
  simp [Circle.ext_iff, Complex.exp_eq_one_iff, ← mul_assoc, Complex.I_ne_zero,
    ← Complex.ofReal_inj]

lemma exp_inj {r s : ℝ} : exp r = exp s ↔ r ≡ s [PMOD (2 * π)] := by
  simp [AddCommGroup.modEq_iff_zsmul', ← exp_eq_one, div_eq_one, eq_comm (a := exp r)]

lemma exp_sub_two_pi (x : ℝ) : exp (x - 2 * π) = exp x := periodic_exp.sub_eq x
lemma exp_add_two_pi (x : ℝ) : exp (x + 2 * π) = exp x := periodic_exp x

lemma exp_injOn_of_forall_sub_mem_Ioo {s : Set ℝ}
    (hs : ∀ x ∈ s, ∀ y ∈ s, x - y ∈ Ioo (-2 * π) (2 * π)) : InjOn exp s := by
  intro t₁ ht₁ t₂ ht₂ heq
  obtain ⟨h1, h2⟩ := hs t₁ ht₁ t₂ ht₂
  rw [neg_mul] at h1
  rw [← sub_eq_zero, ← cos_eq_one_iff_of_lt_of_lt h1 h2, ← exp_ofReal_mul_I_re]
  replace heq : cexp _ = cexp _ := congrArg Subtype.val heq
  rw [exp_eq_exp_iff_exp_sub_eq_one, ← sub_mul, ← ofReal_sub, Complex.ext_iff] at heq
  exact heq.1

lemma exp_injOn_Icc {a b : ℝ} (h : b - a < 2 * π) : InjOn exp (Icc a b) :=
  exp_injOn_of_forall_sub_mem_Ioo <| fun x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ ↦ by constructor <;> linarith

lemma exp_injOn_Ico {a b : ℝ} (h : b - a ≤ 2 * π) : InjOn exp (Ico a b) :=
  exp_injOn_of_forall_sub_mem_Ioo <| fun x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ ↦ by constructor <;> linarith

lemma exp_injOn_Ioc {a b : ℝ} (h : b - a ≤ 2 * π) : InjOn exp (Ioc a b) :=
  exp_injOn_of_forall_sub_mem_Ioo <| fun x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ ↦ by constructor <;> linarith

lemma exp_surjective : Surjective exp := fun z => ⟨z.val.arg, exp_arg z⟩

instance : PathConnectedSpace Circle := exp_surjective.pathConnectedSpace exp.continuous

variable {x y : Circle}

/-- Length of the anti-clockwise arc from `x` to `y`. -/
@[grind]
noncomputable def angleDiff (x y : Circle) : ℝ :=
  if x.val.arg ≤ y.val.arg then y.val.arg - x.val.arg else 2 * π + y.val.arg - x.val.arg

@[simp]
lemma angleDiff_nonneg (x y : Circle) : 0 ≤ angleDiff x y := by
  grind [neg_pi_lt_arg y.val, arg_le_pi x.val]

lemma angleDiff_pos (h : x ≠ y) : 0 < angleDiff x y := by
  grind [arg_eq_arg, neg_pi_lt_arg y.val, arg_le_pi x.val]

lemma angleDiff_lt_two_pi (x y : Circle) : angleDiff x y < 2 * π := by
  grind [neg_pi_lt_arg x.val, arg_le_pi y.val]

@[simp]
lemma angleDiff_add_angleDiff (h : x ≠ y) : angleDiff x y + angleDiff y x = 2 * π := by
  grind [arg_eq_arg, neg_pi_lt_arg x.val, arg_le_pi y.val]

@[simp]
lemma exp_angleDiff_mul : exp (angleDiff x y) * x = y := by
  rw [← exp_arg x, ← exp_add, angleDiff]
  split_ifs with hxy <;> simp

lemma Icc_union_Icc_angleDiff_add_arg (h : x ≠ y) :
    Icc x.val.arg (angleDiff x y + x.val.arg) ∪ Icc y.val.arg (angleDiff y x + y.val.arg) =
    Icc (min x.val.arg y.val.arg) (min x.val.arg y.val.arg + 2 * π) := by
  grind [arg_eq_arg, arg_lt_arg_add_two_pi y x, arg_lt_arg_add_two_pi x y]

lemma Ico_union_Ico_angleDiff_add_arg (h : x ≠ y) :
    Ico x.val.arg (angleDiff x y + x.val.arg) ∪ Ico y.val.arg (angleDiff y x + y.val.arg) =
    Ico (min x.val.arg y.val.arg) (min x.val.arg y.val.arg + 2 * π) := by
  grind [arg_eq_arg, arg_lt_arg_add_two_pi y x, arg_lt_arg_add_two_pi x y]

lemma Ioc_union_Ioc_angleDiff_add_arg (h : x ≠ y) :
    Ioc x.val.arg (angleDiff x y + x.val.arg) ∪ Ioc y.val.arg (angleDiff y x + y.val.arg) =
    Ioc (min x.val.arg y.val.arg) (min x.val.arg y.val.arg + 2 * π) := by
  grind [arg_eq_arg, arg_lt_arg_add_two_pi y x, arg_lt_arg_add_two_pi x y]

/-- Path from `x` to `y` on the circle traversing in anti-clockwise direction. -/
noncomputable def path (x y : Circle) : Path x y :=
  (Path.segment x.val.arg <| angleDiff x y + x.val.arg).map exp.continuous
    |>.cast (by simp) (by simp)

@[simp]
lemma path_apply (x y : Circle) (a : unitInterval) :
    path x y a = exp (Path.segment x.val.arg (x.angleDiff y + x.val.arg) a) := by
  simp [path]

@[simp]
lemma coe_path (x y : Circle) : (path x y : _ → _) =
    exp ∘ ⇑(Path.segment x.val.arg (x.angleDiff y + x.val.arg)) := by
  ext t
  rw [path_apply, comp_apply]

@[simp]
lemma path_self (x : Circle) : path x x = Path.refl x := by
  ext a
  simp [path, angleDiff]

lemma path_injective_of_ne (hne : x ≠ y) : Injective (path x y) := by
  rw [coe_path]
  refine (exp_injOn_Icc (a := x.val.arg) (b := angleDiff x y + x.val.arg)
    <| by simp [angleDiff_lt_two_pi]).injective_iff _ ?_ |>.mpr
    <| Path.segment_injective_of_ne <| by simp [angleDiff_pos hne |>.ne']
  rw [Path.range_segment, segment_eq_Icc (by simp)]

lemma range_path (x y : Circle) :
    range (path x y) = exp '' Icc x.val.arg (angleDiff x y + x.val.arg) := by
  rw [coe_path, range_comp, Path.range_segment, segment_eq_Icc (by simp)]

lemma path_image_Ico_of_ne (h : x ≠ y) :
    path x y '' Ico 0 1 = exp '' Ico x.val.arg (angleDiff x y + x.val.arg) := by
  rw [coe_path, image_comp, segment_image_Ico (by simp [angleDiff_pos h])]

lemma path_image_Ioc_of_ne (h : x ≠ y) :
    path x y '' Ioc 0 1 = exp '' Ioc x.val.arg (angleDiff x y + x.val.arg) := by
  rw [coe_path, image_comp, segment_image_Ioc (by simp [angleDiff_pos h])]

lemma range_path_union_range_path (h : x ≠ y) : range (path x y) ∪ range (path y x) = univ := by
  rw [range_path, range_path, ← image_union, Icc_union_Icc_angleDiff_add_arg h,
    periodic_exp.image_Icc two_pi_pos]
  exact exp_surjective.range_eq

lemma path_image_Ioc_union (h : x ≠ y) : path x y '' Ioc 0 1 ∪ path y x '' Ioc 0 1 = univ := by
  rw [path_image_Ioc_of_ne h, path_image_Ioc_of_ne h.symm, ← image_union,
    Ioc_union_Ioc_angleDiff_add_arg h, periodic_exp.image_Ioc two_pi_pos]
  exact exp_surjective.range_eq

lemma disjoint_path_image_Ioc (h : x ≠ y) :
    Disjoint (path x y '' Ioc 0 1) (path y x '' Ioc 0 1) := by
  have hdisj : Disjoint (Ioc x.val.arg (angleDiff x y + x.val.arg))
      (Ioc y.val.arg (angleDiff y x + y.val.arg)) := by grind [angleDiff]
  rw [path_image_Ioc_of_ne h, path_image_Ioc_of_ne h.symm]
  refine Set.disjoint_image_image fun a ha b hb ↦ ?_
  refine exp_injOn_Ioc (a := min x.val.arg y.val.arg) (b := min x.val.arg y.val.arg + 2 * π)
    (by simp) |>.ne ?_ ?_ <| hdisj.ne_of_mem ha hb
  all_goals
    rw [← Ioc_union_Ioc_angleDiff_add_arg h]
    tauto

lemma compl_path_image_Ioc (h : x ≠ y) : (path x y '' Ioc 0 1)ᶜ = path y x '' Ioc 0 1 :=
  (compl_subset_iff_union.mpr <| path_image_Ioc_union h).antisymm
    <| (disjoint_path_image_Ioc h.symm).subset_compl_right

lemma compl_range_path (h : x ≠ y) : (range (path x y))ᶜ = path y x '' Ioo 0 1 := by
  rw [range_path, ← Ioc_insert_left (by simp), image_insert_eq,
    ← path_image_Ioc_of_ne h, ← union_singleton, compl_union, compl_path_image_Ioc h,
    ← Ioo_insert_right (by simp), image_insert_eq, (y.path x).target, exp_arg,
    insert_inter_of_notMem (by simp), inter_eq_left]
  rintro z ⟨t, ht, rfl⟩
  exact (path_injective_of_ne h.symm).ne ht.2.ne |>.trans_eq (y.path x).target

lemma range_path_ssubset_univ (x y : Circle) : range (path x y) ⊂ univ := by
  rw [ssubset_univ_iff_nonempty_compl]
  obtain rfl | hne := eq_or_ne x y
  · use -x, by simp [neg_ne_self]
  rw [compl_range_path hne]
  use y.path x ⟨2⁻¹, by simp only [mem_Icc, inv_nonneg, Nat.ofNat_nonneg, true_and]; linarith⟩
  refine mem_image_of_mem _ ⟨by simp [← unitInterval.coe_pos], unitInterval.coe_lt_one.mp ?_⟩
  linarith

lemma range_path_inter_range_path (h : x ≠ y) : range (path x y) ∩ range (path y x) = {x, y} := by
  rw [← image_univ, ← image_univ, unitInterval.univ_eq_Icc, ← Ioc_insert_left (by simp),
    ← Ioo_insert_right (by simp)]
  simp_rw [image_insert_eq]
  have h : Disjoint ((x.path y) '' Ioo 0 1) ((y.path x) '' Ioo 0 1) := by
    refine (disjoint_path_image_Ioc h).mono ?_ ?_ <;> exact image_mono Ioo_subset_Ioc_self
  grind

lemma isPathConnected_compl_singleton (x : Circle) : IsPathConnected {x}ᶜ := by
  refine ⟨-x, neg_ne_self x, fun y (hyx : y ≠ x) ↦ ?_⟩
  obtain hxP | hxP := (em (x ∈ range (path (-x) y))).symm
  · exact ⟨(path (-x) y), fun t ↦ by grind⟩
  refine ⟨(path y (-x)).symm, ?_⟩
  have hne : -x ≠ y := by
    rintro rfl
    simp [(neg_ne_self x).symm] at hxP
  have hP₂ : x ∉ range (path y (-x)) := by
    rintro hP₂
    have h : x ∈ range _ ∩ _ := ⟨hxP, hP₂⟩
    rw [range_path_inter_range_path hne] at h
    simp [(neg_ne_self x).symm, hyx.symm] at h
  grind

lemma not_isPreconnected_compl_pair (hxy : x ≠ y) : ¬ IsPreconnected {x, y}ᶜ := by
  simp only [isPreconnected_iff_subset_of_disjoint_closed, not_forall, not_or, exists_and_left]
  refine ⟨range (path x y), ?_, range (path y x), (isCompact_range (path x y).continuous).isClosed,
    (isCompact_range (path y x).continuous).isClosed, ?_, ?_, ?_⟩
  · rw [compl_subset_iff_union, union_eq_right.mpr (by simp only [pair_subset_iff,
      (path x y).source_mem_range, (path x y).target_mem_range, and_self])]
    exact (range_path_ssubset_univ x y).ne
  · rw [range_path_union_range_path hxy]
    exact subset_univ _
  · rw [range_path_inter_range_path hxy]
    exact compl_inter_self {x, y}
  rw [compl_subset_iff_union, union_eq_right.mpr (by simp only [pair_subset_iff,
      (path y x).source_mem_range, (path y x).target_mem_range, and_self])]
  exact (range_path_ssubset_univ y x).ne

end Circle

namespace Real.Angle

/-- `Circle.exp`, applied to a `Real.Angle`. -/
noncomputable def toCircle (θ : Angle) : Circle := Circle.periodic_exp.lift θ

@[simp] lemma toCircle_coe (x : ℝ) : toCircle x = .exp x := rfl

lemma coe_toCircle (θ : Angle) : (θ.toCircle : ℂ) = θ.cos + θ.sin * I := by
  induction θ using Angle.induction_on
  simp [exp_mul_I]

@[simp] lemma toCircle_zero : toCircle 0 = 1 := by rw [← coe_zero, toCircle_coe, Circle.exp_zero]

@[simp] lemma toCircle_neg (θ : Angle) : toCircle (-θ) = (toCircle θ)⁻¹ := by
  induction θ using Angle.induction_on
  simp_rw [← coe_neg, toCircle_coe, Circle.exp_neg]

@[simp] lemma toCircle_add (θ₁ θ₂ : Angle) : toCircle (θ₁ + θ₂) = toCircle θ₁ * toCircle θ₂ := by
  induction θ₁ using Angle.induction_on
  induction θ₂ using Angle.induction_on
  exact Circle.exp_add _ _

@[simp] lemma arg_toCircle (θ : Angle) : (arg θ.toCircle : Angle) = θ := by
  induction θ using Angle.induction_on
  rw [toCircle_coe, Circle.coe_exp, exp_mul_I, ← ofReal_cos, ← ofReal_sin, ←
    Angle.cos_coe, ← Angle.sin_coe, arg_cos_add_sin_mul_I_coe_angle]

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

@[fun_prop, continuity]
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
    IsAddQuotientCoveringMap exp (AddSubgroup.zmultiples (2 * π)) := by
  convert (isAddQuotientCoveringMap_coe _).homeomorph_comp (homeomorphCircle _)
  on_goal 2 => simp
  ext; simp [homeomorphCircle_apply, toCircle]

theorem Circle.isCoveringMap_exp : IsCoveringMap exp := isAddQuotientCoveringMap_exp.isCoveringMap

lemma isLocalHomeomorph_circleExp : IsLocalHomeomorph Circle.exp :=
  Circle.isCoveringMap_exp.isLocalHomeomorph

theorem Circle.isOpen_centeredArc (r : ℝ) : IsOpen (centeredArc r) := by
  simpa [centeredArc, abs_lt] using isLocalHomeomorph_circleExp.isOpenMap _ isOpen_Ioo

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
