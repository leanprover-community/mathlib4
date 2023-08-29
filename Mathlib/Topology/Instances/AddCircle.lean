/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Ring.AddAut
import Mathlib.GroupTheory.Divisible
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Order.Floor
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.PathConnected

#align_import topology.instances.add_circle from "leanprover-community/mathlib"@"213b0cff7bc5ab6696ee07cceec80829ce42efec"

/-!
# The additive circle

We define the additive circle `AddCircle p` as the quotient `𝕜 ⧸ (ℤ ∙ p)` for some period `p : 𝕜`.

See also `Circle` and `Real.angle`.  For the normed group structure on `AddCircle`, see
`AddCircle.NormedAddCommGroup` in a later file.

## Main definitions and results:

 * `AddCircle`: the additive circle `𝕜 ⧸ (ℤ ∙ p)` for some period `p : 𝕜`
 * `UnitAddCircle`: the special case `ℝ ⧸ ℤ`
 * `AddCircle.equivAddCircle`: the rescaling equivalence `AddCircle p ≃+ AddCircle q`
 * `AddCircle.equivIco`: the natural equivalence `AddCircle p ≃ Ico a (a + p)`
 * `AddCircle.addOrderOf_div_of_gcd_eq_one`: rational points have finite order
 * `AddCircle.exists_gcd_eq_one_of_isOfFinAddOrder`: finite-order points are rational
 * `AddCircle.homeoIccQuot`: the natural topological equivalence between `AddCircle p` and
   `Icc a (a + p)` with its endpoints identified.
 * `AddCircle.liftIco_continuous`: if `f : ℝ → B` is continuous, and `f a = f (a + p)` for
   some `a`, then there is a continuous function `AddCircle p → B` which agrees with `f` on
   `Icc a (a + p)`.

## Implementation notes:

Although the most important case is `𝕜 = ℝ` we wish to support other types of scalars, such as
the rational circle `AddCircle (1 : ℚ)`, and so we set things up more generally.

## TODO

 * Link with periodicity
 * Lie group structure
 * Exponential equivalence to `Circle`

-/


noncomputable section

open AddCommGroup Set Function AddSubgroup TopologicalSpace

open Topology

variable {𝕜 B : Type*}

section Continuity

variable [LinearOrderedAddCommGroup 𝕜] [Archimedean 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  {p : 𝕜} (hp : 0 < p) (a x : 𝕜)

theorem continuous_right_toIcoMod : ContinuousWithinAt (toIcoMod hp a) (Ici x) x := by
  intro s h
  -- ⊢ s ∈ Filter.map (toIcoMod hp a) (𝓝[Ici x] x)
  rw [Filter.mem_map, mem_nhdsWithin_iff_exists_mem_nhds_inter]
  -- ⊢ ∃ u, u ∈ 𝓝 x ∧ u ∩ Ici x ⊆ toIcoMod hp a ⁻¹' s
  haveI : Nontrivial 𝕜 := ⟨⟨0, p, hp.ne⟩⟩
  -- ⊢ ∃ u, u ∈ 𝓝 x ∧ u ∩ Ici x ⊆ toIcoMod hp a ⁻¹' s
  simp_rw [mem_nhds_iff_exists_Ioo_subset] at h ⊢
  -- ⊢ ∃ u, (∃ l u_1, x ∈ Ioo l u_1 ∧ Ioo l u_1 ⊆ u) ∧ u ∩ Ici x ⊆ toIcoMod hp a ⁻¹ …
  obtain ⟨l, u, hxI, hIs⟩ := h
  -- ⊢ ∃ u, (∃ l u_1, x ∈ Ioo l u_1 ∧ Ioo l u_1 ⊆ u) ∧ u ∩ Ici x ⊆ toIcoMod hp a ⁻¹ …
  let d := toIcoDiv hp a x • p
  -- ⊢ ∃ u, (∃ l u_1, x ∈ Ioo l u_1 ∧ Ioo l u_1 ⊆ u) ∧ u ∩ Ici x ⊆ toIcoMod hp a ⁻¹ …
  have hd := toIcoMod_mem_Ico hp a x
  -- ⊢ ∃ u, (∃ l u_1, x ∈ Ioo l u_1 ∧ Ioo l u_1 ⊆ u) ∧ u ∩ Ici x ⊆ toIcoMod hp a ⁻¹ …
  simp_rw [subset_def, mem_inter_iff]
  -- ⊢ ∃ u, (∃ l u_1, x ∈ Ioo l u_1 ∧ ∀ (x : 𝕜), x ∈ Ioo l u_1 → x ∈ u) ∧ ∀ (x_1 :  …
  refine' ⟨_, ⟨l + d, min (a + p) u + d, _, fun x => id⟩, fun y => _⟩ <;>
  -- ⊢ x ∈ Ioo (l + d) (min (a + p) u + d)
    simp_rw [← sub_mem_Ioo_iff_left, mem_Ioo, lt_min_iff]
    -- ⊢ l < x - toIcoDiv hp a x • p ∧ x - toIcoDiv hp a x • p < a + p ∧ x - toIcoDiv …
    -- ⊢ (l < y - toIcoDiv hp a x • p ∧ y - toIcoDiv hp a x • p < a + p ∧ y - toIcoDi …
  · exact ⟨hxI.1, hd.2, hxI.2⟩
    -- 🎉 no goals
  · rintro ⟨h, h'⟩
    -- ⊢ y ∈ toIcoMod hp a ⁻¹' s
    apply hIs
    -- ⊢ toIcoMod hp a y ∈ Ioo l u
    rw [← toIcoMod_sub_zsmul, (toIcoMod_eq_self _).2]
    exacts [⟨h.1, h.2.2⟩, ⟨hd.1.trans (sub_le_sub_right h' _), h.2.1⟩]
    -- 🎉 no goals
#align continuous_right_to_Ico_mod continuous_right_toIcoMod

theorem continuous_left_toIocMod : ContinuousWithinAt (toIocMod hp a) (Iic x) x := by
  rw [(funext fun y => Eq.trans (by rw [neg_neg]) <| toIocMod_neg _ _ _ :
      toIocMod hp a = (fun x => p - x) ∘ toIcoMod hp (-a) ∘ Neg.neg)]
  -- Porting note: added
  have : ContinuousNeg 𝕜 := TopologicalAddGroup.toContinuousNeg
  -- ⊢ ContinuousWithinAt ((fun x => p - x) ∘ toIcoMod hp (-a) ∘ Neg.neg) (Iic x) x
  exact
    (continuous_sub_left _).continuousAt.comp_continuousWithinAt <|
      (continuous_right_toIcoMod _ _ _).comp continuous_neg.continuousWithinAt fun y => neg_le_neg
#align continuous_left_to_Ioc_mod continuous_left_toIocMod

variable {x} (hx : (x : 𝕜 ⧸ zmultiples p) ≠ a)

theorem toIcoMod_eventuallyEq_toIocMod : toIcoMod hp a =ᶠ[𝓝 x] toIocMod hp a :=
  IsOpen.mem_nhds
      (by
        rw [Ico_eq_locus_Ioc_eq_iUnion_Ioo]
        -- ⊢ IsOpen (⋃ (z : ℤ), Ioo (a + z • p) (a + p + z • p))
        exact isOpen_iUnion fun i => isOpen_Ioo) <|
        -- 🎉 no goals
    (not_modEq_iff_toIcoMod_eq_toIocMod hp).1 <| not_modEq_iff_ne_mod_zmultiples.2 hx
#align to_Ico_mod_eventually_eq_to_Ioc_mod toIcoMod_eventuallyEq_toIocMod

theorem continuousAt_toIcoMod : ContinuousAt (toIcoMod hp a) x :=
  let h := toIcoMod_eventuallyEq_toIocMod hp a hx
  continuousAt_iff_continuous_left_right.2 <|
    ⟨(continuous_left_toIocMod hp a x).congr_of_eventuallyEq (h.filter_mono nhdsWithin_le_nhds)
        h.eq_of_nhds,
      continuous_right_toIcoMod hp a x⟩
#align continuous_at_to_Ico_mod continuousAt_toIcoMod

theorem continuousAt_toIocMod : ContinuousAt (toIocMod hp a) x :=
  let h := toIcoMod_eventuallyEq_toIocMod hp a hx
  continuousAt_iff_continuous_left_right.2 <|
    ⟨continuous_left_toIocMod hp a x,
      (continuous_right_toIcoMod hp a x).congr_of_eventuallyEq
        (h.symm.filter_mono nhdsWithin_le_nhds) h.symm.eq_of_nhds⟩
#align continuous_at_to_Ioc_mod continuousAt_toIocMod

end Continuity

/-- The "additive circle": `𝕜 ⧸ (ℤ ∙ p)`. See also `Circle` and `Real.angle`. -/
@[nolint unusedArguments]
def AddCircle [LinearOrderedAddCommGroup 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] (p : 𝕜) :=
  𝕜 ⧸ zmultiples p
#align add_circle AddCircle

-- Porting note: the following section replaces a failing `deriving` statement
section instances

variable [LinearOrderedAddCommGroup 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] (p : 𝕜)

instance : AddCommGroup (AddCircle p) :=
  inferInstanceAs (AddCommGroup (𝕜 ⧸ zmultiples p))
instance : TopologicalSpace (AddCircle p) :=
  inferInstanceAs (TopologicalSpace (𝕜 ⧸ zmultiples p))
instance : TopologicalAddGroup (AddCircle p) :=
  inferInstanceAs (TopologicalAddGroup (𝕜 ⧸ zmultiples p))
instance : Inhabited (AddCircle p) :=
  inferInstanceAs (Inhabited (𝕜 ⧸ zmultiples p))

instance : Coe 𝕜 (AddCircle p) := ⟨QuotientAddGroup.mk⟩

end instances

namespace AddCircle

section LinearOrderedAddCommGroup

variable [LinearOrderedAddCommGroup 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] (p : 𝕜)

theorem coe_nsmul {n : ℕ} {x : 𝕜} : (↑(n • x) : AddCircle p) = n • (x : AddCircle p) :=
  rfl
#align add_circle.coe_nsmul AddCircle.coe_nsmul

theorem coe_zsmul {n : ℤ} {x : 𝕜} : (↑(n • x) : AddCircle p) = n • (x : AddCircle p) :=
  rfl
#align add_circle.coe_zsmul AddCircle.coe_zsmul

theorem coe_add (x y : 𝕜) : (↑(x + y) : AddCircle p) = (x : AddCircle p) + (y : AddCircle p) :=
  rfl
#align add_circle.coe_add AddCircle.coe_add

theorem coe_sub (x y : 𝕜) : (↑(x - y) : AddCircle p) = (x : AddCircle p) - (y : AddCircle p) :=
  rfl
#align add_circle.coe_sub AddCircle.coe_sub

theorem coe_neg {x : 𝕜} : (↑(-x) : AddCircle p) = -(x : AddCircle p) :=
  rfl
#align add_circle.coe_neg AddCircle.coe_neg

theorem coe_eq_zero_iff {x : 𝕜} : (x : AddCircle p) = 0 ↔ ∃ n : ℤ, n • p = x := by
  simp [AddSubgroup.mem_zmultiples_iff]
  -- 🎉 no goals
#align add_circle.coe_eq_zero_iff AddCircle.coe_eq_zero_iff

theorem coe_eq_zero_of_pos_iff (hp : 0 < p) {x : 𝕜} (hx : 0 < x) :
    (x : AddCircle p) = 0 ↔ ∃ n : ℕ, n • p = x := by
  rw [coe_eq_zero_iff]
  -- ⊢ (∃ n, n • p = x) ↔ ∃ n, n • p = x
  constructor <;> rintro ⟨n, rfl⟩
  -- ⊢ (∃ n, n • p = x) → ∃ n, n • p = x
                  -- ⊢ ∃ n_1, n_1 • p = n • p
                  -- ⊢ ∃ n_1, n_1 • p = n • p
  · replace hx : 0 < n
    -- ⊢ 0 < n
    · contrapose! hx
      -- ⊢ n • p ≤ 0
      simpa only [← neg_nonneg, ← zsmul_neg, zsmul_neg'] using zsmul_nonneg hp.le (neg_nonneg.2 hx)
      -- 🎉 no goals
    exact ⟨n.toNat, by rw [← coe_nat_zsmul, Int.toNat_of_nonneg hx.le]⟩
    -- 🎉 no goals
  · exact ⟨(n : ℤ), by simp⟩
    -- 🎉 no goals
#align add_circle.coe_eq_zero_of_pos_iff AddCircle.coe_eq_zero_of_pos_iff

theorem coe_period : (p : AddCircle p) = 0 :=
  (QuotientAddGroup.eq_zero_iff p).2 <| mem_zmultiples p
#align add_circle.coe_period AddCircle.coe_period

/- Porting note: `simp` attribute removed because linter reports:
simp can prove this:
  by simp only [@mem_zmultiples, @QuotientAddGroup.mk_add_of_mem]
-/
theorem coe_add_period (x : 𝕜) : ((x + p : 𝕜) : AddCircle p) = x := by
  rw [coe_add, ← eq_sub_iff_add_eq', sub_self, coe_period]
  -- 🎉 no goals
#align add_circle.coe_add_period AddCircle.coe_add_period

@[continuity, nolint unusedArguments]
protected theorem continuous_mk' :
    Continuous (QuotientAddGroup.mk' (zmultiples p) : 𝕜 → AddCircle p) :=
  continuous_coinduced_rng
#align add_circle.continuous_mk' AddCircle.continuous_mk'

variable [hp : Fact (0 < p)] (a : 𝕜) [Archimedean 𝕜]

instance instCircularOrderAddCircle : CircularOrder (AddCircle p) :=
  QuotientAddGroup.circularOrder

/-- The equivalence between `AddCircle p` and the half-open interval `[a, a + p)`, whose inverse
is the natural quotient map. -/
def equivIco : AddCircle p ≃ Ico a (a + p) :=
  QuotientAddGroup.equivIcoMod hp.out a
#align add_circle.equiv_Ico AddCircle.equivIco

/-- The equivalence between `AddCircle p` and the half-open interval `(a, a + p]`, whose inverse
is the natural quotient map. -/
def equivIoc : AddCircle p ≃ Ioc a (a + p) :=
  QuotientAddGroup.equivIocMod hp.out a
#align add_circle.equiv_Ioc AddCircle.equivIoc

/-- Given a function on `𝕜`, return the unique function on `AddCircle p` agreeing with `f` on
`[a, a + p)`. -/
def liftIco (f : 𝕜 → B) : AddCircle p → B :=
  restrict _ f ∘ AddCircle.equivIco p a
#align add_circle.lift_Ico AddCircle.liftIco

/-- Given a function on `𝕜`, return the unique function on `AddCircle p` agreeing with `f` on
`(a, a + p]`. -/
def liftIoc (f : 𝕜 → B) : AddCircle p → B :=
  restrict _ f ∘ AddCircle.equivIoc p a
#align add_circle.lift_Ioc AddCircle.liftIoc

variable {p a}

theorem coe_eq_coe_iff_of_mem_Ico {x y : 𝕜} (hx : x ∈ Ico a (a + p)) (hy : y ∈ Ico a (a + p)) :
    (x : AddCircle p) = y ↔ x = y := by
  refine' ⟨fun h => _, by tauto⟩
  -- ⊢ x = y
  suffices (⟨x, hx⟩ : Ico a (a + p)) = ⟨y, hy⟩ by exact Subtype.mk.inj this
  -- ⊢ { val := x, property := hx } = { val := y, property := hy }
  apply_fun equivIco p a at h
  -- ⊢ { val := x, property := hx } = { val := y, property := hy }
  rw [← (equivIco p a).right_inv ⟨x, hx⟩, ← (equivIco p a).right_inv ⟨y, hy⟩]
  -- ⊢ Equiv.toFun (equivIco p a) (Equiv.invFun (equivIco p a) { val := x, property …
  exact h
  -- 🎉 no goals
#align add_circle.coe_eq_coe_iff_of_mem_Ico AddCircle.coe_eq_coe_iff_of_mem_Ico

theorem liftIco_coe_apply {f : 𝕜 → B} {x : 𝕜} (hx : x ∈ Ico a (a + p)) :
  liftIco p a f ↑x = f x := by
  have : (equivIco p a) x = ⟨x, hx⟩ := by
    rw [Equiv.apply_eq_iff_eq_symm_apply]
    rfl
  rw [liftIco, comp_apply, this]
  -- ⊢ restrict (Ico a (a + p)) f { val := x, property := hx } = f x
  rfl
  -- 🎉 no goals
#align add_circle.lift_Ico_coe_apply AddCircle.liftIco_coe_apply

theorem liftIoc_coe_apply {f : 𝕜 → B} {x : 𝕜} (hx : x ∈ Ioc a (a + p)) :
  liftIoc p a f ↑x = f x := by
  have : (equivIoc p a) x = ⟨x, hx⟩ := by
    rw [Equiv.apply_eq_iff_eq_symm_apply]
    rfl
  rw [liftIoc, comp_apply, this]
  -- ⊢ restrict (Ioc a (a + p)) f { val := x, property := hx } = f x
  rfl
  -- 🎉 no goals
#align add_circle.lift_Ioc_coe_apply AddCircle.liftIoc_coe_apply

variable (p a)

section Continuity

@[continuity]
theorem continuous_equivIco_symm : Continuous (equivIco p a).symm :=
  continuous_quotient_mk'.comp continuous_subtype_val
#align add_circle.continuous_equiv_Ico_symm AddCircle.continuous_equivIco_symm

@[continuity]
theorem continuous_equivIoc_symm : Continuous (equivIoc p a).symm :=
  continuous_quotient_mk'.comp continuous_subtype_val
#align add_circle.continuous_equiv_Ioc_symm AddCircle.continuous_equivIoc_symm

variable {x : AddCircle p} (hx : x ≠ a)

theorem continuousAt_equivIco : ContinuousAt (equivIco p a) x := by
  induction x using QuotientAddGroup.induction_on'
  -- ⊢ ContinuousAt ↑(equivIco p a) ↑z✝
  rw [ContinuousAt, Filter.Tendsto, QuotientAddGroup.nhds_eq, Filter.map_map]
  -- ⊢ Filter.map (↑(equivIco p a) ∘ QuotientAddGroup.mk) (𝓝 z✝) ≤ 𝓝 (↑(equivIco p  …
  exact (continuousAt_toIcoMod hp.out a hx).codRestrict _
  -- 🎉 no goals
#align add_circle.continuous_at_equiv_Ico AddCircle.continuousAt_equivIco

theorem continuousAt_equivIoc : ContinuousAt (equivIoc p a) x := by
  induction x using QuotientAddGroup.induction_on'
  -- ⊢ ContinuousAt ↑(equivIoc p a) ↑z✝
  rw [ContinuousAt, Filter.Tendsto, QuotientAddGroup.nhds_eq, Filter.map_map]
  -- ⊢ Filter.map (↑(equivIoc p a) ∘ QuotientAddGroup.mk) (𝓝 z✝) ≤ 𝓝 (↑(equivIoc p  …
  exact (continuousAt_toIocMod hp.out a hx).codRestrict _
  -- 🎉 no goals
#align add_circle.continuous_at_equiv_Ioc AddCircle.continuousAt_equivIoc

end Continuity

/-- The image of the closed-open interval `[a, a + p)` under the quotient map `𝕜 → AddCircle p` is
the entire space. -/
@[simp]
theorem coe_image_Ico_eq : ((↑) : 𝕜 → AddCircle p) '' Ico a (a + p) = univ := by
  rw [image_eq_range]
  -- ⊢ (range fun x => ↑↑x) = univ
  exact (equivIco p a).symm.range_eq_univ
  -- 🎉 no goals
#align add_circle.coe_image_Ico_eq AddCircle.coe_image_Ico_eq

/-- The image of the closed-open interval `[a, a + p)` under the quotient map `𝕜 → AddCircle p` is
the entire space. -/
@[simp]
theorem coe_image_Ioc_eq : ((↑) : 𝕜 → AddCircle p) '' Ioc a (a + p) = univ := by
  rw [image_eq_range]
  -- ⊢ (range fun x => ↑↑x) = univ
  exact (equivIoc p a).symm.range_eq_univ
  -- 🎉 no goals
#align add_circle.coe_image_Ioc_eq AddCircle.coe_image_Ioc_eq

/-- The image of the closed interval `[0, p]` under the quotient map `𝕜 → AddCircle p` is the
entire space. -/
@[simp]
theorem coe_image_Icc_eq : ((↑) : 𝕜 → AddCircle p) '' Icc a (a + p) = univ :=
  eq_top_mono (image_subset _ Ico_subset_Icc_self) <| coe_image_Ico_eq _ _
#align add_circle.coe_image_Icc_eq AddCircle.coe_image_Icc_eq

end LinearOrderedAddCommGroup

section LinearOrderedField

variable [LinearOrderedField 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] (p q : 𝕜)

/-- The rescaling equivalence between additive circles with different periods. -/
def equivAddCircle (hp : p ≠ 0) (hq : q ≠ 0) : AddCircle p ≃+ AddCircle q :=
  QuotientAddGroup.congr _ _ (AddAut.mulRight <| (Units.mk0 p hp)⁻¹ * Units.mk0 q hq) <| by
    rw [AddMonoidHom.map_zmultiples, AddMonoidHom.coe_coe, AddAut.mulRight_apply, Units.val_mul,
      Units.val_mk0, Units.val_inv_eq_inv_val, Units.val_mk0, mul_inv_cancel_left₀ hp]
#align add_circle.equiv_add_circle AddCircle.equivAddCircle

@[simp]
theorem equivAddCircle_apply_mk (hp : p ≠ 0) (hq : q ≠ 0) (x : 𝕜) :
    equivAddCircle p q hp hq (x : 𝕜) = (x * (p⁻¹ * q) : 𝕜) :=
  rfl
#align add_circle.equiv_add_circle_apply_mk AddCircle.equivAddCircle_apply_mk

@[simp]
theorem equivAddCircle_symm_apply_mk (hp : p ≠ 0) (hq : q ≠ 0) (x : 𝕜) :
    (equivAddCircle p q hp hq).symm (x : 𝕜) = (x * (q⁻¹ * p) : 𝕜) :=
  rfl
#align add_circle.equiv_add_circle_symm_apply_mk AddCircle.equivAddCircle_symm_apply_mk

variable [hp : Fact (0 < p)]

section FloorRing

variable [FloorRing 𝕜]

@[simp]
theorem coe_equivIco_mk_apply (x : 𝕜) :
    (equivIco p 0 <| QuotientAddGroup.mk x : 𝕜) = Int.fract (x / p) * p :=
  toIcoMod_eq_fract_mul _ x
#align add_circle.coe_equiv_Ico_mk_apply AddCircle.coe_equivIco_mk_apply

instance : DivisibleBy (AddCircle p) ℤ where
  div x n := (↑((n : 𝕜)⁻¹ * (equivIco p 0 x : 𝕜)) : AddCircle p)
  div_zero x := by
    simp only [algebraMap.coe_zero, Int.cast_zero, inv_zero, zero_mul, QuotientAddGroup.mk_zero]
    -- 🎉 no goals
  div_cancel {n} x hn := by
    replace hn : (n : 𝕜) ≠ 0
    -- ⊢ ↑n ≠ 0
    · norm_cast
      -- 🎉 no goals
    change n • QuotientAddGroup.mk' _ ((n : 𝕜)⁻¹ * ↑(equivIco p 0 x)) = x
    -- ⊢ n • ↑(QuotientAddGroup.mk' (zmultiples p)) ((↑n)⁻¹ * ↑(↑(equivIco p 0) x)) = x
    rw [← map_zsmul, ← smul_mul_assoc, zsmul_eq_mul, mul_inv_cancel hn, one_mul]
    -- ⊢ ↑(QuotientAddGroup.mk' (zmultiples p)) ↑(↑(equivIco p 0) x) = x
    exact (equivIco p 0).symm_apply_apply x
    -- 🎉 no goals

end FloorRing

section FiniteOrderPoints

variable {p}

theorem addOrderOf_period_div {n : ℕ} (h : 0 < n) : addOrderOf ((p / n : 𝕜) : AddCircle p) = n := by
  rw [addOrderOf_eq_iff h]
  -- ⊢ n • ↑(p / ↑n) = 0 ∧ ∀ (m : ℕ), m < n → 0 < m → m • ↑(p / ↑n) ≠ 0
  replace h : 0 < (n : 𝕜) := Nat.cast_pos.2 h
  -- ⊢ n • ↑(p / ↑n) = 0 ∧ ∀ (m : ℕ), m < n → 0 < m → m • ↑(p / ↑n) ≠ 0
  refine' ⟨_, fun m hn h0 => _⟩ <;> simp only [Ne, ← coe_nsmul, nsmul_eq_mul]
  -- ⊢ n • ↑(p / ↑n) = 0
                                    -- ⊢ ↑(↑n * (p / ↑n)) = 0
                                    -- ⊢ ¬↑(↑m * (p / ↑n)) = 0
  · rw [mul_div_cancel' _ h.ne', coe_period]
    -- 🎉 no goals
  rw [coe_eq_zero_of_pos_iff p hp.out (mul_pos (Nat.cast_pos.2 h0) <| div_pos hp.out h)]
  -- ⊢ ¬∃ n_1, n_1 • p = ↑m * (p / ↑n)
  rintro ⟨k, hk⟩
  -- ⊢ False
  rw [mul_div, eq_div_iff h.ne', nsmul_eq_mul, mul_right_comm, ← Nat.cast_mul,
    (mul_left_injective₀ hp.out.ne').eq_iff, Nat.cast_inj, mul_comm] at hk
  exact (Nat.le_of_dvd h0 ⟨_, hk.symm⟩).not_lt hn
  -- 🎉 no goals
#align add_circle.add_order_of_period_div AddCircle.addOrderOf_period_div

variable (p)

theorem gcd_mul_addOrderOf_div_eq {n : ℕ} (m : ℕ) (hn : 0 < n) :
    m.gcd n * addOrderOf (↑(↑m / ↑n * p) : AddCircle p) = n := by
  rw [mul_comm_div, ← nsmul_eq_mul, coe_nsmul, addOrderOf_nsmul'']
  -- ⊢ Nat.gcd m n * (addOrderOf ↑(p / ↑n) / Nat.gcd (addOrderOf ↑(p / ↑n)) m) = n
  · rw [addOrderOf_period_div hn, Nat.gcd_comm, Nat.mul_div_cancel']
    -- ⊢ Nat.gcd n m ∣ n
    exact n.gcd_dvd_left m
    -- 🎉 no goals
  · rw [← addOrderOf_pos_iff, addOrderOf_period_div hn]
    -- ⊢ 0 < n
    exact hn
    -- 🎉 no goals
#align add_circle.gcd_mul_add_order_of_div_eq AddCircle.gcd_mul_addOrderOf_div_eq

variable {p}

theorem addOrderOf_div_of_gcd_eq_one {m n : ℕ} (hn : 0 < n) (h : m.gcd n = 1) :
    addOrderOf (↑(↑m / ↑n * p) : AddCircle p) = n := by
  convert gcd_mul_addOrderOf_div_eq p m hn
  -- ⊢ addOrderOf ↑(↑m / ↑n * p) = Nat.gcd m n * addOrderOf ↑(↑m / ↑n * p)
  rw [h, one_mul]
  -- 🎉 no goals
#align add_circle.add_order_of_div_of_gcd_eq_one AddCircle.addOrderOf_div_of_gcd_eq_one

theorem addOrderOf_div_of_gcd_eq_one' {m : ℤ} {n : ℕ} (hn : 0 < n) (h : m.natAbs.gcd n = 1) :
    addOrderOf (↑(↑m / ↑n * p) : AddCircle p) = n := by
  induction m
  -- ⊢ addOrderOf ↑(↑(Int.ofNat a✝) / ↑n * p) = n
  · simp only [Int.ofNat_eq_coe, Int.cast_ofNat, Int.natAbs_ofNat] at h ⊢
    -- ⊢ addOrderOf ↑(↑a✝ / ↑n * p) = n
    exact addOrderOf_div_of_gcd_eq_one hn h
    -- 🎉 no goals
  · simp only [Int.cast_negSucc, neg_div, neg_mul, coe_neg, addOrderOf_neg]
    -- ⊢ addOrderOf ↑(↑(a✝ + 1) / ↑n * p) = n
    exact addOrderOf_div_of_gcd_eq_one hn h
    -- 🎉 no goals
#align add_circle.add_order_of_div_of_gcd_eq_one' AddCircle.addOrderOf_div_of_gcd_eq_one'

theorem addOrderOf_coe_rat {q : ℚ} : addOrderOf (↑(↑q * p) : AddCircle p) = q.den := by
  have : (↑(q.den : ℤ) : 𝕜) ≠ 0 := by
    norm_cast
    exact q.pos.ne.symm
  rw [← @Rat.num_den q, Rat.cast_mk_of_ne_zero _ _ this, Int.cast_ofNat, Rat.num_den,
    addOrderOf_div_of_gcd_eq_one' q.pos q.reduced]
#align add_circle.add_order_of_coe_rat AddCircle.addOrderOf_coe_rat

theorem addOrderOf_eq_pos_iff {u : AddCircle p} {n : ℕ} (h : 0 < n) :
    addOrderOf u = n ↔ ∃ m < n, m.gcd n = 1 ∧ ↑(↑m / ↑n * p) = u := by
  refine' ⟨QuotientAddGroup.induction_on' u fun k hk => _, _⟩
  -- ⊢ (∃ m, m < n ∧ Nat.gcd m n = 1 ∧ ↑(↑m / ↑n * p) = u) → addOrderOf u = n
  · rintro ⟨m, _, h₁, rfl⟩
    -- ⊢ addOrderOf ↑(↑m / ↑n * p) = n
    exact addOrderOf_div_of_gcd_eq_one h h₁
    -- 🎉 no goals
  have h0 := addOrderOf_nsmul_eq_zero (k : AddCircle p)
  -- ⊢ ∃ m, m < n ∧ Nat.gcd m n = 1 ∧ ↑(↑m / ↑n * p) = ↑k
  rw [hk, ← coe_nsmul, coe_eq_zero_iff] at h0
  -- ⊢ ∃ m, m < n ∧ Nat.gcd m n = 1 ∧ ↑(↑m / ↑n * p) = ↑k
  obtain ⟨a, ha⟩ := h0
  -- ⊢ ∃ m, m < n ∧ Nat.gcd m n = 1 ∧ ↑(↑m / ↑n * p) = ↑k
  have h0 : (_ : 𝕜) ≠ 0 := Nat.cast_ne_zero.2 h.ne'
  -- ⊢ ∃ m, m < n ∧ Nat.gcd m n = 1 ∧ ↑(↑m / ↑n * p) = ↑k
  rw [nsmul_eq_mul, mul_comm, ← div_eq_iff h0, ← a.ediv_add_emod' n, add_smul, add_div,
    zsmul_eq_mul, Int.cast_mul, Int.cast_ofNat, mul_assoc, ← mul_div, mul_comm _ p,
    mul_div_cancel p h0] at ha
  have han : _ = a % n := Int.toNat_of_nonneg (Int.emod_nonneg _ <| by exact_mod_cast h.ne')
  -- ⊢ ∃ m, m < n ∧ Nat.gcd m n = 1 ∧ ↑(↑m / ↑n * p) = ↑k
  have he : (↑(↑((a % n).toNat) / ↑n * p) : AddCircle p) = k
  -- ⊢ ↑(↑(Int.toNat (a % ↑n)) / ↑n * p) = ↑k
  · convert congr_arg (QuotientAddGroup.mk : 𝕜 → (AddCircle p)) ha using 1
    -- ⊢ ↑(↑(Int.toNat (a % ↑n)) / ↑n * p) = ↑(↑(a / ↑n) * p + (a % ↑n) • p / ↑n)
    rw [coe_add, ← Int.cast_ofNat, han, zsmul_eq_mul, mul_div_right_comm, eq_comm, add_left_eq_self,
      ←zsmul_eq_mul, coe_zsmul, coe_period, smul_zero]
  refine' ⟨(a % n).toNat, _, _, he⟩
  -- ⊢ Int.toNat (a % ↑n) < n
  · rw [← Int.ofNat_lt, han]
    -- ⊢ a % ↑n < ↑n
    exact Int.emod_lt_of_pos _ (Int.ofNat_lt.2 h)
    -- 🎉 no goals
  · have := (gcd_mul_addOrderOf_div_eq p (Int.toNat (a % ↑n)) h).trans
      ((congr_arg addOrderOf he).trans hk).symm
    rw [he, Nat.mul_left_eq_self_iff] at this
    -- ⊢ Nat.gcd (Int.toNat (a % ↑n)) n = 1
    · exact this
      -- 🎉 no goals
    · rwa [hk]
      -- 🎉 no goals
#align add_circle.add_order_of_eq_pos_iff AddCircle.addOrderOf_eq_pos_iff

theorem exists_gcd_eq_one_of_isOfFinAddOrder {u : AddCircle p} (h : IsOfFinAddOrder u) :
    ∃ m : ℕ, m.gcd (addOrderOf u) = 1 ∧ m < addOrderOf u ∧ ↑((m : 𝕜) / addOrderOf u * p) = u :=
  let ⟨m, hl, hg, he⟩ := (addOrderOf_eq_pos_iff <| addOrderOf_pos' h).1 rfl
  ⟨m, hg, hl, he⟩
#align add_circle.exists_gcd_eq_one_of_is_of_fin_add_order AddCircle.exists_gcd_eq_one_of_isOfFinAddOrder

variable (p)

/-- The natural bijection between points of order `n` and natural numbers less than and coprime to
`n`. The inverse of the map sends `m ↦ (m/n * p : AddCircle p)` where `m` is coprime to `n` and
satisfies `0 ≤ m < n`. -/
def setAddOrderOfEquiv {n : ℕ} (hn : 0 < n) :
    { u : AddCircle p | addOrderOf u = n } ≃ { m | m < n ∧ m.gcd n = 1 } :=
  Equiv.symm <|
    Equiv.ofBijective (fun m => ⟨↑((m : 𝕜) / n * p), addOrderOf_div_of_gcd_eq_one hn m.prop.2⟩)
      (by
        refine' ⟨fun m₁ m₂ h => Subtype.ext _, fun u => _⟩
        -- ⊢ ↑m₁ = ↑m₂
        · simp_rw [Subtype.ext_iff] at h
          -- ⊢ ↑m₁ = ↑m₂
          rw [← sub_eq_zero, ← coe_sub, ← sub_mul, ← sub_div, ← Int.cast_ofNat m₁,
            ← Int.cast_ofNat m₂, ← Int.cast_sub, coe_eq_zero_iff] at h
          obtain ⟨m, hm⟩ := h
          -- ⊢ ↑m₁ = ↑m₂
          rw [← mul_div_right_comm, eq_div_iff, mul_comm, ← zsmul_eq_mul, mul_smul_comm, ←
            nsmul_eq_mul, ← coe_nat_zsmul, smul_smul,
            (zsmul_strictMono_left hp.out).injective.eq_iff, mul_comm] at hm
          swap
          -- ⊢ ↑n ≠ 0
          · exact Nat.cast_ne_zero.2 hn.ne'
            -- 🎉 no goals
          rw [← @Nat.cast_inj ℤ, ← sub_eq_zero]
          -- ⊢ ↑↑m₁ - ↑↑m₂ = 0
          refine' Int.eq_zero_of_abs_lt_dvd ⟨_, hm.symm⟩ (abs_sub_lt_iff.2 ⟨_, _⟩) <;>
          -- ⊢ ↑↑m₁ - ↑↑m₂ < ↑n
            apply (Int.sub_le_self _ <| Nat.cast_nonneg _).trans_lt (Nat.cast_lt.2 _)
            -- ⊢ ↑m₁ < n
            -- ⊢ ↑m₂ < n
          exacts [m₁.2.1, m₂.2.1]
          -- 🎉 no goals
        obtain ⟨m, hmn, hg, he⟩ := (addOrderOf_eq_pos_iff hn).mp u.2
        -- ⊢ ∃ a, (fun m => { val := ↑(↑↑m / ↑n * p), property := (_ : addOrderOf ↑(↑↑m / …
        exact ⟨⟨m, hmn, hg⟩, Subtype.ext he⟩)
        -- 🎉 no goals
#align add_circle.set_add_order_of_equiv AddCircle.setAddOrderOfEquiv

@[simp]
theorem card_addOrderOf_eq_totient {n : ℕ} :
    Nat.card { u : AddCircle p // addOrderOf u = n } = n.totient := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  -- ⊢ Nat.card { u // addOrderOf u = 0 } = Nat.totient 0
  · simp only [Nat.totient_zero, addOrderOf_eq_zero_iff]
    -- ⊢ Nat.card { u // ¬IsOfFinAddOrder u } = 0
    rcases em (∃ u : AddCircle p, ¬IsOfFinAddOrder u) with (⟨u, hu⟩ | h)
    -- ⊢ Nat.card { u // ¬IsOfFinAddOrder u } = 0
    · have : Infinite { u : AddCircle p // ¬IsOfFinAddOrder u } := by
        erw [infinite_coe_iff]
        exact infinite_not_isOfFinAddOrder hu
      exact Nat.card_eq_zero_of_infinite
      -- 🎉 no goals
    · have : IsEmpty { u : AddCircle p // ¬IsOfFinAddOrder u } := by simpa using h
      -- ⊢ Nat.card { u // ¬IsOfFinAddOrder u } = 0
      exact Nat.card_of_isEmpty
      -- 🎉 no goals
  · rw [← coe_setOf, Nat.card_congr (setAddOrderOfEquiv p hn),
      n.totient_eq_card_lt_and_coprime]
    simp only [Nat.gcd_comm]
    -- 🎉 no goals
#align add_circle.card_add_order_of_eq_totient AddCircle.card_addOrderOf_eq_totient

theorem finite_setOf_add_order_eq {n : ℕ} (hn : 0 < n) :
    { u : AddCircle p | addOrderOf u = n }.Finite :=
  finite_coe_iff.mp <|
    Nat.finite_of_card_ne_zero <| by
      simpa only [coe_setOf, card_addOrderOf_eq_totient p] using (Nat.totient_pos hn).ne'
      -- 🎉 no goals
#align add_circle.finite_set_of_add_order_eq AddCircle.finite_setOf_add_order_eq

end FiniteOrderPoints

end LinearOrderedField

variable (p : ℝ)

instance pathConnectedSpace : PathConnectedSpace $ AddCircle p :=
  (inferInstance : PathConnectedSpace (Quotient _))

/-- The "additive circle" `ℝ ⧸ (ℤ ∙ p)` is compact. -/
instance compactSpace [Fact (0 < p)] : CompactSpace <| AddCircle p := by
  rw [← isCompact_univ_iff, ← coe_image_Icc_eq p 0]
  -- ⊢ IsCompact (QuotientAddGroup.mk '' Icc 0 (0 + p))
  exact isCompact_Icc.image (AddCircle.continuous_mk' p)
  -- 🎉 no goals
#align add_circle.compact_space AddCircle.compactSpace

/-- The action on `ℝ` by right multiplication of its the subgroup `zmultiples p` (the multiples of
`p:ℝ`) is properly discontinuous. -/
instance : ProperlyDiscontinuousVAdd (AddSubgroup.opposite (zmultiples p)) ℝ :=
  (zmultiples p).properlyDiscontinuousVAdd_opposite_of_tendsto_cofinite
    (AddSubgroup.tendsto_zmultiples_subtype_cofinite p)

/-- The "additive circle" `ℝ ⧸ (ℤ ∙ p)` is Hausdorff. -/
instance : T2Space (AddCircle p) :=
  t2Space_of_properlyDiscontinuousVAdd_of_t2Space

/-- The "additive circle" `ℝ ⧸ (ℤ ∙ p)` is normal. -/
instance [Fact (0 < p)] : NormalSpace (AddCircle p) :=
  normalOfCompactT2

/-- The "additive circle" `ℝ ⧸ (ℤ ∙ p)` is second-countable. -/
instance : SecondCountableTopology (AddCircle p) :=
  QuotientAddGroup.secondCountableTopology

end AddCircle

attribute [local instance] Real.fact_zero_lt_one

/- ./././Mathport/Syntax/Translate/Command.lean:328:31: unsupported: @[derive] abbrev -/
/-- The unit circle `ℝ ⧸ ℤ`. -/
abbrev UnitAddCircle :=
  AddCircle (1 : ℝ)
#align unit_add_circle UnitAddCircle

section IdentifyIccEnds

/-! This section proves that for any `a`, the natural map from `[a, a + p] ⊂ 𝕜` to `AddCircle p`
gives an identification of `AddCircle p`, as a topological space, with the quotient of `[a, a + p]`
by the equivalence relation identifying the endpoints. -/


namespace AddCircle

variable [LinearOrderedAddCommGroup 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] (p a : 𝕜)
  [hp : Fact (0 < p)]

local notation "𝕋" => AddCircle p

/-- The relation identifying the endpoints of `Icc a (a + p)`. -/
inductive EndpointIdent : Icc a (a + p) → Icc a (a + p) → Prop
  | mk :
    EndpointIdent ⟨a, left_mem_Icc.mpr <| le_add_of_nonneg_right hp.out.le⟩
      ⟨a + p, right_mem_Icc.mpr <| le_add_of_nonneg_right hp.out.le⟩
#align add_circle.endpoint_ident AddCircle.EndpointIdent

variable [Archimedean 𝕜]

/-- The equivalence between `AddCircle p` and the quotient of `[a, a + p]` by the relation
identifying the endpoints. -/
def equivIccQuot : 𝕋 ≃ Quot (EndpointIdent p a) where
  toFun x := Quot.mk _ <| inclusion Ico_subset_Icc_self (equivIco _ _ x)
  invFun x :=
    Quot.liftOn x (↑) <| by
      rintro _ _ ⟨_⟩
      -- ⊢ (fun x => ↑↑x) { val := a, property := (_ : a ∈ Icc a (a + p)) } = (fun x => …
      exact (coe_add_period p a).symm
      -- 🎉 no goals
  left_inv := (equivIco p a).symm_apply_apply
  right_inv :=
    Quot.ind <| by
      rintro ⟨x, hx⟩
      -- ⊢ (fun x => Quot.mk (EndpointIdent p a) (Set.inclusion (_ : Ico a (a + p) ⊆ Ic …
      rcases ne_or_eq x (a + p) with (h | rfl)
      -- ⊢ (fun x => Quot.mk (EndpointIdent p a) (Set.inclusion (_ : Ico a (a + p) ⊆ Ic …
      · revert x
        -- ⊢ ∀ (x : 𝕜) (hx : x ∈ Icc a (a + p)), x ≠ a + p → (fun x => Quot.mk (EndpointI …
        dsimp only
        -- ⊢ ∀ (x : 𝕜) (hx : x ∈ Icc a (a + p)), x ≠ a + p → Quot.mk (EndpointIdent p a)  …
        intro x hx h
        -- ⊢ Quot.mk (EndpointIdent p a) (Set.inclusion (_ : Ico a (a + p) ⊆ Icc a (a + p …
        congr
        -- ⊢ Set.inclusion (_ : Ico a (a + p) ⊆ Icc a (a + p)) (↑(equivIco p a) (Quot.lif …
        ext1
        -- ⊢ ↑(Set.inclusion (_ : Ico a (a + p) ⊆ Icc a (a + p)) (↑(equivIco p a) (Quot.l …
        apply congr_arg Subtype.val ((equivIco p a).right_inv ⟨x, hx.1, hx.2.lt_of_ne h⟩)
        -- 🎉 no goals
      · rw [← Quot.sound EndpointIdent.mk]
        -- ⊢ (fun x => Quot.mk (EndpointIdent p a) (Set.inclusion (_ : Ico a (a + p) ⊆ Ic …
        dsimp only
        -- ⊢ Quot.mk (EndpointIdent p a) (Set.inclusion (_ : Ico a (a + p) ⊆ Icc a (a + p …
        congr
        -- ⊢ Set.inclusion (_ : Ico a (a + p) ⊆ Icc a (a + p)) (↑(equivIco p a) (Quot.lif …
        ext1
        -- ⊢ ↑(Set.inclusion (_ : Ico a (a + p) ⊆ Icc a (a + p)) (↑(equivIco p a) (Quot.l …
        apply congr_arg Subtype.val
          ((equivIco p a).right_inv ⟨a, le_refl a, lt_add_of_pos_right a hp.out⟩)
#align add_circle.equiv_Icc_quot AddCircle.equivIccQuot

theorem equivIccQuot_comp_mk_eq_toIcoMod :
    equivIccQuot p a ∘ Quotient.mk'' = fun x =>
      Quot.mk _ ⟨toIcoMod hp.out a x, Ico_subset_Icc_self <| toIcoMod_mem_Ico _ _ x⟩ :=
  rfl
#align add_circle.equiv_Icc_quot_comp_mk_eq_to_Ico_mod AddCircle.equivIccQuot_comp_mk_eq_toIcoMod

theorem equivIccQuot_comp_mk_eq_toIocMod :
    equivIccQuot p a ∘ Quotient.mk'' = fun x =>
      Quot.mk _ ⟨toIocMod hp.out a x, Ioc_subset_Icc_self <| toIocMod_mem_Ioc _ _ x⟩ := by
  rw [equivIccQuot_comp_mk_eq_toIcoMod]
  -- ⊢ (fun x => Quot.mk (EndpointIdent p a) { val := toIcoMod (_ : 0 < p) a x, pro …
  funext x
  -- ⊢ Quot.mk (EndpointIdent p a) { val := toIcoMod (_ : 0 < p) a x, property := ( …
  by_cases a ≡ x [PMOD p]
  -- ⊢ Quot.mk (EndpointIdent p a) { val := toIcoMod (_ : 0 < p) a x, property := ( …
  -- ⊢ Quot.mk (EndpointIdent p a) { val := toIcoMod (_ : 0 < p) a x, property := ( …
  · simp_rw [(modEq_iff_toIcoMod_eq_left hp.out).1 h, (modEq_iff_toIocMod_eq_right hp.out).1 h]
    -- ⊢ Quot.mk (EndpointIdent p a) { val := a, property := (_ : (fun x => x ∈ Icc a …
    exact Quot.sound EndpointIdent.mk
    -- 🎉 no goals
  · simp_rw [(not_modEq_iff_toIcoMod_eq_toIocMod hp.out).1 h]
    -- 🎉 no goals
#align add_circle.equiv_Icc_quot_comp_mk_eq_to_Ioc_mod AddCircle.equivIccQuot_comp_mk_eq_toIocMod

/-- The natural map from `[a, a + p] ⊂ 𝕜` with endpoints identified to `𝕜 / ℤ • p`, as a
homeomorphism of topological spaces. -/
def homeoIccQuot : 𝕋 ≃ₜ Quot (EndpointIdent p a) where
  toEquiv := equivIccQuot p a
  continuous_toFun := by
    -- Porting note: was `simp_rw`
    rw [quotientMap_quotient_mk'.continuous_iff]
    -- ⊢ Continuous ((equivIccQuot p a).toFun ∘ Quotient.mk')
    simp_rw [continuous_iff_continuousAt,
      continuousAt_iff_continuous_left_right]
    intro x; constructor
    -- ⊢ ContinuousWithinAt ((equivIccQuot p a).toFun ∘ Quotient.mk') (Iic x) x ∧ Con …
             -- ⊢ ContinuousWithinAt ((equivIccQuot p a).toFun ∘ Quotient.mk') (Iic x) x
    on_goal 1 => erw [equivIccQuot_comp_mk_eq_toIocMod]
    -- ⊢ ContinuousWithinAt (fun x => Quot.mk (EndpointIdent p a) { val := toIocMod ( …
    -- ⊢ ContinuousWithinAt (fun x => Quot.mk (EndpointIdent p a) { val := toIocMod ( …
    on_goal 2 => erw [equivIccQuot_comp_mk_eq_toIcoMod]
    -- ⊢ ContinuousWithinAt (fun x => Quot.mk (EndpointIdent p a) { val := toIocMod ( …
    -- ⊢ ContinuousWithinAt (fun x => Quot.mk (EndpointIdent p a) { val := toIocMod ( …
    all_goals
      apply continuous_quot_mk.continuousAt.comp_continuousWithinAt
      rw [inducing_subtype_val.continuousWithinAt_iff]
    · apply continuous_left_toIocMod
      -- 🎉 no goals
    · apply continuous_right_toIcoMod
      -- 🎉 no goals
  continuous_invFun :=
    continuous_quot_lift _ ((AddCircle.continuous_mk' p).comp continuous_subtype_val)
#align add_circle.homeo_Icc_quot AddCircle.homeoIccQuot

/-! We now show that a continuous function on `[a, a + p]` satisfying `f a = f (a + p)` is the
pullback of a continuous function on `AddCircle p`. -/


variable {p a}

theorem liftIco_eq_lift_Icc {f : 𝕜 → B} (h : f a = f (a + p)) :
    liftIco p a f =
      Quot.lift (restrict (Icc a <| a + p) f)
          (by
            rintro _ _ ⟨_⟩
            -- ⊢ restrict (Icc a (a + p)) f { val := a, property := (_ : a ∈ Icc a (a + p)) } …
            exact h) ∘
            -- 🎉 no goals
        equivIccQuot p a :=
  rfl
#align add_circle.lift_Ico_eq_lift_Icc AddCircle.liftIco_eq_lift_Icc

theorem liftIco_continuous [TopologicalSpace B] {f : 𝕜 → B} (hf : f a = f (a + p))
    (hc : ContinuousOn f <| Icc a (a + p)) : Continuous (liftIco p a f) := by
  rw [liftIco_eq_lift_Icc hf]
  -- ⊢ Continuous (Quot.lift (restrict (Icc a (a + p)) f) (_ : ∀ (a_1 b : ↑(Icc a ( …
  refine' Continuous.comp _ (homeoIccQuot p a).continuous_toFun
  -- ⊢ Continuous (Quot.lift (restrict (Icc a (a + p)) f) (_ : ∀ (a_1 b : ↑(Icc a ( …
  exact continuous_coinduced_dom.mpr (continuousOn_iff_continuous_restrict.mp hc)
  -- 🎉 no goals
#align add_circle.lift_Ico_continuous AddCircle.liftIco_continuous

section ZeroBased

theorem liftIco_zero_coe_apply {f : 𝕜 → B} {x : 𝕜} (hx : x ∈ Ico 0 p) : liftIco p 0 f ↑x = f x :=
  liftIco_coe_apply (by rwa [zero_add])
                        -- 🎉 no goals
#align add_circle.lift_Ico_zero_coe_apply AddCircle.liftIco_zero_coe_apply

theorem liftIco_zero_continuous [TopologicalSpace B] {f : 𝕜 → B} (hf : f 0 = f p)
    (hc : ContinuousOn f <| Icc 0 p) : Continuous (liftIco p 0 f) :=
  liftIco_continuous (by rwa [zero_add] : f 0 = f (0 + p)) (by rwa [zero_add])
                         -- 🎉 no goals
                                                               -- 🎉 no goals
#align add_circle.lift_Ico_zero_continuous AddCircle.liftIco_zero_continuous

end ZeroBased

end AddCircle

end IdentifyIccEnds
