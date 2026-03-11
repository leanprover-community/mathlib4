/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Order.Group.Pointwise.Interval
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Topology.Perfect

/-!
# Normed division rings and fields

In this file we define normed fields, and (more generally) normed division rings. We also prove
some theorems about these definitions.

Some useful results that relate the topology of the normed field to the discrete topology include:
* `norm_eq_one_iff_ne_zero_of_discrete`

Methods for constructing a normed field instance from a given real absolute value on a field are
given in:
* AbsoluteValue.toNormedField
-/

@[expose] public section

-- Guard against import creep.
assert_not_exists AddChar comap_norm_atTop DilationEquiv Finset.sup_mul_le_mul_sup_of_nonneg
  IsOfFinOrder Isometry.norm_map_of_map_one NNReal.isOpen_Ico_zero Rat.norm_cast_real
  RestrictScalars

variable {G α β ι : Type*}

open Filter
open scoped Topology NNReal ENNReal

/-- A normed division ring is a division ring endowed with a seminorm which satisfies the equality
`‖x y‖ = ‖x‖ ‖y‖`. -/
class NormedDivisionRing (α : Type*) extends Norm α, DivisionRing α, MetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = norm (-x + y)
  /-- The norm is multiplicative. -/
  protected norm_mul : ∀ a b, norm (a * b) = norm a * norm b

-- see Note [lower instance priority]
/-- A normed division ring is a normed ring. -/
instance (priority := 100) NormedDivisionRing.toNormedRing [β : NormedDivisionRing α] :
    NormedRing α :=
  { β with norm_mul_le a b := (NormedDivisionRing.norm_mul a b).le }

-- see Note [lower instance priority]
/-- The norm on a normed division ring is strictly multiplicative. -/
instance (priority := 100) NormedDivisionRing.toNormMulClass [NormedDivisionRing α] :
    NormMulClass α where
  norm_mul := NormedDivisionRing.norm_mul

section NormedDivisionRing

variable [NormedDivisionRing α] {a b : α}

instance (priority := 900) NormedDivisionRing.to_normOneClass : NormOneClass α :=
  ⟨mul_left_cancel₀ (mt norm_eq_zero.1 (one_ne_zero' α)) <| by rw [← norm_mul, mul_one, mul_one]⟩

@[simp]
theorem norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖ :=
  map_div₀ (normHom : α →*₀ ℝ) a b

@[simp]
theorem nnnorm_div (a b : α) : ‖a / b‖₊ = ‖a‖₊ / ‖b‖₊ :=
  map_div₀ (nnnormHom : α →*₀ ℝ≥0) a b

@[simp]
theorem norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹ :=
  map_inv₀ (normHom : α →*₀ ℝ) a

@[simp]
theorem nnnorm_inv (a : α) : ‖a⁻¹‖₊ = ‖a‖₊⁻¹ :=
  NNReal.eq <| by simp

@[simp]
lemma enorm_inv {a : α} (ha : a ≠ 0) : ‖a⁻¹‖ₑ = ‖a‖ₑ⁻¹ := by simp [enorm, ENNReal.coe_inv, ha]

@[simp]
theorem norm_zpow : ∀ (a : α) (n : ℤ), ‖a ^ n‖ = ‖a‖ ^ n :=
  map_zpow₀ (normHom : α →*₀ ℝ)

@[simp]
theorem nnnorm_zpow : ∀ (a : α) (n : ℤ), ‖a ^ n‖₊ = ‖a‖₊ ^ n :=
  map_zpow₀ (nnnormHom : α →*₀ ℝ≥0)

theorem dist_inv_inv₀ {z w : α} (hz : z ≠ 0) (hw : w ≠ 0) :
    dist z⁻¹ w⁻¹ = dist z w / (‖z‖ * ‖w‖) := by
  rw [dist_eq_norm, inv_sub_inv' hz hw, norm_mul, norm_mul, norm_inv, norm_inv, mul_comm ‖z‖⁻¹,
    mul_assoc, dist_eq_norm', div_eq_mul_inv, mul_inv]

theorem nndist_inv_inv₀ {z w : α} (hz : z ≠ 0) (hw : w ≠ 0) :
    nndist z⁻¹ w⁻¹ = nndist z w / (‖z‖₊ * ‖w‖₊) :=
  NNReal.eq <| dist_inv_inv₀ hz hw

lemma norm_commutator_sub_one_le (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖a * b * a⁻¹ * b⁻¹ - 1‖ ≤ 2 * ‖a‖⁻¹ * ‖b‖⁻¹ * ‖a - 1‖ * ‖b - 1‖ := by
  simpa using norm_commutator_units_sub_one_le (.mk0 a ha) (.mk0 b hb)

lemma nnnorm_commutator_sub_one_le (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖a * b * a⁻¹ * b⁻¹ - 1‖₊ ≤ 2 * ‖a‖₊⁻¹ * ‖b‖₊⁻¹ * ‖a - 1‖₊ * ‖b - 1‖₊ := by
  simpa using nnnorm_commutator_units_sub_one_le (.mk0 a ha) (.mk0 b hb)

namespace NormedDivisionRing

section Discrete

variable {𝕜 : Type*} [NormedDivisionRing 𝕜] [DiscreteTopology 𝕜]

lemma norm_eq_one_iff_ne_zero_of_discrete {x : 𝕜} : ‖x‖ = 1 ↔ x ≠ 0 := by
  constructor <;> intro hx
  · contrapose! hx
    simp [hx]
  · have : IsOpen {(0 : 𝕜)} := isOpen_discrete {0}
    simp_rw [Metric.isOpen_singleton_iff, dist_eq_norm, sub_zero] at this
    obtain ⟨ε, εpos, h'⟩ := this
    wlog! h : ‖x‖ < 1 generalizing 𝕜 with H
    · rcases h.eq_or_lt with h | h
      · rw [h]
      replace h := norm_inv x ▸ inv_lt_one_of_one_lt₀ h
      rw [← inv_inj, inv_one, ← norm_inv]
      exact H (by simpa) h' h
    obtain ⟨k, hk⟩ : ∃ k : ℕ, ‖x‖ ^ k < ε := exists_pow_lt_of_lt_one εpos h
    rw [← norm_pow] at hk
    specialize h' _ hk
    simp [hx] at h'

@[simp]
lemma norm_le_one_of_discrete
    (x : 𝕜) : ‖x‖ ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · simp [norm_eq_one_iff_ne_zero_of_discrete.mpr hx]

lemma unitClosedBall_eq_univ_of_discrete : (Metric.closedBall 0 1 : Set 𝕜) = Set.univ := by
  ext
  simp

end Discrete

end NormedDivisionRing

end NormedDivisionRing

/-- A normed field is a field with a norm satisfying ‖x y‖ = ‖x‖ ‖y‖. -/
class NormedField (α : Type*) extends Norm α, Field α, MetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = norm (-x + y)
  /-- The norm is multiplicative. -/
  protected norm_mul : ∀ a b, norm (a * b) = norm a * norm b

/-- A nontrivially normed field is a normed field in which there is an element of norm different
from `0` and `1`. This makes it possible to bring any element arbitrarily close to `0` by
multiplication by the powers of any element, and thus to relate algebra and topology. -/
class NontriviallyNormedField (α : Type*) extends NormedField α where
  /-- The norm attains a value exceeding 1. -/
  non_trivial : ∃ x : α, 1 < ‖x‖

/-- A densely normed field is a normed field for which the image of the norm is dense in `ℝ≥0`,
which means it is also nontrivially normed. However, not all nontrivially normed fields are densely
normed; in particular, the `Padic`s exhibit this fact. -/
class DenselyNormedField (α : Type*) extends NormedField α where
  /-- The range of the norm is dense in the collection of nonnegative real numbers. -/
  lt_norm_lt : ∀ x y : ℝ, 0 ≤ x → x < y → ∃ a : α, x < ‖a‖ ∧ ‖a‖ < y

section NormedField

/-- A densely normed field is always a nontrivially normed field.
See note [lower instance priority]. -/
instance (priority := 100) DenselyNormedField.toNontriviallyNormedField [DenselyNormedField α] :
    NontriviallyNormedField α where
  non_trivial :=
    let ⟨a, h, _⟩ := DenselyNormedField.lt_norm_lt 1 2 zero_le_one one_lt_two
    ⟨a, h⟩

variable [NormedField α]

-- see Note [lower instance priority]
instance (priority := 100) NormedField.toNormedDivisionRing : NormedDivisionRing α :=
  { ‹NormedField α› with }

-- see Note [lower instance priority]
instance (priority := 100) NormedField.toNormedCommRing : NormedCommRing α :=
  { ‹NormedField α› with norm_mul_le a b := (norm_mul a b).le }

end NormedField

namespace NormedField

section Nontrivially

variable (α) [NontriviallyNormedField α]

theorem exists_one_lt_norm : ∃ x : α, 1 < ‖x‖ :=
  ‹NontriviallyNormedField α›.non_trivial

theorem exists_one_lt_nnnorm : ∃ x : α, 1 < ‖x‖₊ := exists_one_lt_norm α

theorem exists_one_lt_enorm : ∃ x : α, 1 < ‖x‖ₑ :=
  exists_one_lt_nnnorm α |>.imp fun _ => ENNReal.coe_lt_coe.mpr

theorem exists_lt_norm (r : ℝ) : ∃ x : α, r < ‖x‖ :=
  let ⟨w, hw⟩ := exists_one_lt_norm α
  let ⟨n, hn⟩ := pow_unbounded_of_one_lt r hw
  ⟨w ^ n, by rwa [norm_pow]⟩

theorem exists_lt_nnnorm (r : ℝ≥0) : ∃ x : α, r < ‖x‖₊ := exists_lt_norm α r

theorem exists_lt_enorm {r : ℝ≥0∞} (hr : r ≠ ∞) : ∃ x : α, r < ‖x‖ₑ := by
  lift r to ℝ≥0 using hr
  exact mod_cast exists_lt_nnnorm α r

theorem exists_norm_lt {r : ℝ} (hr : 0 < r) : ∃ x : α, 0 < ‖x‖ ∧ ‖x‖ < r :=
  let ⟨w, hw⟩ := exists_lt_norm α r⁻¹
  ⟨w⁻¹, by rwa [← Set.mem_Ioo, norm_inv, ← Set.mem_inv, Set.inv_Ioo_0_left hr]⟩

theorem exists_nnnorm_lt {r : ℝ≥0} (hr : 0 < r) : ∃ x : α, 0 < ‖x‖₊ ∧ ‖x‖₊ < r :=
  exists_norm_lt α hr

/-- TODO: merge with `_root_.exists_enorm_lt`. -/
theorem exists_enorm_lt {r : ℝ≥0∞} (hr : 0 < r) : ∃ x : α, 0 < ‖x‖ₑ ∧ ‖x‖ₑ < r :=
  match r with
  | ∞ => exists_one_lt_enorm α |>.imp fun _ hx => ⟨zero_le_one.trans_lt hx, ENNReal.coe_lt_top⟩
  | (r : ℝ≥0) => exists_nnnorm_lt α (ENNReal.coe_pos.mp hr) |>.imp fun _ =>
    And.imp ENNReal.coe_pos.mpr ENNReal.coe_lt_coe.mpr

theorem exists_norm_lt_one : ∃ x : α, 0 < ‖x‖ ∧ ‖x‖ < 1 :=
  exists_norm_lt α one_pos

theorem exists_nnnorm_lt_one : ∃ x : α, 0 < ‖x‖₊ ∧ ‖x‖₊ < 1 := exists_norm_lt_one _

theorem exists_enorm_lt_one : ∃ x : α, 0 < ‖x‖ₑ ∧ ‖x‖ₑ < 1 := exists_enorm_lt _ one_pos

variable {α}

@[instance]
theorem instPerfectSpace : PerfectSpace α := by
  intro x
  rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
  rintro ε ε0
  rcases exists_norm_lt α ε0 with ⟨b, hb0, hbε⟩
  refine ⟨x + b, mt (Set.mem_singleton_iff.trans add_eq_left).1 <| norm_pos_iff.1 hb0, ?_⟩
  rwa [dist_comm, dist_eq_norm, add_sub_cancel_left]

@[instance]
theorem nhdsWithin_isUnit_neBot : NeBot (𝓝[{ x : α | IsUnit x }] 0) := by
  simpa only [isUnit_iff_ne_zero] using instPerfectSpace (0 : α)

end Nontrivially

section Densely

variable (α) [DenselyNormedField α]

theorem exists_lt_norm_lt {r₁ r₂ : ℝ} (h₀ : 0 ≤ r₁) (h : r₁ < r₂) : ∃ x : α, r₁ < ‖x‖ ∧ ‖x‖ < r₂ :=
  DenselyNormedField.lt_norm_lt r₁ r₂ h₀ h

theorem exists_lt_nnnorm_lt {r₁ r₂ : ℝ≥0} (h : r₁ < r₂) : ∃ x : α, r₁ < ‖x‖₊ ∧ ‖x‖₊ < r₂ :=
  mod_cast exists_lt_norm_lt α r₁.prop h

instance denselyOrdered_range_norm : DenselyOrdered (Set.range (norm : α → ℝ)) where
  dense := by
    rintro ⟨-, x, rfl⟩ ⟨-, y, rfl⟩ hxy
    let ⟨z, h⟩ := exists_lt_norm_lt α (norm_nonneg _) hxy
    exact ⟨⟨‖z‖, z, rfl⟩, h⟩

instance denselyOrdered_range_nnnorm : DenselyOrdered (Set.range (nnnorm : α → ℝ≥0)) where
  dense := by
    rintro ⟨-, x, rfl⟩ ⟨-, y, rfl⟩ hxy
    let ⟨z, h⟩ := exists_lt_nnnorm_lt α hxy
    exact ⟨⟨‖z‖₊, z, rfl⟩, h⟩

end Densely

end NormedField

/-- A normed field is nontrivially normed
provided that the norm of some nonzero element is not one. -/
def NontriviallyNormedField.ofNormNeOne {𝕜 : Type*} [h' : NormedField 𝕜]
    (h : ∃ x : 𝕜, x ≠ 0 ∧ ‖x‖ ≠ 1) : NontriviallyNormedField 𝕜 where
  toNormedField := h'
  non_trivial := by
    rcases h with ⟨x, hx, hx1⟩
    rcases hx1.lt_or_gt with hlt | hlt
    · use x⁻¹
      rw [norm_inv]
      exact (one_lt_inv₀ (norm_pos_iff.2 hx)).2 hlt
    · exact ⟨x, hlt⟩

noncomputable instance Real.normedField : NormedField ℝ :=
  { Real.normedAddCommGroup, Real.instField with
    norm_mul := abs_mul }

noncomputable instance Real.denselyNormedField : DenselyNormedField ℝ where
  lt_norm_lt _ _ h₀ hr :=
    let ⟨x, h⟩ := exists_between hr
    ⟨x, by rwa [Real.norm_eq_abs, abs_of_nonneg (h₀.trans h.1.le)]⟩

namespace Real

theorem toNNReal_mul_nnnorm {x : ℝ} (y : ℝ) (hx : 0 ≤ x) : x.toNNReal * ‖y‖₊ = ‖x * y‖₊ := by
  ext
  simp only [NNReal.coe_mul, nnnorm_mul, coe_nnnorm, Real.toNNReal_of_nonneg, norm_of_nonneg, hx,
    NNReal.coe_mk]

theorem nnnorm_mul_toNNReal (x : ℝ) {y : ℝ} (hy : 0 ≤ y) : ‖x‖₊ * y.toNNReal = ‖x * y‖₊ := by
  rw [mul_comm, mul_comm x, toNNReal_mul_nnnorm x hy]

end Real

/-! ### Induced normed structures -/

section Induced

variable {F : Type*} (R S : Type*) [FunLike F R S]

/-- An injective non-unital ring homomorphism from a `DivisionRing` to a `NormedRing` induces a
`NormedDivisionRing` structure on the domain.

See note [reducible non-instances] -/
abbrev NormedDivisionRing.induced [DivisionRing R] [NormedDivisionRing S]
    [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Injective f) : NormedDivisionRing R :=
  { NormedAddCommGroup.induced R S f hf, ‹DivisionRing R› with
    norm_mul x y := show ‖f _‖ = _ from (map_mul f x y).symm ▸ norm_mul (f x) (f y) }

/-- An injective non-unital ring homomorphism from a `Field` to a `NormedRing` induces a
`NormedField` structure on the domain.

See note [reducible non-instances] -/
abbrev NormedField.induced [Field R] [NormedField S] [NonUnitalRingHomClass F R S] (f : F)
    (hf : Function.Injective f) : NormedField R :=
  { NormedDivisionRing.induced R S f hf with
    mul_comm := mul_comm }

end Induced

namespace SubfieldClass

variable {S F : Type*} [SetLike S F]

/--
If `s` is a subfield of a normed field `F`, then `s` is equipped with an induced normed
field structure.
-/
instance toNormedField [NormedField F] [SubfieldClass S F] (s : S) : NormedField s :=
  NormedField.induced s F (SubringClass.subtype s) Subtype.val_injective

end SubfieldClass

namespace AbsoluteValue

/-- A real absolute value on a field determines a `NormedField` structure. -/
@[implicit_reducible]
noncomputable def toNormedField {K : Type*} [Field K] (v : AbsoluteValue K ℝ) : NormedField K where
  toField := inferInstanceAs (Field K)
  __ := v.toNormedRing
  norm_mul := v.map_mul

end AbsoluteValue
