/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis, Yaël Dillies
-/
import Mathlib.Algebra.Order.SMul

#align_import algebra.order.module from "leanprover-community/mathlib"@"3ba15165bd6927679be7c22d6091a87337e3cd0c"

/-!
# Ordered module

In this file we provide lemmas about `OrderedSMul` that hold once a module structure is present.

## References

* https://en.wikipedia.org/wiki/Ordered_module

## Tags

ordered module, ordered scalar, ordered smul, ordered action, ordered vector space
-/


open Pointwise

variable {ι k M N : Type*}

instance instModuleOrderDual [Semiring k] [OrderedAddCommMonoid M] [Module k M] : Module k Mᵒᵈ
    where
  add_smul _ _ x := OrderDual.rec (add_smul _ _) x
  zero_smul m := OrderDual.rec (zero_smul _) m

section Semiring

variable [OrderedSemiring k] [OrderedAddCommGroup M] [Module k M] [OrderedSMul k M] {a b : M}
  {c : k}

/- Can be generalized from `Module k M` to `DistribMulActionWithZero k M` once it exists.
where `DistribMulActionWithZero k M`is the conjunction of `DistribMulAction k M` and
`SMulWithZero k M`.-/
theorem smul_neg_iff_of_pos (hc : 0 < c) : c • a < 0 ↔ a < 0 := by
  rw [← neg_neg a, smul_neg, neg_neg_iff_pos, neg_neg_iff_pos]
  exact smul_pos_iff_of_pos hc
#align smul_neg_iff_of_pos smul_neg_iff_of_pos

end Semiring

section Ring

variable [OrderedRing k] [OrderedAddCommGroup M] [Module k M] [OrderedSMul k M] {a b : M} {c d : k}

theorem smul_lt_smul_of_neg (h : a < b) (hc : c < 0) : c • b < c • a := by
  rw [← neg_neg c, neg_smul, neg_smul (-c), neg_lt_neg_iff]
  exact smul_lt_smul_of_pos h (neg_pos_of_neg hc)
#align smul_lt_smul_of_neg smul_lt_smul_of_neg

theorem smul_le_smul_of_nonpos (h : a ≤ b) (hc : c ≤ 0) : c • b ≤ c • a := by
  rw [← neg_neg c, neg_smul, neg_smul (-c), neg_le_neg_iff]
  exact smul_le_smul_of_nonneg h (neg_nonneg_of_nonpos hc)
#align smul_le_smul_of_nonpos smul_le_smul_of_nonpos

theorem eq_of_smul_eq_smul_of_neg_of_le (hab : c • a = c • b) (hc : c < 0) (h : a ≤ b) : a = b := by
  rw [← neg_neg c, neg_smul, neg_smul (-c), neg_inj] at hab
  exact eq_of_smul_eq_smul_of_pos_of_le hab (neg_pos_of_neg hc) h
#align eq_of_smul_eq_smul_of_neg_of_le eq_of_smul_eq_smul_of_neg_of_le

theorem lt_of_smul_lt_smul_of_nonpos (h : c • a < c • b) (hc : c ≤ 0) : b < a := by
  rw [← neg_neg c, neg_smul, neg_smul (-c), neg_lt_neg_iff] at h
  exact lt_of_smul_lt_smul_of_nonneg h (neg_nonneg_of_nonpos hc)
#align lt_of_smul_lt_smul_of_nonpos lt_of_smul_lt_smul_of_nonpos

lemma smul_le_smul_of_nonneg_right (h : c ≤ d) (hb : 0 ≤ b) : c • b ≤ d • b := by
  rw [←sub_nonneg, ←sub_smul]; exact smul_nonneg (sub_nonneg.2 h) hb

lemma smul_le_smul (hcd : c ≤ d) (hab : a ≤ b) (ha : 0 ≤ a) (hd : 0 ≤ d) : c • a ≤ d • b :=
  (smul_le_smul_of_nonneg_right hcd ha).trans $ smul_le_smul_of_nonneg_left hab hd

theorem smul_lt_smul_iff_of_neg (hc : c < 0) : c • a < c • b ↔ b < a := by
  rw [← neg_neg c, neg_smul, neg_smul (-c), neg_lt_neg_iff]
  exact smul_lt_smul_iff_of_pos (neg_pos_of_neg hc)
#align smul_lt_smul_iff_of_neg smul_lt_smul_iff_of_neg

theorem smul_neg_iff_of_neg (hc : c < 0) : c • a < 0 ↔ 0 < a := by
  rw [← neg_neg c, neg_smul, neg_neg_iff_pos]
  exact smul_pos_iff_of_pos (neg_pos_of_neg hc)
#align smul_neg_iff_of_neg smul_neg_iff_of_neg

theorem smul_pos_iff_of_neg (hc : c < 0) : 0 < c • a ↔ a < 0 := by
  rw [← neg_neg c, neg_smul, neg_pos]
  exact smul_neg_iff_of_pos (neg_pos_of_neg hc)
#align smul_pos_iff_of_neg smul_pos_iff_of_neg

theorem smul_nonpos_of_nonpos_of_nonneg (hc : c ≤ 0) (ha : 0 ≤ a) : c • a ≤ 0 :=
  calc
    c • a ≤ c • (0 : M) := smul_le_smul_of_nonpos ha hc
    _ = 0 := smul_zero c
#align smul_nonpos_of_nonpos_of_nonneg smul_nonpos_of_nonpos_of_nonneg

theorem smul_nonneg_of_nonpos_of_nonpos (hc : c ≤ 0) (ha : a ≤ 0) : 0 ≤ c • a :=
  @smul_nonpos_of_nonpos_of_nonneg k Mᵒᵈ _ _ _ _ _ _ hc ha
#align smul_nonneg_of_nonpos_of_nonpos smul_nonneg_of_nonpos_of_nonpos

alias ⟨_, smul_pos_of_neg_of_neg⟩ := smul_pos_iff_of_neg
#align smul_pos_of_neg_of_neg smul_pos_of_neg_of_neg

alias ⟨_, smul_neg_of_pos_of_neg⟩ := smul_neg_iff_of_pos
#align smul_neg_of_pos_of_neg smul_neg_of_pos_of_neg

alias ⟨_, smul_neg_of_neg_of_pos⟩ := smul_neg_iff_of_neg
#align smul_neg_of_neg_of_pos smul_neg_of_neg_of_pos

theorem antitone_smul_left (hc : c ≤ 0) : Antitone (SMul.smul c : M → M) := fun _ _ h =>
  smul_le_smul_of_nonpos h hc
#align antitone_smul_left antitone_smul_left

theorem strict_anti_smul_left (hc : c < 0) : StrictAnti (SMul.smul c : M → M) := fun _ _ h =>
  smul_lt_smul_of_neg h hc
#align strict_anti_smul_left strict_anti_smul_left

/-- Binary **rearrangement inequality**. -/
theorem smul_add_smul_le_smul_add_smul [ContravariantClass M M (· + ·) (· ≤ ·)] {a b : k} {c d : M}
    (hab : a ≤ b) (hcd : c ≤ d) : a • d + b • c ≤ a • c + b • d := by
  obtain ⟨b, rfl⟩ := exists_add_of_le hab
  obtain ⟨d, rfl⟩ := exists_add_of_le hcd
  rw [smul_add, add_right_comm, smul_add, ← add_assoc, add_smul _ _ d]
  rw [le_add_iff_nonneg_right] at hab hcd
  exact add_le_add_left (le_add_of_nonneg_right <| smul_nonneg hab hcd) _
#align smul_add_smul_le_smul_add_smul smul_add_smul_le_smul_add_smul

/-- Binary **rearrangement inequality**. -/
theorem smul_add_smul_le_smul_add_smul' [ContravariantClass M M (· + ·) (· ≤ ·)] {a b : k} {c d : M}
    (hba : b ≤ a) (hdc : d ≤ c) : a • d + b • c ≤ a • c + b • d := by
  rw [add_comm (a • d), add_comm (a • c)]
  exact smul_add_smul_le_smul_add_smul hba hdc
#align smul_add_smul_le_smul_add_smul' smul_add_smul_le_smul_add_smul'

/-- Binary strict **rearrangement inequality**. -/
theorem smul_add_smul_lt_smul_add_smul [CovariantClass M M (· + ·) (· < ·)]
    [ContravariantClass M M (· + ·) (· < ·)] {a b : k} {c d : M} (hab : a < b) (hcd : c < d) :
    a • d + b • c < a • c + b • d := by
  obtain ⟨b, rfl⟩ := exists_add_of_le hab.le
  obtain ⟨d, rfl⟩ := exists_add_of_le hcd.le
  rw [smul_add, add_right_comm, smul_add, ← add_assoc, add_smul _ _ d]
  rw [lt_add_iff_pos_right] at hab hcd
  exact add_lt_add_left (lt_add_of_pos_right _ <| smul_pos hab hcd) _
#align smul_add_smul_lt_smul_add_smul smul_add_smul_lt_smul_add_smul

/-- Binary strict **rearrangement inequality**. -/
theorem smul_add_smul_lt_smul_add_smul' [CovariantClass M M (· + ·) (· < ·)]
    [ContravariantClass M M (· + ·) (· < ·)] {a b : k} {c d : M} (hba : b < a) (hdc : d < c) :
    a • d + b • c < a • c + b • d := by
  rw [add_comm (a • d), add_comm (a • c)]
  exact smul_add_smul_lt_smul_add_smul hba hdc
#align smul_add_smul_lt_smul_add_smul' smul_add_smul_lt_smul_add_smul'

end Ring

section Field

variable [LinearOrderedField k] [OrderedAddCommGroup M] [Module k M] [OrderedSMul k M] {a b : M}
  {c : k}

theorem smul_le_smul_iff_of_neg (hc : c < 0) : c • a ≤ c • b ↔ b ≤ a := by
  rw [← neg_neg c, neg_smul, neg_smul (-c), neg_le_neg_iff]
  exact smul_le_smul_iff_of_pos (neg_pos_of_neg hc)
#align smul_le_smul_iff_of_neg smul_le_smul_iff_of_neg

theorem inv_smul_le_iff_of_neg (h : c < 0) : c⁻¹ • a ≤ b ↔ c • b ≤ a := by
  rw [← smul_le_smul_iff_of_neg h, smul_inv_smul₀ h.ne]
#align inv_smul_le_iff_of_neg inv_smul_le_iff_of_neg

theorem inv_smul_lt_iff_of_neg (h : c < 0) : c⁻¹ • a < b ↔ c • b < a := by
  rw [← smul_lt_smul_iff_of_neg h, smul_inv_smul₀ h.ne]
#align inv_smul_lt_iff_of_neg inv_smul_lt_iff_of_neg

theorem smul_inv_le_iff_of_neg (h : c < 0) : a ≤ c⁻¹ • b ↔ b ≤ c • a := by
  rw [← smul_le_smul_iff_of_neg h, smul_inv_smul₀ h.ne]
#align smul_inv_le_iff_of_neg smul_inv_le_iff_of_neg

theorem smul_inv_lt_iff_of_neg (h : c < 0) : a < c⁻¹ • b ↔ b < c • a := by
  rw [← smul_lt_smul_iff_of_neg h, smul_inv_smul₀ h.ne]
#align smul_inv_lt_iff_of_neg smul_inv_lt_iff_of_neg

variable (M)

/-- Left scalar multiplication as an order isomorphism. -/
@[simps]
def OrderIso.smulLeftDual {c : k} (hc : c < 0) : M ≃o Mᵒᵈ where
  toFun b := OrderDual.toDual (c • b)
  invFun b := c⁻¹ • OrderDual.ofDual b
  left_inv := inv_smul_smul₀ hc.ne
  right_inv := smul_inv_smul₀ hc.ne
  map_rel_iff' := (@OrderDual.toDual_le_toDual M).trans <| smul_le_smul_iff_of_neg hc
#align order_iso.smul_left_dual OrderIso.smulLeftDual

end Field

/-! ### Upper/lower bounds -/


section OrderedRing

variable [OrderedRing k] [OrderedAddCommGroup M] [Module k M] [OrderedSMul k M] {s : Set M} {c : k}

theorem smul_lowerBounds_subset_upperBounds_smul (hc : c ≤ 0) :
    c • lowerBounds s ⊆ upperBounds (c • s) :=
  (antitone_smul_left hc).image_lowerBounds_subset_upperBounds_image
#align smul_lower_bounds_subset_upper_bounds_smul smul_lowerBounds_subset_upperBounds_smul

theorem smul_upperBounds_subset_lowerBounds_smul (hc : c ≤ 0) :
    c • upperBounds s ⊆ lowerBounds (c • s) :=
  (antitone_smul_left hc).image_upperBounds_subset_lowerBounds_image
#align smul_upper_bounds_subset_lower_bounds_smul smul_upperBounds_subset_lowerBounds_smul

theorem BddBelow.smul_of_nonpos (hc : c ≤ 0) (hs : BddBelow s) : BddAbove (c • s) :=
  (antitone_smul_left hc).map_bddBelow hs
#align bdd_below.smul_of_nonpos BddBelow.smul_of_nonpos

theorem BddAbove.smul_of_nonpos (hc : c ≤ 0) (hs : BddAbove s) : BddBelow (c • s) :=
  (antitone_smul_left hc).map_bddAbove hs
#align bdd_above.smul_of_nonpos BddAbove.smul_of_nonpos

end OrderedRing

section LinearOrderedRing
variable [LinearOrderedRing k] [LinearOrderedAddCommGroup M] [Module k M] [OrderedSMul k M]
  {f : ι → k} {g : ι → M} {s : Set ι} {a a₁ a₂ : k} {b b₁ b₂ : M}

theorem smul_max_of_nonpos (ha : a ≤ 0) (b₁ b₂ : M) : a • max b₁ b₂ = min (a • b₁) (a • b₂) :=
  (antitone_smul_left ha : Antitone (_ : M → M)).map_max
#align smul_max_of_nonpos smul_max_of_nonpos

theorem smul_min_of_nonpos (ha : a ≤ 0) (b₁ b₂ : M) : a • min b₁ b₂ = max (a • b₁) (a • b₂) :=
  (antitone_smul_left ha : Antitone (_ : M → M)).map_min
#align smul_min_of_nonpos smul_min_of_nonpos

lemma nonneg_and_nonneg_or_nonpos_and_nonpos_of_smul_nonneg (hab : 0 ≤ a • b) :
    0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  simp only [Decidable.or_iff_not_and_not, not_and, not_le]
  refine fun ab nab ↦ hab.not_lt ?_
  obtain ha | rfl | ha := lt_trichotomy 0 a
  exacts [smul_neg_of_pos_of_neg ha (ab ha.le), ((ab le_rfl).asymm (nab le_rfl)).elim,
    smul_neg_of_neg_of_pos ha (nab ha.le)]

lemma smul_nonneg_iff : 0 ≤ a • b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 :=
  ⟨nonneg_and_nonneg_or_nonpos_and_nonpos_of_smul_nonneg,
    fun h ↦ h.elim (and_imp.2 smul_nonneg) (and_imp.2 smul_nonneg_of_nonpos_of_nonpos)⟩

lemma smul_nonpos_iff : a • b ≤ 0 ↔ 0 ≤ a ∧ b ≤ 0 ∨ a ≤ 0 ∧ 0 ≤ b := by
  rw [←neg_nonneg, ←smul_neg, smul_nonneg_iff, neg_nonneg, neg_nonpos]

lemma smul_nonneg_iff_pos_imp_nonneg : 0 ≤ a • b ↔ (0 < a → 0 ≤ b) ∧ (0 < b → 0 ≤ a) := by
  refine smul_nonneg_iff.trans ?_
  simp_rw [←not_le, ←or_iff_not_imp_left]
  have := le_total a 0
  have := le_total b 0
  tauto

lemma smul_nonneg_iff_neg_imp_nonpos : 0 ≤ a • b ↔ (a < 0 → b ≤ 0) ∧ (b < 0 → a ≤ 0) := by
  rw [←neg_smul_neg, smul_nonneg_iff_pos_imp_nonneg]; simp only [neg_pos, neg_nonneg]

lemma smul_nonpos_iff_pos_imp_nonpos : a • b ≤ 0 ↔ (0 < a → b ≤ 0) ∧ (b < 0 → 0 ≤ a) := by
  rw [←neg_nonneg, ←smul_neg, smul_nonneg_iff_pos_imp_nonneg]; simp only [neg_pos, neg_nonneg]

lemma smul_nonpos_iff_neg_imp_nonneg : a • b ≤ 0 ↔ (a < 0 → 0 ≤ b) ∧ (0 < b → a ≤ 0) := by
  rw [←neg_nonneg, ←neg_smul, smul_nonneg_iff_pos_imp_nonneg]; simp only [neg_pos, neg_nonneg]

end LinearOrderedRing

section LinearOrderedField

variable [LinearOrderedField k] [OrderedAddCommGroup M] [Module k M] [OrderedSMul k M] {s : Set M}
  {c : k}

@[simp]
theorem lowerBounds_smul_of_neg (hc : c < 0) : lowerBounds (c • s) = c • upperBounds s :=
  (OrderIso.smulLeftDual M hc).upperBounds_image
#align lower_bounds_smul_of_neg lowerBounds_smul_of_neg

@[simp]
theorem upperBounds_smul_of_neg (hc : c < 0) : upperBounds (c • s) = c • lowerBounds s :=
  (OrderIso.smulLeftDual M hc).lowerBounds_image
#align upper_bounds_smul_of_neg upperBounds_smul_of_neg

@[simp]
theorem bddBelow_smul_iff_of_neg (hc : c < 0) : BddBelow (c • s) ↔ BddAbove s :=
  (OrderIso.smulLeftDual M hc).bddAbove_image
#align bdd_below_smul_iff_of_neg bddBelow_smul_iff_of_neg

@[simp]
theorem bddAbove_smul_iff_of_neg (hc : c < 0) : BddAbove (c • s) ↔ BddBelow s :=
  (OrderIso.smulLeftDual M hc).bddBelow_image
#align bdd_above_smul_iff_of_neg bddAbove_smul_iff_of_neg

end LinearOrderedField
