/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.ZMultiples

/-!
# The additive circle over `ℝ`

Results specific to the additive circle over `ℝ`.
-/


noncomputable section

open AddCommGroup Set Function AddSubgroup TopologicalSpace Topology

namespace AddCircle

variable (p : ℝ)

instance pathConnectedSpace : PathConnectedSpace <| AddCircle p :=
  (inferInstance : PathConnectedSpace (Quotient _))

/-- The "additive circle" `ℝ ⧸ (ℤ ∙ p)` is compact. -/
instance compactSpace [Fact (0 < p)] : CompactSpace <| AddCircle p := by
  rw [← isCompact_univ_iff, ← coe_image_Icc_eq p 0]
  exact isCompact_Icc.image (AddCircle.continuous_mk' p)

/-- The action on `ℝ` by right multiplication of its the subgroup `zmultiples p` (the multiples of
`p:ℝ`) is properly discontinuous. -/
instance : ProperlyDiscontinuousVAdd (zmultiples p).op ℝ :=
  (zmultiples p).properlyDiscontinuousVAdd_opposite_of_tendsto_cofinite
    (AddSubgroup.tendsto_zmultiples_subtype_cofinite p)

end AddCircle

section UnitAddCircle

/-- The unit circle `ℝ ⧸ ℤ`. -/
abbrev UnitAddCircle :=
  AddCircle (1 : ℝ)

end UnitAddCircle

namespace ZMod

variable {N : ℕ} [NeZero N]

/-- The `AddMonoidHom` from `ZMod N` to `ℝ / ℤ` sending `j mod N` to `j / N mod 1`. -/
noncomputable def toAddCircle : ZMod N →+ UnitAddCircle :=
  lift N ⟨AddMonoidHom.mk' (fun j ↦ ↑(j / N : ℝ)) (by simp [add_div]),
    by simp [div_self (NeZero.ne _)]⟩

lemma toAddCircle_intCast (j : ℤ) :
    toAddCircle (j : ZMod N) = ↑(j / N : ℝ) := by
  simp [toAddCircle]

lemma toAddCircle_natCast (j : ℕ) :
    toAddCircle (j : ZMod N) = ↑(j / N : ℝ) := by
  simpa using toAddCircle_intCast (N := N) j

/--
Explicit formula for `toCircle j`. Note that this is "evil" because it uses `ZMod.val`. Where
possible, it is recommended to lift `j` to `ℤ` and use `toAddCircle_intCast` instead.
-/
lemma toAddCircle_apply (j : ZMod N) :
    toAddCircle j = ↑(j.val / N : ℝ) := by
  rw [← toAddCircle_natCast, natCast_zmod_val]

variable (N) in
lemma toAddCircle_injective : Function.Injective (toAddCircle : ZMod N → _) := by
  intro x y hxy
  have : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos _)
  rwa [toAddCircle_apply, toAddCircle_apply, AddCircle.coe_eq_coe_iff_of_mem_Ico,
    div_left_inj' this.ne', Nat.cast_inj, (val_injective N).eq_iff] at hxy <;>
  exact ⟨by positivity, by simpa only [zero_add, div_lt_one this, Nat.cast_lt] using val_lt _⟩

@[simp] lemma toAddCircle_inj {j k : ZMod N} : toAddCircle j = toAddCircle k ↔ j = k :=
  (toAddCircle_injective N).eq_iff

@[simp] lemma toAddCircle_eq_zero {j : ZMod N} : toAddCircle j = 0 ↔ j = 0 :=
  map_eq_zero_iff _ (toAddCircle_injective N)

end ZMod
