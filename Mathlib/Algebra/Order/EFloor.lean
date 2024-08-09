/-
Copyright (c) 2024 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Algebra.CharZero.Lemmas
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Algebra.Group.Int
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Set.Subsingleton
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Order.GaloisConnection
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Instances.ENNReal
import Mathlib.Data.Real.ENatENNReal

/-!
# Floor in extended nonnegative numbers

## Summary

We define the extended natural number -valued floor functions.

## Main Definitions

* `EFloorSemiring`: An ordered semiring with natural-valued floor.
* `Nat.floor a`: Greatest natural `n` such that `n ≤ a`. Equal to `0` if `a < 0`.

## Notations

* `⌊a⌋ᵢ` is `ENat.floor a`.

The index `ᵢ` in the notations for `ENat.floor` indicates the possibility of `+∞` (`⊤`) and
disambiguates from the common floor notation.

## TODO

Add `ENat.ceil`.

## Tags

floor
-/


open Set ENNReal

-- TODO: Add. (Counterpart of `Nat.pos_of_ne_zero`.)
lemma ENat.pos_of_ne_zero {n : ℕ∞} (hn : n ≠ 0) : 0 < n :=
  pos_iff_ne_zero.mpr hn

variable {F α β : Type*}

/-! ### EFloor semiring -/

/-- A `EFloorSemiring` is an ordered semiring over `α` with a function
`floor : α → ℕ∞` satisfying `∀ (n : ℕ) (x : α), n ≤ ⌊x⌋ ↔ (n : α) ≤ x)`.
Note that many lemmas require a `LinearOrder`. -/
class EFloorSemiring (α) [Semiring α] [Preorder α] [CoeTC ℕ∞ α] where
  /-- `EFloorSemiring.floor a` computes the greatest natural `n` such that `(n : α) ≤ a`. -/
  floor : α → ℕ∞
  floor_of_neg {a : α} (ha : a < 0) : floor a = 0
  /-- An extended natural number `n` is smaller than `FloorSemiring.floor a` iff its coercion
  to `α` is smaller than `a`. -/
  gc_floor {a : α} {n : ℕ∞} (ha : 0 ≤ a) : n ≤ floor a ↔ (n : α) ≤ a
  floor_lt {a : α} {n : ℕ∞} (ha : 0 ≤ a) : floor a < n ↔ a < n

instance : EFloorSemiring ℕ∞ where
  floor := id
  floor_of_neg ha := (ENat.not_lt_zero _ ha).elim
  gc_floor _ := by rfl
  floor_lt _ := by rfl

class CastNatENatClass (α : Type*) [Semiring α] [Preorder α] [CoeTC ℕ∞ α] where
  cast_nat : ∀ (n : ℕ), (n : ℕ∞) = (n : α)
  cast_enat_lt_iff : ∀ (n m : ℕ∞), (n : α) < (m : α) ↔ n < m
  cast_enat_le_iff : ∀ (n m : ℕ∞), (n : α) ≤ (m : α) ↔ n ≤ m
  cast_nonneg {n : ℕ∞} : (0 : α) ≤ n

@[simp, norm_cast]
lemma ENat.cast_nat [Semiring α] [Preorder α] [CoeTC ℕ∞ α] [CastNatENatClass α] {n : ℕ} :
    (n : ℕ∞) = (n : α) :=
  CastNatENatClass.cast_nat n

@[simp] lemma ENat.cast_zero [Semiring α] [Preorder α] [CoeTC ℕ∞ α] [CastNatENatClass α] :
    (0 : ℕ∞) = (0 : α) := by
  exact_mod_cast ENat.cast_nat (α := α) (n := 0)

@[simp] lemma ENat.cast_one [Semiring α] [Preorder α] [CoeTC ℕ∞ α] [CastNatENatClass α] :
    (1 : ℕ∞) = (1 : α) := by
  exact_mod_cast ENat.cast_nat (α := α) (n := 1)

@[simp]
lemma cast_enat_lt_iff [Semiring α] [Preorder α] [CoeTC ℕ∞ α] [CastNatENatClass α] {n m : ℕ∞} :
    (n : α) < (m : α) ↔ n < m :=
  CastNatENatClass.cast_enat_lt_iff n m

@[simp]
lemma cast_enat_le_iff [Semiring α] [Preorder α] [CoeTC ℕ∞ α] [CastNatENatClass α] {n m : ℕ∞} :
    (n : α) ≤ (m : α) ↔ n ≤ m :=
  CastNatENatClass.cast_enat_le_iff n m

lemma lt_of_cast_enat_lt [Semiring α] [Preorder α] [CoeTC ℕ∞ α] [CastNatENatClass α]
    {n m : ℕ∞} (h : (n : α) < (m : α)) :
    n < m :=
  lt_of_le_of_ne (cast_enat_le_iff.mp h.le) fun con ↦ lt_irrefl _ (con ▸ h)

lemma ENat.cast_nonneg [Semiring α] [Preorder α] [CoeTC ℕ∞ α] [CastNatENatClass α] (n : ℕ∞) :
    0 ≤ (n : α) :=
  CastNatENatClass.cast_nonneg

noncomputable instance : CastNatENatClass ℕ∞ where
  cast_nat _ := rfl
  cast_enat_lt_iff _ _ := by rfl
  cast_enat_le_iff _ _ := by rfl
  cast_nonneg := zero_le _

noncomputable instance : CastNatENatClass ℝ≥0∞ where
  cast_nat _ := rfl
  cast_enat_lt_iff n m := by rw [← ENat.toENNReal_lt]; rfl
  cast_enat_le_iff n m := by rw [← ENat.toENNReal_le]; rfl
  cast_nonneg := zero_le _

namespace ENat

section OrderedSemiring

variable [Semiring α] [Preorder α] [CoeTC ℕ∞ α] [EFloorSemiring α] {a : α} {n : ℕ∞}

/-- `⌊a⌋ᵢ` is the greatest extended natural number `n` such that `n ≤ a`. If `a` is negative,
then `⌊a⌋ᵢ = 0`. -/
def floor : α → ℕ∞ := EFloorSemiring.floor

@[simp]
lemma floor_enat : (ENat.floor : ℕ∞ → ℕ∞) = id := rfl

@[inherit_doc]
notation "⌊" a "⌋ᵢ" => ENat.floor a

end OrderedSemiring

section LinearOrderedSemiring

#check LinearOrderedSemiring
#check ZeroLEOneClass
--#check ZeroLEOneClass

variable [Semiring α] [LinearOrder α] [ZeroLEOneClass α]
variable [CoeTC ℕ∞ α] [EFloorSemiring α] [CastNatENatClass α]
variable {a : α} {n : ℕ∞}

lemma le_floor_iff (ha : 0 ≤ a) : n ≤ ⌊a⌋ᵢ ↔ (n : α) ≤ a :=
  EFloorSemiring.gc_floor ha

lemma le_floor (h : (n : α) ≤ a) : n ≤ ⌊a⌋ᵢ := (le_floor_iff <| n.cast_nonneg.trans h).2 h

lemma floor_lt (ha : 0 ≤ a) : ⌊a⌋ᵢ < n ↔ a < n := lt_iff_lt_of_le_iff_le <| le_floor_iff ha

lemma floor_lt_one (ha : 0 ≤ a) : ⌊a⌋ᵢ < 1 ↔ a < 1 := by simpa using (floor_lt ha (n := 1))

lemma lt_of_floor_lt (h : ⌊a⌋ᵢ < n) : a < n := lt_of_not_le fun h' => (le_floor h').not_lt h

lemma lt_one_of_floor_lt_one (h : ⌊a⌋ᵢ < 1) : a < 1 := by simpa using lt_of_floor_lt h

lemma floor_le (ha : 0 ≤ a) : (⌊a⌋ᵢ : α) ≤ a := (le_floor_iff ha).1 le_rfl

@[simp]
lemma floor_enatCast (n : ℕ∞) : ⌊(n : α)⌋ᵢ = n :=
  eq_of_forall_le_iff fun a => by
    rw [le_floor_iff n.cast_nonneg]
    exact cast_enat_le_iff

@[simp]
lemma floor_zero : ⌊(0 : α)⌋ᵢ = 0 := by
  rw [← Nat.cast_zero, ← floor_enatCast (α := α) 0]
  simp

@[simp]
lemma floor_one : ⌊(1 : α)⌋ᵢ = 1 := by
  rw [← Nat.cast_one, ← floor_enatCast (α := α) 1]
  simp

lemma floor_of_nonpos (ha : a ≤ 0) : ⌊a⌋ᵢ = 0 :=
  ha.lt_or_eq.elim EFloorSemiring.floor_of_neg <| by
    rintro rfl
    exact floor_zero

lemma floor_mono : Monotone (floor : α → ℕ∞) := fun a b h => by
  obtain ha | ha := le_total a 0
  · rw [floor_of_nonpos ha]
    exact zero_le _
  · exact le_floor ((floor_le ha).trans h)

@[gcongr]
lemma floor_le_floor : ∀ x y : α, x ≤ y → ⌊x⌋ᵢ ≤ ⌊y⌋ᵢ := floor_mono

variable [Nontrivial α]

lemma le_floor_iff' (hn : n ≠ 0) : n ≤ ⌊a⌋ᵢ ↔ (n : α) ≤ a := by
  obtain ha | ha := le_total a 0
  · rw [floor_of_nonpos ha, iff_of_false (ENat.pos_of_ne_zero hn).not_le]
    apply not_le_of_lt (ha.trans_lt _)
    refine lt_of_lt_of_le ?_ <| (cast_enat_le_iff (α := α)).mpr <| one_le_iff_ne_zero.mpr hn
    apply lt_of_le_of_ne (by simp [show (0 : α) ≤ (1 : α) from zero_le_one])
    simp
  · exact le_floor_iff ha

@[simp] lemma one_le_floor_iff (x : α) :
    1 ≤ ⌊x⌋ᵢ ↔ 1 ≤ x := by
  simp [@le_floor_iff' α _ _ _ _ _ _ x 1 _ one_ne_zero]

lemma floor_lt' (hn : n ≠ 0) : ⌊a⌋ᵢ < n ↔ a < n := lt_iff_lt_of_le_iff_le <| le_floor_iff' hn

lemma floor_pos : 0 < ⌊a⌋ᵢ ↔ 1 ≤ a := by simpa [← one_le_floor_iff] using one_le_iff_pos.symm

lemma pos_of_floor_pos (h : 0 < ⌊a⌋ᵢ) :
    0 < a := by
  rw [floor_pos] at h; exact lt_of_lt_of_le zero_lt_one h

lemma lt_of_lt_floor (h : n < ⌊a⌋ᵢ) :
    ↑n < a := by
  apply lt_of_lt_of_le _ <| floor_le (pos_of_floor_pos <| (zero_le n).trans_lt h).le
  rwa [← cast_enat_lt_iff (α := α)] at h

lemma floor_le_of_le (h : a ≤ n) : ⌊a⌋ᵢ ≤ n := le_imp_le_iff_lt_imp_lt.2 lt_of_lt_floor h

lemma floor_le_one_of_le_one (h : a ≤ 1) :
    ⌊a⌋ᵢ ≤ 1 :=
  floor_le_of_le <| h.trans_eq <| ENat.cast_one.symm

@[simp] lemma floor_eq_zero :
    ⌊a⌋ᵢ = 0 ↔ a < 1 := by
  rw [lt_one_iff_eq_zero.symm, ← @cast_one α]
  exact floor_lt' one_ne_zero

@[simp] lemma preimage_floor_zero : (floor : α → ℕ∞) ⁻¹' {0} = Iio 1 := ext fun _ => floor_eq_zero

end LinearOrderedSemiring

end ENat



open Filter BigOperators TopologicalSpace Topology Set ENNReal NNReal ENat

section ENat_topology

instance : TopologicalSpace ℕ∞ := TopologicalSpace.induced ENat.toENNReal inferInstance

lemma ENat.continuous_toENNReal : Continuous ENat.toENNReal :=
  continuous_iff_le_induced.mpr fun _ h ↦ h

instance : OrderTopology ℕ∞ := sorry

-- TODO: Move to the appropriate file `Data.ENat.Basic`.
lemma ENat.toENNReal_coe_eq_top_iff {m : ℕ∞} :
    (m : ℝ≥0∞) = ∞ ↔ m = ⊤ := by
  rw [← toENNReal_coe_eq_iff, toENNReal_top]

-- TODO: Move to the appropriate file `Data.ENat.Basic`.
lemma ENat.toENNReal_coe_ne_top_iff {m : ℕ∞} :
    (m : ℝ≥0∞) ≠ ∞ ↔ m ≠ ⊤ :=
  not_iff_not.mpr toENNReal_coe_eq_top_iff

end ENat_topology



section ENNReal

namespace ENNReal

/-- The floor function `ℝ≥0∞ → ℕ∞`: the floor of `x` is the supremum of the extended natural
numbers `n` satisfying `n ≤ x`. -/
noncomputable def floorAux (x : ℝ≥0∞) : ℕ∞ := sSup {n : ℕ∞ | n ≤ x}

variable {x y : ℝ≥0∞} {m : ℕ∞}

private lemma floorAux_mono (h : x ≤ y) : x.floorAux ≤ y.floorAux :=
  sSup_le_sSup <| fun _ hx ↦ hx.trans h

/-- The floor function `ℝ≥0∞ → ℝ≥0∞` is increasing. -/
private lemma monotone_floorAux : Monotone floorAux := fun _ _ h ↦ floorAux_mono h

private lemma floorAux_eq_sSup_range_toENNReal_inter_Iic :
    floorAux x = sSup (Set.range (fun (m : ℕ∞) ↦ (m : ℝ≥0∞)) ∩ Iic x) := by
  simp only [floorAux]
  rw [toENNReal_mono.map_sSup_of_continuousAt ENat.continuous_toENNReal.continuousAt (by simp)]
  congr
  ext m
  simp only [mem_image, mem_setOf_eq, mem_inter_iff, mem_range, mem_Iic]
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · obtain ⟨n, hn⟩ := hx
    refine ⟨⟨n, hn.2⟩, hn.2 ▸ hn.1⟩
  · obtain ⟨n, hn⟩ := hx.1
    refine ⟨n, ⟨hn ▸ hx.2, hn⟩⟩

private lemma floorAux_le (x : ℝ≥0∞) : floorAux x ≤ x := by
  simpa only [floorAux_eq_sSup_range_toENNReal_inter_Iic] using sSup_le fun _ h ↦ h.2

private lemma le_floorAux (h : m ≤ x) : m ≤ x.floorAux := le_sSup <| by simp [h]

noncomputable instance : EFloorSemiring ℝ≥0∞ where
  floor := floorAux
  floor_of_neg ha := (ENNReal.not_lt_zero ha).elim
  gc_floor := by
    intro a n _
    refine ⟨fun h ↦ le_trans ?_ <| floorAux_le a, fun h ↦ le_floorAux <| by exact_mod_cast h⟩
    rwa [← cast_enat_le_iff (α := ℝ≥0∞)] at h
  floor_lt := by
    intro a n _
    refine ⟨fun h ↦ ?_, fun h ↦ ENat.toENNReal_lt.mp <| lt_of_le_of_lt (floorAux_le _) h⟩
    · by_contra con
      exact (lt_self_iff_false n).mp <| (le_floorAux <| le_of_not_lt con).trans_lt h

end ENNReal

end ENNReal
