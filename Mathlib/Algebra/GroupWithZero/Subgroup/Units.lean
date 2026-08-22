/-
Copyright (c) 2026 Edison Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xu
-/
module

public import Mathlib.Algebra.GroupWithZero.Subgroup.Lattice
public import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Subgroups with zero of `G₀` versus subgroups of `G₀ˣ`

Taking the units of a subgroup with zero and adjoining `0` to a subgroup of `G₀ˣ` are mutually
inverse order isomorphisms. This is the device that lets the `Subgroup G₀ˣ` API be reused for
subgroups with zero rather than reproved.

## Main definitions

* `SubgroupWithZero.units s`: the units of `s`, as a subgroup of `G₀ˣ`;
* `Subgroup.withZero H`: the subgroup with zero `insert 0 (Units.val '' H)`;
* `SubgroupWithZero.unitsOrderIso`: the order isomorphism between the two;

## Main results

* `SubgroupWithZero.units_closure`: taking units turns `SubgroupWithZero.closure` into
  `Subgroup.closure` of the preimage.

## Tags
subgroup with zero, units
-/

@[expose] public section

assert_not_exists Ring

variable {G₀ : Type*} [GroupWithZero G₀]

namespace SubgroupWithZero

/-- The units of a subgroup with zero of `G₀`, as a subgroup of `G₀ˣ`. -/
def units (s : SubgroupWithZero G₀) : Subgroup G₀ˣ where
  carrier := {u : G₀ˣ | (u : G₀) ∈ s}
  one_mem' := one_mem s
  mul_mem' {u v} hu hv := by
    change ((u : G₀ˣ) : G₀) ∈ s at hu
    change ((v : G₀ˣ) : G₀) ∈ s at hv
    change ((u * v : G₀ˣ) : G₀) ∈ s
    rw [Units.val_mul]
    exact mul_mem hu hv
  inv_mem' {u} hu := by
    change ((u : G₀ˣ) : G₀) ∈ s at hu
    change ((u⁻¹ : G₀ˣ) : G₀) ∈ s
    rw [Units.val_inv_eq_inv_val]
    exact inv_mem hu

@[simp]
theorem mem_units {s : SubgroupWithZero G₀} {u : G₀ˣ} : u ∈ s.units ↔ (u : G₀) ∈ s := Iff.rfl

@[simp, norm_cast]
theorem coe_units (s : SubgroupWithZero G₀) :
    (s.units : Set G₀ˣ) = Units.val ⁻¹' (s : Set G₀) := rfl

@[gcongr]
theorem units_mono {s t : SubgroupWithZero G₀} (h : s ≤ t) : s.units ≤ t.units := fun _ hu ↦ h hu

end SubgroupWithZero

namespace Subgroup

/-- A subgroup of `G₀ˣ`, regarded as a subgroup with zero of `G₀` by adjoining `0`. -/
def withZero (H : Subgroup G₀ˣ) : SubgroupWithZero G₀ where
  carrier := insert 0 (Units.val '' (H : Set G₀ˣ))
  zero_mem' := Set.mem_insert _ _
  one_mem' := Set.mem_insert_of_mem _ ⟨1, H.one_mem, rfl⟩
  mul_mem' {a b} ha hb := by
    rcases ha with rfl | ⟨u, hu, rfl⟩
    · simp
    rcases hb with rfl | ⟨v, hv, rfl⟩
    · simp
    exact Set.mem_insert_of_mem _ ⟨u * v, H.mul_mem hu hv, by simp⟩
  inv_mem' {a} ha := by
    rcases ha with rfl | ⟨u, hu, rfl⟩
    · simp
    exact Set.mem_insert_of_mem _ ⟨u⁻¹, H.inv_mem hu, by simp⟩

@[simp]
theorem mem_withZero {H : Subgroup G₀ˣ} {x : G₀} :
    x ∈ H.withZero ↔ x = 0 ∨ ∃ u ∈ H, (u : G₀) = x := Iff.rfl

@[simp, norm_cast]
theorem coe_withZero (H : Subgroup G₀ˣ) :
    (H.withZero : Set G₀) = insert 0 (Units.val '' (H : Set G₀ˣ)) := rfl

theorem mem_withZero_of_ne_zero {H : Subgroup G₀ˣ} {x : G₀} (hx : x ≠ 0) :
    x ∈ H.withZero ↔ ∃ u ∈ H, (u : G₀) = x := by simp [hx]

@[gcongr]
theorem withZero_mono {H K : Subgroup G₀ˣ} (h : H ≤ K) : H.withZero ≤ K.withZero := by
  rintro x hx
  rw [mem_withZero] at hx ⊢
  rcases hx with rfl | ⟨u, hu, rfl⟩
  · exact .inl rfl
  · exact .inr ⟨u, h hu, rfl⟩

end Subgroup

namespace SubgroupWithZero

@[simp]
theorem withZero_units (s : SubgroupWithZero G₀) : s.units.withZero = s := by
  ext x
  rcases eq_or_ne x 0 with rfl | hx
  · simp [zero_mem s]
  · rw [Subgroup.mem_withZero_of_ne_zero hx]
    exact ⟨fun ⟨u, hu, hux⟩ ↦ hux ▸ hu, fun hxs ↦ ⟨Units.mk0 x hx, hxs, rfl⟩⟩

@[simp]
theorem units_withZero (H : Subgroup G₀ˣ) : H.withZero.units = H := by
  ext u
  rw [mem_units, Subgroup.mem_withZero]
  constructor
  · rintro (h0 | ⟨v, hv, hvu⟩)
    · exact absurd h0 u.ne_zero
    · exact (Units.val_injective hvu : v = u) ▸ hv
  · exact fun hu ↦ .inr ⟨u, hu, rfl⟩

/-- **Subgroups with zero of `G₀` are the same thing as subgroups of `G₀ˣ`.** -/
@[simps]
def unitsOrderIso : SubgroupWithZero G₀ ≃o Subgroup G₀ˣ where
  toFun := units
  invFun := Subgroup.withZero
  left_inv := withZero_units
  right_inv := units_withZero
  map_rel_iff' {s t} := by
    refine ⟨fun h ↦ ?_, units_mono⟩
    have h' : s.units ≤ t.units := h
    simpa only [withZero_units] using Subgroup.withZero_mono h'

@[simp] theorem units_top : (⊤ : SubgroupWithZero G₀).units = ⊤ := by ext u; simp

@[simp] theorem units_bot : (⊥ : SubgroupWithZero G₀).units = ⊥ := by
  ext u
  rw [mem_units, mem_bot, Subgroup.mem_bot]
  refine ⟨fun h ↦ ?_, fun h ↦ .inr (by rw [h]; rfl)⟩
  rcases h with h | h
  · exact absurd h u.ne_zero
  · exact Units.val_eq_one.1 h

@[simp]
theorem units_eq_bot {s : SubgroupWithZero G₀} : s.units = ⊥ ↔ s = ⊥ := by
  rw [← units_bot]
  exact unitsOrderIso.injective.eq_iff

/-! ### Non-degeneracy

`⊥ = {0, 1}`, so `Nontrivial ↥s` holds for *every* subgroup with zero and is useless as a
non-degeneracy hypothesis: there is no analogue of `Subgroup.nontrivial_iff_ne_bot`.
`Nontrivial (↥s)ˣ` is the right condition. -/

theorem eq_bot_iff_forall {s : SubgroupWithZero G₀} : s = ⊥ ↔ ∀ x ∈ s, x = 0 ∨ x = 1 := by
  rw [eq_bot_iff]
  exact ⟨fun h _ hx ↦ mem_bot.1 (h hx), fun h _ hx ↦ mem_bot.2 (h _ hx)⟩

theorem ne_bot_iff_exists {s : SubgroupWithZero G₀} : s ≠ ⊥ ↔ ∃ x ∈ s, x ≠ 0 ∧ x ≠ 1 := by
  simp [eq_bot_iff_forall, not_or]

/-- **The non-degeneracy criterion.** Note that `Nontrivial ↥s` is *not* equivalent to `s ≠ ⊥`:
it holds for every `s`, since `⊥ = {0, 1}`. -/
@[simp]
theorem nontrivial_units_iff_ne_bot {s : SubgroupWithZero G₀} : Nontrivial (↥s)ˣ ↔ s ≠ ⊥ := by
  rw [ne_bot_iff_exists]
  constructor
  · rintro ⟨u, w, huw⟩
    rcases eq_or_ne u 1 with rfl | hu
    · refine ⟨((w : ↥s) : G₀), (w : ↥s).2, ZeroMemClass.coe_eq_zero.not.2 w.ne_zero, ?_⟩
      exact OneMemClass.coe_eq_one.not.2 fun h ↦ huw.symm (Units.ext (by simpa using h))
    · refine ⟨((u : ↥s) : G₀), (u : ↥s).2, ZeroMemClass.coe_eq_zero.not.2 u.ne_zero, ?_⟩
      exact OneMemClass.coe_eq_one.not.2 fun h ↦ hu (Units.ext (by simpa using h))
  · rintro ⟨x, hx, hx0, hx1⟩
    refine ⟨Units.mk0 (⟨x, hx⟩ : ↥s) (fun h ↦ hx0 (ZeroMemClass.coe_eq_zero.2 h)), 1, ?_⟩
    intro h
    rw [Units.ext_iff] at h
    exact hx1 (congrArg Subtype.val h)

/-- The units of the *subtype* `↥s` versus the subgroup of units `s.units`. These are not
definitionally equal, so this equivalence is what lets statements about `(↥s)ˣ` reach the
`Subgroup G₀ˣ` API. -/
def unitsMulEquiv (s : SubgroupWithZero G₀) : (↥s)ˣ ≃* ↥s.units where
  toFun u := ⟨Units.mk0 ((u : ↥s) : G₀) (ZeroMemClass.coe_eq_zero.not.2 u.ne_zero), (u : ↥s).2⟩
  invFun w := Units.mk0 (⟨((w : G₀ˣ) : G₀), w.2⟩ : ↥s)
    fun h ↦ (w : G₀ˣ).ne_zero (congrArg Subtype.val h)
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_mul' _ _ := by ext; rfl

instance nontrivial_units_subgroup (s : SubgroupWithZero G₀) [Nontrivial (↥s)ˣ] :
    Nontrivial ↥s.units :=
  (unitsMulEquiv s).toEquiv.injective.nontrivial

/-- Taking units turns the closure of `k` into the `Subgroup` closure of the preimage of `k`.

This is the hook through which the whole `Subgroup.closure` API — `closure_induction`,
`mem_closure_iff`, `zpowers`, `IsCyclic`, … — transfers to subgroups with zero. -/
@[simp]
theorem units_closure (k : Set G₀) :
    (closure k).units = Subgroup.closure (Units.val ⁻¹' k) := by
  refine le_antisymm ?_ ((Subgroup.closure_le _).2 fun u hu ↦ subset_closure hu)
  rw [← units_withZero (Subgroup.closure (Units.val ⁻¹' k))]
  refine units_mono (closure_le.2 fun x hx ↦ ?_)
  rcases eq_or_ne x 0 with rfl | hx0
  · exact zero_mem _
  · exact Subgroup.mem_withZero.2 <| .inr ⟨Units.mk0 x hx0, Subgroup.subset_closure hx, rfl⟩

theorem closure_eq_withZero (k : Set G₀) :
    closure k = (Subgroup.closure (Units.val ⁻¹' k)).withZero := by
  rw [← units_closure, withZero_units]

end SubgroupWithZero
