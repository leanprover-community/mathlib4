/-
Copyright (c) 2024 Emilie Burgun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilie Burgun
-/
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Dynamics.PeriodicPts
import Mathlib.Data.Set.Pointwise.SMul

/-!
# Properties of `fixedPoints` and `fixedBy`

This module contains some useful properties of `MulAction.fixedPoints` and `MulAction.fixedBy`
that don't directly belong to `Mathlib.GroupTheory.GroupAction.Basic`,
as well as the definition of `MulAction.movedBy` and `AddAction.movedBy`,
the complements of `MulAction.fixedBy` and `AddAction.fixedBy` respectively.

## Main theorems

* `MulAction.fixedBy_mul`, `MulAction.movedBy_mul` (and their `AddAction` equivalents),
  for the different relationship between the `movedBy`/`fixedBy` sets of `g*h`.
* `MulAction.fixedBy_conj` and `MulAction.movedBy_conj`: the pointwise group action on the sets
  `fixedBy α g` and `movedBy α g` translates to the conjugation action on `g`.
* `MulAction.smul_mem_of_movedBy_subset` shows that if a set `s` is a superset of
  `movedBy α g`, then the group action of `g` cannot send elements of `s` outside of `s`.
* `MulAction.not_commute_of_disjoint_movedBy_preimage` allows one to prove that two group elements
  do not commute from the disjointness of the `movedBy` set and its image by the second group
  element, which is a property used in the proof of Rubin's theorem.
-/

namespace MulAction
open Pointwise

variable {α : Type*}
variable {G : Type*} [Group G] [MulAction G α]
variable {M : Type*} [Monoid M] [MulAction M α]


section FixedPoints

variable (α) in
/-- In a multiplicative group action, the points fixed by `g` are also fixed by `g⁻¹` -/
@[to_additive (attr := simp) "In an additive group action, the points fixed by `g` are also fixed by `g⁻¹`"]
theorem fixedBy_inv_eq_fixedBy (g : G) : fixedBy α g⁻¹ = fixedBy α g := by
  ext x
  rw [mem_fixedBy, mem_fixedBy, inv_smul_eq_iff, eq_comm]

@[to_additive]
theorem smul_mem_fixedBy_iff_mem_fixedBy {a : α} {g : G} :
    g • a ∈ fixedBy α g ↔ a ∈ fixedBy α g := by
  rw [mem_fixedBy, smul_left_cancel_iff]
  rfl

theorem minimalPeriod_eq_one_of_fixedBy {a : α} {g : G} (a_in_fixedBy : a ∈ fixedBy α g) :
    Function.minimalPeriod (fun x => g • x) a = 1 := by
  rwa [Function.minimalPeriod_eq_one_iff_isFixedPt]

section AddAction.minimalPeriod_eq_one_of_fixedBy
variable {G : Type*} [AddGroup G] [AddAction G α]

theorem _root_.AddAction.minimalPeriod_eq_one_of_fixedBy {a : α} {g : G}
    (a_in_fixedBy : a ∈ AddAction.fixedBy α g) :
    Function.minimalPeriod (fun x => g +ᵥ x) a = 1 := by
  rwa [Function.minimalPeriod_eq_one_iff_isFixedPt]

end AddAction.minimalPeriod_eq_one_of_fixedBy

attribute [to_additive existing AddAction.minimalPeriod_eq_one_of_fixedBy]
  minimalPeriod_eq_one_of_fixedBy

variable (α) in
@[to_additive]
theorem fixedBy_subset_fixedBy_zpow (g : G) (j : ℤ) :
    fixedBy α g ⊆ fixedBy α (g ^ j) := by
  intro a a_in_fixedBy
  rw [mem_fixedBy, zpow_smul_eq_iff_minimalPeriod_dvd,
    minimalPeriod_eq_one_of_fixedBy a_in_fixedBy, Nat.cast_one]
  exact one_dvd j

variable (M α) in
@[to_additive (attr := simp)]
theorem fixedBy_one_eq_univ : fixedBy α (1 : M) = Set.univ :=
  Set.eq_univ_iff_forall.mpr (fun a => one_smul M a)

variable (α) in
@[to_additive]
theorem fixedBy_mul (m₁ m₂ : M) : fixedBy α m₁ ∩ fixedBy α m₂ ⊆ fixedBy α (m₁ * m₂) := by
  intro a ⟨h₁, h₂⟩
  rw [mem_fixedBy, mul_smul, h₂, h₁]

variable (α) in
@[to_additive]
theorem fixedBy_conj (g h : G) :
    fixedBy α (h * g * h⁻¹) = (fun a => h⁻¹ • a) ⁻¹' fixedBy α g := by
  ext a
  rw [Set.mem_preimage, mem_fixedBy, mem_fixedBy]
  repeat rw [mul_smul]
  exact smul_eq_iff_eq_inv_smul h

end FixedPoints

section MovedBy

/-!
## Moved points

`MulAction.movedBy` and `AddAction.movedBy` describe the sets of points `a : α` for which
`g • a ≠ a` (resp. `g +ᵥ a ≠ a`).
-/

variable (α) in
/-- The set of points moved by an element of the action. -/
@[to_additive "The set of points moved by an element of the action."]
def movedBy (m : M) : Set α := { a : α | m • a ≠ a }

@[to_additive (attr := simp)]
theorem mem_movedBy {m : M} {a : α} : a ∈ movedBy α m ↔ m • a ≠ a :=
  Iff.rfl

@[to_additive]
theorem movedBy_eq_compl_fixedBy {m : M} : movedBy α m = (fixedBy α m)ᶜ := rfl

@[to_additive]
theorem fixedBy_eq_compl_movedBy {m : M} : fixedBy α m = (movedBy α m)ᶜ := by
  rw [← compl_compl (fixedBy α m), movedBy_eq_compl_fixedBy]

@[to_additive]
theorem not_mem_fixedBy_iff_mem_movedBy {m : M} {a : α} : a ∉ fixedBy α m ↔ a ∈ movedBy α m :=
  Iff.rfl

@[to_additive]
theorem not_mem_movedBy_iff_mem_fixedBy {m : M} {a : α} : a ∉ movedBy α m ↔ a ∈ fixedBy α m := by
  rw [movedBy_eq_compl_fixedBy, Set.not_mem_compl_iff]

variable (α)

/-- In a multiplicative group action, the points moved by `g` are also moved by `g⁻¹` -/
@[to_additive "In an additive group action, the points moved by `g` are also moved by `g⁻¹`"]
theorem movedBy_eq_movedBy_inv (g : G) : movedBy α g = movedBy α g⁻¹ := by
  repeat rw [movedBy_eq_compl_fixedBy]
  rw [fixedBy_inv_eq_fixedBy]

variable {α}

@[to_additive]
theorem smul_mem_movedBy_iff_mem_movedBy {a : α} {g : G} :
    g • a ∈ movedBy α g ↔ a ∈ movedBy α g := by
  repeat rw [← not_mem_fixedBy_iff_mem_movedBy]
  rw [smul_mem_fixedBy_iff_mem_fixedBy]

@[to_additive]
theorem smul_inv_mem_movedBy_iff_mem_movedBy {a : α} {g : G} :
    g⁻¹ • a ∈ movedBy α g ↔ a ∈ movedBy α g :=
  (movedBy_eq_movedBy_inv α g) ▸ smul_mem_movedBy_iff_mem_movedBy

@[to_additive]
theorem movedBy_zpow_subset_movedBy (g : G) (j : ℤ) :
    movedBy α (g ^ j) ⊆ movedBy α g := by
  repeat rw [movedBy_eq_compl_fixedBy]
  rw [Set.compl_subset_compl]
  exact fixedBy_subset_fixedBy_zpow α g j

variable (M α) in
@[to_additive (attr := simp)]
theorem movedBy_one_eq_empty : movedBy α (1 : M) = ∅ := by
  rw [movedBy_eq_compl_fixedBy, fixedBy_one_eq_univ, Set.compl_univ]

variable (α) in
@[to_additive]
theorem movedBy_mul (m₁ m₂ : M) : movedBy α (m₁ * m₂) ⊆ movedBy α m₁ ∪ movedBy α m₂ := by
  repeat rw [movedBy_eq_compl_fixedBy]
  rw [← Set.compl_inter, Set.compl_subset_compl]
  exact fixedBy_mul α m₁ m₂

variable (α) in
@[to_additive]
theorem movedBy_conj (g h : G) :
    movedBy α (h * g * h⁻¹) = (fun a => h⁻¹ • a) ⁻¹' movedBy α g := by
  repeat rw [movedBy_eq_compl_fixedBy]
  rw [Set.preimage_compl, fixedBy_conj]

@[to_additive]
theorem smul_movedBy {g h : G} :
    h • movedBy α g = movedBy α (h * g * h⁻¹) := by
  rw [movedBy_conj, Set.preimage_smul, inv_inv]

end MovedBy

section Image

/-!
### Images of supersets of `movedBy α g`

If a set `s : Set α` is a superset of `MulAction.movedBy α g` (resp. `AddAction.movedBy α g`),
the no point or subset of `s` can be moved outside of `s` by the group action of `g`.
-/

/-- If `movedBy α g ⊆ s`, then `g` cannot move a point of `s` outside of `s`. -/
@[to_additive "If `movedBy α g ⊆ s`, then `g` cannot move a point of `s` outside of `s`."]
theorem smul_zpow_mem_of_movedBy_subset {a : α} {s : Set α} {g : G} (s_subset : movedBy α g ⊆ s)
    (j : ℤ) : g ^ j • a ∈ s ↔ a ∈ s := by
  by_cases a ∈ movedBy α (g ^ j)
  case pos a_moved =>
    constructor
    all_goals (intro; apply s_subset)
    all_goals apply movedBy_zpow_subset_movedBy g j
    · exact a_moved
    · rw [smul_mem_movedBy_iff_mem_movedBy]
      exact a_moved
  case neg a_fixed =>
    rw [not_mem_movedBy_iff_mem_fixedBy, mem_fixedBy] at a_fixed
    rw [a_fixed]

@[to_additive]
theorem smul_mem_of_movedBy_subset {a : α} {s : Set α} {g : G} (superset : movedBy α g ⊆ s) :
    g • a ∈ s ↔ a ∈ s := (zpow_one g) ▸ smul_zpow_mem_of_movedBy_subset superset 1

@[to_additive]
theorem smul_zpow_preimage_eq_of_movedBy_subset {s : Set α} {g : G} (superset : movedBy α g ⊆ s)
    (j : ℤ) : (fun a => g ^ j • a) ⁻¹' s = s := by
  ext a
  rw [Set.mem_preimage, smul_zpow_mem_of_movedBy_subset superset]

/-- If `movedBy α g ⊆ t`, then `g` cannot send a subset of `t` outside of `t`. -/
@[to_additive "If `movedBy α g ⊆ t`, then `g` cannot send a subset of `t` outside of `t`."]
theorem smul_zpow_subset_of_movedBy_subset {s t : Set α} {g : G}  (t_superset : movedBy α g ⊆ t)
    (s_ss_t : s ⊆ t) (j : ℤ): (fun a => g ^ j • a) ⁻¹' s ⊆ t := by
  rw [← smul_zpow_preimage_eq_of_movedBy_subset t_superset j]
  repeat rw [Set.preimage_smul]
  exact Set.smul_set_mono s_ss_t

end Image

section Commute

/-!
If two group elements `g` and `h` commute, then `g` fixes `h • x` (resp. `h +ᵥ x`)
if and only if `g` fixes `x`.

In other words, if `Commute g h`, then `fixedBy α g ∈ fixedBy (Set α) h` and
`movedBy α g ∈ fixedBy (Set α) h`.
-/

/--
If `g` and `h` commute, then `g` fixes `h • x` iff `g` fixes `x`.
This is equivalent to say that the set `fixedBy α g` is fixed by `h`.
-/
@[to_additive "If `g` and `h` commute, then `g` fixes `h +ᵥ x` iff `g` fixes `x`.
This is equivalent to say that the set `fixedBy α g` is fixed by `h`.
"]
theorem fixedBy_mem_fixedBy_of_commute {g h : G} (comm: Commute g h) :
    (fixedBy α g) ∈ fixedBy (Set α) h := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem, mem_fixedBy, ← mul_smul, comm.inv_right, mul_smul,
    smul_left_cancel_iff]
  rfl

/--
If `g` and `h` commute, then `g` fixes `(h^j) • x` iff `g` fixes `x`.
-/
@[to_additive "If `g` and `h` commute, then `g` fixes `(j • h) +ᵥ x` iff `g` fixes `x`."]
theorem smul_zpow_fixedBy_eq_of_commute {g h : G} (comm : Commute g h) (j : ℤ):
    h^j • fixedBy α g = fixedBy α g :=
  fixedBy_subset_fixedBy_zpow (Set α) h j (fixedBy_mem_fixedBy_of_commute comm)

/--
If `g` and `h` commute, then `g` moves `h • x` iff `g` moves `x`.
This is equivalent to say that the set `movedBy α g` is fixed by `h`.
-/
@[to_additive "If `g` and `h` commute, then `g` moves `h +ᵥ x` iff `g` moves `x`.
This is equivalent to say that the set `movedBy α g` is fixed by `h`."]
theorem movedBy_mem_fixedBy_of_commute {g h : G} (comm: Commute g h) :
    (movedBy α g) ∈ fixedBy (Set α) h := by
  rw [mem_fixedBy, movedBy_eq_compl_fixedBy, Set.compl_eq_univ_diff, Set.smul_set_sdiff,
    Set.smul_set_univ, fixedBy_mem_fixedBy_of_commute comm]

/--
If `g` and `h` commute, then `g` moves `h^j • x` iff `g` moves `x`.
-/
@[to_additive "If `g` and `h` commute, then `g` moves `(j • h) +ᵥ x` iff `g` moves `x`."]
theorem smul_zpow_movedBy_eq_of_commute {g h : G} (comm : Commute g h) (j : ℤ):
    h ^ j • movedBy α g = movedBy α g :=
  fixedBy_subset_fixedBy_zpow (Set α) h j (movedBy_mem_fixedBy_of_commute comm)

end Commute

section Faithful

variable [FaithfulSMul G α]
variable [FaithfulSMul M α]

/-- If the multiplicative action of `M` on `α` is faithful,
then an empty `movedBy α m` set implies that `m = 1`. -/
@[to_additive "If the additive action of `M` on `α` is faithful,
then an empty `movedBy α m` set implies that `m = 1`."]
theorem movedBy_empty_iff_eq_one {m : M} : movedBy α m = ∅ ↔ m = 1 := by
  constructor
  · intro moved_empty
    apply FaithfulSMul.eq_of_smul_eq_smul (α := α)
    intro a
    rw [one_smul]
    by_contra ma_ne_a
    rwa [← ne_eq, ← mem_movedBy, moved_empty] at ma_ne_a
  · intro eq_one
    rw [eq_one]
    exact movedBy_one_eq_empty α M

/--
If the image of the `movedBy α g` set by the multiplicative action of `h: G`
is disjoint from `movedBy α g`, then `g` and `h` cannot commute.
-/
theorem not_commute_of_disjoint_movedBy_preimage {g h : G} (ne_one : g ≠ 1)
    (disjoint : Disjoint (movedBy α g) (h • movedBy α g)) : ¬Commute g h := by
  intro comm
  rw [movedBy_mem_fixedBy_of_commute comm, disjoint_self, Set.bot_eq_empty,
    movedBy_empty_iff_eq_one] at disjoint
  exact ne_one disjoint

end Faithful

end MulAction
