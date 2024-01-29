/-
Copyright (c) 2024 Emilie Burgun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilie Burgun
-/
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Period
import Mathlib.Data.Set.Pointwise.SMul

/-!
# Properties of `fixedPoints` and `fixedBy`

This module contains some useful properties of `MulAction.fixedPoints` and `MulAction.fixedBy`
that don't directly belong to `Mathlib.GroupTheory.GroupAction.Basic`.

## Main theorems

* `MulAction.fixedBy_mul`: `fixedBy α (g * h) ⊆ fixedBy α g ∪ fixedBy α h`
* `MulAction.fixedBy_conj` and `MulAction.smul_fixedBy`: the pointwise group action of `h` on
  `fixedBy α g` is equal to the `fixedBy` set of the conjugation of `h` with `g`
  (`fixedBy α (h * g * h⁻¹)`).
* `MulAction.set_mem_fixedBy_of_movedBy_subset` shows that if a set `s` is a superset of
  `(fixedBy α g)ᶜ`, then the group action of `g` cannot send elements of `s` outside of `s`.
  This is expressed as `s ∈ fixedBy (Set α) g`, and `MulAction.set_mem_fixedBy_iff` allows one
  to convert the relationship back to `g • x ∈ s ↔ x ∈ s`.
* `MulAction.not_commute_of_disjoint_smul_movedBy` allows one to prove that `g` and `h`
  do not commute from the disjointness of the `(fixedBy α g)ᶜ` set and `h • (fixedBy α g)ᶜ`,
  which is a property used in the proof of Rubin's theorem.

The theorems above are also available for `AddAction`.

## Pointwise group action and `fixedBy (Set α) g`

Since `fixedBy α g = { x | g • x = x }` by definition, properties about the pointwise action of
a set `s : Set α` can be expressed using `fixedBy (Set α) g`.
To properly use theorems using `fixedBy (Set α) g`, you should `open Pointwise` in your file.

`s ∈ fixedBy (Set α) g` means that `g • s = s`, which is equivalent to say that
`∀ x, g • x ∈ s ↔ x ∈ s` (the translation can be done using `MulAction.set_mem_fixedBy_iff`).

`s ∈ fixedBy (Set α) g` is a weaker statement than `s ⊆ fixedBy α g`: the latter requires that
all points in `s` are fixed by `g`, whereas the former only requires that `g • x ∈ s`.
-/

namespace MulAction
open Pointwise

variable {α : Type*}
variable {G : Type*} [Group G] [MulAction G α]
variable {M : Type*} [Monoid M] [MulAction M α]


section FixedPoints

variable (α) in
/-- In a multiplicative group action, the points fixed by `g` are also fixed by `g⁻¹` -/
@[to_additive (attr := simp)
  "In an additive group action, the points fixed by `g` are also fixed by `-g`"]
theorem fixedBy_inv (g : G) : fixedBy α g⁻¹ = fixedBy α g := by
  ext
  rw [mem_fixedBy, mem_fixedBy, inv_smul_eq_iff, eq_comm]

@[to_additive]
theorem smul_mem_fixedBy_iff_mem_fixedBy {a : α} {g : G} :
    g • a ∈ fixedBy α g ↔ a ∈ fixedBy α g := by
  rw [mem_fixedBy, smul_left_cancel_iff]
  rfl

@[to_additive]
theorem smul_inv_mem_fixedBy_iff_mem_fixedBy {a : α} {g : G} :
    g⁻¹ • a ∈ fixedBy α g ↔ a ∈ fixedBy α g := by
  rw [← fixedBy_inv, smul_mem_fixedBy_iff_mem_fixedBy, fixedBy_inv]

@[to_additive period_eq_one_iff_fixedBy]
theorem period_eq_one_iff_fixedBy {a : α} {g : G} :
    period g a = 1 ↔ a ∈ fixedBy α g :=
  Function.minimalPeriod_eq_one_iff_isFixedPt

variable (α) in
@[to_additive]
theorem fixedBy_subset_fixedBy_zpow (g : G) (j : ℤ) :
    fixedBy α g ⊆ fixedBy α (g ^ j) := by
  intro a a_in_fixedBy
  rw [mem_fixedBy, zpow_smul_eq_iff_minimalPeriod_dvd,
    minimalPeriod_eq_one_iff_fixedBy.mpr a_in_fixedBy, Nat.cast_one]
  exact one_dvd j

variable (α) in
@[to_additive]
theorem fixedBy_zpow_subset_of_dvd (g : G) {j k : ℤ} (dvd : j ∣ k):
    fixedBy α (g ^ j) ⊆ fixedBy α (g ^ k) := by
  intro a a_in_fixedBy
  let ⟨n, eq⟩ := dvd
  rw [eq, zpow_mul]
  apply fixedBy_subset_fixedBy_zpow
  exact a_in_fixedBy

variable (α) in
@[to_additive]
theorem fixedBy_pow_subset_of_dvd (g : G) {n m : ℕ} (dvd : n ∣ m):
    fixedBy α (g ^ n) ⊆ fixedBy α (g ^ m) := by
  rw [← zpow_ofNat, ← zpow_ofNat]
  exact fixedBy_zpow_subset_of_dvd α g (Nat.coe_nat_dvd dvd)

variable (M α) in
@[to_additive (attr := simp)]
theorem fixedBy_one_eq_univ : fixedBy α (1 : M) = Set.univ :=
  Set.eq_univ_iff_forall.mpr <| one_smul M

variable (α) in
@[to_additive]
theorem fixedBy_mul (m₁ m₂ : M) : fixedBy α m₁ ∩ fixedBy α m₂ ⊆ fixedBy α (m₁ * m₂) := by
  intro a ⟨h₁, h₂⟩
  rw [mem_fixedBy, mul_smul, h₂, h₁]

variable (α) in
@[to_additive]
theorem smul_fixedBy (g h: G) :
    h • fixedBy α g = fixedBy α (h * g * h⁻¹) := by
  ext a
  simp_rw [Set.mem_smul_set_iff_inv_smul_mem, mem_fixedBy, mul_smul, smul_eq_iff_eq_inv_smul h]

variable (α) in
theorem fixedBy_commutatorElement (g h : G) :
    fixedBy α h ∩ g • fixedBy α h ⊆ fixedBy α ⁅g, h⁆ := by
  rw [smul_fixedBy, commutatorElement_def, Set.inter_comm, ← fixedBy_inv_eq_fixedBy α (g := h)]
  apply fixedBy_mul α

@[to_additive]
theorem mem_fixedBy_pow_period (g : G) (x : α) : x ∈ fixedBy α (g ^ period g x) := by
  rw [mem_fixedBy, smul_pow_period_fixed]

end FixedPoints

section Pointwise

/-!
### `fixedBy` sets of the pointwise group action

The theorems below need the `Pointwise` scoped to be opened (using `open Pointwise`)
to be used effectively.
-/

/--
If a set `s : Set α` is in `fixedBy (Set α) g`, then all points of `s` will stay in `s` after being
moved by `g`.
-/
@[to_additive "If a set `s : Set α` is in `fixedBy (Set α) g`, then all points of `s` will stay in
`s` after being moved by `g`."]
theorem set_mem_fixedBy_iff (s : Set α) (g : G) :
    s ∈ fixedBy (Set α) g ↔ ∀ x, g • x ∈ s ↔ x ∈ s := by
  simp_rw [mem_fixedBy, ← eq_inv_smul_iff, Set.ext_iff, Set.mem_inv_smul_set_iff, Iff.comm]

theorem smul_mem_of_set_mem_fixedBy {s : Set α} {g : G} (s_in_fixedBy : s ∈ fixedBy (Set α) g)
    {x : α} : g • x ∈ s ↔ x ∈ s := (set_mem_fixedBy_iff s g).mp s_in_fixedBy x

/--
If `s ⊆ fixedBy α g`, then `g • s = s`, which means that `s ∈ fixedBy (Set α) g`.

Note that the reverse implication is in general not true, as `s ∈ fixedBy (Set α) g` is a
weaker statement (it allows for points `x ∈ s` for which `g • x ≠ x` and `g • x ∈ s`).
-/
@[to_additive "If `s ⊆ fixedBy α g`, then `g +ᵥ s = s`, which means that `s ∈ fixedBy (Set α) g`.

Note that the reverse implication is in general not true, as `s ∈ fixedBy (Set α) g` is a
weaker statement (it allows for points `x ∈ s` for which `g +ᵥ x ≠ x` and `g +ᵥ x ∈ s`)."]
theorem set_mem_fixedBy_of_subset_fixedBy {s : Set α} {g : G} (s_ss_fixedBy : s ⊆ fixedBy α g) :
    s ∈ fixedBy (Set α) g := by
  rw [← fixedBy_inv]
  ext x
  rw [Set.mem_inv_smul_set_iff]
  refine ⟨fun gxs => ?xs, fun xs => (s_ss_fixedBy xs).symm ▸ xs⟩
  rw [← fixedBy_inv] at s_ss_fixedBy
  rwa [← s_ss_fixedBy gxs, inv_smul_smul] at gxs

theorem smul_subset_of_set_mem_fixedBy {s t : Set α} {g : G} (t_ss_s : t ⊆ s)
    (s_in_fixedBy : s ∈ fixedBy (Set α) g) : g • t ⊆ s :=
  (Set.set_smul_subset_set_smul_iff.mpr t_ss_s).trans s_in_fixedBy.subset

/-!
If a set `s : Set α` is a superset of `(MulAction.fixedBy α g)ᶜ` (resp. `(AddAction.fixedBy α g)ᶜ`),
then no point or subset of `s` can be moved outside of `s` by the group action of `g`.
-/

/-- If `(fixedBy α g)ᶜ ⊆ s`, then `g` cannot move a point of `s` outside of `s`. -/
@[to_additive "If `(fixedBy α g)ᶜ ⊆ s`, then `g` cannot move a point of `s` outside of `s`."]
theorem set_mem_fixedBy_of_movedBy_subset {s : Set α} {g : G} (s_subset : (fixedBy α g)ᶜ ⊆ s) :
    s ∈ fixedBy (Set α) g := by
  rw [← fixedBy_inv]
  ext a
  rw [Set.mem_inv_smul_set_iff]
  by_cases a ∈ fixedBy α g
  case pos a_fixed =>
    rw [a_fixed]
  case neg a_moved =>
    constructor <;> (intro; apply s_subset)
    · exact a_moved
    · rwa [Set.mem_compl_iff, smul_mem_fixedBy_iff_mem_fixedBy]

/--
If the action of `f` does not move points of `s` outside of `s`, and `g • s` is disjoint from `s`,
then all points of `s` are fixed by `g * f * g⁻¹`.
-/
theorem subset_fixedBy_conj_of_movedBy_subset_of_disj {f g : G} {s : Set α}
    (superset : (fixedBy α f)ᶜ ⊆ s) (disj : Disjoint s (g • s)) : s ⊆ fixedBy α (g * f * g⁻¹) := by
  rw [← smul_fixedBy, ← Set.compl_subset_compl, ← Set.smul_set_compl]
  apply subset_trans _ disj.subset_compl_left
  exact Set.smul_set_mono superset

/--
If all points of `s` are fixed by `g * f * g⁻¹`, then `⁅f, g⁆ • s = f • s`
-/
lemma commutatorElement_smul_eq_of_subset_fixedBy_conj {f g : G} {s : Set α}
    (subset : s ⊆ fixedBy α (g * f * g⁻¹)) : ⁅f, g⁆ • s = f • s := by
  rw [commutatorElement_def]
  repeat rw [mul_smul]
  rw [smul_left_cancel_iff]
  repeat rw [← mul_smul]
  rw [← smul_fixedBy, ← fixedBy_inv_eq_fixedBy, smul_fixedBy] at subset
  exact set_mem_fixedBy_of_subset_fixedBy subset

end Pointwise

section InjOn

/-! ## `fixedBy` and `Set.InjOn s (· • x)`
-/

theorem mem_fixedBy_compl_mul_of_smul_injOn {s : Set G} {x : α} (inj_on : s.InjOn (· • x)) {g h : G}
    (g_in_s : g ∈ s) (h_in_s : h ∈ s) (g_ne_h : g ≠ h) : x ∈ (fixedBy α (h⁻¹ * g))ᶜ := by
  rw [Set.mem_compl_iff, mem_fixedBy, mul_smul, smul_eq_iff_eq_inv_smul, inv_inv]
  exact mt (inj_on g_in_s h_in_s) g_ne_h

end InjOn

section Commute

/-!
## Pointwise image of the `fixedBy` set by a commuting group element

If two group elements `g` and `h` commute, then `g` fixes `h • x` (resp. `h +ᵥ x`)
if and only if `g` fixes `x`.

This is equivalent to say that if `Commute g h`, then `fixedBy α g ∈ fixedBy (Set α) h` and
`(fixedBy α g)ᶜ ∈ fixedBy (Set α) h`.
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
    smul_left_cancel_iff, mem_fixedBy]

/--
If `g` and `h` commute, then `g` fixes `(h ^ j) • x` iff `g` fixes `x`.
-/
@[to_additive "If `g` and `h` commute, then `g` fixes `(j • h) +ᵥ x` iff `g` fixes `x`."]
theorem smul_zpow_fixedBy_eq_of_commute {g h : G} (comm : Commute g h) (j : ℤ) :
    h ^ j • fixedBy α g = fixedBy α g :=
  fixedBy_subset_fixedBy_zpow (Set α) h j (fixedBy_mem_fixedBy_of_commute comm)

/--
If `g` and `h` commute, then `g` moves `h • x` iff `g` moves `x`.
This is equivalent to say that the set `(fixedBy α g)ᶜ` is fixed by `h`.
-/
@[to_additive "If `g` and `h` commute, then `g` moves `h +ᵥ x` iff `g` moves `x`.
This is equivalent to say that the set `(fixedBy α g)ᶜ` is fixed by `h`."]
theorem movedBy_mem_fixedBy_of_commute {g h : G} (comm: Commute g h) :
    (fixedBy α g)ᶜ ∈ fixedBy (Set α) h := by
  rw [mem_fixedBy, Set.smul_set_compl, fixedBy_mem_fixedBy_of_commute comm]

/--
If `g` and `h` commute, then `g` moves `h ^ j • x` iff `g` moves `x`.
-/
@[to_additive "If `g` and `h` commute, then `g` moves `(j • h) +ᵥ x` iff `g` moves `x`."]
theorem smul_zpow_movedBy_eq_of_commute {g h : G} (comm : Commute g h) (j : ℤ) :
    h ^ j • (fixedBy α g)ᶜ = (fixedBy α g)ᶜ :=
  fixedBy_subset_fixedBy_zpow (Set α) h j (movedBy_mem_fixedBy_of_commute comm)

end Commute

section Faithful

variable [FaithfulSMul G α]
variable [FaithfulSMul M α]

/-- If the multiplicative action of `M` on `α` is faithful,
then `fixedBy α m = Set.univ` implies that `m = 1`. -/
@[to_additive "If the additive action of `M` on `α` is faithful,
then `fixedBy α m = Set.univ` implies that `m = 1`."]
theorem fixedBy_eq_univ_iff_eq_one {m : M} : fixedBy α m = Set.univ ↔ m = 1 := by
  rw [← (smul_left_injective' (M := M) (α := α)).eq_iff, Set.eq_univ_iff_forall]
  simp_rw [Function.funext_iff, one_smul, mem_fixedBy]

variable (α) in
/-- `m ≠ 1` implies that `m` must move some point. -/
@[to_additive "`m ≠ 0` implies that `m` must move some point."]
theorem fixedBy_compl_nonempty_of_ne_one {m : M} (g_ne_one : m ≠ 1) : (fixedBy α m)ᶜ.Nonempty := by
  by_contra empty
  rw [Set.not_nonempty_iff_eq_empty, ← Set.compl_univ, compl_inj_iff,
    fixedBy_eq_univ_iff_eq_one] at empty
  exact g_ne_one empty

/--
If the image of the `(fixedBy α g)ᶜ` set by the pointwise action of `h: G`
is disjoint from `(fixedBy α g)ᶜ`, then `g` and `h` cannot commute.
-/
@[to_additive "If the image of the `(fixedBy α g)ᶜ` set by the pointwise action of `h: G`
is disjoint from `(fixedBy α g)ᶜ`, then `g` and `h` cannot commute."]
theorem not_commute_of_disjoint_movedBy_preimage {g h : G} (ne_one : g ≠ 1)
    (disjoint : Disjoint (fixedBy α g)ᶜ (h • (fixedBy α g)ᶜ)) : ¬Commute g h := by
  contrapose! ne_one with comm
  rwa [movedBy_mem_fixedBy_of_commute comm, disjoint_self, Set.bot_eq_empty, ← Set.compl_univ,
    compl_inj_iff, fixedBy_eq_univ_iff_eq_one] at disjoint

variable (α) in
/--
If the action is faithful, then `g` and `h` commute if `(fixedBy α g)ᶜ` is disjoint from
`(fixedBy α h)ᶜ`.
-/
theorem commute_of_disjoint_movedBy {g h : G} (disjoint : Disjoint (fixedBy α g)ᶜ (fixedBy α h)ᶜ) :
    Commute g h := by
  apply FaithfulSMul.eq_of_smul_eq_smul (α := α)
  intro a
  rw [mul_smul, mul_smul]

  by_cases a_fixed : a ∈ fixedBy α g
  rw [Set.disjoint_compl_left_iff_subset] at disjoint
  swap
  have a_fixed := Set.disjoint_compl_right_iff_subset.mp disjoint a_fixed
  rw [Set.disjoint_compl_right_iff_subset] at disjoint

  all_goals {
    rw [a_fixed]
    rw [← fixedBy_inv_eq_fixedBy] at disjoint
    rw [← set_mem_fixedBy_of_movedBy_subset disjoint, Set.mem_inv_smul_set_iff] at a_fixed
    rw [a_fixed]
  }

end Faithful

end MulAction
