/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Aaron Anderson, Yakov Pechersky
-/
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Set.Finite

#align_import group_theory.perm.support from "leanprover-community/mathlib"@"9003f28797c0664a49e4179487267c494477d853"

/-!
# support of a permutation

## Main definitions

In the following, `f g : Equiv.Perm α`.

* `Equiv.Perm.Disjoint`: two permutations `f` and `g` are `Disjoint` if every element is fixed
  either by `f`, or by `g`.
  Equivalently, `f` and `g` are `Disjoint` iff their `support` are disjoint.
* `Equiv.Perm.IsSwapOn f x y`: `f` maps `x` to `y`, `y` to `x`, and fixes all other elements.
* `Equiv.Perm.IsSwap`: `f` transposes some distinct elements `x` and `y`, and
  fixes all other elements.
* `Equiv.Perm.support`: the elements `x : α` that are not fixed by `f`.
* `Equiv.Perm.supportCard`: the cardinality of `f.support` when it is finite. Noncomputable but
  has a computable representation when `α` is a `Fintype` with decidable equality.

Assume `α` is a Fintype:
* `Equiv.Perm.fixed_point_card_lt_of_ne_one f` says that `f` has
  strictly less than `Fintype.card α - 1` fixed points, unless `f = 1`.
  (Equivalently, `f.support` has at least 2 elements.)

-/


open Equiv Set

namespace Equiv.Perm

variable {α β : Type*}

section Disjoint

/-- Two permutations `f` and `g` are `Disjoint` if their supports are disjoint, i.e.,
every element is fixed either by `f`, or by `g`. -/
def Disjoint (f g : Perm α) :=
  ∀ x, f x = x ∨ g x = x
#align equiv.perm.disjoint Equiv.Perm.Disjoint

variable {f g h : Perm α}

theorem disjoint_iff_eq_or_eq : Disjoint f g ↔ ∀ x : α, f x = x ∨ g x = x :=
  Iff.rfl
#align equiv.perm.disjoint_iff_eq_or_eq Equiv.Perm.disjoint_iff_eq_or_eq

@[symm]
theorem Disjoint.symm : Disjoint f g → Disjoint g f := by simp only [Disjoint, or_comm, imp_self]
#align equiv.perm.disjoint.symm Equiv.Perm.Disjoint.symm

theorem Disjoint.symmetric : Symmetric (@Disjoint α) := fun _ _ => Disjoint.symm
#align equiv.perm.disjoint.symmetric Equiv.Perm.Disjoint.symmetric

instance : IsSymm (Perm α) Disjoint :=
  ⟨Disjoint.symmetric⟩

theorem disjoint_comm : Disjoint f g ↔ Disjoint g f :=
  ⟨Disjoint.symm, Disjoint.symm⟩
#align equiv.perm.disjoint_comm Equiv.Perm.disjoint_comm

theorem Disjoint.commute (h : Disjoint f g) : Commute f g :=
  Equiv.ext fun x =>
    (h x).elim
      (fun hf =>
        (h (g x)).elim (fun hg => by simp [mul_apply, hf, hg]) fun hg => by
          simp [mul_apply, hf, g.injective hg])
      fun hg =>
      (h (f x)).elim (fun hf => by simp [mul_apply, f.injective hf, hg]) fun hf => by
        simp [mul_apply, hf, hg]
#align equiv.perm.disjoint.commute Equiv.Perm.Disjoint.commute

@[simp]
theorem disjoint_one_left (f : Perm α) : Disjoint 1 f := fun _ => Or.inl rfl
#align equiv.perm.disjoint_one_left Equiv.Perm.disjoint_one_left

@[simp]
theorem disjoint_one_right (f : Perm α) : Disjoint f 1 := fun _ => Or.inr rfl
#align equiv.perm.disjoint_one_right Equiv.Perm.disjoint_one_right

@[simp]
theorem disjoint_refl_iff : Disjoint f f ↔ f = 1 := by
  refine ⟨fun h => ?_, fun h => h.symm ▸ disjoint_one_left 1⟩
  ext x
  cases' h x with hx hx <;> simp [hx]
#align equiv.perm.disjoint_refl_iff Equiv.Perm.disjoint_refl_iff

theorem Disjoint.inv_left (h : Disjoint f g) : Disjoint f⁻¹ g := by
  intro x
  rw [inv_eq_iff_eq, eq_comm]
  exact h x
#align equiv.perm.disjoint.inv_left Equiv.Perm.Disjoint.inv_left

theorem Disjoint.inv_right (h : Disjoint f g) : Disjoint f g⁻¹ :=
  h.symm.inv_left.symm
#align equiv.perm.disjoint.inv_right Equiv.Perm.Disjoint.inv_right

@[simp]
theorem disjoint_inv_left_iff : Disjoint f⁻¹ g ↔ Disjoint f g := by
  refine ⟨fun h => ?_, Disjoint.inv_left⟩
  convert h.inv_left
#align equiv.perm.disjoint_inv_left_iff Equiv.Perm.disjoint_inv_left_iff

@[simp]
theorem disjoint_inv_right_iff : Disjoint f g⁻¹ ↔ Disjoint f g := by
  rw [disjoint_comm, disjoint_inv_left_iff, disjoint_comm]
#align equiv.perm.disjoint_inv_right_iff Equiv.Perm.disjoint_inv_right_iff

theorem Disjoint.mul_left (H1 : Disjoint f h) (H2 : Disjoint g h) : Disjoint (f * g) h := fun x =>
  by cases H1 x <;> cases H2 x <;> simp [*]
#align equiv.perm.disjoint.mul_left Equiv.Perm.Disjoint.mul_left

theorem Disjoint.mul_right (H1 : Disjoint f g) (H2 : Disjoint f h) : Disjoint f (g * h) := by
  rw [disjoint_comm]
  exact H1.symm.mul_left H2.symm
#align equiv.perm.disjoint.mul_right Equiv.Perm.Disjoint.mul_right

-- Porting note (#11215): TODO: make it `@[simp]`
theorem disjoint_conj (h : Perm α) : Disjoint (h * f * h⁻¹) (h * g * h⁻¹) ↔ Disjoint f g :=
  (h⁻¹).forall_congr fun {_} ↦ by simp only [mul_apply, eq_inv_iff_eq]

theorem Disjoint.conj (H : Disjoint f g) (h : Perm α) : Disjoint (h * f * h⁻¹) (h * g * h⁻¹) :=
  (disjoint_conj h).2 H

theorem disjoint_prod_right (l : List (Perm α)) (h : ∀ g ∈ l, Disjoint f g) :
    Disjoint f l.prod := by
  induction' l with g l ih
  · exact disjoint_one_right _
  · rw [List.prod_cons]
    exact (h _ (List.mem_cons_self _ _)).mul_right (ih fun g hg => h g (List.mem_cons_of_mem _ hg))
#align equiv.perm.disjoint_prod_right Equiv.Perm.disjoint_prod_right

open scoped List in
theorem disjoint_prod_perm {l₁ l₂ : List (Perm α)} (hl : l₁.Pairwise Disjoint) (hp : l₁ ~ l₂) :
    l₁.prod = l₂.prod :=
  hp.prod_eq' <| hl.imp Disjoint.commute
#align equiv.perm.disjoint_prod_perm Equiv.Perm.disjoint_prod_perm

theorem nodup_of_pairwise_disjoint {l : List (Perm α)} (h1 : (1 : Perm α) ∉ l)
    (h2 : l.Pairwise Disjoint) : l.Nodup := by
  refine List.Pairwise.imp_of_mem ?_ h2
  intro τ σ h_mem _ h_disjoint _
  subst τ
  suffices (σ : Perm α) = 1 by
    rw [this] at h_mem
    exact h1 h_mem
  exact ext fun a => or_self_iff.mp (h_disjoint a)
#align equiv.perm.nodup_of_pairwise_disjoint Equiv.Perm.nodup_of_pairwise_disjoint

theorem Disjoint.mul_apply_eq_iff {σ τ : Perm α} (hστ : Disjoint σ τ) {a : α} :
    (σ * τ) a = a ↔ σ a = a ∧ τ a = a := by
  refine ⟨fun h => ?_, fun h => by rw [mul_apply, h.2, h.1]⟩
  cases' hστ a with hσ hτ
  · exact ⟨hσ, σ.injective (h.trans hσ.symm)⟩
  · exact ⟨(congr_arg σ hτ).symm.trans h, hτ⟩
#align equiv.perm.disjoint.mul_apply_eq_iff Equiv.Perm.Disjoint.mul_apply_eq_iff

theorem Disjoint.mul_eq_one_iff {σ τ : Perm α} (hστ : Disjoint σ τ) :
    σ * τ = 1 ↔ σ = 1 ∧ τ = 1 := by simp_rw [ext_iff, one_apply, hστ.mul_apply_eq_iff, forall_and]
#align equiv.perm.disjoint.mul_eq_one_iff Equiv.Perm.Disjoint.mul_eq_one_iff

end Disjoint

section IsSwap

/-- `f.IsSwapOn x y` indicates that the permutation `f` is a transposition of the two elements `x`
and `y`. Note that this means that `f` might be trivial, if `x = y`. -/
def IsSwapOn (f : Perm α) (x y : α) : Prop :=
  (∀ {z}, z ≠ x → z ≠ y → f z = z) ∧ f x = y ∧ f y = x

theorem IsSwapOn.apply_of_ne_of_ne {f : Perm α} {x y z : α} (h : f.IsSwapOn x y) :
    z ≠ x → z ≠ y → f z = z := h.1

theorem IsSwapOn.apply_of_ne_of_ne' {f : Perm α} {x y z : α} (h : f.IsSwapOn x y) :
    z ≠ y → z ≠ x → f z = z := Function.swap h.apply_of_ne_of_ne

theorem IsSwapOn.apply_left {f : Perm α} {x y : α} (h : f.IsSwapOn x y) :
    f x = y := h.2.1

theorem IsSwapOn.apply_right {f : Perm α} {x y : α} (h : f.IsSwapOn x y) :
    f y = x := h.2.2

theorem IsSwapOn.comm {f : Perm α} {x y : α} (h : f.IsSwapOn x y) :
    f.IsSwapOn y x := ⟨h.apply_of_ne_of_ne', h.apply_right, h.apply_left⟩

theorem IsSwapOn.eq_or_eq_of_mem_support {f : Perm α} {x y z : α}
    (h : f.IsSwapOn x y) (hz : f z ≠ z) : z = x ∨ z = y := by
  contrapose! hz
  exact h.apply_of_ne_of_ne hz.1 hz.2

theorem IsSwapOn.congr {f g : Perm α} {x y : α} (hf : f.IsSwapOn x y)
    (hg : g.IsSwapOn x y) : f = g := by
  rw [Equiv.ext_iff]
  intros z
  rcases eq_or_ne z x with rfl | hzx
  · rw [hf.apply_left, hg.apply_left]
  · rcases eq_or_ne z y with rfl | hzy
    · rw [hf.apply_right, hg.apply_right]
    · rw [hf.apply_of_ne_of_ne hzx hzy, hg.apply_of_ne_of_ne hzx hzy]

theorem IsSwapOn.inv {f : Perm α} {x y : α}
    (h : f.IsSwapOn x y) : f⁻¹.IsSwapOn x y := by
  unfold IsSwapOn at h ⊢
  simp_rw [inv_eq_iff_eq, fun a b => eq_comm (a := a) (b := f b)]
  exact ⟨h.1, h.2.2, h.2.1⟩

theorem IsSwapOn.symm {f : Perm α} {x y : α}
    (h : f.IsSwapOn x y) : IsSwapOn f.symm x y := h.inv

theorem IsSwapOn.inv_eq {f : Perm α} {x y : α} (h : f.IsSwapOn x y) : f⁻¹ = f := h.inv.congr h

theorem IsSwapOn.symm_eq {f : Perm α} {x y : α} (h : f.IsSwapOn x y) : f.symm = f := h.inv_eq

theorem IsSwapOn.apply_self {f : Perm α} {x y z : α}
    (h : f.IsSwapOn x y) : f (f z) = z := by rw [← eq_inv_iff_eq, h.inv_eq]

theorem IsSwapOn.mul_self {f : Perm α} {x y : α} (h : f.IsSwapOn x y) : f * f = 1 := by
  rw [mul_eq_one_iff_inv_eq, h.inv_eq]

theorem IsSwapOn.trans_self {f : Perm α} {x y : α}
    (h : f.IsSwapOn x y) : f.trans f = Equiv.refl α := h.mul_self

theorem one_isSwapOn_iff {x y : α} : IsSwapOn 1 x y ↔ x = y := by
  exact ⟨fun h => h.apply_right.symm.trans rfl, fun h => h ▸ ⟨fun _ _ => rfl, rfl, rfl⟩⟩

theorem refl_isSwapOn_iff {x y : α} : IsSwapOn (Equiv.refl α) x y ↔ x = y := by
  exact ⟨fun h => h.apply_right.symm.trans rfl, fun h => h ▸ ⟨fun _ _ => rfl, rfl, rfl⟩⟩

theorem IsSwapOn.eq_one_iff {f : Perm α} {x y : α} (hf : f.IsSwapOn x y) : f = 1 ↔ x = y := by
  rw [← one_isSwapOn_iff (x := x)]
  exact ⟨fun h => h ▸ hf, fun h => hf.congr h⟩

theorem IsSwapOn.eq_refl_iff {f : Perm α} {x y : α} (hf : f.IsSwapOn x y) :
    f = Equiv.refl α ↔ x = y := hf.eq_one_iff

theorem IsSwapOn.eq_one {f : Perm α} {x : α} (hf : f.IsSwapOn x x) : f = 1 := by
  rw [hf.eq_one_iff]

theorem IsSwapOn.eq_refl {f : Perm α} {x : α} (hf : f.IsSwapOn x x) : f = Equiv.refl α := by
  rw [hf.eq_refl_iff]

theorem IsSwapOn.of_subtype_isSwapOn {p : α → Prop} [DecidablePred p] {f : Perm (Subtype p)}
    {x y : Subtype p} : f.IsSwapOn x y → (ofSubtype f).IsSwapOn ↑x ↑y := by
  simp_rw [IsSwapOn, Subtype.forall, ← Subtype.coe_ne_coe,
    Subtype.ext_iff, ← f.ofSubtype_apply_coe]
  exact fun ⟨hzxy, hfxy⟩ => ⟨by_cases (hzxy _) (fun _ _ => f.ofSubtype_apply_of_not_mem ·), hfxy⟩

theorem one_isSwapOn {x : α} : IsSwapOn 1 x x := by rw [one_isSwapOn_iff]

theorem refl_isSwapOn {x : α} : IsSwapOn (Equiv.refl α) x x := one_isSwapOn

theorem swap_isSwapOn [DecidableEq α] {x y : α} : IsSwapOn (swap x y) x y :=
  ⟨swap_apply_of_ne_of_ne, swap_apply_left _ _, swap_apply_right _ _⟩

theorem isSwapOn_iff_eq_swap [DecidableEq α] {f : Perm α} {x y : α} :
    f.IsSwapOn x y ↔ f = swap x y :=
  ⟨fun hf => hf.congr swap_isSwapOn, fun hf => hf ▸ swap_isSwapOn⟩

theorem IsSwapOn.eq_swap [DecidableEq α] {f : Perm α} {x y : α} (hf : f.IsSwapOn x y) :
    f = swap x y := hf.congr swap_isSwapOn

/-- `f.IsSwap` indicates that the permutation `f` is a transposition of two distinct elements. -/
def IsSwap (f : Perm α) : Prop :=
  ∃ x y, x ≠ y ∧ f.IsSwapOn x y
#align equiv.perm.is_swap Equiv.Perm.IsSwap

theorem IsSwap.inv {f : Perm α} (h : f.IsSwap) : f⁻¹.IsSwap := by
  obtain ⟨_, _, hxy, hf⟩ := h
  exact ⟨_, _, hxy, hf.inv⟩

theorem IsSwap.symm {f : Perm α} (h : f.IsSwap) : IsSwap f.symm := h.inv

theorem IsSwap.inv_eq {f : Perm α} (h : f.IsSwap) : f⁻¹ = f := by
  obtain ⟨_, _, _, hf⟩ := h
  exact hf.inv_eq

theorem IsSwap.symm_eq {f : Perm α} (h : f.IsSwap) : f.symm = f := h.inv_eq

theorem IsSwap.apply_self {f : Perm α} {z : α}
    (h : f.IsSwap) : f (f z) = z := by rw [← eq_inv_iff_eq, h.inv_eq]

theorem IsSwap.mul_self {f : Perm α} (h : f.IsSwap) : f * f = 1 := by
  rw [mul_eq_one_iff_inv_eq, h.inv_eq]

theorem IsSwap.trans_self {f : Perm α} (h : f.IsSwap) : f.trans f = Equiv.refl α := h.mul_self

theorem IsSwap.ne_one {f : Perm α} (h : f.IsSwap) : f ≠ 1 := by
  obtain ⟨_, _, hxy, hf⟩ := h
  exact DFunLike.ne_iff.mpr ⟨_, Eq.trans_ne hf.2.2 hxy⟩

theorem IsSwap.of_subtype_isSwap {p : α → Prop} [DecidablePred p] {f : Perm (Subtype p)} :
    f.IsSwap → (ofSubtype f).IsSwap := by
  simp_rw [IsSwap, ← Subtype.coe_ne_coe]
  exact fun ⟨_, _, hxy, H⟩ => ⟨_, _, hxy, H.of_subtype_isSwapOn⟩
#align equiv.perm.is_swap.of_subtype_is_swap Equiv.Perm.IsSwap.of_subtype_isSwap

theorem swap_isSwap [DecidableEq α] {x y : α} (h : x ≠ y) : IsSwap (swap x y) :=
  ⟨x, y, h, swap_isSwapOn⟩

theorem isSwap_iff_exists_distinct_eq_swap [DecidableEq α] {f : Perm α} :
    f.IsSwap ↔ ∃ x y, x ≠ y ∧ f = swap x y := by
  simp_rw [IsSwap, isSwapOn_iff_eq_swap]

theorem IsSwap.exists_distinct_eq_swap [DecidableEq α] {f : Perm α} (hf : f.IsSwap) :
    ∃ x y, x ≠ y ∧ f = swap x y := isSwap_iff_exists_distinct_eq_swap.mp hf

end IsSwap

section support

variable {f g : Perm α}

/-- The `Set` of nonfixed points of a permutation. -/
def support (f : Perm α) : Set α := { x | f x ≠ x }
#align equiv.perm.support Equiv.Perm.support

variable {f g : Perm α}

theorem mem_support {x : α} : x ∈ f.support ↔ f x ≠ x := Iff.rfl
#align equiv.perm.mem_support Equiv.Perm.mem_support

theorem not_mem_support {x : α} : x ∉ f.support ↔ f x = x := by simp_rw [mem_support, not_not]
#align equiv.perm.not_mem_support Equiv.Perm.not_mem_support

@[simp]
theorem support_eq_empty_iff {σ : Perm α} : σ.support = ∅ ↔ σ = 1 := by
  simp_rw [Set.ext_iff, mem_support, Set.not_mem_empty, iff_false_iff, not_not,
    Equiv.Perm.ext_iff, one_apply]
#align equiv.perm.support_eq_empty_iff Equiv.Perm.support_eq_empty_iff

theorem support_nonempty_iff : f.support.Nonempty ↔ f ≠ 1 := by
  rw [Set.nonempty_iff_ne_empty]
  exact support_eq_empty_iff.not

@[simp]
theorem support_ne_singleton {x : α} : f.support ≠ {x} := by
  simp_rw [ne_eq, Set.ext_iff, mem_singleton_iff, mem_support, not_forall, not_iff, not_not]
  exact ⟨f⁻¹ x, by rw [apply_inv_self, eq_comm]⟩

theorem support_nonempty_iff_nontrivial : f.support.Nontrivial ↔ f ≠ 1 := by
  rw [← support_nonempty_iff]
  refine' ⟨Set.Nontrivial.nonempty, fun h => _⟩
  have H := h.exists_eq_singleton_or_nontrivial
  simp_rw [support_ne_singleton, exists_false, false_or] at H
  exact H

theorem support_subsingleton_iff_eq_empty : f.support.Subsingleton ↔ f = 1 := by
  rw [← not_iff_not, not_subsingleton_iff, support_nonempty_iff_nontrivial]

@[simp]
theorem support_one : (1 : Perm α).support = ∅ := by rw [support_eq_empty_iff]
#align equiv.perm.support_one Equiv.Perm.support_one

@[simp]
theorem support_refl : support (Equiv.refl α) = ∅ :=
  support_one
#align equiv.perm.support_refl Equiv.Perm.support_refl

theorem support_congr (h : f.support ⊆ g.support) (h' : ∀ x ∈ g.support, f x = g x) : f = g := by
  ext x
  by_cases hx : x ∈ g.support
  · exact h' x hx
  · rw [not_mem_support.mp hx, ← not_mem_support]
    exact fun H => hx (h H)
#align equiv.perm.support_congr Equiv.Perm.support_congr

theorem support_mul_le (f g : Perm α) : (f * g).support ≤ f.support ⊔ g.support := fun x => by
  simp only [sup_eq_union]
  rw [mem_union, mem_support, mem_support, mem_support, mul_apply, ← not_and_or, not_imp_not]
  rintro ⟨hf, hg⟩
  rw [hg, hf]
#align equiv.perm.support_mul_le Equiv.Perm.support_mul_le

theorem exists_mem_support_of_mem_support_prod {l : List (Perm α)} {x : α}
    (hx : x ∈ l.prod.support) : ∃ f : Perm α, f ∈ l ∧ x ∈ f.support := by
  contrapose! hx
  simp_rw [mem_support, not_not] at hx ⊢
  induction' l with f l ih
  · rfl
  · rw [List.prod_cons, mul_apply, ih, hx]
    · simp only [List.find?, List.mem_cons, true_or]
    intros f' hf'
    refine hx f' ?_
    simp only [List.find?, List.mem_cons]
    exact Or.inr hf'
#align equiv.perm.exists_mem_support_of_mem_support_prod Equiv.Perm.exists_mem_support_of_mem_support_prod

theorem mem_support_inv {x : α} : x ∈ support f⁻¹ ↔ x ∈ f.support := by
  simp_rw [mem_support, not_iff_not, inv_eq_iff_eq.trans eq_comm]

@[simp]
theorem support_inv (f : Perm α) : support f⁻¹ = f.support := by
  simp_rw [Set.ext_iff, mem_support_inv, implies_true]
#align equiv.perm.support_inv Equiv.Perm.support_inv

theorem support_pow_le (f : Perm α) : ∀ n : ℕ, (f ^ n).support ≤ f.support
  | 0 => by simp_rw [pow_zero, support_one, le_eq_subset, empty_subset]
  | (n + 1) => (support_mul_le _ _).trans (sup_le (f.support_pow_le n) le_rfl)
#align equiv.perm.support_pow_le Equiv.Perm.support_pow_le

theorem support_zpow_le (f : Perm α) : ∀ n : ℤ, (f ^ n).support ≤ f.support
  | (Int.ofNat n) => f.support_pow_le _
  | (Int.negSucc n) => by
    rw [zpow_negSucc, support_inv]
    exact f.support_pow_le _
#align equiv.perm.support_zpow_le Equiv.Perm.support_zpow_le

theorem mem_support_of_mem_zpow_support {n : ℤ} {x : α} : x ∈ (f^n).support → x ∈ f.support :=
  fun hx => f.support_zpow_le n hx

theorem mem_support_of_mem_pow_support {n : ℕ} {x : α} : x ∈ (f^n).support → x ∈ f.support :=
  fun hx => f.support_pow_le n hx

theorem mem_support_inv_conj {x : α} :
    x ∈ (g⁻¹ * f * g).support ↔ g x ∈ f.support := by
  simp_rw [mem_support, ne_eq, mul_apply, Equiv.Perm.inv_eq_iff_eq]

theorem mem_support_conj {x : α} : x ∈ (g * f * g⁻¹).support ↔ g⁻¹ x ∈ f.support := by
  simp_rw [← mem_support_inv_conj, inv_inv]

theorem apply_mem_support {x : α} : f x ∈ f.support ↔ x ∈ f.support := by
  simp_rw [← mem_support_inv_conj, mul_assoc, inv_mul_cancel_left]
#align equiv.perm.apply_mem_support Equiv.Perm.apply_mem_support

theorem apply_inv_mem_support {x : α} : f⁻¹ x ∈ f.support ↔ x ∈ f.support := by
  simp_rw [← mem_support_conj, mul_inv_cancel_right]

theorem zpow_apply_mem_support {n : ℤ} {x : α} : (f ^ n) x ∈ f.support ↔ x ∈ f.support := by
  rw [← mem_support_inv_conj, ← zpow_neg, ← zpow_add_one, ← zpow_add, neg_add_cancel_comm, zpow_one]
#align equiv.perm.zpow_apply_mem_support Equiv.Perm.zpow_apply_mem_support

theorem pow_apply_mem_support {n : ℕ} {x : α} : (f ^ n) x ∈ f.support ↔ x ∈ f.support :=
  zpow_apply_mem_support (n := Int.ofNat n)
#align equiv.perm.pow_apply_mem_support Equiv.Perm.pow_apply_mem_support

theorem zpow_apply_eq_self_of_apply_eq_self {x : α} {n : ℤ} : f x = x → (f ^ n) x = x :=
  Function.mtr mem_support_of_mem_zpow_support
#align equiv.perm.zpow_apply_eq_self_of_apply_eq_self Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self

theorem pow_apply_eq_self_of_apply_eq_self {x : α} {n : ℕ} : f x = x → (f ^ n) x = x :=
  Function.mtr mem_support_of_mem_pow_support
#align equiv.perm.pow_apply_eq_self_of_apply_eq_self Equiv.Perm.pow_apply_eq_self_of_apply_eq_self

theorem pow_apply_eq_of_apply_apply_eq_self {x : α} (hffx : f (f x) = x) :
    ∀ n : ℕ, (f ^ n) x = x ∨ (f ^ n) x = f x
  | 0 => Or.inl rfl
  | n + 1 =>
    (pow_apply_eq_of_apply_apply_eq_self hffx n).elim
      (fun h => Or.inr (by rw [pow_succ', mul_apply, h]))
      fun h => Or.inl (by rw [pow_succ', mul_apply, h, hffx])
#align equiv.perm.pow_apply_eq_of_apply_apply_eq_self Equiv.Perm.pow_apply_eq_of_apply_apply_eq_self

theorem zpow_apply_eq_of_apply_apply_eq_self {x : α} (hffx : f (f x) = x) :
    ∀ i : ℤ, (f ^ i) x = x ∨ (f ^ i) x = f x
  | (n : ℕ) => pow_apply_eq_of_apply_apply_eq_self hffx n
  | Int.negSucc n => by
    rw [zpow_negSucc, inv_eq_iff_eq, ← f.injective.eq_iff, ← mul_apply, ← pow_succ', eq_comm,
      inv_eq_iff_eq, ← mul_apply, ← pow_succ, @eq_comm _ x, or_comm]
    exact pow_apply_eq_of_apply_apply_eq_self hffx _
#align equiv.perm.zpow_apply_eq_of_apply_apply_eq_self Equiv.Perm.zpow_apply_eq_of_apply_apply_eq_self

theorem pow_eq_on_of_mem_support (h : ∀ x ∈ f.support ∩ g.support, f x = g x) (k : ℕ) :
    ∀ x ∈ f.support ∩ g.support, (f ^ k) x = (g ^ k) x := by
  induction' k with k hk
  · simp
  · intro x hx
    rw [pow_succ, mul_apply, pow_succ, mul_apply, h _ hx, hk]
    rwa [mem_inter_iff, apply_mem_support, ← h _ hx, apply_mem_support, ← mem_inter_iff]
#align equiv.perm.pow_eq_on_of_mem_support Equiv.Perm.pow_eq_on_of_mem_support

theorem support_prod_le (l : List (Perm α)) : l.prod.support ≤ (l.map support).foldr (· ⊔ ·) ⊥ := by
  induction' l with hd tl hl
  · simp
  · rw [List.prod_cons, List.map_cons, List.foldr_cons]
    refine (support_mul_le hd tl.prod).trans ?_
    exact sup_le_sup le_rfl hl
#align equiv.perm.support_prod_le Equiv.Perm.support_prod_le

@[simp]
theorem support_extend_domain {p : β → Prop} [DecidablePred p] (f : α ≃ Subtype p) {g : Perm α} :
    support (g.extendDomain f) = g.support.image f.asEmbedding := by
  ext b
  simp only [exists_prop, Function.Embedding.coeFn_mk, toEmbedding_apply, mem_image, Ne,
    Function.Embedding.trans_apply, mem_support]
  by_cases pb : p b
  · rw [extendDomain_apply_subtype _ _ pb]
    constructor
    · rintro h
      refine ⟨f.symm ⟨b, pb⟩, ?_, by simp⟩
      contrapose! h
      simp [h]
    · rintro ⟨a, ha, hb⟩
      contrapose! ha
      obtain rfl : a = f.symm ⟨b, pb⟩ := by
        rw [eq_symm_apply]
        exact Subtype.coe_injective hb
      rw [eq_symm_apply]
      exact Subtype.coe_injective ha
  · rw [extendDomain_apply_not_subtype _ _ pb]
    simp only [not_exists, false_iff_iff, not_and, eq_self_iff_true, not_true]
    rintro a _ rfl
    exact pb (Subtype.prop _)
#align equiv.perm.support_extend_domain Equiv.Perm.support_extend_domain

theorem IsSwapOn.support_eq_of_eq {x : α} (hf : f.IsSwapOn x x) : f.support = ∅ := by
  rw [hf.eq_one, support_one]

theorem IsSwapOn.support_eq_of_ne {x y : α} (hxy : x ≠ y) (hf : f.IsSwapOn x y) :
    f.support = {x, y} := by
  simp_rw [Set.ext_iff, mem_insert_iff, mem_singleton_iff]
  refine' fun z => ⟨hf.eq_or_eq_of_mem_support, _⟩
  classical
  exact fun h => h.by_cases
    (fun h => h ▸ hf.apply_left.trans_ne hxy.symm) (fun h => h ▸ hf.apply_right.trans_ne hxy)

theorem ne_of_support_eq_pair {x y : α} (h : f.support = {x, y}) : x ≠ y := by
  intro hxy
  rw [hxy] at h
  simp_rw [insert_eq_of_mem (mem_singleton y), support_ne_singleton] at h

theorem isSwapOn_of_support_eq_pair {x y : α} (h : f.support = {x, y}) : IsSwapOn f x y := by
  simp_rw [Set.ext_iff, mem_insert_iff, mem_singleton_iff] at h
  refine' ⟨fun {z} hzx hzy => not_mem_support.mp <| (h z).not.mpr (not_or.mpr ⟨hzx, hzy⟩), _, _⟩
  · have hx := (h x).mpr (Or.inl rfl)
    have hx' := (h _).mp <| apply_mem_support.mpr hx
    simp_rw [← not_mem_support, hx, not_true, false_or] at hx'
    exact hx'
  · have hy := (h y).mpr (Or.inr rfl)
    have hy' := (h _).mp <| apply_mem_support.mpr hy
    simp_rw [← not_mem_support, hy, not_true, or_false] at hy'
    exact hy'

theorem support_eq_pair_iff {x y : α} : f.support = {x, y} ↔ x ≠ y ∧ IsSwapOn f x y :=
  ⟨imp_and.mpr ⟨ne_of_support_eq_pair, isSwapOn_of_support_eq_pair⟩,
  fun h => h.2.support_eq_of_ne h.1⟩

theorem isSwap_iff_exists_distinct_support_eq_pair :
    IsSwap f ↔ ∃ x y, x ≠ y ∧ f.support = {x, y} := by
  simp_rw [IsSwap, support_eq_pair_iff, and_self_left]

theorem isSwap_iff_exists_support_eq_pair : IsSwap f ↔ ∃ x y, f.support = {x, y} := by
  simp_rw [IsSwap, support_eq_pair_iff]

section DecidableEq

variable [DecidableEq α]

theorem support_swap_iff [DecidableEq α] (x y : α) : support (swap x y) = {x, y} ↔ x ≠ y := by
  simp_rw [support_eq_pair_iff, swap_isSwapOn, and_true]
#align equiv.perm.support_swap_iff Equiv.Perm.support_swap_iff

theorem support_swap_of_eq {x : α} : support (swap x x) = ∅ := swap_isSwapOn.support_eq_of_eq

@[simp]
theorem support_swap_of_ne {x y : α} : x ≠ y → support (swap x y) = {x, y} :=
  swap_isSwapOn.support_eq_of_ne
#align equiv.perm.support_swap Equiv.Perm.support_swap_of_ne

theorem support_swap_mul_swap {x y z : α} (hxz : x ≠ z) :
    support (swap x y * swap y z) = {x, y, z} := by
  rcases eq_or_ne z y with rfl | hzy
  · simp_rw [swap_self, mul_refl, insert_eq_of_mem (mem_singleton z)]
    exact support_swap_of_ne hxz
  · simp_rw [Set.ext_iff, mem_support, mul_apply, mem_insert_iff, mem_singleton_iff]
    refine' fun w => _
    rcases eq_or_ne w y with rfl | hwy
    · simp_rw [swap_apply_left, swap_apply_of_ne_of_ne hxz.symm hzy,
      ne_eq, hzy, true_or, or_true, not_false_eq_true]
    · rcases eq_or_ne w z with rfl | hwz
      · simp_rw [swap_apply_right, ne_eq, hxz, or_true, not_false_eq_true]
      · simp_rw [swap_apply_of_ne_of_ne hwy hwz]
        rcases eq_or_ne w x with rfl | hwx
        · simp_rw [swap_apply_left, true_or, ne_eq, hwy.symm, not_false_eq_true]
        · simp_rw [swap_apply_of_ne_of_ne hwx hwy, ne_eq, not_true_eq_false, false_iff, not_or]
          exact ⟨hwx, hwy, hwz⟩

theorem support_swap_mul_swap_of_nodup {x y z : α} (h : List.Nodup [x, y, z]) :
    support (swap x y * swap y z) = {x, y, z} := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_self, and_true] at h
  rcases h with ⟨⟨_, hxz⟩, _⟩
  rw [support_swap_mul_swap hxz]
#align equiv.perm.support_swap_mul_swap Equiv.Perm.support_swap_mul_swap_of_nodup

theorem support_swap_mul_ge_support_diff (f : Perm α) (x y : α) :
    f.support \ {x, y} ≤ (swap x y * f).support := by
  intro
  simp only [mem_diff, mem_support, Ne, mem_insert_iff, mem_singleton_iff, not_or, coe_mul,
    Function.comp_apply, and_imp]
  push_neg
  rintro ha hx hy H
  rw [swap_apply_eq_iff, swap_apply_of_ne_of_ne hx hy] at H
  exact ha H
#align equiv.perm.support_swap_mul_ge_support_diff Equiv.Perm.support_swap_mul_ge_support_diff

theorem support_swap_mul_eq (f : Perm α) (x : α) (h : f (f x) ≠ x) :
    (swap x (f x) * f).support = f.support \ {x} := by
  by_cases hx : f x = x
  · rw [hx] at h
    exact (h (hx)).elim
  ext z
  simp only [mem_support, coe_mul, Function.comp_apply, ne_eq, mem_diff, mem_singleton_iff]
  by_cases hzx : z = x
  · simp only [hzx, swap_apply_right, not_true_eq_false, and_false]
  by_cases hzf : z = f x
  · simp only [hzf, ne_eq, h, not_false_eq_true, EmbeddingLike.apply_eq_iff_eq, hx,
    swap_apply_of_ne_of_ne, and_self]
  by_cases hzfx : f z = x
  · simp only [hzfx, swap_apply_left, Ne.symm hzf, not_false_eq_true, Ne.symm hzx, hzx, and_self]
  · simp only [ne_eq, hzfx, not_false_eq_true, f.injective.ne hzx, swap_apply_of_ne_of_ne, hzx,
    and_true]
#align equiv.perm.support_swap_mul_eq Equiv.Perm.support_swap_mul_eq

theorem mem_support_swap_mul_imp_mem_support_ne {x y : α} (hy : y ∈ support (swap x (f x) * f)) :
    y ∈ support f ∧ y ≠ x := by
  simp only [mem_support, swap_apply_def, mul_apply, f.injective.eq_iff] at *
  by_cases h : f y = x
  · constructor <;> intro <;> simp_all only [if_true, eq_self_iff_true, not_true, Ne]
  · split_ifs at hy with heq
    · subst heq; exact ⟨h, hy⟩
    · exact ⟨hy, heq⟩
#align equiv.perm.mem_support_swap_mul_imp_mem_support_ne Equiv.Perm.mem_support_swap_mul_imp_mem_support_ne

instance mem_support_decidablePred [DecidableEq α] (f : Perm α) :
    DecidablePred (· ∈ f.support) := fun x => if h : f x ≠ x then isTrue h else isFalse h

end DecidableEq

section Finite

instance support_one_finite : Finite (1 : Perm α).support := support_one ▸ inferInstance

instance support_swap_finite [DecidableEq α] {x y : α} : Finite (swap x y).support :=
  (Decidable.em (x = y)).by_cases (fun hxy => hxy ▸ support_swap_of_eq (x := x) ▸ inferInstance)
  (fun hxy => support_swap_of_ne hxy ▸ inferInstance)

instance support_inv_finite (f : Perm α) [Finite f.support] : Finite (f⁻¹).support :=
  f.support_inv ▸ inferInstance

instance support_zpow_finite (f : Perm α) [Finite f.support] (n : ℤ) : Finite (f ^ n).support :=
  Finite.Set.subset f.support (support_zpow_le _ _)

instance support_pow_finite (f : Perm α) [Finite f.support] (n : ℕ) : Finite (f ^ n).support :=
  Finite.Set.subset f.support (support_pow_le _ _)

instance support_mul_finite (f g : Perm α) [Finite f.support] [Finite g.support] :
    Finite (f * g).support := Finite.Set.subset (f.support ⊔ g.support) (support_mul_le _ _)

instance support_extend_domain_finite [Finite g.support] {p : β → Prop} [DecidablePred p]
    (f : α ≃ Subtype p) : Finite (g.extendDomain f).support :=
  support_extend_domain f ▸ inferInstance

end Finite

section DecidableEqFintype

variable [DecidableEq α] [Fintype α]

instance support_fintype (f : Perm α) : Fintype (f.support) := setFintype f.support

lemma coe_univ_filter_ne_eq_support (f : Perm α) :
    Finset.univ.filter fun x => f x ≠ x = f.support := (Finset.coe_filter_univ _)

lemma support_toFinset (f : Perm α) :
    f.support.toFinset = Finset.univ.filter fun x => f x ≠ x :=
  Finset.coe_injective (by rw [coe_univ_filter_ne_eq_support, Set.coe_toFinset])

end DecidableEqFintype

section Disjoint

variable {f g h : Perm α}

theorem disjoint_iff_disjoint_support : Disjoint f g ↔ _root_.Disjoint f.support g.support := by
  simp_rw [disjoint_iff_eq_or_eq, disjoint_iff, Set.ext_iff, inf_eq_inter, mem_inter_iff,
  mem_support, bot_eq_empty, not_mem_empty, iff_false, not_and_or, not_not]

theorem disjoint_iff_support_inter_le_empty : Disjoint f g ↔ f.support ∩ g.support ⊆ ∅ := by
  simp_rw [disjoint_iff_disjoint_support, Set.disjoint_iff]

theorem Disjoint.zpow_disjoint_zpow {σ τ : Perm α} (hστ : Disjoint σ τ) (m n : ℤ) :
    Disjoint (σ ^ m) (τ ^ n) := by
  rw [disjoint_iff_support_inter_le_empty] at hστ ⊢
  exact (inf_le_inf (support_zpow_le _ _) (support_zpow_le _ _)).trans hστ
#align equiv.perm.disjoint.zpow_disjoint_zpow Equiv.Perm.Disjoint.zpow_disjoint_zpow

theorem Disjoint.pow_disjoint_pow {σ τ : Perm α} (hστ : Disjoint σ τ) (m n : ℕ) :
    Disjoint (σ ^ m) (τ ^ n) := hστ.zpow_disjoint_zpow m n
#align equiv.perm.disjoint.pow_disjoint_pow Equiv.Perm.Disjoint.pow_disjoint_pow

theorem Disjoint.disjoint_support (h : Disjoint f g) : _root_.Disjoint f.support g.support :=
  disjoint_iff_disjoint_support.1 h
#align equiv.perm.disjoint.disjoint_support Equiv.Perm.Disjoint.disjoint_support

theorem Disjoint.inter_le_empty (h : Disjoint f g) : f.support ∩ g.support ⊆ ∅ :=
  disjoint_iff_support_inter_le_empty.1 h

theorem Disjoint.support_mul (h : Disjoint f g) : (f * g).support = f.support ∪ g.support := by
  refine le_antisymm (support_mul_le _ _) fun a => ?_
  rw [mem_union, mem_support, mem_support, mem_support, mul_apply, ← not_and_or, not_imp_not]
  exact
    (h a).elim (fun hf h => ⟨hf, f.apply_eq_iff_eq.mp (h.trans hf.symm)⟩) fun hg h =>
      ⟨(congr_arg f hg).symm.trans h, hg⟩
#align equiv.perm.disjoint.support_mul Equiv.Perm.Disjoint.support_mul

theorem support_prod_of_pairwise_disjoint (l : List (Perm α)) (h : l.Pairwise Disjoint) :
    l.prod.support = (l.map support).foldr (· ⊔ ·) ⊥ := by
  induction' l with hd tl hl
  · simp
  · rw [List.pairwise_cons] at h
    have : Disjoint hd tl.prod := disjoint_prod_right _ h.left
    simp [this.support_mul, hl h.right]
#align equiv.perm.support_prod_of_pairwise_disjoint Equiv.Perm.support_prod_of_pairwise_disjoint

theorem Disjoint.mem_imp (h : Disjoint f g) {x : α} (hx : x ∈ f.support) : x ∉ g.support :=
  disjoint_left.mp h.disjoint_support hx
#align equiv.perm.disjoint.mem_imp Equiv.Perm.Disjoint.mem_imp

theorem eq_on_support_mem_disjoint {l : List (Perm α)} (h : f ∈ l) (hl : l.Pairwise Disjoint) :
    ∀ x ∈ f.support, f x = l.prod x := by
  induction' l with hd tl IH
  · simp at h
  · intro x hx
    rw [List.pairwise_cons] at hl
    rw [List.mem_cons] at h
    rcases h with (rfl | h)
    · rw [List.prod_cons, mul_apply,
        not_mem_support.mp ((disjoint_prod_right tl hl.left).mem_imp hx)]
    · rw [List.prod_cons, mul_apply, ← IH h hl.right _ hx, eq_comm, ← not_mem_support]
      refine (hl.left _ h).symm.mem_imp ?_
      simpa only [mem_support, ne_eq, EmbeddingLike.apply_eq_iff_eq] using hx
#align equiv.perm.eq_on_support_mem_disjoint Equiv.Perm.eq_on_support_mem_disjoint

theorem Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.support ≤ f.support)
    (hg : y.support ≤ g.support) : Disjoint x y := by
  rw [disjoint_iff_disjoint_support] at h ⊢
  exact h.mono hf hg
#align equiv.perm.disjoint.mono Equiv.Perm.Disjoint.mono

theorem support_le_prod_of_mem {l : List (Perm α)} (h : f ∈ l) (hl : l.Pairwise Disjoint) :
    f.support ≤ l.prod.support := by
  intro x hx
  rwa [mem_support, ← eq_on_support_mem_disjoint h hl _ hx, ← mem_support]
#align equiv.perm.support_le_prod_of_mem Equiv.Perm.support_le_prod_of_mem

end Disjoint


@[simp]
theorem support_subtype_perm [DecidableEq α] {s : Finset α} (f : Perm α) (h) :
    ((f.subtypePerm h : Perm { x // x ∈ s }).support) =
    (s.attach.filter ((fun x => decide (f x ≠ x))) : Finset { x // x ∈ s }) := by
  ext
  simp only [mem_support, subtypePerm_apply, ne_eq, Subtype.ext_iff, decide_not, Bool.not_eq_true',
    decide_eq_false_iff_not, Finset.coe_filter, Finset.mem_attach, true_and, mem_setOf_eq]
#align equiv.perm.support_subtype_perm Equiv.Perm.support_subtype_perm

section Conjugation

variable {α : Type*} [Fintype α] [DecidableEq α] {σ τ : Perm α}

@[simp]
theorem support_conj : (σ * τ * σ⁻¹).support = τ.support.image σ := by
  ext x
  rw [mem_support_conj, mem_image]
  refine' ⟨fun h => ⟨_, h, apply_inv_self _ _⟩,
  fun ⟨y, hy, hyx⟩ => by rw [← eq_inv_iff_eq] at hyx; rwa [hyx] at hy⟩
#align equiv.perm.support_conj Equiv.Perm.support_conj

end Conjugation

section SupportCard

/-- The cardinality of the support of the permutation, when the support is finite. -/
noncomputable def supportCard (f : Perm α) [Finite f.support] : ℕ :=
  f.support.toFinite.toFinset.card

theorem supportCard_def [Finite f.support] : f.supportCard = f.support.toFinite.toFinset.card := rfl

theorem supportCard_compute [DecidableEq α] [Fintype α] :
    f.supportCard = f.support.toFinset.card := congrArg _ (Finite.toFinset_eq_toFinset _)

theorem supportCard_le_univ [Fintype α] : f.supportCard ≤ Fintype.card α := by
  rw [supportCard_def]
  exact Finset.card_le_univ _

variable [Finite f.support]

theorem supportCard_eq_zero : f.supportCard = 0 ↔ f = 1 := by
  rw [supportCard_def, Finset.card_eq_zero, Finite.toFinset_eq_empty, support_eq_empty_iff]

@[simp]
theorem supportCard_one : supportCard (1 : Perm α) = 0 := by
  rw [supportCard_eq_zero]

@[simp]
theorem supportCard_inv : supportCard f⁻¹ = supportCard f := by
  simp_rw [supportCard_def, support_inv]

theorem one_lt_supportCard_of_ne_one (h : f ≠ 1) : 1 < f.supportCard := by
  simp_rw [supportCard_def, Finset.one_lt_card_iff, Finite.mem_toFinset, mem_support, ← not_or]
  contrapose! h
  ext a
  specialize h (f a) a
  rwa [apply_eq_iff_eq, or_self_iff, or_self_iff] at h
#align equiv.perm.one_lt_card_support_of_ne_one Equiv.Perm.one_lt_supportCard_of_ne_one

theorem supportCard_ne_one : f.supportCard ≠ 1 := by
  by_cases h : f = 1
  · exact ne_of_eq_of_ne (supportCard_eq_zero.mpr h) zero_ne_one
  · exact ne_of_gt (one_lt_supportCard_of_ne_one h)
#align equiv.perm.card_support_ne_one Equiv.Perm.supportCard_ne_one

@[simp]
theorem supportCard_le_one : f.supportCard ≤ 1 ↔ f = 1 := by
  rw [le_iff_lt_or_eq, Nat.lt_succ_iff, Nat.le_zero, supportCard_eq_zero, or_iff_not_imp_right,
    imp_iff_right f.supportCard_ne_one]
#align equiv.perm.card_support_le_one Equiv.Perm.supportCard_le_one

theorem two_le_supportCard_of_ne_one (h : f ≠ 1) : 2 ≤ f.supportCard :=
  one_lt_supportCard_of_ne_one h
#align equiv.perm.two_le_card_support_of_ne_one Equiv.Perm.two_le_supportCard_of_ne_one

theorem supportCard_swap_mul [DecidableEq α] {x : α} (hx : f x ≠ x) :
    (swap x (f x) * f).supportCard < f.supportCard := by
  refine' Finset.card_lt_card (Finite.toFinset_ssubset_toFinset.mpr
    ⟨fun z hz => (mem_support_swap_mul_imp_mem_support_ne hz).left, fun h =>
      absurd (h (mem_support.2 hx)) (mt mem_support.1 (by simp))⟩)
#align equiv.perm.card_support_swap_mul Equiv.Perm.supportCard_swap_mul

theorem supportCard_swap [DecidableEq α] {x y : α} (hxy : x ≠ y) : (swap x y).supportCard = 2 :=
  show (swap x y).supportCard = Finset.card ⟨x ::ₘ y ::ₘ 0, by simp [hxy]⟩ from
    congr_arg Finset.card <| by simp [support_swap_of_ne hxy, *, Finset.ext_iff]
#align equiv.perm.card_support_swap Equiv.Perm.supportCard_swap

@[simp]
theorem supportCard_eq_two : f.supportCard = 2 ↔ IsSwap f := by
  classical
  simp_rw [supportCard_def, Finset.card_eq_two, isSwap_iff_exists_distinct_support_eq_pair,
    Finset.ext_iff, Set.ext_iff, Finite.mem_toFinset, Finset.mem_insert, Finset.mem_singleton,
    mem_insert_iff, mem_singleton_iff]
#align equiv.perm.card_support_eq_two Equiv.Perm.supportCard_eq_two

theorem supportCard_mul_le [Finite g.support] :
    (f * g).supportCard ≤ f.supportCard + g.supportCard := by
  simp_rw [supportCard_def]
  classical
  exact (Finset.card_union_le _ _).trans'
    (Finset.card_le_card (by
      simp_rw [Finite.toFinset_subset, Finset.coe_union, Finite.coe_toFinset]
      exact support_mul_le _ _))

theorem Disjoint.supportCard_mul [Finite g.support] (h : Disjoint f g) :
    (f * g).supportCard = f.supportCard + g.supportCard := by
  simp_rw [supportCard_def]
  classical
  rw [← Finset.card_union_of_disjoint]
  · congr
    ext
    simp [h.support_mul]
  · simpa using h.disjoint_support
#align equiv.perm.disjoint.card_support_mul Equiv.Perm.Disjoint.supportCard_mul

theorem supportCard_prod_list_of_pairwise_disjoint [Finite α] {l : List (Perm α)}
    (h : l.Pairwise Disjoint) : l.prod.supportCard = (l.map (fun f => f.supportCard)).sum := by
  induction' l with a t ih
  · exact supportCard_eq_zero.mpr rfl
  · obtain ⟨ha, ht⟩ := List.pairwise_cons.1 h
    rw [List.prod_cons, List.map_cons, List.sum_cons, ← ih ht]
    exact (disjoint_prod_right _ ha).supportCard_mul
#align equiv.perm.card_support_prod_list_of_pairwise_disjoint Equiv.Perm.supportCard_prod_list_of_pairwise_disjoint

theorem supportCard_extend_domain [Finite g.support] {p : β → Prop} [DecidablePred p]
    (f : α ≃ Subtype p) : (g.extendDomain f).supportCard = g.supportCard := by
  simp_rw [supportCard_def, support_extend_domain]
  classical
  rw [g.support.toFinite.toFinset_image, Finset.card_image_iff]
  exact injOn_of_injective f.asEmbedding.injective
#align equiv.perm.card_support_extend_domain Equiv.Perm.supportCard_extend_domain

theorem fixed_point_card_lt_of_ne_one [DecidableEq α] [Fintype α] {σ : Perm α} (h : σ ≠ 1) :
    (Finset.filter (fun x => σ x = x) Finset.univ).card < Fintype.card α - 1 := by
  rw [Nat.lt_sub_iff_add_lt, ← Nat.lt_sub_iff_add_lt', ← Finset.card_compl, Finset.compl_filter]
  exact (one_lt_supportCard_of_ne_one h).trans_eq (by rw [supportCard_compute, support_toFinset])
#align equiv.perm.fixed_point_card_lt_of_ne_one Equiv.Perm.fixed_point_card_lt_of_ne_one

theorem supportCard_conj [Finite f.support] [Finite g.support] :
    (g * f * g⁻¹).supportCard = f.supportCard := by
  simp_rw [supportCard_def, support_conj]
  classical
  rw [f.support.toFinite.toFinset_image, Finset.card_image_iff]
  exact injOn_of_injective g.injective
#align equiv.perm.card_support_conj Equiv.Perm.supportCard_conj

theorem supportCard_inv_conj [Finite f.support] [Finite g.support] :
    (g⁻¹ * f * g).supportCard = f.supportCard := by
  simp_rw [← supportCard_conj (f := f) (g := g⁻¹), inv_inv]

end SupportCard

end support

end Equiv.Perm
