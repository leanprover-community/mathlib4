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
* `Equiv.Perm.IsSwap`: `f = swap x y` for `x ≠ y`.
* `Equiv.Perm.support`: the elements `x : α` that are not fixed by `f`.

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

--variable [DecidableEq α]

/-- `f.IsSwap` indicates that the permutation `f` is a transposition of two elements. -/
def IsSwap (f : Perm α) (x y : α) : Prop := (∀ {z}, z ≠ x → z ≠ y → f z = z) ∧ f x = y ∧ f y = x
#align equiv.perm.is_swap Equiv.Perm.IsSwap

theorem swap_isSwap [DecidableEq α] {x y : α} : IsSwap (swap x y) x y :=
⟨swap_apply_of_ne_of_ne, swap_apply_left _ _, swap_apply_right _ _⟩

theorem IsSwap.of_subtype_isSwap {p : α → Prop} [DecidablePred p] {f : Perm (Subtype p)}
    {x y : Subtype p} (h : f.IsSwap x y) : (ofSubtype f).IsSwap x.1 y.1 := by
  unfold IsSwap at h ⊢
  simp_rw [ne_eq, Subtype.ext_iff, Subtype.forall] at h
  simp_rw [ofSubtype_apply_coe]
  refine' ⟨fun {z} => _, h.2⟩
  by_cases hz : (p z)
  · simp_rw [ofSubtype_apply_of_mem _ hz]
    exact h.1 z hz
  · simp_rw [ofSubtype_apply_of_not_mem _ hz, implies_true]
#align equiv.perm.is_swap.of_subtype_is_swap Equiv.Perm.IsSwap.of_subtype_isSwap

/-
theorem ne_and_ne_of_swap_mul_apply_ne_self {f : Perm α} {x y : α} (hy : (swap x (f x) * f) y ≠ y) :
    f y ≠ y ∧ y ≠ x := by
  simp only [swap_apply_def, mul_apply, f.injective.eq_iff] at *
  by_cases h : f y = x
  · constructor <;> intro <;> simp_all only [if_true, eq_self_iff_true, not_true, Ne]
  · split_ifs at hy with h <;> try { simp [*] at * }
#align equiv.perm.ne_and_ne_of_swap_mul_apply_ne_self Equiv.Perm.ne_and_ne_of_swap_mul_apply_ne_self
-/

end IsSwap

section support

variable {f g : Perm α}

/-- The `Set` of nonfixed points of a permutation. -/
def support (f : Perm α) : Set α := { x | f x ≠ x }
#align equiv.perm.support Equiv.Perm.support

variable {f g : Perm α}

@[simp]
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

@[simp]
theorem mem_support_inv {x : α} : x ∈ support f⁻¹ ↔ x ∈ f.support := by
  simp_rw [mem_support, not_iff_not, inv_eq_iff_eq.trans eq_comm]

@[simp]
theorem support_inv (f : Perm α) : support f⁻¹ = f.support := by
  simp_rw [Set.ext_iff, mem_support_inv, implies_true]
#align equiv.perm.support_inv Equiv.Perm.support_inv

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

theorem support_pow_le (σ : Perm α) : ∀ n : ℕ, (σ ^ n).support ≤ σ.support
  | 0 => by simp_rw [pow_zero, support_one, le_eq_subset, empty_subset]
  | (n + 1) => (support_mul_le _ _).trans (sup_le (σ.support_pow_le n) le_rfl)
#align equiv.perm.support_pow_le Equiv.Perm.support_pow_le

theorem support_zpow_le (σ : Perm α) : ∀ n : ℤ, (σ ^ n).support ≤ σ.support
  | (Int.ofNat n) => σ.support_pow_le _
  | (Int.negSucc n) => by
    rw [zpow_negSucc, support_inv]
    exact σ.support_pow_le _
#align equiv.perm.support_zpow_le Equiv.Perm.support_zpow_le

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

theorem support_eq_pair_iff {x y : α} : f.support = {x, y} ↔ x ≠ y ∧ IsSwap f x y := by
  rcases eq_or_ne x y with rfl | hxy
  · simp_rw [insert_eq_of_mem (mem_singleton x), support_ne_singleton, ne_eq, not_true, false_and]
  · simp_rw [ne_eq, hxy, not_false_eq_true, true_and, le_antisymm_iff (a := f.support),
    le_eq_subset, Set.pair_subset_iff, Set.subset_pair_iff, mem_support]
    refine' ⟨fun ⟨hz, hx, hy⟩ => _, fun ⟨hz, hx, hy⟩ => _⟩
    · have Hx := hz _ (apply_mem_support.mpr hx)
      simp_rw [hx, false_or] at Hx
      have Hy := hz _ (apply_mem_support.mpr hy)
      simp_rw [hy, or_false] at Hy
      have Hz := fun {z} => (hz z).mt
      simp_rw [not_or, ne_eq, not_not, and_imp] at Hz
      exact ⟨Hz, Hx, Hy⟩
    · simp_rw [ne_eq, hx, hxy.symm, hy, hxy, not_false_eq_true, and_true]
      simp_rw [← and_imp, ← not_or] at hz
      exact fun z Hz => by_contra (fun h => Hz (hz h))

/-


theorem pow_apply_eq_self_of_apply_eq_self {x : α} (hfx : f x = x) : ∀ n : ℕ, (f ^ n) x = x
  | 0 => rfl
  | n + 1 => by rw [pow_succ, mul_apply, hfx, pow_apply_eq_self_of_apply_eq_self hfx n]
#align equiv.perm.pow_apply_eq_self_of_apply_eq_self Equiv.Perm.pow_apply_eq_self_of_apply_eq_self

theorem zpow_apply_eq_self_of_apply_eq_self {x : α} (hfx : f x = x) : ∀ n : ℤ, (f ^ n) x = x
  | (n : ℕ) => pow_apply_eq_self_of_apply_eq_self hfx n
  | Int.negSucc n => by rw [zpow_negSucc, inv_eq_iff_eq, pow_apply_eq_self_of_apply_eq_self hfx]
#align equiv.perm.zpow_apply_eq_self_of_apply_eq_self Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self

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


section Set

variable (p q : Perm α)

theorem set_support_inv_eq : { x | p⁻¹ x ≠ x } = { x | p x ≠ x } := by
  ext x
  simp only [Set.mem_setOf_eq, Ne]
  rw [inv_def, symm_apply_eq, eq_comm]
#align equiv.perm.set_support_inv_eq Equiv.Perm.set_support_inv_eq

theorem set_support_apply_mem {p : Perm α} {a : α} :
    p a ∈ { x | p x ≠ x } ↔ a ∈ { x | p x ≠ x } := by simp
#align equiv.perm.set_support_apply_mem Equiv.Perm.set_support_apply_mem

theorem set_support_zpow_subset (n : ℤ) : { x | (p ^ n) x ≠ x } ⊆ { x | p x ≠ x } := by
  intro x
  simp only [Set.mem_setOf_eq, Ne]
  intro hx H
  simp [zpow_apply_eq_self_of_apply_eq_self H] at hx
#align equiv.perm.set_support_zpow_subset Equiv.Perm.set_support_zpow_subset

theorem set_support_mul_subset : { x | (p * q) x ≠ x } ⊆ { x | p x ≠ x } ∪ { x | q x ≠ x } := by
  intro x
  simp only [Perm.coe_mul, Function.comp_apply, Ne, Set.mem_union, Set.mem_setOf_eq]
  by_cases hq : q x = x <;> simp [hq]
#align equiv.perm.set_support_mul_subset Equiv.Perm.set_support_mul_subset

end Set
-/

/-
theorem coe_support_eq_set_support (f : Perm α) : (f.support : Set α) = { x | f x ≠ x } := by
  ext
  simp
#align equiv.perm.coe_support_eq_set_support Equiv.Perm.coe_support_eq_set_support
-/


/-
@[simp]
theorem apply_pow_apply_eq_iff (f : Perm α) (n : ℕ) {x : α} :
    f ((f ^ n) x) = (f ^ n) x ↔ f x = x := by
  rw [← mul_apply, Commute.self_pow f, mul_apply, apply_eq_iff_eq]


@[simp]
theorem apply_zpow_apply_eq_iff (f : Perm α) (n : ℤ) {x : α} :
    f ((f ^ n) x) = (f ^ n) x ↔ f x = x := by
  rw [← mul_apply, Commute.self_zpow f, mul_apply, apply_eq_iff_eq]
-/


section DecidableEq

variable [DecidableEq α]

theorem support_swap_iff [DecidableEq α] (x y : α) : support (swap x y) = {x, y} ↔ x ≠ y := by
  simp_rw [support_eq_pair_iff, swap_isSwap, and_true]
#align equiv.perm.support_swap_iff Equiv.Perm.support_swap_iff

@[simp]
theorem support_swap {x y : α} (h : x ≠ y) : support (swap x y) = {x, y} := by
  rwa [support_swap_iff]
#align equiv.perm.support_swap Equiv.Perm.support_swap

theorem support_swap_mul_swap {x y z : α} (hxz : x ≠ z) :
    support (swap x y * swap y z) = {x, y, z} := by
  rcases eq_or_ne z y with rfl | hzy
  · simp_rw [swap_self, mul_refl, insert_eq_of_mem (mem_singleton z)]
    exact support_swap hxz
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
  by_cases hzx : z = x
  · simp [hzx]
  by_cases hzf : z = f x
  · simp [hzf, hx, h, swap_apply_of_ne_of_ne]
  by_cases hzfx : f z = x
  · simp [Ne.symm hzx, hzx, Ne.symm hzf, hzfx]
  · simp [Ne.symm hzx, hzx, Ne.symm hzf, hzfx, f.injective.ne hzx, swap_apply_of_ne_of_ne]
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

section DecidableEqFintype

variable [DecidableEq α] [Fintype α]

instance fintype_support (f : Perm α) : Fintype (f.support) := setFintype f.support

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

theorem Disjoint.zpow_disjoint_zpow {σ τ : Perm α} (hστ : Disjoint σ τ) (m n : ℤ) :
    Disjoint (σ ^ m) (τ ^ n) := by
  rw [disjoint_iff_disjoint_support, disjoint_iff, eq_bot_iff] at hστ ⊢
  exact (inf_le_inf (support_zpow_le _ _) (support_zpow_le _ _)).trans hστ
#align equiv.perm.disjoint.zpow_disjoint_zpow Equiv.Perm.Disjoint.zpow_disjoint_zpow

theorem Disjoint.pow_disjoint_pow {σ τ : Perm α} (hστ : Disjoint σ τ) (m n : ℕ) :
    Disjoint (σ ^ m) (τ ^ n) := hστ.zpow_disjoint_zpow m n
#align equiv.perm.disjoint.pow_disjoint_pow Equiv.Perm.Disjoint.pow_disjoint_pow

theorem Disjoint.disjoint_support (h : Disjoint f g) : _root_.Disjoint f.support g.support :=
  disjoint_iff_disjoint_support.1 h
#align equiv.perm.disjoint.disjoint_support Equiv.Perm.Disjoint.disjoint_support

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
      simpa using hx
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
  simp [Subtype.ext_iff]
#align equiv.perm.support_subtype_perm Equiv.Perm.support_subtype_perm

section Conjugation

variable {α : Type*} [Fintype α] [DecidableEq α] {σ τ : Perm α}

@[simp]
theorem support_conj : (σ * τ * σ⁻¹).support = τ.support.image σ := by
  ext x
  rw [mem_support_conj, mem_image]
  refine' ⟨fun h => ⟨_, h, apply_inv_self _ _⟩,
  fun ⟨y, hy, hyx⟩ => by rw [← eq_inv_iff_eq] at hyx ; rwa [hyx] at hy⟩
#align equiv.perm.support_conj Equiv.Perm.support_conj

end Conjugation


section Card

variable [Fintype α] [DecidableEq α]

theorem card_support_eq_zero {f : Perm α} : f.support.toFinset.card = 0 ↔ f = 1 := by
  rw [Finset.card_eq_zero, toFinset_eq_empty, support_eq_empty_iff]
#align equiv.perm.card_support_eq_zero Equiv.Perm.card_support_eq_zero

theorem one_lt_card_support_of_ne_one {f : Perm α} (h : f ≠ 1) : 1 < f.support.toFinset.card := by
  simp_rw [Finset.one_lt_card_iff, mem_toFinset, mem_support, ← not_or]
  contrapose! h
  ext a
  specialize h (f a) a
  rwa [apply_eq_iff_eq, or_self_iff, or_self_iff] at h
#align equiv.perm.one_lt_card_support_of_ne_one Equiv.Perm.one_lt_card_support_of_ne_one

theorem card_support_ne_one (f : Perm α) : f.support.toFinset.card ≠ 1 := by
  by_cases h : f = 1
  · exact ne_of_eq_of_ne (card_support_eq_zero.mpr h) zero_ne_one
  · exact ne_of_gt (one_lt_card_support_of_ne_one h)
#align equiv.perm.card_support_ne_one Equiv.Perm.card_support_ne_one

@[simp]
theorem card_support_le_one {f : Perm α} : f.support.toFinset.card ≤ 1 ↔ f = 1 := by
  rw [le_iff_lt_or_eq, Nat.lt_succ_iff, Nat.le_zero, card_support_eq_zero, or_iff_not_imp_right,
    imp_iff_right f.card_support_ne_one]
#align equiv.perm.card_support_le_one Equiv.Perm.card_support_le_one

theorem two_le_card_support_of_ne_one {f : Perm α} (h : f ≠ 1) : 2 ≤ f.support.toFinset.card :=
  one_lt_card_support_of_ne_one h
#align equiv.perm.two_le_card_support_of_ne_one Equiv.Perm.two_le_card_support_of_ne_one

theorem card_support_swap_mul {f : Perm α} {x : α} (hx : f x ≠ x) :
    (swap x (f x) * f).support.toFinset.card < f.support.toFinset.card := by
  refine' Finset.card_lt_card (toFinset_ssubset_toFinset.mpr
    ⟨fun z hz => (mem_support_swap_mul_imp_mem_support_ne hz).left, fun h =>
      absurd (h (mem_support.2 hx)) (mt mem_support.1 (by simp))⟩)
#align equiv.perm.card_support_swap_mul Equiv.Perm.card_support_swap_mul

theorem card_support_swap {x y : α} (hxy : x ≠ y) : (swap x y).support.toFinset.card = 2 :=
  show (swap x y).support.toFinset.card = Finset.card ⟨x ::ₘ y ::ₘ 0, by simp [hxy]⟩ from
    congr_arg Finset.card <| by simp [support_swap hxy, *, Finset.ext_iff]
#align equiv.perm.card_support_swap Equiv.Perm.card_support_swap

@[simp]
theorem card_support_eq_two {f : Perm α} :
    f.support.toFinset.card = 2 ↔ ∃ x y, x ≠ y ∧ IsSwap f x y := by
  constructor <;> intro h
  · obtain ⟨x, t, hmem, hins, ht⟩ := Finset.card_eq_succ.1 h
    obtain ⟨y, rfl⟩ := Finset.card_eq_one.1 ht
    simp only [Finset.mem_singleton] at hmem
    refine ⟨x, y, hmem, ?_⟩
    ext a
    have key : ∀ b, f b ≠ b ↔ _ := fun b => by rw [← mem_support, ← hins, mem_insert, mem_singleton]
    by_cases ha : f a = a
    · have ha' := not_or.mp (mt (key a).mpr (not_not.mpr ha))
      rw [ha, swap_apply_of_ne_of_ne ha'.1 ha'.2]
    · have ha' := (key (f a)).mp (mt f.apply_eq_iff_eq.mp ha)
      obtain rfl | rfl := (key a).mp ha
      · rw [Or.resolve_left ha' ha, swap_apply_left]
      · rw [Or.resolve_right ha' ha, swap_apply_right]
  · obtain ⟨x, y, hxy, rfl⟩ := h
    exact card_support_swap hxy
#align equiv.perm.card_support_eq_two Equiv.Perm.card_support_eq_two


theorem card_support_prod_list_of_pairwise_disjoint {l : List (Perm α)} (h : l.Pairwise Disjoint) :
    l.prod.support.card = (l.map (Finset.card ∘ support)).sum := by
  induction' l with a t ih
  · exact card_support_eq_zero.mpr rfl
  · obtain ⟨ha, ht⟩ := List.pairwise_cons.1 h
    rw [List.prod_cons, List.map_cons, List.sum_cons, ← ih ht]
    exact (disjoint_prod_right _ ha).card_support_mul
#align equiv.perm.card_support_prod_list_of_pairwise_disjoint Equiv.Perm.card_support_prod_list_of_pairwise_disjoint

theorem card_support_extend_domain (f : α ≃ Subtype p) {g : Perm α} :
    (g.extendDomain f).support.card = g.support.card := by simp
#align equiv.perm.card_support_extend_domain Equiv.Perm.card_support_extend_domain




end Card

/-
-- support_toFinset
section Card









theorem Disjoint.card_support_mul (h : Disjoint f g) :
    (f * g).support.card = f.support.card + g.support.card := by
  rw [← Finset.card_union_of_disjoint]
  · congr
    ext
    simp [h.support_mul]
  · simpa using h.disjoint_support
#align equiv.perm.disjoint.card_support_mul Equiv.Perm.Disjoint.card_support_mul


end Card
section FixedPoints

namespace Equiv.Perm
/-!
### Fixed points
-/

variable {α : Type*}

theorem fixed_point_card_lt_of_ne_one [DecidableEq α] [Fintype α] {σ : Perm α} (h : σ ≠ 1) :
    (filter (fun x => σ x = x) univ).card < Fintype.card α - 1 := by
  rw [Nat.lt_sub_iff_add_lt, ← Nat.lt_sub_iff_add_lt', ← Finset.card_compl, Finset.compl_filter]
  exact one_lt_card_support_of_ne_one h
#align equiv.perm.fixed_point_card_lt_of_ne_one Equiv.Perm.fixed_point_card_lt_of_ne_one

end Equiv.Perm

end FixedPoints
-/

/-

theorem card_support_conj : (σ * τ * σ⁻¹).support.card = τ.support.card := by simp
#align equiv.perm.card_support_conj Equiv.Perm.card_support_conj

-/

end support

end Equiv.Perm
