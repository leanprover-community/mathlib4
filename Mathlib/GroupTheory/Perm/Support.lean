/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Aaron Anderson, Yakov Pechersky
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.GroupTheory.Perm.Basic

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

-/


open Equiv Finset

namespace Equiv.Perm

variable {α : Type*}

section Disjoint

/-- Two permutations `f` and `g` are `Disjoint` if their supports are disjoint, i.e.,
every element is fixed either by `f`, or by `g`. -/
def Disjoint (f g : Perm α) :=
  ∀ x, f x = x ∨ g x = x
#align equiv.perm.disjoint Equiv.Perm.Disjoint

variable {f g h : Perm α}

@[symm]
theorem Disjoint.symm : Disjoint f g → Disjoint g f := by simp only [Disjoint, or_comm, imp_self]
                                                          -- 🎉 no goals
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
                                     -- 🎉 no goals
          simp [mul_apply, hf, g.injective hg])
          -- 🎉 no goals
      fun hg =>
      (h (f x)).elim (fun hf => by simp [mul_apply, f.injective hf, hg]) fun hf => by
                                   -- 🎉 no goals
        simp [mul_apply, hf, hg]
        -- 🎉 no goals
#align equiv.perm.disjoint.commute Equiv.Perm.Disjoint.commute

@[simp]
theorem disjoint_one_left (f : Perm α) : Disjoint 1 f := fun _ => Or.inl rfl
#align equiv.perm.disjoint_one_left Equiv.Perm.disjoint_one_left

@[simp]
theorem disjoint_one_right (f : Perm α) : Disjoint f 1 := fun _ => Or.inr rfl
#align equiv.perm.disjoint_one_right Equiv.Perm.disjoint_one_right

theorem disjoint_iff_eq_or_eq : Disjoint f g ↔ ∀ x : α, f x = x ∨ g x = x :=
  Iff.rfl
#align equiv.perm.disjoint_iff_eq_or_eq Equiv.Perm.disjoint_iff_eq_or_eq

@[simp]
theorem disjoint_refl_iff : Disjoint f f ↔ f = 1 := by
  refine' ⟨fun h => _, fun h => h.symm ▸ disjoint_one_left 1⟩
  -- ⊢ f = 1
  ext x
  -- ⊢ ↑f x = ↑1 x
  cases' h x with hx hx <;> simp [hx]
  -- ⊢ ↑f x = ↑1 x
                            -- 🎉 no goals
                            -- 🎉 no goals
#align equiv.perm.disjoint_refl_iff Equiv.Perm.disjoint_refl_iff

theorem Disjoint.inv_left (h : Disjoint f g) : Disjoint f⁻¹ g := by
  intro x
  -- ⊢ ↑f⁻¹ x = x ∨ ↑g x = x
  rw [inv_eq_iff_eq, eq_comm]
  -- ⊢ ↑f x = x ∨ ↑g x = x
  exact h x
  -- 🎉 no goals
#align equiv.perm.disjoint.inv_left Equiv.Perm.Disjoint.inv_left

theorem Disjoint.inv_right (h : Disjoint f g) : Disjoint f g⁻¹ :=
  h.symm.inv_left.symm
#align equiv.perm.disjoint.inv_right Equiv.Perm.Disjoint.inv_right

@[simp]
theorem disjoint_inv_left_iff : Disjoint f⁻¹ g ↔ Disjoint f g := by
  refine' ⟨fun h => _, Disjoint.inv_left⟩
  -- ⊢ Disjoint f g
  convert h.inv_left
  -- 🎉 no goals
#align equiv.perm.disjoint_inv_left_iff Equiv.Perm.disjoint_inv_left_iff

@[simp]
theorem disjoint_inv_right_iff : Disjoint f g⁻¹ ↔ Disjoint f g := by
  rw [disjoint_comm, disjoint_inv_left_iff, disjoint_comm]
  -- 🎉 no goals
#align equiv.perm.disjoint_inv_right_iff Equiv.Perm.disjoint_inv_right_iff

theorem Disjoint.mul_left (H1 : Disjoint f h) (H2 : Disjoint g h) : Disjoint (f * g) h := fun x =>
  by cases H1 x <;> cases H2 x <;> simp [*]
     -- ⊢ ↑(f * g) x = x ∨ ↑h x = x
                    -- ⊢ ↑(f * g) x = x ∨ ↑h x = x
                    -- ⊢ ↑(f * g) x = x ∨ ↑h x = x
                                   -- 🎉 no goals
                                   -- 🎉 no goals
                                   -- 🎉 no goals
                                   -- 🎉 no goals
#align equiv.perm.disjoint.mul_left Equiv.Perm.Disjoint.mul_left

theorem Disjoint.mul_right (H1 : Disjoint f g) (H2 : Disjoint f h) : Disjoint f (g * h) := by
  rw [disjoint_comm]
  -- ⊢ Disjoint (g * h) f
  exact H1.symm.mul_left H2.symm
  -- 🎉 no goals
#align equiv.perm.disjoint.mul_right Equiv.Perm.Disjoint.mul_right

-- porting note: todo: make it `@[simp]`
theorem disjoint_conj (h : Perm α) : Disjoint (h * f * h⁻¹) (h * g * h⁻¹) ↔ Disjoint f g :=
  (h⁻¹).forall_congr fun {_} ↦ by simp only [mul_apply, eq_inv_iff_eq]
                                  -- 🎉 no goals

theorem Disjoint.conj (H : Disjoint f g) (h : Perm α) : Disjoint (h * f * h⁻¹) (h * g * h⁻¹) :=
  (disjoint_conj h).2 H

theorem disjoint_prod_right (l : List (Perm α)) (h : ∀ g ∈ l, Disjoint f g) :
    Disjoint f l.prod := by
  induction' l with g l ih
  -- ⊢ Disjoint f (List.prod [])
  · exact disjoint_one_right _
    -- 🎉 no goals
  · rw [List.prod_cons]
    -- ⊢ Disjoint f (g * List.prod l)
    exact (h _ (List.mem_cons_self _ _)).mul_right (ih fun g hg => h g (List.mem_cons_of_mem _ hg))
    -- 🎉 no goals
#align equiv.perm.disjoint_prod_right Equiv.Perm.disjoint_prod_right

theorem disjoint_prod_perm {l₁ l₂ : List (Perm α)} (hl : l₁.Pairwise Disjoint) (hp : l₁ ~ l₂) :
    l₁.prod = l₂.prod :=
  hp.prod_eq' <| hl.imp Disjoint.commute
#align equiv.perm.disjoint_prod_perm Equiv.Perm.disjoint_prod_perm

theorem nodup_of_pairwise_disjoint {l : List (Perm α)} (h1 : (1 : Perm α) ∉ l)
     (h2 : l.Pairwise Disjoint) : l.Nodup := by
  refine' List.Pairwise.imp_of_mem _ h2
  -- ⊢ ∀ {a b : Perm α}, a ∈ l → b ∈ l → Disjoint a b → a ≠ b
  intro τ σ h_mem _ h_disjoint _
  -- ⊢ False
  subst τ
  -- ⊢ False
  suffices (σ : Perm α) = 1 by
    rw [this] at h_mem
    exact h1 h_mem
  exact ext fun a => (or_self_iff _).mp (h_disjoint a)
  -- 🎉 no goals
#align equiv.perm.nodup_of_pairwise_disjoint Equiv.Perm.nodup_of_pairwise_disjoint

theorem pow_apply_eq_self_of_apply_eq_self {x : α} (hfx : f x = x) : ∀ n : ℕ, (f ^ n) x = x
  | 0 => rfl
  | n + 1 => by rw [pow_succ', mul_apply, hfx, pow_apply_eq_self_of_apply_eq_self hfx n]
                -- 🎉 no goals
#align equiv.perm.pow_apply_eq_self_of_apply_eq_self Equiv.Perm.pow_apply_eq_self_of_apply_eq_self

theorem zpow_apply_eq_self_of_apply_eq_self {x : α} (hfx : f x = x) : ∀ n : ℤ, (f ^ n) x = x
  | (n : ℕ) => pow_apply_eq_self_of_apply_eq_self hfx n
  | Int.negSucc n => by rw [zpow_negSucc, inv_eq_iff_eq, pow_apply_eq_self_of_apply_eq_self hfx]
                        -- 🎉 no goals
#align equiv.perm.zpow_apply_eq_self_of_apply_eq_self Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self

theorem pow_apply_eq_of_apply_apply_eq_self {x : α} (hffx : f (f x) = x) :
    ∀ n : ℕ, (f ^ n) x = x ∨ (f ^ n) x = f x
  | 0 => Or.inl rfl
  | n + 1 =>
    (pow_apply_eq_of_apply_apply_eq_self hffx n).elim
      (fun h => Or.inr (by rw [pow_succ, mul_apply, h]))
                           -- 🎉 no goals
      fun h => Or.inl (by rw [pow_succ, mul_apply, h, hffx])
                          -- 🎉 no goals
#align equiv.perm.pow_apply_eq_of_apply_apply_eq_self Equiv.Perm.pow_apply_eq_of_apply_apply_eq_self

theorem zpow_apply_eq_of_apply_apply_eq_self {x : α} (hffx : f (f x) = x) :
    ∀ i : ℤ, (f ^ i) x = x ∨ (f ^ i) x = f x
  | (n : ℕ) => pow_apply_eq_of_apply_apply_eq_self hffx n
  | Int.negSucc n => by
    rw [zpow_negSucc, inv_eq_iff_eq, ← f.injective.eq_iff, ← mul_apply, ← pow_succ, eq_comm,
      inv_eq_iff_eq, ← mul_apply, ← pow_succ', @eq_comm _ x, or_comm]
    exact pow_apply_eq_of_apply_apply_eq_self hffx _
    -- 🎉 no goals
#align equiv.perm.zpow_apply_eq_of_apply_apply_eq_self Equiv.Perm.zpow_apply_eq_of_apply_apply_eq_self

theorem Disjoint.mul_apply_eq_iff {σ τ : Perm α} (hστ : Disjoint σ τ) {a : α} :
    (σ * τ) a = a ↔ σ a = a ∧ τ a = a := by
  refine' ⟨fun h => _, fun h => by rw [mul_apply, h.2, h.1]⟩
  -- ⊢ ↑σ a = a ∧ ↑τ a = a
  cases' hστ a with hσ hτ
  -- ⊢ ↑σ a = a ∧ ↑τ a = a
  · exact ⟨hσ, σ.injective (h.trans hσ.symm)⟩
    -- 🎉 no goals
  · exact ⟨(congr_arg σ hτ).symm.trans h, hτ⟩
    -- 🎉 no goals
#align equiv.perm.disjoint.mul_apply_eq_iff Equiv.Perm.Disjoint.mul_apply_eq_iff

theorem Disjoint.mul_eq_one_iff {σ τ : Perm α} (hστ : Disjoint σ τ) : σ * τ = 1 ↔ σ = 1 ∧ τ = 1 :=
  by simp_rw [ext_iff, one_apply, hστ.mul_apply_eq_iff, forall_and]
     -- 🎉 no goals
#align equiv.perm.disjoint.mul_eq_one_iff Equiv.Perm.Disjoint.mul_eq_one_iff

theorem Disjoint.zpow_disjoint_zpow {σ τ : Perm α} (hστ : Disjoint σ τ) (m n : ℤ) :
    Disjoint (σ ^ m) (τ ^ n) := fun x =>
  Or.imp (fun h => zpow_apply_eq_self_of_apply_eq_self h m)
    (fun h => zpow_apply_eq_self_of_apply_eq_self h n) (hστ x)
#align equiv.perm.disjoint.zpow_disjoint_zpow Equiv.Perm.Disjoint.zpow_disjoint_zpow

theorem Disjoint.pow_disjoint_pow {σ τ : Perm α} (hστ : Disjoint σ τ) (m n : ℕ) :
    Disjoint (σ ^ m) (τ ^ n) :=
  hστ.zpow_disjoint_zpow m n
#align equiv.perm.disjoint.pow_disjoint_pow Equiv.Perm.Disjoint.pow_disjoint_pow

end Disjoint

section IsSwap

variable [DecidableEq α]

/-- `f.IsSwap` indicates that the permutation `f` is a transposition of two elements. -/
def IsSwap (f : Perm α) : Prop :=
  ∃ x y, x ≠ y ∧ f = swap x y
#align equiv.perm.is_swap Equiv.Perm.IsSwap

@[simp]
theorem ofSubtype_swap_eq {p : α → Prop} [DecidablePred p] (x y : Subtype p) :
    ofSubtype (Equiv.swap x y) = Equiv.swap ↑x ↑y :=
  Equiv.ext fun z => by
    by_cases hz : p z
    -- ⊢ ↑(↑ofSubtype (swap x y)) z = ↑(swap ↑x ↑y) z
    · rw [swap_apply_def, ofSubtype_apply_of_mem _ hz]
      -- ⊢ ↑(↑(swap x y) { val := z, property := hz }) = if z = ↑x then ↑y else if z =  …
      split_ifs with hzx hzy
      · simp_rw [hzx, Subtype.coe_eta, swap_apply_left]
        -- 🎉 no goals
      · simp_rw [hzy, Subtype.coe_eta, swap_apply_right]
        -- 🎉 no goals
      · rw [swap_apply_of_ne_of_ne] <;>
        -- ⊢ { val := z, property := hz } ≠ x
        simp [Subtype.ext_iff, *]
        -- 🎉 no goals
        -- 🎉 no goals
    · rw [ofSubtype_apply_of_not_mem _ hz, swap_apply_of_ne_of_ne]
      -- ⊢ z ≠ ↑x
      intro h
      -- ⊢ False
      apply hz
      -- ⊢ p z
      rw [h]
      -- ⊢ p ↑x
      exact Subtype.prop x
      -- ⊢ z ≠ ↑y
      intro h
      -- ⊢ False
      apply hz
      -- ⊢ p z
      rw [h]
      -- ⊢ p ↑y
      exact Subtype.prop y
      -- 🎉 no goals
#align equiv.perm.of_subtype_swap_eq Equiv.Perm.ofSubtype_swap_eq

theorem IsSwap.of_subtype_isSwap {p : α → Prop} [DecidablePred p] {f : Perm (Subtype p)}
    (h : f.IsSwap) : (ofSubtype f).IsSwap :=
  let ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := h
  ⟨x, y, by
    simp only [Ne.def, Subtype.ext_iff] at hxy
    -- ⊢ x ≠ y
    exact hxy.1, by
    -- 🎉 no goals
    rw [hxy.2, ofSubtype_swap_eq]⟩
    -- 🎉 no goals
#align equiv.perm.is_swap.of_subtype_is_swap Equiv.Perm.IsSwap.of_subtype_isSwap

theorem ne_and_ne_of_swap_mul_apply_ne_self {f : Perm α} {x y : α} (hy : (swap x (f x) * f) y ≠ y) :
    f y ≠ y ∧ y ≠ x := by
  simp only [swap_apply_def, mul_apply, f.injective.eq_iff] at *
  -- ⊢ ↑f y ≠ y ∧ y ≠ x
  by_cases h : f y = x
  -- ⊢ ↑f y ≠ y ∧ y ≠ x
  · constructor <;> intro <;> simp_all only [if_true, eq_self_iff_true, not_true, Ne.def]
    -- ⊢ ↑f y ≠ y
                    -- ⊢ False
                    -- ⊢ False
                              -- 🎉 no goals
                              -- 🎉 no goals
  · split_ifs at hy with h h <;> try { subst x } <;> try { simp [*] at * }
                                 -- ⊢ ↑f y ≠ y ∧ y ≠ x
                                 -- ⊢ ↑f y ≠ y ∧ y ≠ x
                                 -- ⊢ ↑f y ≠ y ∧ y ≠ x
                                                     -- 🎉 no goals
                                                     -- 🎉 no goals
                                                     -- 🎉 no goals
#align equiv.perm.ne_and_ne_of_swap_mul_apply_ne_self Equiv.Perm.ne_and_ne_of_swap_mul_apply_ne_self

end IsSwap

section support

section Set

variable (p q : Perm α)

theorem set_support_inv_eq : { x | p⁻¹ x ≠ x } = { x | p x ≠ x } := by
  ext x
  -- ⊢ x ∈ {x | ↑p⁻¹ x ≠ x} ↔ x ∈ {x | ↑p x ≠ x}
  simp only [Set.mem_setOf_eq, Ne.def]
  -- ⊢ ¬↑p⁻¹ x = x ↔ ¬↑p x = x
  rw [inv_def, symm_apply_eq, eq_comm]
  -- 🎉 no goals
#align equiv.perm.set_support_inv_eq Equiv.Perm.set_support_inv_eq

theorem set_support_apply_mem {p : Perm α} {a : α} : p a ∈ { x | p x ≠ x } ↔ a ∈ { x | p x ≠ x } :=
  by simp
     -- 🎉 no goals
#align equiv.perm.set_support_apply_mem Equiv.Perm.set_support_apply_mem

theorem set_support_zpow_subset (n : ℤ) : { x | (p ^ n) x ≠ x } ⊆ { x | p x ≠ x } := by
  intro x
  -- ⊢ x ∈ {x | ↑(p ^ n) x ≠ x} → x ∈ {x | ↑p x ≠ x}
  simp only [Set.mem_setOf_eq, Ne.def]
  -- ⊢ ¬↑(p ^ n) x = x → ¬↑p x = x
  intro hx H
  -- ⊢ False
  simp [zpow_apply_eq_self_of_apply_eq_self H] at hx
  -- 🎉 no goals
#align equiv.perm.set_support_zpow_subset Equiv.Perm.set_support_zpow_subset

theorem set_support_mul_subset : { x | (p * q) x ≠ x } ⊆ { x | p x ≠ x } ∪ { x | q x ≠ x } := by
  intro x
  -- ⊢ x ∈ {x | ↑(p * q) x ≠ x} → x ∈ {x | ↑p x ≠ x} ∪ {x | ↑q x ≠ x}
  simp only [Perm.coe_mul, Function.comp_apply, Ne.def, Set.mem_union, Set.mem_setOf_eq]
  -- ⊢ ¬↑p (↑q x) = x → ¬↑p x = x ∨ ¬↑q x = x
  by_cases hq : q x = x <;> simp [hq]
  -- ⊢ ¬↑p (↑q x) = x → ¬↑p x = x ∨ ¬↑q x = x
                            -- 🎉 no goals
                            -- 🎉 no goals
#align equiv.perm.set_support_mul_subset Equiv.Perm.set_support_mul_subset

end Set

variable [DecidableEq α] [Fintype α] {f g : Perm α}

/-- The `Finset` of nonfixed points of a permutation. -/
def support (f : Perm α) : Finset α :=
  univ.filter fun x => f x ≠ x
#align equiv.perm.support Equiv.Perm.support

@[simp]
theorem mem_support {x : α} : x ∈ f.support ↔ f x ≠ x := by
  rw [support, mem_filter, and_iff_right (mem_univ x)]
  -- 🎉 no goals
#align equiv.perm.mem_support Equiv.Perm.mem_support

theorem not_mem_support {x : α} : x ∉ f.support ↔ f x = x := by simp
                                                                -- 🎉 no goals
#align equiv.perm.not_mem_support Equiv.Perm.not_mem_support

theorem coe_support_eq_set_support (f : Perm α) : (f.support : Set α) = { x | f x ≠ x } := by
  ext
  -- ⊢ x✝ ∈ ↑(support f) ↔ x✝ ∈ {x | ↑f x ≠ x}
  simp
  -- 🎉 no goals
#align equiv.perm.coe_support_eq_set_support Equiv.Perm.coe_support_eq_set_support

@[simp]
theorem support_eq_empty_iff {σ : Perm α} : σ.support = ∅ ↔ σ = 1 := by
  simp_rw [Finset.ext_iff, mem_support, Finset.not_mem_empty, iff_false_iff, not_not,
    Equiv.Perm.ext_iff, one_apply]
#align equiv.perm.support_eq_empty_iff Equiv.Perm.support_eq_empty_iff

@[simp]
theorem support_one : (1 : Perm α).support = ∅ := by rw [support_eq_empty_iff]
                                                     -- 🎉 no goals
#align equiv.perm.support_one Equiv.Perm.support_one

@[simp]
theorem support_refl : support (Equiv.refl α) = ∅ :=
  support_one
#align equiv.perm.support_refl Equiv.Perm.support_refl

theorem support_congr (h : f.support ⊆ g.support) (h' : ∀ x ∈ g.support, f x = g x) : f = g := by
  ext x
  -- ⊢ ↑f x = ↑g x
  by_cases hx : x ∈ g.support
  -- ⊢ ↑f x = ↑g x
  · exact h' x hx
    -- 🎉 no goals
  · rw [not_mem_support.mp hx, ← not_mem_support]
    -- ⊢ ¬x ∈ support f
    exact fun H => hx (h H)
    -- 🎉 no goals
#align equiv.perm.support_congr Equiv.Perm.support_congr

theorem support_mul_le (f g : Perm α) : (f * g).support ≤ f.support ⊔ g.support := fun x => by
  simp only [sup_eq_union]
  -- ⊢ x ∈ support (f * g) → x ∈ support f ∪ support g
  rw [mem_union, mem_support, mem_support, mem_support, mul_apply, ← not_and_or, not_imp_not]
  -- ⊢ ↑f x = x ∧ ↑g x = x → ↑f (↑g x) = x
  rintro ⟨hf, hg⟩
  -- ⊢ ↑f (↑g x) = x
  rw [hg, hf]
  -- 🎉 no goals
#align equiv.perm.support_mul_le Equiv.Perm.support_mul_le

theorem exists_mem_support_of_mem_support_prod {l : List (Perm α)} {x : α}
    (hx : x ∈ l.prod.support) : ∃ f : Perm α, f ∈ l ∧ x ∈ f.support := by
  contrapose! hx
  -- ⊢ ¬x ∈ support (List.prod l)
  simp_rw [mem_support, not_not] at hx ⊢
  -- ⊢ ↑(List.prod l) x = x
  induction' l with f l ih
  -- ⊢ ↑(List.prod []) x = x
  · rfl
    -- 🎉 no goals
  · rw [List.prod_cons, mul_apply, ih, hx]
    -- ⊢ f ∈ f :: l
    simp only [List.find?, List.mem_cons, true_or]
    -- ⊢ ∀ (f : Perm α), f ∈ l → ↑f x = x
    intros f' hf'
    -- ⊢ ↑f' x = x
    refine' hx f' _
    -- ⊢ f' ∈ f :: l
    simp only [List.find?, List.mem_cons]
    -- ⊢ f' = f ∨ f' ∈ l
    exact Or.inr hf'
    -- 🎉 no goals
#align equiv.perm.exists_mem_support_of_mem_support_prod Equiv.Perm.exists_mem_support_of_mem_support_prod

theorem support_pow_le (σ : Perm α) (n : ℕ) : (σ ^ n).support ≤ σ.support := fun _ h1 =>
  mem_support.mpr fun h2 => mem_support.mp h1 (pow_apply_eq_self_of_apply_eq_self h2 n)
#align equiv.perm.support_pow_le Equiv.Perm.support_pow_le

@[simp]
theorem support_inv (σ : Perm α) : support σ⁻¹ = σ.support := by
  simp_rw [Finset.ext_iff, mem_support, not_iff_not, inv_eq_iff_eq.trans eq_comm, imp_true_iff]
  -- 🎉 no goals
#align equiv.perm.support_inv Equiv.Perm.support_inv

-- @[simp] -- Porting note: simp can prove this
theorem apply_mem_support {x : α} : f x ∈ f.support ↔ x ∈ f.support := by
  rw [mem_support, mem_support, Ne.def, Ne.def, apply_eq_iff_eq]
  -- 🎉 no goals
#align equiv.perm.apply_mem_support Equiv.Perm.apply_mem_support

-- Porting note: new theorem
@[simp]
theorem apply_pow_apply_eq_iff (f : Perm α) (n : ℕ) {x : α} :
    f ((f ^ n) x) = (f ^ n) x ↔ f x = x := by
  rw [← mul_apply, Commute.self_pow f, mul_apply, apply_eq_iff_eq]
  -- 🎉 no goals

-- @[simp] -- Porting note: simp can prove this
theorem pow_apply_mem_support {n : ℕ} {x : α} : (f ^ n) x ∈ f.support ↔ x ∈ f.support := by
  simp only [mem_support, ne_eq, apply_pow_apply_eq_iff]
  -- 🎉 no goals
#align equiv.perm.pow_apply_mem_support Equiv.Perm.pow_apply_mem_support

-- Porting note: new theorem
@[simp]
theorem apply_zpow_apply_eq_iff (f : Perm α) (n : ℤ) {x : α} :
    f ((f ^ n) x) = (f ^ n) x ↔ f x = x := by
  rw [← mul_apply, Commute.self_zpow f, mul_apply, apply_eq_iff_eq]
  -- 🎉 no goals

-- @[simp] -- Porting note: simp can prove this
theorem zpow_apply_mem_support {n : ℤ} {x : α} : (f ^ n) x ∈ f.support ↔ x ∈ f.support := by
  simp only [mem_support, ne_eq, apply_zpow_apply_eq_iff]
  -- 🎉 no goals
#align equiv.perm.zpow_apply_mem_support Equiv.Perm.zpow_apply_mem_support

theorem pow_eq_on_of_mem_support (h : ∀ x ∈ f.support ∩ g.support, f x = g x) (k : ℕ) :
    ∀ x ∈ f.support ∩ g.support, (f ^ k) x = (g ^ k) x := by
  induction' k with k hk
  -- ⊢ ∀ (x : α), x ∈ support f ∩ support g → ↑(f ^ Nat.zero) x = ↑(g ^ Nat.zero) x
  · simp
    -- 🎉 no goals
  · intro x hx
    -- ⊢ ↑(f ^ Nat.succ k) x = ↑(g ^ Nat.succ k) x
    rw [pow_succ', mul_apply, pow_succ', mul_apply, h _ hx, hk]
    -- ⊢ ↑g x ∈ support f ∩ support g
    rwa [mem_inter, apply_mem_support, ← h _ hx, apply_mem_support, ← mem_inter]
    -- 🎉 no goals
#align equiv.perm.pow_eq_on_of_mem_support Equiv.Perm.pow_eq_on_of_mem_support

theorem disjoint_iff_disjoint_support : Disjoint f g ↔ _root_.Disjoint f.support g.support := by
  simp [disjoint_iff_eq_or_eq, disjoint_iff, disjoint_iff, Finset.ext_iff, not_and_or,
    imp_iff_not_or]
#align equiv.perm.disjoint_iff_disjoint_support Equiv.Perm.disjoint_iff_disjoint_support

theorem Disjoint.disjoint_support (h : Disjoint f g) : _root_.Disjoint f.support g.support :=
  disjoint_iff_disjoint_support.1 h
#align equiv.perm.disjoint.disjoint_support Equiv.Perm.Disjoint.disjoint_support

theorem Disjoint.support_mul (h : Disjoint f g) : (f * g).support = f.support ∪ g.support := by
  refine' le_antisymm (support_mul_le _ _) fun a => _
  -- ⊢ a ∈ support f ∪ support g → a ∈ support (f * g)
  rw [mem_union, mem_support, mem_support, mem_support, mul_apply, ← not_and_or, not_imp_not]
  -- ⊢ ↑f (↑g a) = a → ↑f a = a ∧ ↑g a = a
  exact
    (h a).elim (fun hf h => ⟨hf, f.apply_eq_iff_eq.mp (h.trans hf.symm)⟩) fun hg h =>
      ⟨(congr_arg f hg).symm.trans h, hg⟩
#align equiv.perm.disjoint.support_mul Equiv.Perm.Disjoint.support_mul

theorem support_prod_of_pairwise_disjoint (l : List (Perm α)) (h : l.Pairwise Disjoint) :
    l.prod.support = (l.map support).foldr (· ⊔ ·) ⊥ := by
  induction' l with hd tl hl
  -- ⊢ support (List.prod []) = List.foldr (fun x x_1 => x ⊔ x_1) ⊥ (List.map suppo …
  · simp
    -- 🎉 no goals
  · rw [List.pairwise_cons] at h
    -- ⊢ support (List.prod (hd :: tl)) = List.foldr (fun x x_1 => x ⊔ x_1) ⊥ (List.m …
    have : Disjoint hd tl.prod := disjoint_prod_right _ h.left
    -- ⊢ support (List.prod (hd :: tl)) = List.foldr (fun x x_1 => x ⊔ x_1) ⊥ (List.m …
    simp [this.support_mul, hl h.right]
    -- 🎉 no goals
#align equiv.perm.support_prod_of_pairwise_disjoint Equiv.Perm.support_prod_of_pairwise_disjoint

theorem support_prod_le (l : List (Perm α)) : l.prod.support ≤ (l.map support).foldr (· ⊔ ·) ⊥ := by
  induction' l with hd tl hl
  -- ⊢ support (List.prod []) ≤ List.foldr (fun x x_1 => x ⊔ x_1) ⊥ (List.map suppo …
  · simp
    -- 🎉 no goals
  · rw [List.prod_cons, List.map_cons, List.foldr_cons]
    -- ⊢ support (hd * List.prod tl) ≤ support hd ⊔ List.foldr (fun x x_1 => x ⊔ x_1) …
    refine' (support_mul_le hd tl.prod).trans _
    -- ⊢ support hd ⊔ support (List.prod tl) ≤ support hd ⊔ List.foldr (fun x x_1 =>  …
    exact sup_le_sup le_rfl hl
    -- 🎉 no goals
#align equiv.perm.support_prod_le Equiv.Perm.support_prod_le

theorem support_zpow_le (σ : Perm α) (n : ℤ) : (σ ^ n).support ≤ σ.support := fun _ h1 =>
  mem_support.mpr fun h2 => mem_support.mp h1 (zpow_apply_eq_self_of_apply_eq_self h2 n)
#align equiv.perm.support_zpow_le Equiv.Perm.support_zpow_le

@[simp]
theorem support_swap {x y : α} (h : x ≠ y) : support (swap x y) = {x, y} := by
  ext z
  -- ⊢ z ∈ support (swap x y) ↔ z ∈ {x, y}
  by_cases hx : z = x
  -- ⊢ z ∈ support (swap x y) ↔ z ∈ {x, y}
  any_goals simpa [hx] using h.symm
  -- ⊢ z ∈ support (swap x y) ↔ z ∈ {x, y}
  by_cases hy : z = y <;>
  -- ⊢ z ∈ support (swap x y) ↔ z ∈ {x, y}
  · simp [swap_apply_of_ne_of_ne, hx, hy] <;>
    -- ⊢ ¬x = y
    -- 🎉 no goals
    -- 🎉 no goals
    exact h
#align equiv.perm.support_swap Equiv.Perm.support_swap

theorem support_swap_iff (x y : α) : support (swap x y) = {x, y} ↔ x ≠ y := by
  refine' ⟨fun h => _, fun h => support_swap h⟩
  -- ⊢ x ≠ y
  by_contra'
  -- ⊢ False
  rw [← this] at h
  -- ⊢ False
  simp only [swap_self, support_refl, pair_eq_singleton] at h
  -- ⊢ False
  have : x ∈ ∅ := by
    rw [h]
    exact mem_singleton.mpr rfl
  have := (Finset.ne_empty_of_mem this)
  -- ⊢ False
  exact this rfl
  -- 🎉 no goals
#align equiv.perm.support_swap_iff Equiv.Perm.support_swap_iff

theorem support_swap_mul_swap {x y z : α} (h : List.Nodup [x, y, z]) :
    support (swap x y * swap y z) = {x, y, z} := by
  simp only [List.not_mem_nil, and_true_iff, List.mem_cons, not_false_iff, List.nodup_cons,
    List.mem_singleton, and_self_iff, List.nodup_nil] at h
  push_neg at h
  -- ⊢ support (swap x y * swap y z) = {x, y, z}
  apply le_antisymm
  -- ⊢ support (swap x y * swap y z) ≤ {x, y, z}
  · convert support_mul_le (swap x y) (swap y z) using 1
    -- ⊢ {x, y, z} = support (swap x y) ⊔ support (swap y z)
    rw [support_swap h.left.left, support_swap h.right.left]
    -- ⊢ {x, y, z} = {x, y} ⊔ {y, z}
    simp only [sup_eq_union]
    -- ⊢ {x, y, z} = {x, y} ∪ {y, z}
    simp only [mem_singleton, mem_insert, union_insert, insert_union, mem_union, true_or, or_true,
      insert_eq_of_mem]
    rfl
    -- 🎉 no goals
  · intro
    -- ⊢ a✝ ∈ {x, y, z} → a✝ ∈ support (swap x y * swap y z)
    simp only [mem_insert, mem_singleton]
    -- ⊢ a✝ = x ∨ a✝ = y ∨ a✝ = z → a✝ ∈ support (swap x y * swap y z)
    rintro (rfl | rfl | rfl | _) <;>
      simp [swap_apply_of_ne_of_ne, h.left.left, h.left.left.symm, h.left.right.symm,
        h.left.right.left.symm, h.right.left.symm]
#align equiv.perm.support_swap_mul_swap Equiv.Perm.support_swap_mul_swap

theorem support_swap_mul_ge_support_diff (f : Perm α) (x y : α) :
    f.support \ {x, y} ≤ (swap x y * f).support := by
  intro
  -- ⊢ a✝ ∈ support f \ {x, y} → a✝ ∈ support (swap x y * f)
  simp only [and_imp, Perm.coe_mul, Function.comp_apply, Ne.def, mem_support, mem_insert, mem_sdiff,
    mem_singleton]
  push_neg
  -- ⊢ ↑f a✝ ≠ a✝ → a✝ ≠ x ∧ a✝ ≠ y → ↑(swap x y) (↑f a✝) ≠ a✝
  rintro ha ⟨hx, hy⟩ H
  -- ⊢ False
  rw [swap_apply_eq_iff, swap_apply_of_ne_of_ne hx hy] at H
  -- ⊢ False
  exact ha H
  -- 🎉 no goals
#align equiv.perm.support_swap_mul_ge_support_diff Equiv.Perm.support_swap_mul_ge_support_diff

theorem support_swap_mul_eq (f : Perm α) (x : α) (h : f (f x) ≠ x) :
    (swap x (f x) * f).support = f.support \ {x} := by
  by_cases hx : f x = x
  -- ⊢ support (swap x (↑f x) * f) = support f \ {x}
  · simp [hx, sdiff_singleton_eq_erase, not_mem_support.mpr hx, erase_eq_of_not_mem]
    -- 🎉 no goals
  ext z
  -- ⊢ z ∈ support (swap x (↑f x) * f) ↔ z ∈ support f \ {x}
  by_cases hzx : z = x
  -- ⊢ z ∈ support (swap x (↑f x) * f) ↔ z ∈ support f \ {x}
  · simp [hzx]
    -- 🎉 no goals
  by_cases hzf : z = f x
  -- ⊢ z ∈ support (swap x (↑f x) * f) ↔ z ∈ support f \ {x}
  · simp [hzf, hx, h, swap_apply_of_ne_of_ne]
    -- 🎉 no goals
  by_cases hzfx : f z = x
  -- ⊢ z ∈ support (swap x (↑f x) * f) ↔ z ∈ support f \ {x}
  · simp [Ne.symm hzx, hzx, Ne.symm hzf, hzfx]
    -- 🎉 no goals
  · simp [Ne.symm hzx, hzx, Ne.symm hzf, hzfx, f.injective.ne hzx, swap_apply_of_ne_of_ne]
    -- 🎉 no goals
#align equiv.perm.support_swap_mul_eq Equiv.Perm.support_swap_mul_eq

theorem mem_support_swap_mul_imp_mem_support_ne {x y : α} (hy : y ∈ support (swap x (f x) * f)) :
    y ∈ support f ∧ y ≠ x := by
  simp only [mem_support, swap_apply_def, mul_apply, f.injective.eq_iff] at *
  -- ⊢ ↑f y ≠ y ∧ y ≠ x
  by_cases h : f y = x
  -- ⊢ ↑f y ≠ y ∧ y ≠ x
  · constructor <;> intro <;> simp_all only [if_true, eq_self_iff_true, not_true, Ne.def]
    -- ⊢ ↑f y ≠ y
                    -- ⊢ False
                    -- ⊢ False
                              -- 🎉 no goals
                              -- 🎉 no goals
  · split_ifs at hy with hf heq <;>
    simp_all only [not_true]
    -- 🎉 no goals
    -- ⊢ ↑f x ≠ x ∧ x ≠ x
    -- ⊢ ↑f y ≠ y ∧ y ≠ x
    exact ⟨h, hy⟩
    -- ⊢ ↑f y ≠ y ∧ y ≠ x
    refine' ⟨hy, heq⟩
    -- 🎉 no goals
#align equiv.perm.mem_support_swap_mul_imp_mem_support_ne Equiv.Perm.mem_support_swap_mul_imp_mem_support_ne

theorem Disjoint.mem_imp (h : Disjoint f g) {x : α} (hx : x ∈ f.support) : x ∉ g.support :=
  disjoint_left.mp h.disjoint_support hx
#align equiv.perm.disjoint.mem_imp Equiv.Perm.Disjoint.mem_imp

theorem eq_on_support_mem_disjoint {l : List (Perm α)} (h : f ∈ l) (hl : l.Pairwise Disjoint) :
    ∀ x ∈ f.support, f x = l.prod x := by
  induction' l with hd tl IH
  -- ⊢ ∀ (x : α), x ∈ support f → ↑f x = ↑(List.prod []) x
  · simp at h
    -- 🎉 no goals
  · intro x hx
    -- ⊢ ↑f x = ↑(List.prod (hd :: tl)) x
    rw [List.pairwise_cons] at hl
    -- ⊢ ↑f x = ↑(List.prod (hd :: tl)) x
    rw [List.mem_cons] at h
    -- ⊢ ↑f x = ↑(List.prod (hd :: tl)) x
    rcases h with (rfl | h)
    -- ⊢ ↑f x = ↑(List.prod (f :: tl)) x
    · rw [List.prod_cons, mul_apply,
        not_mem_support.mp ((disjoint_prod_right tl hl.left).mem_imp hx)]
    · rw [List.prod_cons, mul_apply, ← IH h hl.right _ hx, eq_comm, ← not_mem_support]
      -- ⊢ ¬↑f x ∈ support hd
      refine' (hl.left _ h).symm.mem_imp _
      -- ⊢ ↑f x ∈ support f
      simpa using hx
      -- 🎉 no goals
#align equiv.perm.eq_on_support_mem_disjoint Equiv.Perm.eq_on_support_mem_disjoint

theorem Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.support ≤ f.support)
    (hg : y.support ≤ g.support) : Disjoint x y := by
  rw [disjoint_iff_disjoint_support] at h ⊢
  -- ⊢ _root_.Disjoint (support x) (support y)
  exact h.mono hf hg
  -- 🎉 no goals
#align equiv.perm.disjoint.mono Equiv.Perm.Disjoint.mono

theorem support_le_prod_of_mem {l : List (Perm α)} (h : f ∈ l) (hl : l.Pairwise Disjoint) :
    f.support ≤ l.prod.support := by
  intro x hx
  -- ⊢ x ∈ support (List.prod l)
  rwa [mem_support, ← eq_on_support_mem_disjoint h hl _ hx, ← mem_support]
  -- 🎉 no goals
#align equiv.perm.support_le_prod_of_mem Equiv.Perm.support_le_prod_of_mem

section ExtendDomain

variable {β : Type*} [DecidableEq β] [Fintype β] {p : β → Prop} [DecidablePred p]

@[simp]
theorem support_extend_domain (f : α ≃ Subtype p) {g : Perm α} :
    support (g.extendDomain f) = g.support.map f.asEmbedding := by
  ext b
  -- ⊢ b ∈ support (extendDomain g f) ↔ b ∈ map (asEmbedding f) (support g)
  simp only [exists_prop, Function.Embedding.coeFn_mk, toEmbedding_apply, mem_map, Ne.def,
    Function.Embedding.trans_apply, mem_support]
  by_cases pb : p b
  -- ⊢ ¬↑(extendDomain g f) b = b ↔ ∃ a, ¬↑g a = a ∧ ↑(asEmbedding f) a = b
  · rw [extendDomain_apply_subtype _ _ pb]
    -- ⊢ ¬↑(↑f (↑g (↑f.symm { val := b, property := pb }))) = b ↔ ∃ a, ¬↑g a = a ∧ ↑( …
    constructor
    -- ⊢ ¬↑(↑f (↑g (↑f.symm { val := b, property := pb }))) = b → ∃ a, ¬↑g a = a ∧ ↑( …
    · rintro h
      -- ⊢ ∃ a, ¬↑g a = a ∧ ↑(asEmbedding f) a = b
      refine' ⟨f.symm ⟨b, pb⟩, _, by simp⟩
      -- ⊢ ¬↑g (↑f.symm { val := b, property := pb }) = ↑f.symm { val := b, property := …
      contrapose! h
      -- ⊢ ↑(↑f (↑g (↑f.symm { val := b, property := pb }))) = b
      simp [h]
      -- 🎉 no goals
    · rintro ⟨a, ha, hb⟩
      -- ⊢ ¬↑(↑f (↑g (↑f.symm { val := b, property := pb }))) = b
      contrapose! ha
      -- ⊢ ↑g a = a
      obtain rfl : a = f.symm ⟨b, pb⟩ := by
        rw [eq_symm_apply]
        exact Subtype.coe_injective hb
      rw [eq_symm_apply]
      -- ⊢ ↑f (↑g (↑f.symm { val := b, property := pb })) = { val := b, property := pb }
      exact Subtype.coe_injective ha
      -- 🎉 no goals
  · rw [extendDomain_apply_not_subtype _ _ pb]
    -- ⊢ ¬b = b ↔ ∃ a, ¬↑g a = a ∧ ↑(asEmbedding f) a = b
    simp only [not_exists, false_iff_iff, not_and, eq_self_iff_true, not_true]
    -- ⊢ ∀ (x : α), ¬↑g x = x → ¬↑(asEmbedding f) x = b
    rintro a _ rfl
    -- ⊢ False
    exact pb (Subtype.prop _)
    -- 🎉 no goals
#align equiv.perm.support_extend_domain Equiv.Perm.support_extend_domain

theorem card_support_extend_domain (f : α ≃ Subtype p) {g : Perm α} :
    (g.extendDomain f).support.card = g.support.card := by simp
                                                           -- 🎉 no goals
#align equiv.perm.card_support_extend_domain Equiv.Perm.card_support_extend_domain

end ExtendDomain

section Card

-- @[simp] -- Porting note: simp can prove this
theorem card_support_eq_zero {f : Perm α} : f.support.card = 0 ↔ f = 1 := by
  rw [Finset.card_eq_zero, support_eq_empty_iff]
  -- 🎉 no goals
#align equiv.perm.card_support_eq_zero Equiv.Perm.card_support_eq_zero

theorem one_lt_card_support_of_ne_one {f : Perm α} (h : f ≠ 1) : 1 < f.support.card := by
  simp_rw [one_lt_card_iff, mem_support, ← not_or]
  -- ⊢ ∃ a b, ¬(↑f a = a ∨ ↑f b = b ∨ a = b)
  contrapose! h
  -- ⊢ f = 1
  ext a
  -- ⊢ ↑f a = ↑1 a
  specialize h (f a) a
  -- ⊢ ↑f a = ↑1 a
  rwa [apply_eq_iff_eq, or_self_iff, or_self_iff] at h
  -- 🎉 no goals
#align equiv.perm.one_lt_card_support_of_ne_one Equiv.Perm.one_lt_card_support_of_ne_one

theorem card_support_ne_one (f : Perm α) : f.support.card ≠ 1 := by
  by_cases h : f = 1
  -- ⊢ card (support f) ≠ 1
  · exact ne_of_eq_of_ne (card_support_eq_zero.mpr h) zero_ne_one
    -- 🎉 no goals
  · exact ne_of_gt (one_lt_card_support_of_ne_one h)
    -- 🎉 no goals
#align equiv.perm.card_support_ne_one Equiv.Perm.card_support_ne_one

@[simp]
theorem card_support_le_one {f : Perm α} : f.support.card ≤ 1 ↔ f = 1 := by
  rw [le_iff_lt_or_eq, Nat.lt_succ_iff, le_zero_iff, card_support_eq_zero, or_iff_not_imp_right,
    imp_iff_right f.card_support_ne_one]
#align equiv.perm.card_support_le_one Equiv.Perm.card_support_le_one

theorem two_le_card_support_of_ne_one {f : Perm α} (h : f ≠ 1) : 2 ≤ f.support.card :=
  one_lt_card_support_of_ne_one h
#align equiv.perm.two_le_card_support_of_ne_one Equiv.Perm.two_le_card_support_of_ne_one

theorem card_support_swap_mul {f : Perm α} {x : α} (hx : f x ≠ x) :
    (swap x (f x) * f).support.card < f.support.card :=
  Finset.card_lt_card
    ⟨fun z hz => (mem_support_swap_mul_imp_mem_support_ne hz).left, fun h =>
      absurd (h (mem_support.2 hx)) (mt mem_support.1 (by simp))⟩
                                                          -- 🎉 no goals
#align equiv.perm.card_support_swap_mul Equiv.Perm.card_support_swap_mul

theorem card_support_swap {x y : α} (hxy : x ≠ y) : (swap x y).support.card = 2 :=
  show (swap x y).support.card = Finset.card ⟨x ::ₘ y ::ₘ 0, by simp [hxy]⟩ from
                                                                -- 🎉 no goals
    congr_arg card <| by simp [support_swap hxy, *, Finset.ext_iff]
                         -- 🎉 no goals
#align equiv.perm.card_support_swap Equiv.Perm.card_support_swap

@[simp]
theorem card_support_eq_two {f : Perm α} : f.support.card = 2 ↔ IsSwap f := by
  constructor <;> intro h
  -- ⊢ card (support f) = 2 → IsSwap f
                  -- ⊢ IsSwap f
                  -- ⊢ card (support f) = 2
  · obtain ⟨x, t, hmem, hins, ht⟩ := card_eq_succ.1 h
    -- ⊢ IsSwap f
    obtain ⟨y, rfl⟩ := card_eq_one.1 ht
    -- ⊢ IsSwap f
    rw [mem_singleton] at hmem
    -- ⊢ IsSwap f
    refine' ⟨x, y, hmem, _⟩
    -- ⊢ f = swap x y
    ext a
    -- ⊢ ↑f a = ↑(swap x y) a
    have key : ∀ b, f b ≠ b ↔ _ := fun b => by rw [← mem_support, ← hins, mem_insert, mem_singleton]
    -- ⊢ ↑f a = ↑(swap x y) a
    by_cases ha : f a = a
    -- ⊢ ↑f a = ↑(swap x y) a
    · have ha' := not_or.mp (mt (key a).mpr (not_not.mpr ha))
      -- ⊢ ↑f a = ↑(swap x y) a
      rw [ha, swap_apply_of_ne_of_ne ha'.1 ha'.2]
      -- 🎉 no goals
    · have ha' := (key (f a)).mp (mt f.apply_eq_iff_eq.mp ha)
      -- ⊢ ↑f a = ↑(swap x y) a
      obtain rfl | rfl := (key a).mp ha
      -- ⊢ ↑f a = ↑(swap a y) a
      · rw [Or.resolve_left ha' ha, swap_apply_left]
        -- 🎉 no goals
      · rw [Or.resolve_right ha' ha, swap_apply_right]
        -- 🎉 no goals
  · obtain ⟨x, y, hxy, rfl⟩ := h
    -- ⊢ card (support (swap x y)) = 2
    exact card_support_swap hxy
    -- 🎉 no goals
#align equiv.perm.card_support_eq_two Equiv.Perm.card_support_eq_two

theorem Disjoint.card_support_mul (h : Disjoint f g) :
    (f * g).support.card = f.support.card + g.support.card := by
  rw [← Finset.card_disjoint_union]
  -- ⊢ card (support (f * g)) = card (support f ∪ support g)
  · congr
    -- ⊢ support (f * g) = support f ∪ support g
    ext
    -- ⊢ a✝ ∈ support (f * g) ↔ a✝ ∈ support f ∪ support g
    simp [h.support_mul]
    -- 🎉 no goals
  · simpa using h.disjoint_support
    -- 🎉 no goals
#align equiv.perm.disjoint.card_support_mul Equiv.Perm.Disjoint.card_support_mul

theorem card_support_prod_list_of_pairwise_disjoint {l : List (Perm α)} (h : l.Pairwise Disjoint) :
    l.prod.support.card = (l.map (Finset.card ∘ support)).sum := by
  induction' l with a t ih
  -- ⊢ card (support (List.prod [])) = List.sum (List.map (card ∘ support) [])
  · exact card_support_eq_zero.mpr rfl
    -- 🎉 no goals
  · obtain ⟨ha, ht⟩ := List.pairwise_cons.1 h
    -- ⊢ card (support (List.prod (a :: t))) = List.sum (List.map (card ∘ support) (a …
    rw [List.prod_cons, List.map_cons, List.sum_cons, ← ih ht]
    -- ⊢ card (support (a * List.prod t)) = (card ∘ support) a + card (support (List. …
    exact (disjoint_prod_right _ ha).card_support_mul
    -- 🎉 no goals
#align equiv.perm.card_support_prod_list_of_pairwise_disjoint Equiv.Perm.card_support_prod_list_of_pairwise_disjoint

end Card

end support

@[simp]
theorem support_subtype_perm [DecidableEq α] {s : Finset α} (f : Perm α) (h) :
    ((f.subtypePerm h : Perm { x // x ∈ s }).support) =
    (s.attach.filter ((fun x => decide (f x ≠ x))) : Finset { x // x ∈ s }) := by
  ext
  -- ⊢ a✝ ∈ support (subtypePerm f h) ↔ a✝ ∈ filter (fun x => decide (↑f ↑x ≠ ↑x) = …
  simp [Subtype.ext_iff]
  -- 🎉 no goals
#align equiv.perm.support_subtype_perm Equiv.Perm.support_subtype_perm

end Equiv.Perm
