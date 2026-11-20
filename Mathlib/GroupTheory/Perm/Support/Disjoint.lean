/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Aaron Anderson, Yakov Pechersky
-/
module

public import Mathlib.GroupTheory.Perm.Support.Basic

import Mathlib.Data.Set.Image

/-!
# Disjoint permutations

## Main definitions

In the following, `f g : Equiv.Perm α`.

* `Equiv.Perm.Disjoint`: two permutations `f` and `g` are `Disjoint` if every element is fixed
  either by `f`, or by `g`: equivalently, their supports are disjoint.
-/

public section

namespace Equiv.Perm

variable {α : Type*}

section Disjoint

/-- Two permutations `f` and `g` are `Disjoint` if their supports are disjoint, i.e.,
every element is fixed either by `f`, or by `g`. -/
@[irreducible] protected def Disjoint (f g : Perm α) := Disjoint f.support g.support

variable {f g h : Perm α}

unseal Perm.Disjoint in @[grind =]
theorem disjoint_iff_disjoint_support : f.Disjoint g ↔ Disjoint f.support g.support := Iff.rfl

theorem _root_.Disjoint.disjoint_perm (h : Disjoint f.support g.support) : f.Disjoint g :=
  disjoint_iff_disjoint_support.mpr h

theorem Disjoint.disjoint_support (h : f.Disjoint g) : Disjoint f.support g.support :=
  disjoint_iff_disjoint_support.mp h

theorem Disjoint.mono {x y : Perm α} (hf : x.support ≤ f.support) (hg : y.support ≤ g.support)
    (h : f.Disjoint g) : x.Disjoint y := (h.disjoint_support.mono hf hg).disjoint_perm

theorem disjoint_iff_forall_apply_eq_or_apply_eq : f.Disjoint g ↔ ∀ x : α, f x = x ∨ g x = x := by
  simp only [disjoint_iff_disjoint_support, Set.disjoint_iff_inter_eq_empty, Set.ext_iff,
    Set.mem_inter_iff, mem_support, Set.mem_empty_iff_false, iff_false, not_and_or, not_not]

theorem Disjoint.apply_eq_or_apply_eq (h : f.Disjoint g) (x : α) : f x = x ∨ g x = x :=
  disjoint_iff_forall_apply_eq_or_apply_eq.mp h x

@[deprecated (since := "2026-11-17")] alias disjoint_iff_eq_or_eq :=
  disjoint_iff_forall_apply_eq_or_apply_eq

@[symm] theorem Disjoint.symm (h : f.Disjoint g) : g.Disjoint f :=
  h.disjoint_support.symm.disjoint_perm

instance Disjoint.stdSymm : Std.Symm (α := Perm α) Perm.Disjoint where
  symm _ _ := Disjoint.symm

@[deprecated (since := "2026-06-10")] alias Disjoint.symmetric := Disjoint.stdSymm

theorem disjoint_comm : f.Disjoint g ↔ g.Disjoint f := ⟨Disjoint.symm, Disjoint.symm⟩

theorem Disjoint.mem_left_imp (h : f.Disjoint g) {x : α}
    (hx : x ∈ f.support) : x ∉ g.support :=
  Set.disjoint_left.mp h.disjoint_support hx

@[deprecated (since := "2026-11-17")] alias Disjoint.mem_imp := Disjoint.mem_left_imp

theorem Disjoint.mem_right_imp (h : f.Disjoint g) {x : α}
    (hx : x ∈ g.support) : x ∉ f.support :=
  Set.disjoint_right.mp h.disjoint_support hx

theorem Disjoint.of_apply_left_ne (hfg : f.Disjoint g) {x} (h : f x ≠ x) : g x = x :=
  notMem_support.mp (hfg.mem_left_imp (mem_support.mpr h))

theorem Disjoint.of_apply_right_ne (hfg : f.Disjoint g) {x} (h : g x ≠ x) : f x = x :=
  notMem_support.mp (hfg.mem_right_imp (mem_support.mpr h))

theorem Disjoint.commute (h : f.Disjoint g) : Commute f g := Equiv.ext fun x => by
  rcases h.apply_eq_or_apply_eq x with hf | hg
  · rcases h.apply_eq_or_apply_eq (g x) <;> simp_all [mul_apply]
  · rcases h.apply_eq_or_apply_eq (f x) <;> simp_all [mul_apply]

@[simp]
theorem disjoint_one_left (f : Perm α) : (1 : Perm α).Disjoint f := by
  simp [disjoint_iff_disjoint_support]

@[simp]
theorem disjoint_one_right (f : Perm α) : f.Disjoint 1 := by
  simp [disjoint_iff_disjoint_support]

@[simp]
theorem disjoint_refl_iff : f.Disjoint f ↔ f = 1 := by
  simp [disjoint_iff_disjoint_support]

theorem Disjoint.eq_one : f.Disjoint f → f = 1 := by simp

theorem Disjoint.inv_left : f.Disjoint g → f⁻¹.Disjoint g := by
  simp [disjoint_iff_disjoint_support]

theorem Disjoint.inv_right (h : f.Disjoint g) : f.Disjoint g⁻¹ :=
  h.symm.inv_left.symm

@[simp] theorem disjoint_inv_left_iff : f⁻¹.Disjoint g ↔ f.Disjoint g := by
  simp [disjoint_iff_disjoint_support]

@[simp] theorem disjoint_inv_right_iff : f.Disjoint g⁻¹ ↔ f.Disjoint g := by
  simp [disjoint_iff_disjoint_support]

theorem Disjoint.mul_left (H1 : f.Disjoint h) (H2 : g.Disjoint h) : (f * g).Disjoint h :=
  ((H1.disjoint_support.union_left H2.disjoint_support).mono_left
    (support_mul_subset f g)).disjoint_perm

theorem Disjoint.mul_right (H1 : f.Disjoint g) (H2 : f.Disjoint h) : f.Disjoint (g * h) := by
  rw [disjoint_comm]
  exact H1.symm.mul_left H2.symm

theorem Disjoint.support_mul (h : f.Disjoint g) :
    (f * g).support = f.support ∪ g.support := by
  refine le_antisymm (support_mul_subset _ _) fun a => ?_
  rw [Set.mem_union, mem_support, mem_support, mem_support, mul_apply, ← not_and_or,
    not_imp_not]
  exact (h.apply_eq_or_apply_eq a).elim
    (fun hf h => ⟨hf, f.apply_eq_iff_eq.mp (h.trans hf.symm)⟩)
    fun hg h => ⟨congr(f $hg).symm.trans h, hg⟩

@[simp]
theorem disjoint_conj (h : Perm α) : (h * f * h⁻¹).Disjoint (h * g * h⁻¹) ↔ f.Disjoint g := by
  simp [disjoint_iff_disjoint_support, Set.disjoint_image_iff h.injective]

theorem Disjoint.conj (H : f.Disjoint g) (h : Perm α) : (h * f * h⁻¹).Disjoint (h * g * h⁻¹) :=
  (disjoint_conj h).2 H

theorem disjoint_prod_right (l : List (Perm α)) (h : ∀ g ∈ l, f.Disjoint g) :
    f.Disjoint l.prod := by
  induction l with | nil => exact disjoint_one_right _ | cons g l ih =>
    rw [List.prod_cons]
    exact (h _ List.mem_cons_self).mul_right (ih fun g hg => h g (List.mem_cons_of_mem _ hg))

open scoped List in
theorem disjoint_prod_perm {l₁ l₂ : List (Perm α)} (hl : l₁.Pairwise Perm.Disjoint)
    (hp : l₁ ~ l₂) : l₁.prod = l₂.prod := by induction hp with
  | nil => rfl
  | cons => grind
  | swap x y => simp [← mul_assoc, (List.rel_of_pairwise_cons hl List.mem_cons_self).commute.eq]
  | trans h₁ _ ih₁ ih₂ => exact (ih₁ hl).trans (ih₂ (hl.perm h₁ Disjoint.symm))

theorem nodup_of_pairwise_disjoint {l : List (Perm α)} (h1 : (1 : Perm α) ∉ l)
    (h2 : l.Pairwise Perm.Disjoint) : l.Nodup :=
  h2.imp_of_mem fun _ hb hab ↦ mt (fun h => (h ▸ hab).eq_one ▸ hb) h1

theorem Disjoint.apply_apply_eq_iff (hfg : f.Disjoint g) {a : α} :
    f (g a) = a ↔ f a = a ∧ g a = a :=
  ⟨by rcases hfg.apply_eq_or_apply_eq a <;> grind [f.injective], by grind⟩

theorem Disjoint.mul_apply_eq_iff (hfg : f.Disjoint g) {a : α} :
    (f * g) a = a ↔ f a = a ∧ g a = a := hfg.apply_apply_eq_iff

theorem Disjoint.mul_eq_one_iff {σ τ : Perm α} (hστ : σ.Disjoint τ) :
    σ * τ = 1 ↔ σ = 1 ∧ τ = 1 := by
  simp_rw [Perm.ext_iff, one_apply, mul_apply, hστ.apply_apply_eq_iff, forall_and]

theorem Disjoint.zpow_disjoint_zpow {σ τ : Perm α} (hστ : σ.Disjoint τ) (m n : ℤ) :
    (σ ^ m).Disjoint (τ ^ n) := hστ.mono (support_zpow_subset m) (support_zpow_subset n)

theorem Disjoint.pow_disjoint_pow {σ τ : Perm α} (hστ : σ.Disjoint τ) (m n : ℕ) :
    (σ ^ m).Disjoint (τ ^ n) :=
  hστ.zpow_disjoint_zpow m n

theorem disjoint_swap_swap [DecidableEq α] {x y z t : α} (h : [x, y, z, t].Nodup) :
    (swap x y).Disjoint (swap z t) := by grind

end Disjoint

section Support

variable {f : Perm α}

theorem support_prod_of_pairwise_disjoint (l : List (Perm α)) (h : l.Pairwise Perm.Disjoint) :
    l.prod.support = (l.map support).foldr (· ∪ ·) ⊥ := by
  induction h with | nil => simp | cons ha => simp_all [(disjoint_prod_right _ ha).support_mul]

theorem eq_on_support_mem_disjoint {l : List (Perm α)} (h : f ∈ l)
    (hl : l.Pairwise Perm.Disjoint) :
    ∀ x ∈ f.support, f x = l.prod x := by
  induction hl with
  | nil => simp at h
  | cons ha hx IH =>
    intros x hx
    rcases List.eq_or_mem_of_mem_cons h with (rfl | h)
    · rw [List.prod_cons, mul_apply,
        (disjoint_prod_right _ ha).of_apply_left_ne (mem_support.mp hx)]
    · rw [List.prod_cons, mul_apply, ← IH h _ hx, eq_comm, ← notMem_support]
      refine (ha _ h).symm.mem_left_imp ?_
      simpa using hx

theorem support_subset_prod_of_mem {l : List (Perm α)} (h : f ∈ l)
    (hl : l.Pairwise Perm.Disjoint) :
    f.support ⊆ l.prod.support := fun x hx => by
  rwa [mem_support, ← eq_on_support_mem_disjoint h hl _ hx, ← mem_support]

end Support

end Equiv.Perm
