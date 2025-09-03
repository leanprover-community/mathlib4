/-
Copyright (c) 2025 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos Fernández, Xavier Généreux
-/
import Mathlib.Algebra.SkewMonoidAlgebra.Basic
/-!
# Modifying Skew Monoid Algebra at exactly one point

This file contains basic results on updating/erasing an element of a skew monoid algebras using
one point of the domain.
-/

noncomputable section

namespace SkewMonoidAlgebra

variable {k G H : Type*}

section erase

variable {M α : Type*} [AddCommMonoid M] (a a' : α) (b : M) (f : SkewMonoidAlgebra M α)

/--
Given an element `f` of a skew monoid algebra, `erase a f` is an element with the same coefficients
as `f` except at `a` where the coefficient is `0`.
If `a` is not in the support of `f` then `erase a f = f`. -/
def erase : SkewMonoidAlgebra M α :=
    ⟨ haveI := Classical.decEq α
      f.support.erase a,
      fun a' ↦ haveI := Classical.decEq α
        if a' = a then 0 else f.coeff a',
      by aesop⟩

@[simp]
theorem toFinsupp_erase : (f.erase a).toFinsupp = f.toFinsupp.erase a := rfl

@[simp]
theorem support_erase [DecidableEq α] : (f.erase a).support = f.support.erase a := by
  rcases f with ⟨⟩
  ext
  simp only [support, erase, Finset.mem_erase, Finsupp.mem_support_iff]

@[simp]
theorem erase_same : (f.erase a).coeff a = 0 := by
  simp [erase]

@[simp]
theorem erase_ne [DecidableEq α] (h : a' ≠ a) : (f.erase a).coeff a' = f.coeff a' := by
  rcases f with ⟨⟩
  simp [erase, h]

@[simp]
theorem erase_single [DecidableEq α] : erase a (single a b) = 0 := by
  aesop (add norm [erase, coeff_single])

@[simp]
theorem coeff_erase [DecidableEq α] : (f.erase a).coeff a' = if a' = a then 0 else f.coeff a' :=
  ite_congr rfl (fun _ ↦ rfl) (fun _ ↦ rfl)

@[simp]
theorem erase_zero [DecidableEq α] {a : α} :
    erase a (0 : SkewMonoidAlgebra M α) = 0 := by
  classical rw [← support_eq_empty, support_erase, support_zero, Finset.erase_empty]

theorem single_add_erase (a : α) (f : SkewMonoidAlgebra M α) :
    single a (f.coeff a) + f.erase a = f := by
  apply toFinsupp_injective
  simp only [single, ← toFinsupp_apply, toFinsupp_add, toFinsupp_erase]
  rw [Finsupp.single_add_erase]

@[elab_as_elim]
theorem induction {p : SkewMonoidAlgebra M α → Prop} (f : SkewMonoidAlgebra M α) (h0 : p 0)
    (ha : ∀ (a b) (f : SkewMonoidAlgebra M α), a ∉ f.support → b ≠ 0 → p f → p (single a b + f)) :
    p f :=
  suffices ∀ (s) (f : SkewMonoidAlgebra M α), f.support = s → p f from this _ _ rfl
  fun s ↦
  Finset.cons_induction_on s (fun f hf ↦ by rwa [support_eq_empty.1 hf]) fun a s has ih f hf ↦ by
    suffices p (single a (f.coeff a) + f.erase a) by rwa [single_add_erase] at this
    classical
    apply ha
    · rw [support_erase, Finset.mem_erase]
      exact fun H ↦ H.1 rfl
    · simp only [← mem_support_iff, hf, Finset.mem_cons_self]
    · apply ih
      rw [support_erase, hf, Finset.erase_cons]

end erase

section update

variable {M α : Type*} [AddCommMonoid M] (f : SkewMonoidAlgebra M α) (a a' : α) (b : M)

/-- Replace the coefficent of an element `f` of a skew monoid algebra at a given point `a : α` by
a given value `b : M`.
If `b = 0`, this amounts to removing `a` from the support of `f`.
Otherwise, if `a` was not in the `support` of `f`, it is added to it. -/
def update : SkewMonoidAlgebra M α :=
  ⟨ haveI := Classical.decEq α; haveI := Classical.decEq M
    if b = 0 then f.support.erase a else insert a f.support,
    haveI := Classical.decEq α
    Function.update f.toFinsupp a b,
    by aesop (add norm [Function.update, Finset.mem_erase])⟩

@[simp]
theorem toFinsupp_update : (f.update a b).toFinsupp = f.toFinsupp.update a b := rfl

@[simp]
theorem update_self : f.update a (f.coeff a) = f := by
  rcases f with ⟨f⟩
  apply toFinsupp_injective
  simp

@[simp]
theorem zero_update : update 0 a b = single a b := by
  apply toFinsupp_injective
  simp

theorem support_update [DecidableEq α] [DecidableEq M] :
    support (f.update a b) = if b = 0 then f.support.erase a else insert a f.support := by
  aesop (add norm update)

theorem coeff_update [DecidableEq α] : (f.update a b).coeff = Function.update f.coeff a b := by
  simp only [coeff, update, Finsupp.coe_mk]
  congr!

theorem coeff_update_apply [DecidableEq α] :
    (f.update a b).coeff a' = if a' = a then b else f.coeff a' := by
  rw [coeff_update, Function.update_apply]

@[simp]
theorem coeff_update_same [DecidableEq α] : (f.update a b).coeff a = b := by
  rw [f.coeff_update_apply, if_pos rfl]

theorem coeff_update_ne [DecidableEq α] (h : a' ≠ a) : (f.update a b).coeff a' = f.coeff a' := by
  rw [f.coeff_update_apply, if_neg h]

@[simp]
theorem update_zero_eq_erase [DecidableEq α] : f.update a 0 = f.erase a := by
  ext
  simp [coeff_update_apply, coeff_erase]

end update

end SkewMonoidAlgebra
