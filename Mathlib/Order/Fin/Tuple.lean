/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yury Kudryashov, Sébastien Gouëzel, Chris Hughes
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Order.PiLex
import Mathlib.Order.Interval.Set.Defs

/-!
# Order properties on tuples
-/

assert_not_exists Monoid

open Function Set

namespace Fin
variable {m n : ℕ} {α : Fin (n + 1) → Type*} (x : α 0) (q : ∀ i, α i) (p : ∀ i : Fin n, α i.succ)
  (i : Fin n) (y : α i.succ) (z : α 0)

lemma pi_lex_lt_cons_cons {x₀ y₀ : α 0} {x y : ∀ i : Fin n, α i.succ}
    (s : ∀ {i : Fin n.succ}, α i → α i → Prop) :
    Pi.Lex (· < ·) (@s) (Fin.cons x₀ x) (Fin.cons y₀ y) ↔
      s x₀ y₀ ∨ x₀ = y₀ ∧ Pi.Lex (· < ·) (@fun i : Fin n ↦ @s i.succ) x y := by
  simp_rw [Pi.Lex, Fin.exists_fin_succ, Fin.cons_succ, Fin.cons_zero, Fin.forall_iff_succ]
  simp [and_assoc, exists_and_left]

variable [∀ i, Preorder (α i)]

lemma insertNth_mem_Icc {i : Fin (n + 1)} {x : α i} {p : ∀ j, α (i.succAbove j)}
    {q₁ q₂ : ∀ j, α j} :
    i.insertNth x p ∈ Icc q₁ q₂ ↔
      x ∈ Icc (q₁ i) (q₂ i) ∧ p ∈ Icc (fun j ↦ q₁ (i.succAbove j)) fun j ↦ q₂ (i.succAbove j) := by
  simp only [mem_Icc, insertNth_le_iff, le_insertNth_iff, and_assoc, @and_left_comm (x ≤ q₂ i)]

lemma preimage_insertNth_Icc_of_mem {i : Fin (n + 1)} {x : α i} {q₁ q₂ : ∀ j, α j}
    (hx : x ∈ Icc (q₁ i) (q₂ i)) :
    i.insertNth x ⁻¹' Icc q₁ q₂ = Icc (fun j ↦ q₁ (i.succAbove j)) fun j ↦ q₂ (i.succAbove j) :=
  Set.ext fun p ↦ by simp only [mem_preimage, insertNth_mem_Icc, hx, true_and]

lemma preimage_insertNth_Icc_of_notMem {i : Fin (n + 1)} {x : α i} {q₁ q₂ : ∀ j, α j}
    (hx : x ∉ Icc (q₁ i) (q₂ i)) : i.insertNth x ⁻¹' Icc q₁ q₂ = ∅ :=
  Set.ext fun p ↦ by
    simp only [mem_preimage, insertNth_mem_Icc, hx, false_and, mem_empty_iff_false]

@[deprecated (since := "2025-05-23")]
alias preimage_insertNth_Icc_of_not_mem := preimage_insertNth_Icc_of_notMem

end Fin

open Fin Matrix

variable {α : Type*}

open scoped Relator in
lemma liftFun_vecCons {n : ℕ} (r : α → α → Prop) [IsTrans α r] {f : Fin (n + 1) → α} {a : α} :
    ((· < ·) ⇒ r) (vecCons a f) (vecCons a f) ↔ r a (f 0) ∧ ((· < ·) ⇒ r) f f := by
  simp only [liftFun_iff_succ r, forall_iff_succ, cons_val_succ, cons_val_zero, ← succ_castSucc,
    castSucc_zero]

variable [Preorder α] {n : ℕ} {f : Fin (n + 1) → α} {a : α}

@[simp] lemma strictMono_vecCons : StrictMono (vecCons a f) ↔ a < f 0 ∧ StrictMono f :=
  liftFun_vecCons (· < ·)

@[simp]
lemma monotone_vecCons : Monotone (vecCons a f) ↔ a ≤ f 0 ∧ Monotone f := by
  simpa only [monotone_iff_forall_lt] using @liftFun_vecCons α n (· ≤ ·) _ f a

@[simp] lemma monotone_vecEmpty : Monotone ![a]
  | ⟨0, _⟩, ⟨0, _⟩, _ => le_refl _

@[simp] lemma strictMono_vecEmpty : StrictMono ![a]
  | ⟨0, _⟩, ⟨0, _⟩, h => (irrefl _ h).elim

@[simp] lemma strictAnti_vecCons : StrictAnti (vecCons a f) ↔ f 0 < a ∧ StrictAnti f :=
  liftFun_vecCons (· > ·)

@[simp] lemma antitone_vecCons : Antitone (vecCons a f) ↔ f 0 ≤ a ∧ Antitone f :=
  monotone_vecCons (α := αᵒᵈ)

@[simp] lemma antitone_vecEmpty : Antitone (vecCons a vecEmpty)
  | ⟨0, _⟩, ⟨0, _⟩, _ => le_rfl

@[simp] lemma strictAnti_vecEmpty : StrictAnti (vecCons a vecEmpty)
  | ⟨0, _⟩, ⟨0, _⟩, h => (irrefl _ h).elim

lemma StrictMono.vecCons (hf : StrictMono f) (ha : a < f 0) : StrictMono (vecCons a f) :=
  strictMono_vecCons.2 ⟨ha, hf⟩

lemma StrictAnti.vecCons (hf : StrictAnti f) (ha : f 0 < a) : StrictAnti (vecCons a f) :=
  strictAnti_vecCons.2 ⟨ha, hf⟩

lemma Monotone.vecCons (hf : Monotone f) (ha : a ≤ f 0) : Monotone (vecCons a f) :=
  monotone_vecCons.2 ⟨ha, hf⟩

lemma Antitone.vecCons (hf : Antitone f) (ha : f 0 ≤ a) : Antitone (vecCons a f) :=
  antitone_vecCons.2 ⟨ha, hf⟩

example : Monotone ![1, 2, 2, 3] := by decide


variable {n : ℕ}

/-- `Π i : Fin 2, α i` is order equivalent to `α 0 × α 1`. See also `OrderIso.finTwoArrowEquiv`
for a non-dependent version. -/
def OrderIso.piFinTwoIso (α : Fin 2 → Type*) [∀ i, Preorder (α i)] : (∀ i, α i) ≃o α 0 × α 1 where
  toEquiv := piFinTwoEquiv α
  map_rel_iff' := Iff.symm Fin.forall_fin_two

/-- The space of functions `Fin 2 → α` is order equivalent to `α × α`. See also
`OrderIso.piFinTwoIso`. -/
def OrderIso.finTwoArrowIso (α : Type*) [Preorder α] : (Fin 2 → α) ≃o α × α :=
  { OrderIso.piFinTwoIso fun _ => α with toEquiv := finTwoArrowEquiv α }

namespace Fin

/-- Order isomorphism between tuples of length `n + 1` and pairs of an element and a tuple of length
`n` given by separating out the first element of the tuple.

This is `Fin.cons` as an `OrderIso`. -/
@[simps!, simps toEquiv]
def consOrderIso (α : Fin (n + 1) → Type*) [∀ i, LE (α i)] :
    α 0 × (∀ i, α (succ i)) ≃o ∀ i, α i where
  toEquiv := consEquiv α
  map_rel_iff' := forall_iff_succ

/-- Order isomorphism between tuples of length `n + 1` and pairs of an element and a tuple of length
`n` given by separating out the last element of the tuple.

This is `Fin.snoc` as an `OrderIso`. -/
@[simps!, simps toEquiv]
def snocOrderIso (α : Fin (n + 1) → Type*) [∀ i, LE (α i)] :
    α (last n) × (∀ i, α (castSucc i)) ≃o ∀ i, α i where
  toEquiv := snocEquiv α
  map_rel_iff' := by simp [Pi.le_def, Prod.le_def, forall_iff_castSucc]

/-- Order isomorphism between tuples of length `n + 1` and pairs of an element and a tuple of length
`n` given by separating out the `p`-th element of the tuple.

This is `Fin.insertNth` as an `OrderIso`. -/
@[simps!, simps toEquiv]
def insertNthOrderIso (α : Fin (n + 1) → Type*) [∀ i, LE (α i)] (p : Fin (n + 1)) :
    α p × (∀ i, α (p.succAbove i)) ≃o ∀ i, α i where
  toEquiv := insertNthEquiv α p
  map_rel_iff' := by simp [Pi.le_def, Prod.le_def, p.forall_iff_succAbove]

@[simp] lemma insertNthOrderIso_zero (α : Fin (n + 1) → Type*) [∀ i, LE (α i)] :
    insertNthOrderIso α 0 = consOrderIso α := by ext; simp [insertNthOrderIso]

/-- Note this lemma can only be written about non-dependent tuples as `insertNth (last n) = snoc` is
not a definitional equality. -/
@[simp] lemma insertNthOrderIso_last (n : ℕ) (α : Type*) [LE α] :
    insertNthOrderIso (fun _ ↦ α) (last n) = snocOrderIso (fun _ ↦ α) := by ext; simp

end Fin

/-- `Fin.succAbove` as an order isomorphism between `Fin n` and `{x : Fin (n + 1) // x ≠ p}`. -/
def finSuccAboveOrderIso (p : Fin (n + 1)) : Fin n ≃o { x : Fin (n + 1) // x ≠ p } where
  __ := finSuccAboveEquiv p
  map_rel_iff' := p.succAboveOrderEmb.map_rel_iff'

lemma finSuccAboveOrderIso_apply (p : Fin (n + 1)) (i : Fin n) :
    finSuccAboveOrderIso p i = ⟨p.succAbove i, p.succAbove_ne i⟩ := rfl

lemma finSuccAboveOrderIso_symm_apply_last (x : { x : Fin (n + 1) // x ≠ Fin.last n }) :
    (finSuccAboveOrderIso (Fin.last n)).symm x = Fin.castLT x.1 (Fin.val_lt_last x.2) := by
  rw [← Option.some_inj]
  simp [finSuccAboveOrderIso, finSuccAboveEquiv, OrderIso.symm]

lemma finSuccAboveOrderIso_symm_apply_ne_last {p : Fin (n + 1)} (h : p ≠ Fin.last n)
    (x : { x : Fin (n + 1) // x ≠ p }) :
    (finSuccAboveEquiv p).symm x = (p.castLT (Fin.val_lt_last h)).predAbove x := by
  rw [← Option.some_inj]
  simpa [finSuccAboveEquiv, OrderIso.symm] using finSuccEquiv'_ne_last_apply h x.property

/-- Promote a `Fin n` into a larger `Fin m`, as a subtype where the underlying
values are retained. This is the `OrderIso` version of `Fin.castLE`. -/
@[simps apply symm_apply]
def Fin.castLEOrderIso {n m : ℕ} (h : n ≤ m) : Fin n ≃o { i : Fin m // (i : ℕ) < n } where
  toFun i := ⟨Fin.castLE h i, by simp⟩
  invFun i := ⟨i, i.prop⟩
  left_inv _ := by simp
  right_inv _ := by simp
  map_rel_iff' := by simp [(strictMono_castLE h).le_iff_le]
