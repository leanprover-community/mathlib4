/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yury Kudryashov, Sébastien Gouëzel, Chris Hughes
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Fin
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.PiLex

#align_import data.fin.tuple.basic from "leanprover-community/mathlib"@"ef997baa41b5c428be3fb50089a7139bf4ee886b"

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
  simp_rw [Pi.Lex, Fin.exists_fin_succ, Fin.cons_succ, Fin.cons_zero, Fin.forall_fin_succ]
  simp [and_assoc, exists_and_left]
#align fin.pi_lex_lt_cons_cons Fin.pi_lex_lt_cons_cons

variable [∀ i, Preorder (α i)]

lemma insertNth_mem_Icc {i : Fin (n + 1)} {x : α i} {p : ∀ j, α (i.succAbove j)}
    {q₁ q₂ : ∀ j, α j} :
    i.insertNth x p ∈ Icc q₁ q₂ ↔
      x ∈ Icc (q₁ i) (q₂ i) ∧ p ∈ Icc (fun j ↦ q₁ (i.succAbove j)) fun j ↦ q₂ (i.succAbove j) := by
  simp only [mem_Icc, insertNth_le_iff, le_insertNth_iff, and_assoc, @and_left_comm (x ≤ q₂ i)]
#align fin.insert_nth_mem_Icc Fin.insertNth_mem_Icc

lemma preimage_insertNth_Icc_of_mem {i : Fin (n + 1)} {x : α i} {q₁ q₂ : ∀ j, α j}
    (hx : x ∈ Icc (q₁ i) (q₂ i)) :
    i.insertNth x ⁻¹' Icc q₁ q₂ = Icc (fun j ↦ q₁ (i.succAbove j)) fun j ↦ q₂ (i.succAbove j) :=
  Set.ext fun p ↦ by simp only [mem_preimage, insertNth_mem_Icc, hx, true_and_iff]
#align fin.preimage_insert_nth_Icc_of_mem Fin.preimage_insertNth_Icc_of_mem

lemma preimage_insertNth_Icc_of_not_mem {i : Fin (n + 1)} {x : α i} {q₁ q₂ : ∀ j, α j}
    (hx : x ∉ Icc (q₁ i) (q₂ i)) : i.insertNth x ⁻¹' Icc q₁ q₂ = ∅ :=
  Set.ext fun p ↦ by
    simp only [mem_preimage, insertNth_mem_Icc, hx, false_and_iff, mem_empty_iff_false]
#align fin.preimage_insert_nth_Icc_of_not_mem Fin.preimage_insertNth_Icc_of_not_mem

end Fin

open Set Fin Matrix Function

variable {α : Type*}

lemma liftFun_vecCons {n : ℕ} (r : α → α → Prop) [IsTrans α r] {f : Fin (n + 1) → α} {a : α} :
    ((· < ·) ⇒ r) (vecCons a f) (vecCons a f) ↔ r a (f 0) ∧ ((· < ·) ⇒ r) f f := by
  simp only [liftFun_iff_succ r, forall_fin_succ, cons_val_succ, cons_val_zero, ← succ_castSucc,
    castSucc_zero]
#align lift_fun_vec_cons liftFun_vecCons

variable [Preorder α] {n : ℕ} {f : Fin (n + 1) → α} {a : α}

@[simp] lemma strictMono_vecCons : StrictMono (vecCons a f) ↔ a < f 0 ∧ StrictMono f :=
  liftFun_vecCons (· < ·)
#align strict_mono_vec_cons strictMono_vecCons

@[simp]
lemma monotone_vecCons : Monotone (vecCons a f) ↔ a ≤ f 0 ∧ Monotone f := by
  simpa only [monotone_iff_forall_lt] using @liftFun_vecCons α n (· ≤ ·) _ f a
#align monotone_vec_cons monotone_vecCons

@[simp] lemma monotone_vecEmpty : Monotone ![a]
  | ⟨0, _⟩, ⟨0, _⟩, _ => le_refl _

@[simp] lemma strictMono_vecEmpty : StrictMono ![a]
  | ⟨0, _⟩, ⟨0, _⟩, h => (irrefl _ h).elim

@[simp] lemma strictAnti_vecCons : StrictAnti (vecCons a f) ↔ f 0 < a ∧ StrictAnti f :=
  liftFun_vecCons (· > ·)
#align strict_anti_vec_cons strictAnti_vecCons

@[simp] lemma antitone_vecCons : Antitone (vecCons a f) ↔ f 0 ≤ a ∧ Antitone f :=
  monotone_vecCons (α := αᵒᵈ)
#align antitone_vec_cons antitone_vecCons

@[simp] lemma antitone_vecEmpty : Antitone (vecCons a vecEmpty)
  | ⟨0, _⟩, ⟨0, _⟩, _ => le_rfl

@[simp] lemma strictAnti_vecEmpty : StrictAnti (vecCons a vecEmpty)
  | ⟨0, _⟩, ⟨0, _⟩, h => (irrefl _ h).elim

lemma StrictMono.vecCons (hf : StrictMono f) (ha : a < f 0) : StrictMono (vecCons a f) :=
  strictMono_vecCons.2 ⟨ha, hf⟩
#align strict_mono.vec_cons StrictMono.vecCons

lemma StrictAnti.vecCons (hf : StrictAnti f) (ha : f 0 < a) : StrictAnti (vecCons a f) :=
  strictAnti_vecCons.2 ⟨ha, hf⟩
#align strict_anti.vec_cons StrictAnti.vecCons

lemma Monotone.vecCons (hf : Monotone f) (ha : a ≤ f 0) : Monotone (vecCons a f) :=
  monotone_vecCons.2 ⟨ha, hf⟩
#align monotone.vec_cons Monotone.vecCons

lemma Antitone.vecCons (hf : Antitone f) (ha : f 0 ≤ a) : Antitone (vecCons a f) :=
  antitone_vecCons.2 ⟨ha, hf⟩
#align antitone.vec_cons Antitone.vecCons

example : Monotone ![1, 2, 2, 3] := by decide


variable {n : ℕ}

/-- `Π i : Fin 2, α i` is order equivalent to `α 0 × α 1`. See also `OrderIso.finTwoArrowEquiv`
for a non-dependent version. -/
def OrderIso.piFinTwoIso (α : Fin 2 → Type*) [∀ i, Preorder (α i)] : (∀ i, α i) ≃o α 0 × α 1 where
  toEquiv := piFinTwoEquiv α
  map_rel_iff' := Iff.symm Fin.forall_fin_two
#align order_iso.pi_fin_two_iso OrderIso.piFinTwoIso

/-- The space of functions `Fin 2 → α` is order equivalent to `α × α`. See also
`OrderIso.piFinTwoIso`. -/
def OrderIso.finTwoArrowIso (α : Type*) [Preorder α] : (Fin 2 → α) ≃o α × α :=
  { OrderIso.piFinTwoIso fun _ => α with toEquiv := finTwoArrowEquiv α }
#align order_iso.fin_two_arrow_iso OrderIso.finTwoArrowIso

/-- Order isomorphism between `Π j : Fin (n + 1), α j` and
`α i × Π j : Fin n, α (Fin.succAbove i j)`. -/
def OrderIso.piFinSuccAboveIso (α : Fin (n + 1) → Type*) [∀ i, LE (α i)]
    (i : Fin (n + 1)) : (∀ j, α j) ≃o α i × ∀ j, α (i.succAbove j) where
  toEquiv := Equiv.piFinSuccAbove α i
  map_rel_iff' := Iff.symm i.forall_iff_succAbove
#align order_iso.pi_fin_succ_above_iso OrderIso.piFinSuccAboveIso

/-- `Fin.succAbove` as an order isomorphism between `Fin n` and `{x : Fin (n + 1) // x ≠ p}`. -/
def finSuccAboveOrderIso (p : Fin (n + 1)) : Fin n ≃o { x : Fin (n + 1) // x ≠ p } where
  __ := finSuccAboveEquiv p
  map_rel_iff' := p.succAboveOrderEmb.map_rel_iff'
#align fin_succ_above_equiv finSuccAboveOrderIso

lemma finSuccAboveOrderIso_apply (p : Fin (n + 1)) (i : Fin n) :
    finSuccAboveOrderIso p i = ⟨p.succAbove i, p.succAbove_ne i⟩ := rfl
#align fin_succ_above_equiv_apply finSuccAboveOrderIso_apply

lemma finSuccAboveOrderIso_symm_apply_last (x : { x : Fin (n + 1) // x ≠ Fin.last n }) :
    (finSuccAboveOrderIso (Fin.last n)).symm x = Fin.castLT x.1 (Fin.val_lt_last x.2) := by
  rw [← Option.some_inj]
  simpa [finSuccAboveOrderIso, finSuccAboveEquiv, OrderIso.symm]
    using finSuccEquiv'_last_apply x.property
#align fin_succ_above_equiv_symm_apply_last finSuccAboveEquiv_symm_apply_last

lemma finSuccAboveOrderIso_symm_apply_ne_last {p : Fin (n + 1)} (h : p ≠ Fin.last n)
    (x : { x : Fin (n + 1) // x ≠ p }) :
    (finSuccAboveEquiv p).symm x = (p.castLT (Fin.val_lt_last h)).predAbove x := by
  rw [← Option.some_inj]
  simpa [finSuccAboveEquiv, OrderIso.symm] using finSuccEquiv'_ne_last_apply h x.property
#align fin_succ_above_equiv_symm_apply_ne_last finSuccAboveEquiv_symm_apply_ne_last

/-- Promote a `Fin n` into a larger `Fin m`, as a subtype where the underlying
values are retained. This is the `OrderIso` version of `Fin.castLE`. -/
@[simps apply symm_apply]
def Fin.castLEOrderIso {n m : ℕ} (h : n ≤ m) : Fin n ≃o { i : Fin m // (i : ℕ) < n } where
  toFun i := ⟨Fin.castLE h i, by simp⟩
  invFun i := ⟨i, i.prop⟩
  left_inv _ := by simp
  right_inv _ := by simp
  map_rel_iff' := by simp [(strictMono_castLE h).le_iff_le]
#align fin.cast_le_order_iso Fin.castLEOrderIso
#align fin.cast_le_order_iso_apply Fin.castLEOrderIso_apply
#align fin.cast_le_order_iso_symm_apply Fin.castLEOrderIso_symm_apply
