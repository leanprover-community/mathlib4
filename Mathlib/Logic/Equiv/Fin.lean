/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

! This file was ported from Lean 3 source module logic.equiv.fin
! leanprover-community/mathlib commit 2445c98ae4b87eabebdde552593519b9b6dc350c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fin.VecNotation
import Mathbin.Logic.Equiv.Defs

/-!
# Equivalences for `fin n`
-/


universe u

variable {m n : ℕ}

/-- Equivalence between `fin 0` and `empty`. -/
def finZeroEquiv : Fin 0 ≃ Empty :=
  Equiv.equivEmpty _
#align fin_zero_equiv finZeroEquiv

/-- Equivalence between `fin 0` and `pempty`. -/
def finZeroEquiv' : Fin 0 ≃ PEmpty.{u} :=
  Equiv.equivPEmpty _
#align fin_zero_equiv' finZeroEquiv'

/-- Equivalence between `fin 1` and `unit`. -/
def finOneEquiv : Fin 1 ≃ Unit :=
  Equiv.equivPUnit _
#align fin_one_equiv finOneEquiv

/-- Equivalence between `fin 2` and `bool`. -/
def finTwoEquiv : Fin 2 ≃ Bool where
  toFun := ![false, true]
  invFun b := cond b 1 0
  left_inv := Fin.forall_fin_two.2 <| by simp
  right_inv := Bool.forall_bool.2 <| by simp
#align fin_two_equiv finTwoEquiv

/-- `Π i : fin 2, α i` is equivalent to `α 0 × α 1`. See also `fin_two_arrow_equiv` for a
non-dependent version and `prod_equiv_pi_fin_two` for a version with inputs `α β : Type u`. -/
@[simps (config := { fullyApplied := false })]
def piFinTwoEquiv (α : Fin 2 → Type u) : (∀ i, α i) ≃ α 0 × α 1
    where
  toFun f := (f 0, f 1)
  invFun p := Fin.cons p.1 <| Fin.cons p.2 finZeroElim
  left_inv f := funext <| Fin.forall_fin_two.2 ⟨rfl, rfl⟩
  right_inv := fun ⟨x, y⟩ => rfl
#align pi_fin_two_equiv piFinTwoEquiv

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Fin.preimage_apply_01_prod {α : Fin 2 → Type u} (s : Set (α 0)) (t : Set (α 1)) :
    (fun f : ∀ i, α i => (f 0, f 1)) ⁻¹' s ×ˢ t =
      Set.pi Set.univ (Fin.cons s <| Fin.cons t Fin.elim0) :=
  by
  ext f
  have : (Fin.cons s (Fin.cons t Fin.elim0) : ∀ i, Set (α i)) 1 = t := rfl
  simp [Fin.forall_fin_two, this]
#align fin.preimage_apply_01_prod Fin.preimage_apply_01_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Fin.preimage_apply_01_prod' {α : Type u} (s t : Set α) :
    (fun f : Fin 2 → α => (f 0, f 1)) ⁻¹' s ×ˢ t = Set.pi Set.univ ![s, t] :=
  Fin.preimage_apply_01_prod s t
#align fin.preimage_apply_01_prod' Fin.preimage_apply_01_prod'

/-- A product space `α × β` is equivalent to the space `Π i : fin 2, γ i`, where
`γ = fin.cons α (fin.cons β fin_zero_elim)`. See also `pi_fin_two_equiv` and
`fin_two_arrow_equiv`. -/
@[simps (config := { fullyApplied := false })]
def prodEquivPiFinTwo (α β : Type u) : α × β ≃ ∀ i : Fin 2, ![α, β] i :=
  (piFinTwoEquiv (Fin.cons α (Fin.cons β finZeroElim))).symm
#align prod_equiv_pi_fin_two prodEquivPiFinTwo

/-- The space of functions `fin 2 → α` is equivalent to `α × α`. See also `pi_fin_two_equiv` and
`prod_equiv_pi_fin_two`. -/
@[simps (config := { fullyApplied := false })]
def finTwoArrowEquiv (α : Type _) : (Fin 2 → α) ≃ α × α :=
  { piFinTwoEquiv fun _ => α with invFun := fun x => ![x.1, x.2] }
#align fin_two_arrow_equiv finTwoArrowEquiv

/-- `Π i : fin 2, α i` is order equivalent to `α 0 × α 1`. See also `order_iso.fin_two_arrow_equiv`
for a non-dependent version. -/
def OrderIso.piFinTwoIso (α : Fin 2 → Type u) [∀ i, Preorder (α i)] : (∀ i, α i) ≃o α 0 × α 1
    where
  toEquiv := piFinTwoEquiv α
  map_rel_iff' f g := Iff.symm Fin.forall_fin_two
#align order_iso.pi_fin_two_iso OrderIso.piFinTwoIso

/-- The space of functions `fin 2 → α` is order equivalent to `α × α`. See also
`order_iso.pi_fin_two_iso`. -/
def OrderIso.finTwoArrowIso (α : Type _) [Preorder α] : (Fin 2 → α) ≃o α × α :=
  { OrderIso.piFinTwoIso fun _ => α with toEquiv := finTwoArrowEquiv α }
#align order_iso.fin_two_arrow_iso OrderIso.finTwoArrowIso

/-- The 'identity' equivalence between `fin n` and `fin m` when `n = m`. -/
def finCongr {n m : ℕ} (h : n = m) : Fin n ≃ Fin m :=
  (Fin.cast h).toEquiv
#align fin_congr finCongr

@[simp]
theorem finCongr_apply_mk {n m : ℕ} (h : n = m) (k : ℕ) (w : k < n) :
    finCongr h ⟨k, w⟩ =
      ⟨k, by
        subst h
        exact w⟩ :=
  rfl
#align fin_congr_apply_mk finCongr_apply_mk

@[simp]
theorem finCongr_symm {n m : ℕ} (h : n = m) : (finCongr h).symm = finCongr h.symm :=
  rfl
#align fin_congr_symm finCongr_symm

@[simp]
theorem finCongr_apply_coe {n m : ℕ} (h : n = m) (k : Fin n) : (finCongr h k : ℕ) = k :=
  by
  cases k
  rfl
#align fin_congr_apply_coe finCongr_apply_coe

theorem finCongr_symm_apply_coe {n m : ℕ} (h : n = m) (k : Fin m) : ((finCongr h).symm k : ℕ) = k :=
  by
  cases k
  rfl
#align fin_congr_symm_apply_coe finCongr_symm_apply_coe

/-- An equivalence that removes `i` and maps it to `none`.
This is a version of `fin.pred_above` that produces `option (fin n)` instead of
mapping both `i.cast_succ` and `i.succ` to `i`. -/
def finSuccEquiv' {n : ℕ} (i : Fin (n + 1)) : Fin (n + 1) ≃ Option (Fin n)
    where
  toFun := i.insertNth none some
  invFun x := x.casesOn' i (Fin.succAbove i)
  left_inv x := Fin.succAboveCases i (by simp) (fun j => by simp) x
  right_inv x := by cases x <;> dsimp <;> simp
#align fin_succ_equiv' finSuccEquiv'

@[simp]
theorem finSuccEquiv'_at {n : ℕ} (i : Fin (n + 1)) : (finSuccEquiv' i) i = none := by
  simp [finSuccEquiv']
#align fin_succ_equiv'_at finSuccEquiv'_at

@[simp]
theorem finSuccEquiv'_succAbove {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    finSuccEquiv' i (i.succAbove j) = some j :=
  @Fin.insertNth_apply_succAbove n (fun _ => Option (Fin n)) i _ _ _
#align fin_succ_equiv'_succ_above finSuccEquiv'_succAbove

theorem finSuccEquiv'_below {n : ℕ} {i : Fin (n + 1)} {m : Fin n} (h : m.cast_succ < i) :
    (finSuccEquiv' i) m.cast_succ = some m := by
  rw [← Fin.succAbove_below _ _ h, finSuccEquiv'_succAbove]
#align fin_succ_equiv'_below finSuccEquiv'_below

theorem finSuccEquiv'_above {n : ℕ} {i : Fin (n + 1)} {m : Fin n} (h : i ≤ m.cast_succ) :
    (finSuccEquiv' i) m.succ = some m := by
  rw [← Fin.succAbove_above _ _ h, finSuccEquiv'_succAbove]
#align fin_succ_equiv'_above finSuccEquiv'_above

@[simp]
theorem finSuccEquiv'_symm_none {n : ℕ} (i : Fin (n + 1)) : (finSuccEquiv' i).symm none = i :=
  rfl
#align fin_succ_equiv'_symm_none finSuccEquiv'_symm_none

@[simp]
theorem finSuccEquiv'_symm_some {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    (finSuccEquiv' i).symm (some j) = i.succAbove j :=
  rfl
#align fin_succ_equiv'_symm_some finSuccEquiv'_symm_some

theorem finSuccEquiv'_symm_some_below {n : ℕ} {i : Fin (n + 1)} {m : Fin n} (h : m.cast_succ < i) :
    (finSuccEquiv' i).symm (some m) = m.cast_succ :=
  Fin.succAbove_below i m h
#align fin_succ_equiv'_symm_some_below finSuccEquiv'_symm_some_below

theorem finSuccEquiv'_symm_some_above {n : ℕ} {i : Fin (n + 1)} {m : Fin n} (h : i ≤ m.cast_succ) :
    (finSuccEquiv' i).symm (some m) = m.succ :=
  Fin.succAbove_above i m h
#align fin_succ_equiv'_symm_some_above finSuccEquiv'_symm_some_above

theorem finSuccEquiv'_symm_coe_below {n : ℕ} {i : Fin (n + 1)} {m : Fin n} (h : m.cast_succ < i) :
    (finSuccEquiv' i).symm m = m.cast_succ :=
  finSuccEquiv'_symm_some_below h
#align fin_succ_equiv'_symm_coe_below finSuccEquiv'_symm_coe_below

theorem finSuccEquiv'_symm_coe_above {n : ℕ} {i : Fin (n + 1)} {m : Fin n} (h : i ≤ m.cast_succ) :
    (finSuccEquiv' i).symm m = m.succ :=
  finSuccEquiv'_symm_some_above h
#align fin_succ_equiv'_symm_coe_above finSuccEquiv'_symm_coe_above

/-- Equivalence between `fin (n + 1)` and `option (fin n)`.
This is a version of `fin.pred` that produces `option (fin n)` instead of
requiring a proof that the input is not `0`. -/
def finSuccEquiv (n : ℕ) : Fin (n + 1) ≃ Option (Fin n) :=
  finSuccEquiv' 0
#align fin_succ_equiv finSuccEquiv

@[simp]
theorem finSuccEquiv_zero {n : ℕ} : (finSuccEquiv n) 0 = none :=
  rfl
#align fin_succ_equiv_zero finSuccEquiv_zero

@[simp]
theorem finSuccEquiv_succ {n : ℕ} (m : Fin n) : (finSuccEquiv n) m.succ = some m :=
  finSuccEquiv'_above (Fin.zero_le _)
#align fin_succ_equiv_succ finSuccEquiv_succ

@[simp]
theorem finSuccEquiv_symm_none {n : ℕ} : (finSuccEquiv n).symm none = 0 :=
  finSuccEquiv'_symm_none _
#align fin_succ_equiv_symm_none finSuccEquiv_symm_none

@[simp]
theorem finSuccEquiv_symm_some {n : ℕ} (m : Fin n) : (finSuccEquiv n).symm (some m) = m.succ :=
  congr_fun Fin.succAbove_zero m
#align fin_succ_equiv_symm_some finSuccEquiv_symm_some

@[simp]
theorem finSuccEquiv_symm_coe {n : ℕ} (m : Fin n) : (finSuccEquiv n).symm m = m.succ :=
  finSuccEquiv_symm_some m
#align fin_succ_equiv_symm_coe finSuccEquiv_symm_coe

/-- The equiv version of `fin.pred_above_zero`. -/
theorem finSuccEquiv'_zero {n : ℕ} : finSuccEquiv' (0 : Fin (n + 1)) = finSuccEquiv n :=
  rfl
#align fin_succ_equiv'_zero finSuccEquiv'_zero

theorem finSuccEquiv'_last_apply {n : ℕ} {i : Fin (n + 1)} (h : i ≠ Fin.last n) :
    finSuccEquiv' (Fin.last n) i =
      Fin.castLt i (lt_of_le_of_ne (Fin.le_last _) (Fin.val_injective.ne_iff.2 h) : ↑i < n) :=
  by
  have h' : ↑i < n := lt_of_le_of_ne (Fin.le_last _) (fin.coe_injective.ne_iff.2 h)
  conv_lhs => rw [← Fin.castSucc_cast_lt i h']
  convert finSuccEquiv'_below _
  rw [Fin.castSucc_cast_lt i h']
  exact h'
#align fin_succ_equiv'_last_apply finSuccEquiv'_last_apply

theorem finSuccEquiv'_ne_last_apply {i j : Fin (n + 1)} (hi : i ≠ Fin.last n) (hj : j ≠ i) :
    finSuccEquiv' i j =
      (i.castLt (lt_of_le_of_ne (Fin.le_last _) (Fin.val_injective.ne_iff.2 hi) : ↑i < n)).predAbove
        j :=
  by
  rw [Fin.predAbove]
  have hi' : ↑i < n := lt_of_le_of_ne (Fin.le_last _) (fin.coe_injective.ne_iff.2 hi)
  rcases hj.lt_or_lt with (hij | hij)
  · simp only [hij.not_lt, Fin.castSucc_cast_lt, not_false_iff, dif_neg]
    convert finSuccEquiv'_below _
    · simp
    · exact hij
  · simp only [hij, Fin.castSucc_cast_lt, dif_pos]
    convert finSuccEquiv'_above _
    · simp
    · simp [Fin.le_castSucc_iff, hij]
#align fin_succ_equiv'_ne_last_apply finSuccEquiv'_ne_last_apply

/-- `succ_above` as an order isomorphism between `fin n` and `{x : fin (n + 1) // x ≠ p}`. -/
def finSuccAboveEquiv (p : Fin (n + 1)) : Fin n ≃o { x : Fin (n + 1) // x ≠ p } :=
  { Equiv.optionSubtype p ⟨(finSuccEquiv' p).symm, rfl⟩ with
    map_rel_iff' := fun _ _ => p.succAbove.map_rel_iff' }
#align fin_succ_above_equiv finSuccAboveEquiv

theorem finSuccAboveEquiv_apply (p : Fin (n + 1)) (i : Fin n) :
    finSuccAboveEquiv p i = ⟨p.succAbove i, p.succ_above_ne i⟩ :=
  rfl
#align fin_succ_above_equiv_apply finSuccAboveEquiv_apply

theorem finSuccAboveEquiv_symm_apply_last (x : { x : Fin (n + 1) // x ≠ Fin.last n }) :
    (finSuccAboveEquiv (Fin.last n)).symm x =
      Fin.castLt (x : Fin (n + 1))
        (lt_of_le_of_ne (Fin.le_last _) (Fin.val_injective.ne_iff.2 x.property)) :=
  by
  rw [← Option.some_inj, ← Option.coe_def]
  simpa [finSuccAboveEquiv, OrderIso.symm] using finSuccEquiv'_last_apply x.property
#align fin_succ_above_equiv_symm_apply_last finSuccAboveEquiv_symm_apply_last

theorem finSuccAboveEquiv_symm_apply_ne_last {p : Fin (n + 1)} (h : p ≠ Fin.last n)
    (x : { x : Fin (n + 1) // x ≠ p }) :
    (finSuccAboveEquiv p).symm x =
      (p.castLt (lt_of_le_of_ne (Fin.le_last _) (Fin.val_injective.ne_iff.2 h))).predAbove x :=
  by
  rw [← Option.some_inj, ← Option.coe_def]
  simpa [finSuccAboveEquiv, OrderIso.symm] using finSuccEquiv'_ne_last_apply h x.property
#align fin_succ_above_equiv_symm_apply_ne_last finSuccAboveEquiv_symm_apply_ne_last

/-- `equiv` between `fin (n + 1)` and `option (fin n)` sending `fin.last n` to `none` -/
def finSuccEquivLast {n : ℕ} : Fin (n + 1) ≃ Option (Fin n) :=
  finSuccEquiv' (Fin.last n)
#align fin_succ_equiv_last finSuccEquivLast

@[simp]
theorem finSuccEquivLast_castSucc {n : ℕ} (i : Fin n) : finSuccEquivLast i.cast_succ = some i :=
  finSuccEquiv'_below i.2
#align fin_succ_equiv_last_cast_succ finSuccEquivLast_castSucc

@[simp]
theorem finSuccEquivLast_last {n : ℕ} : finSuccEquivLast (Fin.last n) = none := by
  simp [finSuccEquivLast]
#align fin_succ_equiv_last_last finSuccEquivLast_last

@[simp]
theorem finSuccEquivLast_symm_some {n : ℕ} (i : Fin n) :
    finSuccEquivLast.symm (some i) = i.cast_succ :=
  finSuccEquiv'_symm_some_below i.2
#align fin_succ_equiv_last_symm_some finSuccEquivLast_symm_some

@[simp]
theorem finSuccEquivLast_symm_coe {n : ℕ} (i : Fin n) : finSuccEquivLast.symm ↑i = i.cast_succ :=
  finSuccEquiv'_symm_some_below i.2
#align fin_succ_equiv_last_symm_coe finSuccEquivLast_symm_coe

@[simp]
theorem finSuccEquivLast_symm_none {n : ℕ} : finSuccEquivLast.symm none = Fin.last n :=
  finSuccEquiv'_symm_none _
#align fin_succ_equiv_last_symm_none finSuccEquivLast_symm_none

/-- Equivalence between `Π j : fin (n + 1), α j` and `α i × Π j : fin n, α (fin.succ_above i j)`. -/
@[simps (config := { fullyApplied := false })]
def Equiv.piFinSuccAboveEquiv {n : ℕ} (α : Fin (n + 1) → Type u) (i : Fin (n + 1)) :
    (∀ j, α j) ≃ α i × ∀ j, α (i.succAbove j)
    where
  toFun f := (f i, fun j => f (i.succAbove j))
  invFun f := i.insertNth f.1 f.2
  left_inv f := by simp [Fin.insertNth_eq_iff]
  right_inv f := by simp
#align equiv.pi_fin_succ_above_equiv Equiv.piFinSuccAboveEquiv

/-- Order isomorphism between `Π j : fin (n + 1), α j` and
`α i × Π j : fin n, α (fin.succ_above i j)`. -/
def OrderIso.piFinSuccAboveIso {n : ℕ} (α : Fin (n + 1) → Type u) [∀ i, LE (α i)]
    (i : Fin (n + 1)) : (∀ j, α j) ≃o α i × ∀ j, α (i.succAbove j)
    where
  toEquiv := Equiv.piFinSuccAboveEquiv α i
  map_rel_iff' f g := i.forall_iff_succ_above.symm
#align order_iso.pi_fin_succ_above_iso OrderIso.piFinSuccAboveIso

/-- Equivalence between `fin (n + 1) → β` and `β × (fin n → β)`. -/
@[simps (config := { fullyApplied := false })]
def Equiv.piFinSucc (n : ℕ) (β : Type u) : (Fin (n + 1) → β) ≃ β × (Fin n → β) :=
  Equiv.piFinSuccAboveEquiv (fun _ => β) 0
#align equiv.pi_fin_succ Equiv.piFinSucc

/-- Equivalence between `fin m ⊕ fin n` and `fin (m + n)` -/
def finSumFinEquiv : Sum (Fin m) (Fin n) ≃ Fin (m + n)
    where
  toFun := Sum.elim (Fin.castAdd n) (Fin.natAdd m)
  invFun i := @Fin.addCases m n (fun _ => Sum (Fin m) (Fin n)) Sum.inl Sum.inr i
  left_inv x := by cases' x with y y <;> dsimp <;> simp
  right_inv x := by refine' Fin.addCases (fun i => _) (fun i => _) x <;> simp
#align fin_sum_fin_equiv finSumFinEquiv

@[simp]
theorem finSumFinEquiv_apply_left (i : Fin m) :
    (finSumFinEquiv (Sum.inl i) : Fin (m + n)) = Fin.castAdd n i :=
  rfl
#align fin_sum_fin_equiv_apply_left finSumFinEquiv_apply_left

@[simp]
theorem finSumFinEquiv_apply_right (i : Fin n) :
    (finSumFinEquiv (Sum.inr i) : Fin (m + n)) = Fin.natAdd m i :=
  rfl
#align fin_sum_fin_equiv_apply_right finSumFinEquiv_apply_right

@[simp]
theorem finSumFinEquiv_symm_apply_castAdd (x : Fin m) :
    finSumFinEquiv.symm (Fin.castAdd n x) = Sum.inl x :=
  finSumFinEquiv.symm_apply_apply (Sum.inl x)
#align fin_sum_fin_equiv_symm_apply_cast_add finSumFinEquiv_symm_apply_castAdd

@[simp]
theorem finSumFinEquiv_symm_apply_natAdd (x : Fin n) :
    finSumFinEquiv.symm (Fin.natAdd m x) = Sum.inr x :=
  finSumFinEquiv.symm_apply_apply (Sum.inr x)
#align fin_sum_fin_equiv_symm_apply_nat_add finSumFinEquiv_symm_apply_natAdd

@[simp]
theorem finSumFinEquiv_symm_last : finSumFinEquiv.symm (Fin.last n) = Sum.inr 0 :=
  finSumFinEquiv_symm_apply_natAdd 0
#align fin_sum_fin_equiv_symm_last finSumFinEquiv_symm_last

/-- The equivalence between `fin (m + n)` and `fin (n + m)` which rotates by `n`. -/
def finAddFlip : Fin (m + n) ≃ Fin (n + m) :=
  (finSumFinEquiv.symm.trans (Equiv.sumComm _ _)).trans finSumFinEquiv
#align fin_add_flip finAddFlip

@[simp]
theorem finAddFlip_apply_castAdd (k : Fin m) (n : ℕ) :
    finAddFlip (Fin.castAdd n k) = Fin.natAdd n k := by simp [finAddFlip]
#align fin_add_flip_apply_cast_add finAddFlip_apply_castAdd

@[simp]
theorem finAddFlip_apply_natAdd (k : Fin n) (m : ℕ) :
    finAddFlip (Fin.natAdd m k) = Fin.castAdd m k := by simp [finAddFlip]
#align fin_add_flip_apply_nat_add finAddFlip_apply_natAdd

@[simp]
theorem finAddFlip_apply_mk_left {k : ℕ} (h : k < m) (hk : k < m + n := Nat.lt_add_right k m n h)
    (hnk : n + k < n + m := add_lt_add_left h n) :
    finAddFlip (⟨k, hk⟩ : Fin (m + n)) = ⟨n + k, hnk⟩ := by
  convert finAddFlip_apply_castAdd ⟨k, h⟩ n
#align fin_add_flip_apply_mk_left finAddFlip_apply_mk_left

@[simp]
theorem finAddFlip_apply_mk_right {k : ℕ} (h₁ : m ≤ k) (h₂ : k < m + n) :
    finAddFlip (⟨k, h₂⟩ : Fin (m + n)) = ⟨k - m, tsub_le_self.trans_lt <| add_comm m n ▸ h₂⟩ :=
  by
  convert finAddFlip_apply_natAdd ⟨k - m, (tsub_lt_iff_right h₁).2 _⟩ m
  · simp [add_tsub_cancel_of_le h₁]
  · rwa [add_comm]
#align fin_add_flip_apply_mk_right finAddFlip_apply_mk_right

/-- Rotate `fin n` one step to the right. -/
def finRotate : ∀ n, Equiv.Perm (Fin n)
  | 0 => Equiv.refl _
  | n + 1 => finAddFlip.trans (finCongr (add_comm _ _))
#align fin_rotate finRotate

theorem finRotate_of_lt {k : ℕ} (h : k < n) :
    finRotate (n + 1) ⟨k, lt_of_lt_of_le h (Nat.le_succ _)⟩ = ⟨k + 1, Nat.succ_lt_succ h⟩ :=
  by
  dsimp [finRotate]
  simp [h, add_comm]
#align fin_rotate_of_lt finRotate_of_lt

theorem finRotate_last' : finRotate (n + 1) ⟨n, lt_add_one _⟩ = ⟨0, Nat.zero_lt_succ _⟩ :=
  by
  dsimp [finRotate]
  rw [finAddFlip_apply_mk_right]
  simp
#align fin_rotate_last' finRotate_last'

theorem finRotate_last : finRotate (n + 1) (Fin.last _) = 0 :=
  finRotate_last'
#align fin_rotate_last finRotate_last

theorem Fin.snoc_eq_cons_rotate {α : Type _} (v : Fin n → α) (a : α) :
    @Fin.snoc _ (fun _ => α) v a = fun i => @Fin.cons _ (fun _ => α) a v (finRotate _ i) :=
  by
  ext ⟨i, h⟩
  by_cases h' : i < n
  · rw [finRotate_of_lt h', Fin.snoc, Fin.cons, dif_pos h']
    rfl
  · have h'' : n = i := by
      simp only [not_lt] at h'
      exact (Nat.eq_of_le_of_lt_succ h' h).symm
    subst h''
    rw [finRotate_last', Fin.snoc, Fin.cons, dif_neg (lt_irrefl _)]
    rfl
#align fin.snoc_eq_cons_rotate Fin.snoc_eq_cons_rotate

@[simp]
theorem finRotate_zero : finRotate 0 = Equiv.refl _ :=
  rfl
#align fin_rotate_zero finRotate_zero

@[simp]
theorem finRotate_one : finRotate 1 = Equiv.refl _ :=
  Subsingleton.elim _ _
#align fin_rotate_one finRotate_one

@[simp]
theorem finRotate_succ_apply {n : ℕ} (i : Fin n.succ) : finRotate n.succ i = i + 1 :=
  by
  cases n
  · simp
  rcases i.le_last.eq_or_lt with (rfl | h)
  · simp [finRotate_last]
  · cases i
    simp only [Fin.lt_iff_val_lt_val, Fin.val_last, Fin.val_mk] at h
    simp [finRotate_of_lt h, Fin.eq_iff_veq, Fin.add_def, Nat.mod_eq_of_lt (Nat.succ_lt_succ h)]
#align fin_rotate_succ_apply finRotate_succ_apply

@[simp]
theorem finRotate_apply_zero {n : ℕ} : finRotate n.succ 0 = 1 := by
  rw [finRotate_succ_apply, zero_add]
#align fin_rotate_apply_zero finRotate_apply_zero

theorem coe_finRotate_of_ne_last {n : ℕ} {i : Fin n.succ} (h : i ≠ Fin.last n) :
    (finRotate n.succ i : ℕ) = i + 1 :=
  by
  rw [finRotate_succ_apply]
  have : (i : ℕ) < n := lt_of_le_of_ne (nat.succ_le_succ_iff.mp i.2) (fin.coe_injective.ne h)
  exact Fin.val_add_one_of_lt this
#align coe_fin_rotate_of_ne_last coe_finRotate_of_ne_last

theorem coe_finRotate {n : ℕ} (i : Fin n.succ) :
    (finRotate n.succ i : ℕ) = if i = Fin.last n then 0 else i + 1 := by
  rw [finRotate_succ_apply, Fin.val_add_one i]
#align coe_fin_rotate coe_finRotate

/-- Equivalence between `fin m × fin n` and `fin (m * n)` -/
@[simps]
def finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)
    where
  toFun x :=
    ⟨x.2 + n * x.1,
      calc
        x.2.1 + n * x.1.1 + 1 = x.1.1 * n + x.2.1 + 1 := by ac_rfl
        _ ≤ x.1.1 * n + n := Nat.add_le_add_left x.2.2 _
        _ = (x.1.1 + 1) * n := Eq.symm <| Nat.succ_mul _ _
        _ ≤ m * n := Nat.mul_le_mul_right _ x.1.2
        ⟩
  invFun x := (x.divNat, x.modNat)
  left_inv := fun ⟨x, y⟩ =>
    have H : 0 < n := Nat.pos_of_ne_zero fun H => Nat.not_lt_zero y.1 <| H ▸ y.2
    Prod.ext
      (Fin.eq_of_veq <|
        calc
          (y.1 + n * x.1) / n = y.1 / n + x.1 := Nat.add_mul_div_left _ _ H
          _ = 0 + x.1 := by rw [Nat.div_eq_of_lt y.2]
          _ = x.1 := Nat.zero_add x.1
          )
      (Fin.eq_of_veq <|
        calc
          (y.1 + n * x.1) % n = y.1 % n := Nat.add_mul_mod_self_left _ _ _
          _ = y.1 := Nat.mod_eq_of_lt y.2
          )
  right_inv x := Fin.eq_of_veq <| Nat.mod_add_div _ _
#align fin_prod_fin_equiv finProdFinEquiv

/-- Promote a `fin n` into a larger `fin m`, as a subtype where the underlying
values are retained. This is the `order_iso` version of `fin.cast_le`. -/
@[simps apply symmApply]
def Fin.castLeOrderIso {n m : ℕ} (h : n ≤ m) : Fin n ≃o { i : Fin m // (i : ℕ) < n }
    where
  toFun i := ⟨Fin.castLe h i, by simp⟩
  invFun i := ⟨i, i.Prop⟩
  left_inv _ := by simp
  right_inv _ := by simp
  map_rel_iff' _ _ := by simp
#align fin.cast_le_order_iso Fin.castLeOrderIso

/-- `fin 0` is a subsingleton. -/
instance subsingleton_fin_zero : Subsingleton (Fin 0) :=
  finZeroEquiv.Subsingleton
#align subsingleton_fin_zero subsingleton_fin_zero

/-- `fin 1` is a subsingleton. -/
instance subsingleton_fin_one : Subsingleton (Fin 1) :=
  finOneEquiv.Subsingleton
#align subsingleton_fin_one subsingleton_fin_one

