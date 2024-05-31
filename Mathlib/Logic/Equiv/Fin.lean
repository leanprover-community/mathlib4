/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Embedding.Set

#align_import logic.equiv.fin from "leanprover-community/mathlib"@"bd835ef554f37ef9b804f0903089211f89cb370b"

/-!
# Equivalences for `Fin n`
-/

assert_not_exists MonoidWithZero

universe u

variable {m n : ℕ}

/-- Equivalence between `Fin 0` and `Empty`. -/
def finZeroEquiv : Fin 0 ≃ Empty :=
  Equiv.equivEmpty _
#align fin_zero_equiv finZeroEquiv

/-- Equivalence between `Fin 0` and `PEmpty`. -/
def finZeroEquiv' : Fin 0 ≃ PEmpty.{u} :=
  Equiv.equivPEmpty _
#align fin_zero_equiv' finZeroEquiv'

/-- Equivalence between `Fin 1` and `Unit`. -/
def finOneEquiv : Fin 1 ≃ Unit :=
  Equiv.equivPUnit _
#align fin_one_equiv finOneEquiv

/-- Equivalence between `Fin 2` and `Bool`. -/
def finTwoEquiv : Fin 2 ≃ Bool where
  toFun := ![false, true]
  invFun b := b.casesOn 0 1
  left_inv := Fin.forall_fin_two.2 <| by simp
  right_inv := Bool.forall_bool.2 <| by simp
#align fin_two_equiv finTwoEquiv

/-- `Π i : Fin 2, α i` is equivalent to `α 0 × α 1`. See also `finTwoArrowEquiv` for a
non-dependent version and `prodEquivPiFinTwo` for a version with inputs `α β : Type u`. -/
@[simps (config := .asFn)]
def piFinTwoEquiv (α : Fin 2 → Type u) : (∀ i, α i) ≃ α 0 × α 1 where
  toFun f := (f 0, f 1)
  invFun p := Fin.cons p.1 <| Fin.cons p.2 finZeroElim
  left_inv _ := funext <| Fin.forall_fin_two.2 ⟨rfl, rfl⟩
  right_inv := fun _ => rfl
#align pi_fin_two_equiv piFinTwoEquiv
#align pi_fin_two_equiv_symm_apply piFinTwoEquiv_symm_apply
#align pi_fin_two_equiv_apply piFinTwoEquiv_apply

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Fin.preimage_apply_01_prod {α : Fin 2 → Type u} (s : Set (α 0)) (t : Set (α 1)) :
    (fun f : ∀ i, α i => (f 0, f 1)) ⁻¹' s ×ˢ t =
      Set.pi Set.univ (Fin.cons s <| Fin.cons t finZeroElim) := by
  ext f
  simp [Fin.forall_fin_two]
#align fin.preimage_apply_01_prod Fin.preimage_apply_01_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Fin.preimage_apply_01_prod' {α : Type u} (s t : Set α) :
    (fun f : Fin 2 → α => (f 0, f 1)) ⁻¹' s ×ˢ t = Set.pi Set.univ ![s, t] :=
  @Fin.preimage_apply_01_prod (fun _ => α) s t
#align fin.preimage_apply_01_prod' Fin.preimage_apply_01_prod'

/-- A product space `α × β` is equivalent to the space `Π i : Fin 2, γ i`, where
`γ = Fin.cons α (Fin.cons β finZeroElim)`. See also `piFinTwoEquiv` and
`finTwoArrowEquiv`. -/
@[simps! (config := .asFn)]
def prodEquivPiFinTwo (α β : Type u) : α × β ≃ ∀ i : Fin 2, ![α, β] i :=
  (piFinTwoEquiv (Fin.cons α (Fin.cons β finZeroElim))).symm
#align prod_equiv_pi_fin_two prodEquivPiFinTwo
#align prod_equiv_pi_fin_two_apply prodEquivPiFinTwo_apply
#align prod_equiv_pi_fin_two_symm_apply prodEquivPiFinTwo_symm_apply

/-- The space of functions `Fin 2 → α` is equivalent to `α × α`. See also `piFinTwoEquiv` and
`prodEquivPiFinTwo`. -/
@[simps (config := .asFn)]
def finTwoArrowEquiv (α : Type*) : (Fin 2 → α) ≃ α × α :=
  { piFinTwoEquiv fun _ => α with invFun := fun x => ![x.1, x.2] }
#align fin_two_arrow_equiv finTwoArrowEquiv
#align fin_two_arrow_equiv_symm_apply finTwoArrowEquiv_symm_apply
#align fin_two_arrow_equiv_apply finTwoArrowEquiv_apply

/-- `Π i : Fin 2, α i` is order equivalent to `α 0 × α 1`. See also `OrderIso.finTwoArrowEquiv`
for a non-dependent version. -/
def OrderIso.piFinTwoIso (α : Fin 2 → Type u) [∀ i, Preorder (α i)] : (∀ i, α i) ≃o α 0 × α 1 where
  toEquiv := piFinTwoEquiv α
  map_rel_iff' := Iff.symm Fin.forall_fin_two
#align order_iso.pi_fin_two_iso OrderIso.piFinTwoIso

/-- The space of functions `Fin 2 → α` is order equivalent to `α × α`. See also
`OrderIso.piFinTwoIso`. -/
def OrderIso.finTwoArrowIso (α : Type*) [Preorder α] : (Fin 2 → α) ≃o α × α :=
  { OrderIso.piFinTwoIso fun _ => α with toEquiv := finTwoArrowEquiv α }
#align order_iso.fin_two_arrow_iso OrderIso.finTwoArrowIso

/-- An equivalence that removes `i` and maps it to `none`.
This is a version of `Fin.predAbove` that produces `Option (Fin n)` instead of
mapping both `i.cast_succ` and `i.succ` to `i`. -/
def finSuccEquiv' (i : Fin (n + 1)) : Fin (n + 1) ≃ Option (Fin n) where
  toFun := i.insertNth none some
  invFun x := x.casesOn' i (Fin.succAbove i)
  left_inv x := Fin.succAboveCases i (by simp) (fun j => by simp) x
  right_inv x := by cases x <;> dsimp <;> simp
#align fin_succ_equiv' finSuccEquiv'

@[simp]
theorem finSuccEquiv'_at (i : Fin (n + 1)) : (finSuccEquiv' i) i = none := by
  simp [finSuccEquiv']
#align fin_succ_equiv'_at finSuccEquiv'_at

@[simp]
theorem finSuccEquiv'_succAbove (i : Fin (n + 1)) (j : Fin n) :
    finSuccEquiv' i (i.succAbove j) = some j :=
  @Fin.insertNth_apply_succAbove n (fun _ => Option (Fin n)) i _ _ _
#align fin_succ_equiv'_succ_above finSuccEquiv'_succAbove

theorem finSuccEquiv'_below {i : Fin (n + 1)} {m : Fin n} (h : Fin.castSucc m < i) :
    (finSuccEquiv' i) (Fin.castSucc m) = m := by
  rw [← Fin.succAbove_of_castSucc_lt _ _ h, finSuccEquiv'_succAbove]
#align fin_succ_equiv'_below finSuccEquiv'_below

theorem finSuccEquiv'_above {i : Fin (n + 1)} {m : Fin n} (h : i ≤ Fin.castSucc m) :
    (finSuccEquiv' i) m.succ = some m := by
  rw [← Fin.succAbove_of_le_castSucc _ _ h, finSuccEquiv'_succAbove]
#align fin_succ_equiv'_above finSuccEquiv'_above

@[simp]
theorem finSuccEquiv'_symm_none (i : Fin (n + 1)) : (finSuccEquiv' i).symm none = i :=
  rfl
#align fin_succ_equiv'_symm_none finSuccEquiv'_symm_none

@[simp]
theorem finSuccEquiv'_symm_some (i : Fin (n + 1)) (j : Fin n) :
    (finSuccEquiv' i).symm (some j) = i.succAbove j :=
  rfl
#align fin_succ_equiv'_symm_some finSuccEquiv'_symm_some

theorem finSuccEquiv'_symm_some_below {i : Fin (n + 1)} {m : Fin n} (h : Fin.castSucc m < i) :
    (finSuccEquiv' i).symm (some m) = Fin.castSucc m :=
  Fin.succAbove_of_castSucc_lt i m h
#align fin_succ_equiv'_symm_some_below finSuccEquiv'_symm_some_below

theorem finSuccEquiv'_symm_some_above {i : Fin (n + 1)} {m : Fin n} (h : i ≤ Fin.castSucc m) :
    (finSuccEquiv' i).symm (some m) = m.succ :=
  Fin.succAbove_of_le_castSucc i m h
#align fin_succ_equiv'_symm_some_above finSuccEquiv'_symm_some_above

theorem finSuccEquiv'_symm_coe_below {i : Fin (n + 1)} {m : Fin n} (h : Fin.castSucc m < i) :
    (finSuccEquiv' i).symm m = Fin.castSucc m :=
  finSuccEquiv'_symm_some_below h
#align fin_succ_equiv'_symm_coe_below finSuccEquiv'_symm_coe_below

theorem finSuccEquiv'_symm_coe_above {i : Fin (n + 1)} {m : Fin n} (h : i ≤ Fin.castSucc m) :
    (finSuccEquiv' i).symm m = m.succ :=
  finSuccEquiv'_symm_some_above h
#align fin_succ_equiv'_symm_coe_above finSuccEquiv'_symm_coe_above

/-- Equivalence between `Fin (n + 1)` and `Option (Fin n)`.
This is a version of `Fin.pred` that produces `Option (Fin n)` instead of
requiring a proof that the input is not `0`. -/
def finSuccEquiv (n : ℕ) : Fin (n + 1) ≃ Option (Fin n) :=
  finSuccEquiv' 0
#align fin_succ_equiv finSuccEquiv

@[simp]
theorem finSuccEquiv_zero : (finSuccEquiv n) 0 = none :=
  rfl
#align fin_succ_equiv_zero finSuccEquiv_zero

@[simp]
theorem finSuccEquiv_succ (m : Fin n) : (finSuccEquiv n) m.succ = some m :=
  finSuccEquiv'_above (Fin.zero_le _)
#align fin_succ_equiv_succ finSuccEquiv_succ

@[simp]
theorem finSuccEquiv_symm_none : (finSuccEquiv n).symm none = 0 :=
  finSuccEquiv'_symm_none _
#align fin_succ_equiv_symm_none finSuccEquiv_symm_none

@[simp]
theorem finSuccEquiv_symm_some (m : Fin n) : (finSuccEquiv n).symm (some m) = m.succ :=
  congr_fun Fin.succAbove_zero m
#align fin_succ_equiv_symm_some finSuccEquiv_symm_some
#align fin_succ_equiv_symm_coe finSuccEquiv_symm_some

/-- The equiv version of `Fin.predAbove_zero`. -/
theorem finSuccEquiv'_zero : finSuccEquiv' (0 : Fin (n + 1)) = finSuccEquiv n :=
  rfl
#align fin_succ_equiv'_zero finSuccEquiv'_zero

theorem finSuccEquiv'_last_apply_castSucc (i : Fin n) :
    finSuccEquiv' (Fin.last n) (Fin.castSucc i) = i := by
  rw [← Fin.succAbove_last, finSuccEquiv'_succAbove]

theorem finSuccEquiv'_last_apply {i : Fin (n + 1)} (h : i ≠ Fin.last n) :
    finSuccEquiv' (Fin.last n) i = Fin.castLT i (Fin.val_lt_last h) := by
  rcases Fin.exists_castSucc_eq.2 h with ⟨i, rfl⟩
  rw [finSuccEquiv'_last_apply_castSucc]
  rfl
#align fin_succ_equiv'_last_apply finSuccEquiv'_last_apply

theorem finSuccEquiv'_ne_last_apply {i j : Fin (n + 1)} (hi : i ≠ Fin.last n) (hj : j ≠ i) :
    finSuccEquiv' i j = (i.castLT (Fin.val_lt_last hi)).predAbove j := by
  rcases Fin.exists_succAbove_eq hj with ⟨j, rfl⟩
  rcases Fin.exists_castSucc_eq.2 hi with ⟨i, rfl⟩
  simp
#align fin_succ_equiv'_ne_last_apply finSuccEquiv'_ne_last_apply

/-- `Fin.succAbove` as an order isomorphism between `Fin n` and `{x : Fin (n + 1) // x ≠ p}`. -/
def finSuccAboveEquiv (p : Fin (n + 1)) : Fin n ≃o { x : Fin (n + 1) // x ≠ p } :=
  { Equiv.optionSubtype p ⟨(finSuccEquiv' p).symm, rfl⟩ with
    map_rel_iff' := p.succAboveOrderEmb.map_rel_iff' }
#align fin_succ_above_equiv finSuccAboveEquiv

theorem finSuccAboveEquiv_apply (p : Fin (n + 1)) (i : Fin n) :
    finSuccAboveEquiv p i = ⟨p.succAbove i, p.succAbove_ne i⟩ :=
  rfl
#align fin_succ_above_equiv_apply finSuccAboveEquiv_apply

theorem finSuccAboveEquiv_symm_apply_last (x : { x : Fin (n + 1) // x ≠ Fin.last n }) :
    (finSuccAboveEquiv (Fin.last n)).symm x = Fin.castLT x.1 (Fin.val_lt_last x.2) := by
  rw [← Option.some_inj]
  simpa [finSuccAboveEquiv, OrderIso.symm] using finSuccEquiv'_last_apply x.property
#align fin_succ_above_equiv_symm_apply_last finSuccAboveEquiv_symm_apply_last

theorem finSuccAboveEquiv_symm_apply_ne_last {p : Fin (n + 1)} (h : p ≠ Fin.last n)
    (x : { x : Fin (n + 1) // x ≠ p }) :
    (finSuccAboveEquiv p).symm x = (p.castLT (Fin.val_lt_last h)).predAbove x := by
  rw [← Option.some_inj]
  simpa [finSuccAboveEquiv, OrderIso.symm] using finSuccEquiv'_ne_last_apply h x.property
#align fin_succ_above_equiv_symm_apply_ne_last finSuccAboveEquiv_symm_apply_ne_last

/-- `Equiv` between `Fin (n + 1)` and `Option (Fin n)` sending `Fin.last n` to `none` -/
def finSuccEquivLast : Fin (n + 1) ≃ Option (Fin n) :=
  finSuccEquiv' (Fin.last n)
#align fin_succ_equiv_last finSuccEquivLast

@[simp]
theorem finSuccEquivLast_castSucc (i : Fin n) : finSuccEquivLast (Fin.castSucc i) = some i :=
  finSuccEquiv'_below i.2
#align fin_succ_equiv_last_cast_succ finSuccEquivLast_castSucc

@[simp]
theorem finSuccEquivLast_last : finSuccEquivLast (Fin.last n) = none := by
  simp [finSuccEquivLast]
#align fin_succ_equiv_last_last finSuccEquivLast_last

@[simp]
theorem finSuccEquivLast_symm_some (i : Fin n) :
    finSuccEquivLast.symm (some i) = Fin.castSucc i :=
  finSuccEquiv'_symm_some_below i.2
#align fin_succ_equiv_last_symm_some finSuccEquivLast_symm_some
#align fin_succ_equiv_last_symm_coe finSuccEquivLast_symm_some

@[simp] theorem finSuccEquivLast_symm_none : finSuccEquivLast.symm none = Fin.last n :=
  finSuccEquiv'_symm_none _
#align fin_succ_equiv_last_symm_none finSuccEquivLast_symm_none

/-- Equivalence between `Π j : Fin (n + 1), α j` and `α i × Π j : Fin n, α (Fin.succAbove i j)`. -/
@[simps (config := .asFn)]
def Equiv.piFinSuccAbove (α : Fin (n + 1) → Type u) (i : Fin (n + 1)) :
    (∀ j, α j) ≃ α i × ∀ j, α (i.succAbove j) where
  toFun f := i.extractNth f
  invFun f := i.insertNth f.1 f.2
  left_inv f := by simp
  right_inv f := by simp
#align equiv.pi_fin_succ_above_equiv Equiv.piFinSuccAbove
#align equiv.pi_fin_succ_above_equiv_apply Equiv.piFinSuccAbove_apply
#align equiv.pi_fin_succ_above_equiv_symm_apply Equiv.piFinSuccAbove_symm_apply

/-- Order isomorphism between `Π j : Fin (n + 1), α j` and
`α i × Π j : Fin n, α (Fin.succAbove i j)`. -/
def OrderIso.piFinSuccAboveIso (α : Fin (n + 1) → Type u) [∀ i, LE (α i)]
    (i : Fin (n + 1)) : (∀ j, α j) ≃o α i × ∀ j, α (i.succAbove j) where
  toEquiv := Equiv.piFinSuccAbove α i
  map_rel_iff' := Iff.symm i.forall_iff_succAbove
#align order_iso.pi_fin_succ_above_iso OrderIso.piFinSuccAboveIso

/-- Equivalence between `Fin (n + 1) → β` and `β × (Fin n → β)`. -/
@[simps! (config := .asFn)]
def Equiv.piFinSucc (n : ℕ) (β : Type u) : (Fin (n + 1) → β) ≃ β × (Fin n → β) :=
  Equiv.piFinSuccAbove (fun _ => β) 0
#align equiv.pi_fin_succ Equiv.piFinSucc
#align equiv.pi_fin_succ_apply Equiv.piFinSucc_apply
#align equiv.pi_fin_succ_symm_apply Equiv.piFinSucc_symm_apply

/-- An embedding `e : Fin (n+1) ↪ ι` corresponds to an embedding `f : Fin n ↪ ι` (corresponding
the last `n` coordinates of `e`) together with a value not taken by `f` (corresponding to `e 0`). -/
def Equiv.embeddingFinSucc (n : ℕ) (ι : Type*) :
    (Fin (n+1) ↪ ι) ≃ (Σ (e : Fin n ↪ ι), {i // i ∉ Set.range e}) :=
  ((finSuccEquiv n).embeddingCongr (Equiv.refl ι)).trans
    (Function.Embedding.optionEmbeddingEquiv (Fin n) ι)

@[simp] lemma Equiv.embeddingFinSucc_fst {n : ℕ} {ι : Type*} (e : Fin (n+1) ↪ ι) :
    ((Equiv.embeddingFinSucc n ι e).1 : Fin n → ι) = e ∘ Fin.succ := rfl

@[simp] lemma Equiv.embeddingFinSucc_snd {n : ℕ} {ι : Type*} (e : Fin (n+1) ↪ ι) :
    ((Equiv.embeddingFinSucc n ι e).2 : ι) = e 0 := rfl

@[simp] lemma Equiv.coe_embeddingFinSucc_symm {n : ℕ} {ι : Type*}
    (f : Σ (e : Fin n ↪ ι), {i // i ∉ Set.range e}) :
    ((Equiv.embeddingFinSucc n ι).symm f : Fin (n + 1) → ι) = Fin.cons f.2.1 f.1 := by
  ext i
  exact Fin.cases rfl (fun j ↦ rfl) i

/-- Equivalence between `Fin (n + 1) → β` and `β × (Fin n → β)` which separates out the last
element of the tuple. -/
@[simps! (config := .asFn)]
def Equiv.piFinCastSucc (n : ℕ) (β : Type u) : (Fin (n + 1) → β) ≃ β × (Fin n → β) :=
  Equiv.piFinSuccAbove (fun _ => β) (.last _)

/-- Equivalence between `Fin m ⊕ Fin n` and `Fin (m + n)` -/
def finSumFinEquiv : Sum (Fin m) (Fin n) ≃ Fin (m + n) where
  toFun := Sum.elim (Fin.castAdd n) (Fin.natAdd m)
  invFun i := @Fin.addCases m n (fun _ => Sum (Fin m) (Fin n)) Sum.inl Sum.inr i
  left_inv x := by cases' x with y y <;> dsimp <;> simp
  right_inv x := by refine Fin.addCases (fun i => ?_) (fun i => ?_) x <;> simp
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

/-- The equivalence between `Fin (m + n)` and `Fin (n + m)` which rotates by `n`. -/
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
theorem finAddFlip_apply_mk_left {k : ℕ} (h : k < m) (hk : k < m + n := Nat.lt_add_right n h)
    (hnk : n + k < n + m := Nat.add_lt_add_left h n) :
    finAddFlip (⟨k, hk⟩ : Fin (m + n)) = ⟨n + k, hnk⟩ := by
  convert finAddFlip_apply_castAdd ⟨k, h⟩ n
#align fin_add_flip_apply_mk_left finAddFlip_apply_mk_left

@[simp]
theorem finAddFlip_apply_mk_right {k : ℕ} (h₁ : m ≤ k) (h₂ : k < m + n) :
    finAddFlip (⟨k, h₂⟩ : Fin (m + n)) = ⟨k - m, by omega⟩ := by
  convert @finAddFlip_apply_natAdd n ⟨k - m, by omega⟩ m
  simp [Nat.add_sub_cancel' h₁]
#align fin_add_flip_apply_mk_right finAddFlip_apply_mk_right

/-- Rotate `Fin n` one step to the right. -/
def finRotate : ∀ n, Equiv.Perm (Fin n)
  | 0 => Equiv.refl _
  | n + 1 => finAddFlip.trans (finCongr (Nat.add_comm 1 n))
#align fin_rotate finRotate

@[simp] lemma finRotate_zero : finRotate 0 = Equiv.refl _ := rfl
#align fin_rotate_zero finRotate_zero

lemma finRotate_succ (n : ℕ) :
    finRotate (n + 1) = finAddFlip.trans (finCongr (Nat.add_comm 1 n)) := rfl

theorem finRotate_of_lt {k : ℕ} (h : k < n) :
    finRotate (n + 1) ⟨k, h.trans_le n.le_succ⟩ = ⟨k + 1, Nat.succ_lt_succ h⟩ := by
  ext
  dsimp [finRotate_succ]
  simp [finAddFlip_apply_mk_left h, Nat.add_comm]
#align fin_rotate_of_lt finRotate_of_lt

theorem finRotate_last' : finRotate (n + 1) ⟨n, by omega⟩ = ⟨0, Nat.zero_lt_succ _⟩ := by
  dsimp [finRotate_succ]
  rw [finAddFlip_apply_mk_right le_rfl]
  simp
#align fin_rotate_last' finRotate_last'

theorem finRotate_last : finRotate (n + 1) (Fin.last _) = 0 :=
  finRotate_last'
#align fin_rotate_last finRotate_last

theorem Fin.snoc_eq_cons_rotate {α : Type*} (v : Fin n → α) (a : α) :
    @Fin.snoc _ (fun _ => α) v a = fun i => @Fin.cons _ (fun _ => α) a v (finRotate _ i) := by
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
theorem finRotate_one : finRotate 1 = Equiv.refl _ :=
  Subsingleton.elim _ _
#align fin_rotate_one finRotate_one

@[simp] theorem finRotate_succ_apply (i : Fin (n + 1)) : finRotate (n + 1) i = i + 1 := by
  cases n
  · exact @Subsingleton.elim (Fin 1) _ _ _
  rcases i.le_last.eq_or_lt with (rfl | h)
  · simp [finRotate_last]
  · cases i
    simp only [Fin.lt_iff_val_lt_val, Fin.val_last, Fin.val_mk] at h
    simp [finRotate_of_lt h, Fin.ext_iff, Fin.add_def, Nat.mod_eq_of_lt (Nat.succ_lt_succ h)]
#align fin_rotate_succ_apply finRotate_succ_apply

-- Porting note: was a @[simp]
theorem finRotate_apply_zero : finRotate n.succ 0 = 1 := by
  rw [finRotate_succ_apply, Fin.zero_add]
#align fin_rotate_apply_zero finRotate_apply_zero

theorem coe_finRotate_of_ne_last {i : Fin n.succ} (h : i ≠ Fin.last n) :
    (finRotate (n + 1) i : ℕ) = i + 1 := by
  rw [finRotate_succ_apply]
  have : (i : ℕ) < n := Fin.val_lt_last h
  exact Fin.val_add_one_of_lt this
#align coe_fin_rotate_of_ne_last coe_finRotate_of_ne_last

theorem coe_finRotate (i : Fin n.succ) :
    (finRotate n.succ i : ℕ) = if i = Fin.last n then (0 : ℕ) else i + 1 := by
  rw [finRotate_succ_apply, Fin.val_add_one i]
#align coe_fin_rotate coe_finRotate

/-- Equivalence between `Fin m × Fin n` and `Fin (m * n)` -/
@[simps]
def finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n) where
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
      (Fin.eq_of_val_eq <|
        calc
          (y.1 + n * x.1) / n = y.1 / n + x.1 := Nat.add_mul_div_left _ _ H
          _ = 0 + x.1 := by rw [Nat.div_eq_of_lt y.2]
          _ = x.1 := Nat.zero_add x.1
          )
      (Fin.eq_of_val_eq <|
        calc
          (y.1 + n * x.1) % n = y.1 % n := Nat.add_mul_mod_self_left _ _ _
          _ = y.1 := Nat.mod_eq_of_lt y.2
          )
  right_inv x := Fin.eq_of_val_eq <| Nat.mod_add_div _ _
#align fin_prod_fin_equiv finProdFinEquiv
#align fin_prod_fin_equiv_apply_val finProdFinEquiv_apply_val
#align fin_prod_fin_equiv_symm_apply finProdFinEquiv_symm_apply

/-- The equivalence induced by `a ↦ (a / n, a % n)` for nonzero `n`.
This is like `finProdFinEquiv.symm` but with `m` infinite.
See `Nat.div_mod_unique` for a similar propositional statement. -/
@[simps]
def Nat.divModEquiv (n : ℕ) [NeZero n] : ℕ ≃ ℕ × Fin n where
  toFun a := (a / n, ↑a)
  invFun p := p.1 * n + ↑p.2
  -- TODO: is there a canonical order of `*` and `+` here?
  left_inv a := Nat.div_add_mod' _ _
  right_inv p := by
    refine Prod.ext ?_ (Fin.ext <| Nat.mul_add_mod_of_lt p.2.is_lt)
    dsimp only
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ n.pos_of_neZero, Nat.div_eq_of_lt p.2.is_lt,
      Nat.zero_add]
#align nat.div_mod_equiv Nat.divModEquiv

/-- The equivalence induced by `a ↦ (a / n, a % n)` for nonzero `n`.
See `Int.ediv_emod_unique` for a similar propositional statement. -/
@[simps]
def Int.divModEquiv (n : ℕ) [NeZero n] : ℤ ≃ ℤ × Fin n where
  -- TODO: could cast from int directly if we import `Data.ZMod.Defs`, though there are few lemmas
  -- about that coercion.
  toFun a := (a / n, ↑(a.natMod n))
  invFun p := p.1 * n + ↑p.2
  left_inv a := by
    simp_rw [Fin.coe_ofNat_eq_mod, natCast_mod, natMod,
      toNat_of_nonneg (emod_nonneg _ <| natCast_eq_zero.not.2 (NeZero.ne n)), emod_emod,
      ediv_add_emod']
  right_inv := fun ⟨q, r, hrn⟩ => by
    simp only [Fin.val_mk, Prod.mk.inj_iff, Fin.ext_iff]
    obtain ⟨h1, h2⟩ := Int.natCast_nonneg r, Int.ofNat_lt.2 hrn
    rw [Int.add_comm, add_mul_ediv_right _ _ (natCast_eq_zero.not.2 (NeZero.ne n)),
      ediv_eq_zero_of_lt h1 h2, natMod, add_mul_emod_self, emod_eq_of_lt h1 h2, toNat_natCast]
    exact ⟨q.zero_add, Fin.val_cast_of_lt hrn⟩
#align int.div_mod_equiv Int.divModEquiv

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

/-- `Fin 0` is a subsingleton. -/
instance subsingleton_fin_zero : Subsingleton (Fin 0) :=
  finZeroEquiv.subsingleton
#align subsingleton_fin_zero subsingleton_fin_zero

/-- `Fin 1` is a subsingleton. -/
instance subsingleton_fin_one : Subsingleton (Fin 1) :=
  finOneEquiv.subsingleton
#align subsingleton_fin_one subsingleton_fin_one
