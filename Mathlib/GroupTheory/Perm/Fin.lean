/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Option
import Mathlib.Logic.Equiv.Fin
import Mathlib.Logic.Equiv.Fintype

/-!
# Permutations of `Fin n`
-/

assert_not_exists LinearMap

open Equiv

/-- Permutations of `Fin (n + 1)` are equivalent to fixing a single
`Fin (n + 1)` and permuting the remaining with a `Perm (Fin n)`.
The fixed `Fin (n + 1)` is swapped with `0`. -/
def Equiv.Perm.decomposeFin {n : ℕ} : Perm (Fin n.succ) ≃ Fin n.succ × Perm (Fin n) :=
  ((Equiv.permCongr <| finSuccEquiv n).trans Equiv.Perm.decomposeOption).trans
    (Equiv.prodCongr (finSuccEquiv n).symm (Equiv.refl _))

@[simp]
theorem Equiv.Perm.decomposeFin_symm_of_refl {n : ℕ} (p : Fin (n + 1)) :
    Equiv.Perm.decomposeFin.symm (p, Equiv.refl _) = swap 0 p := by
  simp [Equiv.Perm.decomposeFin, Equiv.permCongr_def]

@[simp]
theorem Equiv.Perm.decomposeFin_symm_of_one {n : ℕ} (p : Fin (n + 1)) :
    Equiv.Perm.decomposeFin.symm (p, 1) = swap 0 p :=
  Equiv.Perm.decomposeFin_symm_of_refl p

@[simp]
theorem Equiv.Perm.decomposeFin_symm_apply_zero {n : ℕ} (p : Fin (n + 1)) (e : Perm (Fin n)) :
    Equiv.Perm.decomposeFin.symm (p, e) 0 = p := by simp [Equiv.Perm.decomposeFin]

@[simp]
theorem Equiv.Perm.decomposeFin_symm_apply_succ {n : ℕ} (e : Perm (Fin n)) (p : Fin (n + 1))
    (x : Fin n) : Equiv.Perm.decomposeFin.symm (p, e) x.succ = swap 0 p (e x).succ := by
  refine Fin.cases ?_ ?_ p
  · simp [Equiv.Perm.decomposeFin, EquivFunctor.map]
  · intro i
    by_cases h : i = e x
    · simp [h, Equiv.Perm.decomposeFin, EquivFunctor.map]
    · simp [h, Fin.succ_ne_zero, Equiv.Perm.decomposeFin, EquivFunctor.map,
        swap_apply_def, Ne.symm h]

@[simp]
theorem Equiv.Perm.decomposeFin_symm_apply_one {n : ℕ} (e : Perm (Fin (n + 1))) (p : Fin (n + 2)) :
    Equiv.Perm.decomposeFin.symm (p, e) 1 = swap 0 p (e 0).succ := by
  rw [← Fin.succ_zero_eq_one, Equiv.Perm.decomposeFin_symm_apply_succ e p 0]

@[simp]
theorem Equiv.Perm.decomposeFin.symm_sign {n : ℕ} (p : Fin (n + 1)) (e : Perm (Fin n)) :
    Perm.sign (Equiv.Perm.decomposeFin.symm (p, e)) = ite (p = 0) 1 (-1) * Perm.sign e := by
  refine Fin.cases ?_ ?_ p <;> simp [Equiv.Perm.decomposeFin, Fin.succ_ne_zero]

/-- The set of all permutations of `Fin (n + 1)` can be constructed by augmenting the set of
permutations of `Fin n` by each element of `Fin (n + 1)` in turn. -/
theorem Finset.univ_perm_fin_succ {n : ℕ} :
    @Finset.univ (Perm <| Fin n.succ) _ =
      (Finset.univ : Finset <| Fin n.succ × Perm (Fin n)).map
        Equiv.Perm.decomposeFin.symm.toEmbedding :=
  (Finset.univ_map_equiv_to_embedding _).symm

section CycleRange

/-! ### `cycleRange` section

Define the permutations `Fin.cycleRange i`, the cycle `(0 1 2 ... i)`.
-/


open Equiv.Perm

-- Porting note: renamed from finRotate_succ because there is already a theorem with that name
theorem finRotate_succ_eq_decomposeFin {n : ℕ} :
    finRotate n.succ = decomposeFin.symm (1, finRotate n) := by
  ext i
  cases n; · simp
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  rw [coe_finRotate, decomposeFin_symm_apply_succ, if_congr i.succ_eq_last_succ rfl rfl]
  split_ifs with h
  · simp [h]
  · rw [Fin.val_succ, Function.Injective.map_swap Fin.val_injective, Fin.val_succ, coe_finRotate,
      if_neg h, Fin.val_zero, Fin.val_one,
      swap_apply_of_ne_of_ne (Nat.succ_ne_zero _) (Nat.succ_succ_ne_one _)]

@[simp]
theorem sign_finRotate (n : ℕ) : Perm.sign (finRotate (n + 1)) = (-1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [finRotate_succ_eq_decomposeFin]
    simp [ih, pow_succ]

@[simp]
theorem support_finRotate {n : ℕ} : support (finRotate (n + 2)) = Finset.univ := by
  ext
  simp

theorem support_finRotate_of_le {n : ℕ} (h : 2 ≤ n) : support (finRotate n) = Finset.univ := by
  obtain ⟨m, rfl⟩ := exists_add_of_le h
  rw [add_comm, support_finRotate]

theorem isCycle_finRotate {n : ℕ} : IsCycle (finRotate (n + 2)) := by
  refine ⟨0, by simp, fun x hx' => ⟨x, ?_⟩⟩
  clear hx'
  cases' x with x hx
  rw [zpow_natCast, Fin.ext_iff, Fin.val_mk]
  induction' x with x ih; · rfl
  rw [pow_succ', Perm.mul_apply, coe_finRotate_of_ne_last, ih (lt_trans x.lt_succ_self hx)]
  rw [Ne, Fin.ext_iff, ih (lt_trans x.lt_succ_self hx), Fin.val_last]
  exact ne_of_lt (Nat.lt_of_succ_lt_succ hx)

theorem isCycle_finRotate_of_le {n : ℕ} (h : 2 ≤ n) : IsCycle (finRotate n) := by
  obtain ⟨m, rfl⟩ := exists_add_of_le h
  rw [add_comm]
  exact isCycle_finRotate

@[simp]
theorem cycleType_finRotate {n : ℕ} : cycleType (finRotate (n + 2)) = {n + 2} := by
  rw [isCycle_finRotate.cycleType, support_finRotate, ← Fintype.card, Fintype.card_fin]
  rfl

theorem cycleType_finRotate_of_le {n : ℕ} (h : 2 ≤ n) : cycleType (finRotate n) = {n} := by
  obtain ⟨m, rfl⟩ := exists_add_of_le h
  rw [add_comm, cycleType_finRotate]

namespace Fin

/-- `Fin.cycleRange i` is the cycle `(0 1 2 ... i)` leaving `(i+1 ... (n-1))` unchanged. -/
def cycleRange {n : ℕ} (i : Fin n) : Perm (Fin n) :=
  (finRotate (i + 1)).extendDomain
    (Equiv.ofLeftInverse' (Fin.castLEEmb (Nat.succ_le_of_lt i.is_lt)) (↑)
      (by
        intro x
        ext
        simp))

theorem cycleRange_of_gt {n : ℕ} {i j : Fin n.succ} (h : i < j) : cycleRange i j = j := by
  rw [cycleRange, ofLeftInverse'_eq_ofInjective,
    ← Function.Embedding.toEquivRange_eq_ofInjective, ← viaFintypeEmbedding,
    viaFintypeEmbedding_apply_not_mem_range]
  simpa

theorem cycleRange_of_le {n : ℕ} {i j : Fin n.succ} (h : j ≤ i) :
    cycleRange i j = if j = i then 0 else j + 1 := by
  cases n
  · exact Subsingleton.elim (α := Fin 1) _ _  --Porting note; was `simp`
  have : j = (Fin.castLE (Nat.succ_le_of_lt i.is_lt))
    ⟨j, lt_of_le_of_lt h (Nat.lt_succ_self i)⟩ := by simp
  ext
  erw [this, cycleRange, ofLeftInverse'_eq_ofInjective, ←
    Function.Embedding.toEquivRange_eq_ofInjective, ← viaFintypeEmbedding,
    viaFintypeEmbedding_apply_image, Function.Embedding.coeFn_mk,
    coe_castLE, coe_finRotate]
  simp only [Fin.ext_iff, val_last, val_mk, val_zero, Fin.eta, castLE_mk]
  split_ifs with heq
  · rfl
  · rw [Fin.val_add_one_of_lt]
    exact lt_of_lt_of_le (lt_of_le_of_ne h (mt (congr_arg _) heq)) (le_last i)

theorem coe_cycleRange_of_le {n : ℕ} {i j : Fin n.succ} (h : j ≤ i) :
    (cycleRange i j : ℕ) = if j = i then 0 else (j : ℕ) + 1 := by
  rw [cycleRange_of_le h]
  split_ifs with h'
  · rfl
  exact
    val_add_one_of_lt
      (calc
        (j : ℕ) < i := Fin.lt_iff_val_lt_val.mp (lt_of_le_of_ne h h')
        _ ≤ n := Nat.lt_succ_iff.mp i.2)

theorem cycleRange_of_lt {n : ℕ} {i j : Fin n.succ} (h : j < i) : cycleRange i j = j + 1 := by
  rw [cycleRange_of_le h.le, if_neg h.ne]

theorem coe_cycleRange_of_lt {n : ℕ} {i j : Fin n.succ} (h : j < i) :
    (cycleRange i j : ℕ) = j + 1 := by rw [coe_cycleRange_of_le h.le, if_neg h.ne]

theorem cycleRange_of_eq {n : ℕ} {i j : Fin n.succ} (h : j = i) : cycleRange i j = 0 := by
  rw [cycleRange_of_le h.le, if_pos h]

@[simp]
theorem cycleRange_self {n : ℕ} (i : Fin n.succ) : cycleRange i i = 0 :=
  cycleRange_of_eq rfl

theorem cycleRange_apply {n : ℕ} (i j : Fin n.succ) :
    cycleRange i j = if j < i then j + 1 else if j = i then 0 else j := by
  split_ifs with h₁ h₂
  · exact cycleRange_of_lt h₁
  · exact cycleRange_of_eq h₂
  · exact cycleRange_of_gt (lt_of_le_of_ne (le_of_not_gt h₁) (Ne.symm h₂))

@[simp]
theorem cycleRange_zero (n : ℕ) : cycleRange (0 : Fin n.succ) = 1 := by
  ext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · rw [cycleRange_of_gt (Fin.succ_pos j), one_apply]

@[simp]
theorem cycleRange_last (n : ℕ) : cycleRange (last n) = finRotate (n + 1) := by
  ext i
  rw [coe_cycleRange_of_le (le_last _), coe_finRotate]

@[simp]
theorem cycleRange_zero' {n : ℕ} (h : 0 < n) : cycleRange ⟨0, h⟩ = 1 := by
  cases' n with n
  · cases h
  exact cycleRange_zero n

@[simp]
theorem sign_cycleRange {n : ℕ} (i : Fin n) : Perm.sign (cycleRange i) = (-1) ^ (i : ℕ) := by
  simp [cycleRange]

@[simp]
theorem succAbove_cycleRange {n : ℕ} (i j : Fin n) :
    i.succ.succAbove (i.cycleRange j) = swap 0 i.succ j.succ := by
  cases n
  · rcases j with ⟨_, ⟨⟩⟩
  rcases lt_trichotomy j i with (hlt | heq | hgt)
  · have : castSucc (j + 1) = j.succ := by
      ext
      rw [coe_castSucc, val_succ, Fin.val_add_one_of_lt (lt_of_lt_of_le hlt i.le_last)]
    rw [Fin.cycleRange_of_lt hlt, Fin.succAbove_of_castSucc_lt, this, swap_apply_of_ne_of_ne]
    · apply Fin.succ_ne_zero
    · exact (Fin.succ_injective _).ne hlt.ne
    · rw [Fin.lt_iff_val_lt_val]
      simpa [this] using hlt
  · rw [heq, Fin.cycleRange_self, Fin.succAbove_of_castSucc_lt, swap_apply_right, Fin.castSucc_zero]
    · rw [Fin.castSucc_zero]
      apply Fin.succ_pos
  · rw [Fin.cycleRange_of_gt hgt, Fin.succAbove_of_le_castSucc, swap_apply_of_ne_of_ne]
    · apply Fin.succ_ne_zero
    · apply (Fin.succ_injective _).ne hgt.ne.symm
    · simpa [Fin.le_iff_val_le_val] using hgt

@[simp]
theorem cycleRange_succAbove {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    i.cycleRange (i.succAbove j) = j.succ := by
  cases' lt_or_ge (castSucc j) i with h h
  · rw [Fin.succAbove_of_castSucc_lt _ _ h, Fin.cycleRange_of_lt h, Fin.coeSucc_eq_succ]
  · rw [Fin.succAbove_of_le_castSucc _ _ h, Fin.cycleRange_of_gt (Fin.le_castSucc_iff.mp h)]

@[simp]
theorem cycleRange_symm_zero {n : ℕ} (i : Fin (n + 1)) : i.cycleRange.symm 0 = i :=
  i.cycleRange.injective (by simp)

@[simp]
theorem cycleRange_symm_succ {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    i.cycleRange.symm j.succ = i.succAbove j :=
  i.cycleRange.injective (by simp)

theorem isCycle_cycleRange {n : ℕ} {i : Fin (n + 1)} (h0 : i ≠ 0) : IsCycle (cycleRange i) := by
  cases' i with i hi
  cases i
  · exact (h0 rfl).elim
  exact isCycle_finRotate.extendDomain _

@[simp]
theorem cycleType_cycleRange {n : ℕ} {i : Fin (n + 1)} (h0 : i ≠ 0) :
    cycleType (cycleRange i) = {(i + 1 : ℕ)} := by
  cases' i with i hi
  cases i
  · exact (h0 rfl).elim
  rw [cycleRange, cycleType_extendDomain]
  exact cycleType_finRotate

theorem isThreeCycle_cycleRange_two {n : ℕ} : IsThreeCycle (cycleRange 2 : Perm (Fin (n + 3))) := by
  rw [IsThreeCycle, cycleType_cycleRange] <;> simp [Fin.ext_iff]

end Fin

end CycleRange
