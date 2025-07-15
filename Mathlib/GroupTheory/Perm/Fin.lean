/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Yi Yuan
-/
import Mathlib.Data.Fin.SuccPred
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Option
import Mathlib.Logic.Equiv.Fin.Rotate

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
  · simp [Equiv.Perm.decomposeFin]
  · intro i
    by_cases h : i = e x
    · simp [h, Equiv.Perm.decomposeFin]
    · simp [Equiv.Perm.decomposeFin, swap_apply_def, Ne.symm h]

@[simp]
theorem Equiv.Perm.decomposeFin_symm_apply_one {n : ℕ} (e : Perm (Fin (n + 1))) (p : Fin (n + 2)) :
    Equiv.Perm.decomposeFin.symm (p, e) 1 = swap 0 p (e 0).succ := by
  rw [← Fin.succ_zero_eq_one, Equiv.Perm.decomposeFin_symm_apply_succ e p 0]

@[simp]
theorem Equiv.Perm.decomposeFin.symm_sign {n : ℕ} (p : Fin (n + 1)) (e : Perm (Fin n)) :
    Perm.sign (Equiv.Perm.decomposeFin.symm (p, e)) = ite (p = 0) 1 (-1) * Perm.sign e := by
  refine Fin.cases ?_ ?_ p <;> simp [Equiv.Perm.decomposeFin]

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
  obtain ⟨x, hx⟩ := x
  rw [zpow_natCast, Fin.ext_iff, Fin.val_mk]
  induction x with
  | zero => rfl
  | succ x ih =>
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

theorem cycleType_finRotate_of_le {n : ℕ} (h : 2 ≤ n) : cycleType (finRotate n) = {n} := by
  obtain ⟨m, rfl⟩ := exists_add_of_le h
  rw [add_comm, cycleType_finRotate]

namespace Fin

/-- `Fin.cycleRange i` is the cycle `(0 1 2 ... i)` leaving `(i+1 ... (n-1))` unchanged. -/
def cycleRange {n : ℕ} (i : Fin n) : Perm (Fin n) :=
  (finRotate (i + 1)).extendDomain (castLEEmb (by omega)).toEquivRange

theorem cycleRange_of_gt {n : ℕ} {i j : Fin n} (h : i < j) : cycleRange i j = j := by
  rw [cycleRange, Perm.extendDomain_apply_not_subtype]
  simpa using h

theorem cycleRange_of_le {n : ℕ} [NeZero n] {i j : Fin n} (h : j ≤ i) :
    cycleRange i j = if j = i then 0 else j + 1 := by
  have jin : j ∈ Set.range ⇑(castLEEmb (n := i + 1) (by omega)) := by
    rw [coe_castLEEmb, range_castLE, Set.mem_setOf_eq]
    omega
  have : (castLEEmb (by omega)).toEquivRange (castLT j (by omega)) = ⟨j, jin⟩ := by
    simpa only [coe_castLEEmb] using by rfl
  rw [cycleRange, (finRotate (i + 1)).extendDomain_apply_subtype (castLEEmb
    (by omega)).toEquivRange jin, Function.Embedding.toEquivRange_apply]
  split_ifs with ch
  · have : ((castLEEmb (by omega)).toEquivRange.symm ⟨j, jin⟩) = last i := by
      simpa only [coe_castLEEmb, ← this, symm_apply_apply] using eq_of_val_eq (by simp [ch])
    rw [this, finRotate_last]
    rfl
  · have hj1 : (j + 1).1 = j.1 + 1 := val_add_one_of_lt' (by omega)
    have hj2 : (j.castLT (by omega) + 1 : Fin (i + 1)).1 = (j.castLT (by omega): Fin (i + 1)) + 1 :=
      val_add_one_of_lt' (by simp [lt_of_le_of_ne h ch])
    exact eq_of_val_eq (by simp [← this, hj1, hj2])

theorem coe_cycleRange_of_le {n : ℕ} {i j : Fin n} (h : j ≤ i) :
    (cycleRange i j : ℕ) = if j = i then 0 else (j : ℕ) + 1 := by
  rcases n with - | n
  · exact absurd le_rfl i.pos.not_ge
  rw [cycleRange_of_le h]
  split_ifs with h'
  · rfl
  exact
    val_add_one_of_lt
      (calc
        (j : ℕ) < i := Fin.lt_iff_val_lt_val.mp (lt_of_le_of_ne h h')
        _ ≤ n := Nat.lt_succ_iff.mp i.2)

theorem cycleRange_of_lt {n : ℕ} [NeZero n] {i j : Fin n} (h : j < i) : cycleRange i j = j + 1 := by
  rw [cycleRange_of_le h.le, if_neg h.ne]

theorem coe_cycleRange_of_lt {n : ℕ} {i j : Fin n} (h : j < i) :
    (cycleRange i j : ℕ) = j + 1 := by rw [coe_cycleRange_of_le h.le, if_neg h.ne]

theorem cycleRange_of_eq {n : ℕ} [NeZero n] {i j : Fin n} (h : j = i) : cycleRange i j = 0 := by
  rw [cycleRange_of_le h.le, if_pos h]

@[simp]
theorem cycleRange_self {n : ℕ} [NeZero n] (i : Fin n) : cycleRange i i = 0 :=
  cycleRange_of_eq rfl

theorem cycleRange_apply {n : ℕ} [NeZero n] (i j : Fin n) :
    cycleRange i j = if j < i then j + 1 else if j = i then 0 else j := by
  split_ifs with h₁ h₂
  · exact cycleRange_of_lt h₁
  · exact cycleRange_of_eq h₂
  · exact cycleRange_of_gt (lt_of_le_of_ne (le_of_not_gt h₁) (Ne.symm h₂))

@[simp]
theorem cycleRange_zero (n : ℕ) [NeZero n] : cycleRange (0 : Fin n) = 1 := by
  ext j
  rcases (Fin.zero_le j).eq_or_lt with rfl | hj
  · simp
  · rw [cycleRange_of_gt hj, one_apply]

@[simp]
theorem cycleRange_last (n : ℕ) : cycleRange (last n) = finRotate (n + 1) := by
  ext i
  rw [coe_cycleRange_of_le (le_last _), coe_finRotate]

@[simp]
theorem cycleRange_mk_zero {n : ℕ} (h : 0 < n) : cycleRange ⟨0, h⟩ = 1 :=
  have : NeZero n := .of_pos h
  cycleRange_zero n

@[deprecated (since := "2025-01-28")]
alias cycleRange_zero' := cycleRange_mk_zero

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
  rcases lt_or_ge (castSucc j) i with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ h, Fin.cycleRange_of_lt h, Fin.coeSucc_eq_succ]
  · rw [Fin.succAbove_of_le_castSucc _ _ h, Fin.cycleRange_of_gt (Fin.le_castSucc_iff.mp h)]

@[simp]
theorem cycleRange_symm_zero {n : ℕ} [NeZero n] (i : Fin n) : i.cycleRange.symm 0 = i :=
  i.cycleRange.injective (by simp)

@[simp]
theorem cycleRange_symm_succ {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    i.cycleRange.symm j.succ = i.succAbove j :=
  i.cycleRange.injective (by simp)

@[simp]
theorem insertNth_apply_cycleRange_symm {n : ℕ} {α : Type*} (p : Fin (n + 1)) (a : α)
    (x : Fin n → α) (j : Fin (n + 1)) :
    (p.insertNth a x : _ → α) (p.cycleRange.symm j) = (Fin.cons a x : _ → α) j := by
  cases j using Fin.cases <;> simp

@[simp]
theorem insertNth_comp_cycleRange_symm {n : ℕ} {α : Type*} (p : Fin (n + 1)) (a : α)
    (x : Fin n → α) : (p.insertNth a x ∘ p.cycleRange.symm : _ → α) = Fin.cons a x := by
  ext j
  simp

@[simp]
theorem cons_apply_cycleRange {n : ℕ} {α : Type*} (a : α) (x : Fin n → α)
    (p : Fin (n + 1)) (j : Fin (n + 1)) :
    (Fin.cons a x : _ → α) (p.cycleRange j) = (p.insertNth a x : _ → α) j := by
  rw [← insertNth_apply_cycleRange_symm, Equiv.symm_apply_apply]

@[simp]
theorem cons_comp_cycleRange {n : ℕ} {α : Type*} (a : α) (x : Fin n → α) (p : Fin (n + 1)) :
    (Fin.cons a x : _ → α) ∘ p.cycleRange = p.insertNth a x := by
  ext; simp

theorem isCycle_cycleRange {n : ℕ} [NeZero n] {i : Fin n} (h0 : i ≠ 0) :
    IsCycle (cycleRange i) := by
  obtain ⟨i, hi⟩ := i
  cases i
  · exact (h0 rfl).elim
  exact isCycle_finRotate.extendDomain _

@[simp]
theorem cycleType_cycleRange {n : ℕ} [NeZero n] {i : Fin n} (h0 : i ≠ 0) :
    cycleType (cycleRange i) = {(i + 1 : ℕ)} := by
  obtain ⟨i, hi⟩ := i
  cases i
  · exact (h0 rfl).elim
  rw [cycleRange, cycleType_extendDomain]
  exact cycleType_finRotate

theorem isThreeCycle_cycleRange_two {n : ℕ} : IsThreeCycle (cycleRange 2 : Perm (Fin (n + 3))) := by
  rw [IsThreeCycle, cycleType_cycleRange two_ne_zero]
  simp

end Fin

end CycleRange

section cycleIcc

/-! ### `cycleIcc` section

* Define the permutation `cycleIcc i j`, which is the cycle `(i i+1 .... j)` leaving
`(0 ... i-1)` and `(j+1 ... n-1)` unchanged when `i ≤ j` and returns the dummy value identity when
`i > j`. In other words, it rotates elements in `[i, j]` one step to the right.
-/

namespace Fin

local instance {n : ℕ} {i : Fin n} : NeZero (n - i) := NeZero.of_pos (by omega)

variable {n : ℕ} {i j k : Fin n}

/-- `cycleIcc i j` is the cycle `(i i+1 .... j)` leaving `(0 ... i-1)` and `(j+1 ... n-1)`
unchanged when `i ≤ j` and returns the dummy value identity when `i > j`.
In other words, it rotates elements in `[i, j]` one step to the right.
-/
def cycleIcc (i j : Fin n) : Perm (Fin n) := if hij : i ≤ j then (cycleRange ((j - i).castLT
  (sub_val_lt_sub hij))).extendDomain (natAdd_castLEEmb (Nat.sub_le n i)).toEquivRange
  else Equiv.refl (Fin n)

theorem cycleIcc_of_lt (hij : i ≤ j) (h : k < i) : (cycleIcc i j) k = k := by
  simpa [cycleIcc, hij] using Perm.extendDomain_apply_not_subtype _ _ (by
    rw [range_natAdd_castLEEmb, Set.mem_setOf_eq, not_le]; omega)

private lemma cycleIcc_aux (hij : i ≤ j) (kin : k ∈ Set.range ⇑(natAdd_castLEEmb (Nat.sub_le n i)))
    : (cycleIcc i j) k = (natAdd_castLEEmb (Nat.sub_le n i)) (((j - i).castLT
    (sub_val_lt_sub hij)).cycleRange ((natAdd_castLEEmb (Nat.sub_le n i)).toEquivRange.symm
    ⟨k, kin⟩)) := by
  simp [cycleIcc, hij, ((j - i).castLT (sub_val_lt_sub hij)).cycleRange.extendDomain_apply_subtype
    (natAdd_castLEEmb _).toEquivRange kin]

private lemma cycleIcc_simp_lemma (h : i ≤ k) (kin : k ∈ Set.range ⇑(natAdd_castLEEmb
    (Nat.sub_le n i))) : (((addNatEmb (n - (n - i.1))).trans
    (finCongr _).toEmbedding).toEquivRange.symm ⟨k, kin⟩) = subNat i.1 (k.cast (by omega))
    (by simp [h]) := by
  simpa [symm_apply_eq] using eq_of_val_eq (by simp only [coe_cast, coe_addNat, coe_subNat]; omega)

theorem cycleIcc_of_gt (hij : i ≤ j) (h : j < k) : (cycleIcc i j) k = k := by
  have kin : k ∈ Set.range ⇑(natAdd_castLEEmb (Nat.sub_le n i)) := by
    rw [range_natAdd_castLEEmb, Set.mem_setOf_eq]
    omega
  have : (((j - i).castLT (sub_val_lt_sub hij)).cycleRange (((addNatEmb
      (n - (n - i.1))).trans (finCongr _).toEmbedding).toEquivRange.symm ⟨k, kin⟩))
      = subNat i.1 (k.cast (by omega)) (by simp [le_of_lt (lt_of_le_of_lt hij h)]) := by
    rw [cycleIcc_simp_lemma (le_of_lt (lt_of_le_of_lt hij h)), cycleRange_of_gt]
    exact lt_def.mpr (by rw [coe_castLT, sub_val_of_le hij, coe_subNat, coe_cast]; omega)
  simpa only [cycleIcc_aux hij kin, natAdd_castLEEmb, this] using eq_of_val_eq (by
    simp only [Function.Embedding.trans_apply, addNatEmb_apply, coe_toEmbedding, finCongr_apply,
      coe_cast, coe_addNat, coe_subNat]; omega)

theorem cycleIcc_of (h1 : i ≤ k) (h2 : k ≤ j) [NeZero n] :
    (cycleIcc i j) k = if k = j then i else k + 1 := by
  have hij : i ≤ j := le_trans h1 h2
  have kin : k ∈ Set.range ⇑(natAdd_castLEEmb (Nat.sub_le n i)) := by
    rw [range_natAdd_castLEEmb, Set.mem_setOf_eq]
    omega
  simp only [cycleIcc_aux hij kin, natAdd_castLEEmb, cycleIcc_simp_lemma h1,
    Function.Embedding.trans_apply, addNatEmb_apply, coe_toEmbedding, finCongr_apply]
  refine eq_of_val_eq ?_
  split_ifs with h3
  · have h : subNat i.1 (j.cast (by omega)) (by simp [hij]) = (j - i).castLT (sub_val_lt_sub hij) :=
      eq_of_val_eq (by simp [subNat, coe_castLT, sub_val_of_le hij])
    simpa [h3, cycleRange_of_eq h] using by omega
  · have h : subNat i.1 (k.cast (by omega)) (by simp [h1]) < (j - i).castLT (sub_val_lt_sub hij) :=
      by simp only [subNat, coe_cast, lt_iff_val_lt_val, coe_castLT, sub_val_of_le hij]; omega
    rw [cycleRange_of_lt h, subNat]
    simp only [coe_cast, add_def, val_one', Nat.add_mod_mod, addNat_mk, cast_mk]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

theorem cycleIcc_of_ge_and_lt (h1 : i ≤ k) (h2 : k < j) [NeZero n] : (cycleIcc i j) k = k + 1 := by
  simp [cycleIcc_of h1 (le_of_lt h2), Fin.ne_of_lt h2]

@[simp]
theorem cycleIcc_of_last (hij : i ≤ j) [NeZero n] : (cycleIcc i j) j = i := by
  simp [cycleIcc_of hij (ge_of_eq rfl)]

theorem cycleIcc_of_trivial (hijk : k < i ∨ j < k) : (cycleIcc i j) k = k := by
  rcases Decidable.em (i ≤ j) with hij | hij
  · exact Or.casesOn hijk (fun hki ↦ cycleIcc_of_lt hij hki) fun hjk ↦ cycleIcc_of_gt hij hjk
  · simp [cycleIcc, hij]

@[simp]
theorem sign_cycleIcc (hij : i ≤ j) : Perm.sign (cycleIcc i j) = (-1) ^ (j - i : ℕ) := by
  simp [cycleIcc, hij, sub_val_of_le hij]

theorem isCycle_cycleIcc (hij : i < j) : (cycleIcc i j).IsCycle := by
  simpa [cycleIcc, le_of_lt hij] using Equiv.Perm.IsCycle.extendDomain
    (natAdd_castLEEmb _).toEquivRange (isCycle_cycleRange (castLT_sub_nezero hij))

theorem cycleType_cycleIcc (hij : i < j) : Perm.cycleType (cycleIcc i j) = {(j - i + 1: ℕ)} := by
  simpa [cycleIcc, le_of_lt hij, cycleType_cycleRange (castLT_sub_nezero hij)] using
    sub_val_of_le (le_of_lt hij)

theorem cycleIcc_zero_eq_cycleRange (i : Fin n) [NeZero n] : cycleIcc 0 i = cycleRange i := by
  ext x
  rcases lt_trichotomy x i with ch | ch | ch
  · simp [cycleIcc_of_ge_and_lt (zero_le x) ch, cycleRange_of_lt ch]
  · simp [ch]
  · simp [cycleIcc_of_gt (zero_le i) ch, cycleRange_of_gt ch]

theorem cycleIcc.trans [NeZero n] (hij : i ≤ j) (hjk : j ≤ k) :
    (cycleIcc i j) ∘ (cycleIcc j k) = (cycleIcc i k) := by
  ext x
  rcases lt_or_ge x i with ch | ch
  · simp [cycleIcc_of_lt hjk (lt_of_lt_of_le ch hij), cycleIcc_of_lt hij ch,
      cycleIcc_of_lt (le_trans hij hjk) ch]
  rcases lt_or_ge k x with ch | ch1
  · simp [cycleIcc_of_gt hjk ch, cycleIcc_of_gt hij (lt_of_le_of_lt hjk ch),
      cycleIcc_of_gt ((le_trans hij hjk)) ch]
  rcases lt_or_ge x j with ch2 | ch2
  · simp [cycleIcc_of_lt hjk ch2, cycleIcc_of ch ch1, cycleIcc_of ch (le_of_lt ch2)]
    split_ifs
    repeat omega
  · simp [cycleIcc_of ch2 ch1, cycleIcc_of ch ch1]
    split_ifs with h
    · exact val_eq_of_eq (cycleIcc_of_last hij)
    · simp [cycleIcc_of_gt hij (lt_of_le_of_lt ch2 (lt_add_one_of_succ_lt (by omega)))]

end Fin

end cycleIcc

section Sign

variable {n : ℕ}

theorem Equiv.Perm.sign_eq_prod_prod_Iio (σ : Equiv.Perm (Fin n)) :
    σ.sign = ∏ j, ∏ i ∈ Finset.Iio j, (if σ i < σ j then 1 else -1) := by
  suffices h : σ.sign = σ.signAux by
    rw [h, Finset.prod_sigma', Equiv.Perm.signAux]
    convert rfl using 2 with x hx
    · simp [Finset.ext_iff, Equiv.Perm.mem_finPairsLT]
    simp [← ite_not (p := _ ≤ _)]
  refine σ.swap_induction_on (by simp) fun π i j hne h_eq ↦ ?_
  rw [Equiv.Perm.signAux_mul, Equiv.Perm.sign_mul, h_eq, Equiv.Perm.sign_swap hne,
    Equiv.Perm.signAux_swap hne]

theorem Equiv.Perm.sign_eq_prod_prod_Ioi (σ : Equiv.Perm (Fin n)) :
    σ.sign = ∏ i, ∏ j ∈ Finset.Ioi i, (if σ i < σ j then 1 else -1) := by
  rw [σ.sign_eq_prod_prod_Iio]
  apply Finset.prod_comm' (by simp)

theorem Equiv.Perm.prod_Iio_comp_eq_sign_mul_prod {R : Type*} [CommRing R]
    (σ : Equiv.Perm (Fin n)) {f : Fin n → Fin n → R} (hf : ∀ i j, f i j = -f j i) :
    ∏ j, ∏ i ∈ Finset.Iio j, f (σ i) (σ j) = σ.sign * ∏ j, ∏ i ∈ Finset.Iio j, f i j := by
  simp_rw [← σ.sign_inv, σ⁻¹.sign_eq_prod_prod_Iio, Finset.prod_sigma', Units.coe_prod,
    Int.cast_prod, ← Finset.prod_mul_distrib]
  set D := (Finset.univ : Finset (Fin n)).sigma Finset.Iio with hD
  have hφD : D.image (fun x ↦ ⟨σ x.1 ⊔ σ x.2, σ x.1 ⊓ σ x.2⟩) = D := by
    ext ⟨x1, x2⟩
    suffices (∃ a, ∃ b < a, σ a ⊔ σ b = x1 ∧ σ a ⊓ σ b = x2) ↔ x2 < x1 by simpa [hD]
    refine ⟨?_, fun hlt ↦ ?_⟩
    · rintro ⟨i, j, hij, rfl, rfl⟩
      exact inf_le_sup.lt_of_ne <| by simp [hij.ne.symm]
    obtain hlt' | hle := lt_or_ge (σ.symm x1) (σ.symm x2)
    · exact ⟨_, _, hlt', by simp [hlt.le]⟩
    exact ⟨_, _, hle.lt_of_ne (by simp [hlt.ne]), by simp [hlt.le]⟩
  nth_rw 2 [← hφD]
  rw [Finset.prod_image fun x hx y hy ↦ Finset.injOn_of_card_image_eq (by rw [hφD]) hx hy]
  refine Finset.prod_congr rfl fun ⟨x₁, x₂⟩ hx ↦ ?_
  replace hx : x₂ < x₁ := by simpa [hD] using hx
  obtain hlt | hle := lt_or_ge (σ x₁) (σ x₂)
  · simp [inf_eq_left.2 hlt.le, sup_eq_right.2 hlt.le, hx.not_gt, ← hf]
  simp [inf_eq_right.2 hle, sup_eq_left.2 hle, hx]

theorem Equiv.Perm.prod_Ioi_comp_eq_sign_mul_prod {R : Type*} [CommRing R]
    (σ : Equiv.Perm (Fin n)) {f : Fin n → Fin n → R} (hf : ∀ i j, f i j = -f j i) :
    ∏ i, ∏ j ∈ Finset.Ioi i, f (σ i) (σ j) = σ.sign * ∏ i, ∏ j ∈ Finset.Ioi i, f i j := by
  convert σ.prod_Iio_comp_eq_sign_mul_prod hf using 1
  · apply Finset.prod_comm' (by simp)
  convert rfl using 2
  apply Finset.prod_comm' (by simp)

end Sign
