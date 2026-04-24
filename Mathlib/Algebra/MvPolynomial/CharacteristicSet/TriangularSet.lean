/-
Copyright (c) 2026 Yuxuan Xiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxuan Xiao
-/
module

public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Data.DFinsupp.WellFounded
public import Mathlib.Data.Fintype.WithTopBot

/-!
# Triangular Set

This file defines the structure of a **Triangular Set** of multivariate polynomials.
A Triangular Set is a finite ordered sequence of non-zero polynomials `[P₁, P₂, ..., Pₘ]`
such that their main (max) variables are strictly increasing:
`mainVar(P₁) < mainVar(P₂) < ... < mainVar(Pₘ)`.

## Main Definitions

* `TriangularSet`: The structure definition.
  It bundles the list, the proofs of non-zero elements and ascending main variables.

## Main Results

* `TriangularSet.takeConcat_lt_of_reducedToSet`: Appending a reduced element
  strictly decreases the order, used to prove termination of basic set algorithms.

-/

@[expose] public section

open MvPolynomial

/-- A Triangular Set is a list of polynomials with strictly increasing main variables. -/
structure TriangularSet (σ R : Type*) [CommSemiring R] [LinearOrder σ] where
  /-- The underlying list of non-zero polynomials -/
  toList : List (MvPolynomial σ R)
  /-- No polynomial in the list is zero -/
  zero_notMem' : 0 ∉ toList
  /-- The main variables of successive polynomials are strictly increasing -/
  isChain_max_vars' : toList.IsChain (·.vars.max < ·.vars.max)

namespace TriangularSet

variable {R σ : Type*} [CommSemiring R] [LinearOrder σ]
variable {S T : TriangularSet σ R} {p : MvPolynomial σ R} {m n : ℕ}

/-- Construct an triangular set from a list. -/
def mk' {l : List (MvPolynomial σ R)} (hl1 : 0 ∉ l)
    (hl2 : l.IsChain (·.vars.max < ·.vars.max)) : TriangularSet σ R where
  toList := l
  zero_notMem' := hl1
  isChain_max_vars' := hl2

noncomputable instance instFunLike : FunLike (TriangularSet σ R) ℕ (MvPolynomial σ R) where
  coe S n := S.toList[n]?.getD 0
  coe_injective' := by
    rintro ⟨ls, hs1, hs2⟩ ⟨lt, ht1, ht2⟩ h
    congr
    apply List.ext_getElem? fun n ↦ ?_
    have h : ls[n]?.getD 0 = lt[n]?.getD 0 := congrFun h n
    grind

@[ext]
theorem ext (h : ∀ i, S i = T i) : S = T := DFunLike.ext _ _ h

/-- The length of the triangular set. -/
def length (S : TriangularSet σ R) : ℕ := S.toList.length

theorem ne_zero_iff_lt_length : n < S.length ↔ S n ≠ 0 := by
  change n < S.toList.length ↔ S.toList[n]?.getD 0 ≠ 0
  refine ⟨fun h ↦ ?_, fun h ↦ by grind⟩
  have : S.toList[n]?.isSome := by aesop
  rcases Option.isSome_iff_exists.mp this with ⟨p, hp⟩
  suffices p ≠ 0 from hp ▸ this
  intro hp2
  absurd hp2 ▸ S.zero_notMem'
  exact List.mem_of_getElem? hp

theorem eq_zero_iff_length_le : S.length ≤ n ↔ S n = 0 :=
  not_iff_not.mp <| Iff.trans Nat.not_le ne_zero_iff_lt_length

theorem ext' (h1 : S.length = T.length) (h2 : ∀ i < S.length, S i = T i) : S = T := ext fun i ↦ by
  if h : i < S.length then exact h2 i h
  else
    have h := le_of_not_gt h
    rw [eq_zero_iff_length_le.mp h, eq_zero_iff_length_le.mp <| h1 ▸ h]

@[simp] theorem apply_length_eq_zero : S S.length = 0 := eq_zero_iff_length_le.mp (le_refl _)

theorem toList_getElem?_getD : S.toList[n]?.getD 0 = S n := rfl

theorem toList_getElem {n : ℕ} (h : n < S.length) : S.toList[n] = S n := by
  rw [← toList_getElem?_getD]
  change n < S.toList.length at h
  aesop

@[simp] theorem length_toList (S : TriangularSet σ R) : S.toList.length = S.length := rfl

@[simp] theorem toList_eq_iff_eq : S.toList = T.toList ↔ S = T := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  cases S; cases T
  congr

theorem mem_toList_iff' : p ∈ S.toList ↔ ∃ n < S.length, S n = p := by
  rw [List.mem_iff_getElem]
  constructor
  repeat'
  rintro ⟨n, hn1, hn2⟩
  use n, hn1
  exact toList_getElem hn1 ▸ hn2

theorem zero_notMem_toList (S : TriangularSet σ R) : 0 ∉ S.toList := S.zero_notMem'

theorem toList_non_zero (S : TriangularSet σ R) : ∀ ⦃p⦄, p ∈ S.toList → p ≠ 0 := fun _ hp ↦ by
  have := zero_notMem_toList S
  exact ne_of_mem_of_not_mem hp this

theorem toList_isChain (S : TriangularSet σ R) : S.toList.IsChain (·.vars.max < ·.vars.max) :=
  S.isChain_max_vars'

theorem toList_pairwise (S : TriangularSet σ R) : S.toList.Pairwise (·.vars.max < ·.vars.max) := by
  apply (@List.isChain_iff_pairwise _ _ _ ?_).mp S.toList_isChain
  apply Trans.mk
  intro p q r hpq hqr
  exact lt_trans hpq hqr

instance [DecidableEq (MvPolynomial σ R)] : DecidableEq (TriangularSet σ R) :=
  fun _ _ ↦ decidable_of_iff _ toList_eq_iff_eq

theorem max_vars_lt_next (h : n < S.length - 1) : (S n).vars.max < (S (n + 1)).vars.max := by
  have hn : n < S.length := Nat.lt_of_lt_pred h
  have hn1 : n + 1 < S.length := Nat.add_lt_of_lt_sub h
  rw [← toList_getElem hn, ← toList_getElem hn1]
  exact List.isChain_iff_getElem.mp S.toList_isChain n hn1

theorem max_vars_lt_next' :
    n + 1 < S.length → (S n).vars.max < (S (n + 1)).vars.max :=
  fun h ↦ max_vars_lt_next <| Nat.lt_sub_of_add_lt h

theorem max_vars_lt_next'' :
    0 < n → n < S.length → (S (n - 1)).vars.max < (S n).vars.max := fun h1 h2 ↦
  have : n - 1 < S.length - 1 := Nat.sub_lt_sub_right h1 h2
  Nat.sub_add_cancel h1 ▸ max_vars_lt_next this

theorem max_vars_lt_of_index_lt (h : n < S.length) :
    m < n → (S m).vars.max < (S n).vars.max := fun hmn ↦ by
  induction n with
  | zero => exact absurd hmn <| Nat.not_lt_zero m
  | succ n hn => match Nat.lt_succ_iff_lt_or_eq.mp hmn with
    | Or.inl hmn =>
      exact lt_trans (hn (Nat.lt_of_succ_lt h) hmn) <| max_vars_lt_next' h
    | Or.inr hmn => rw [hmn]; exact max_vars_lt_next' h

theorem index_lt_of_max_vars_lt (h : m < S.length) :
    (S m).vars.max < (S n).vars.max → m < n := fun hs ↦
  Decidable.byContradiction fun hmn ↦ False.elim <| match Nat.eq_or_lt_of_not_lt hmn with
    | Or.inl hmn => Eq.not_lt (congrArg (fun i ↦ (S i).vars.max) hmn) hs
    | Or.inr hmn => (not_lt.mpr <| le_of_lt hs) (max_vars_lt_of_index_lt h hmn)

theorem false_of_max_vars_ge_of_index_lt :
    m < n → n < S.length → (S n).vars.max ≤ (S m).vars.max → False :=
  fun h1 h2 h3 ↦ absurd h3 <| not_le_of_gt <| max_vars_lt_of_index_lt h2 h1

theorem max_vars_le_of_index_le :
    m ≤ n → n < S.length → (S m).vars.max ≤ (S n).vars.max := fun hmn h ↦
  Or.elim (lt_or_eq_of_le hmn)
    (fun hmn ↦ le_of_lt <| max_vars_lt_of_index_lt h hmn)
    (fun hmn ↦ by simp only [hmn, le_refl])

theorem index_eq_of_max_vars_eq :
    m < S.length → n < S.length → (S m).vars.max = (S n).vars.max → m = n :=
  fun hm hn hc ↦ Decidable.byContradiction fun con ↦ by
    match Nat.lt_or_gt_of_ne con with
    | Or.inl con => exact absurd hc <| ne_of_lt <| max_vars_lt_of_index_lt hn con
    | Or.inr con => exact absurd hc.symm <| ne_of_lt <| max_vars_lt_of_index_lt hm con

theorem index_eq_of_apply_eq : m < S.length → n < S.length → S m = S n → m = n :=
  fun hm hn hc ↦ index_eq_of_max_vars_eq hm hn (congrArg (·.vars.max) hc)

theorem index_eq_zero_of_max_vars_eq_bot :
    n < S.length → (S n).vars.max = ⊥ → n = 0 := fun h1 h2 ↦
  Decidable.byContradiction fun hn ↦
    WithBot.not_lt_bot _ (h2 ▸ max_vars_lt_next'' (Nat.zero_lt_of_ne_zero hn) h1)

theorem exists_index_max_vars_between_of_max_vars_first_lt
    (h : (S 0).vars.max < p.vars.max) : ∃ k ≤ S.length,
    (S (k - 1)).vars.max < p.vars.max ∧
    (p.vars.max ≤ (S k).vars.max ∨ k = S.length) := by
  by_contra con
  simp only [not_exists, not_and, not_or, not_le] at con
  have : ∀ k ≤ S.length, (S k).vars.max < p.vars.max := fun k hk ↦ by
    induction k with
    | zero => exact h
    | succ k hk' => exact (con (k + 1) hk <| hk' <| Nat.le_of_succ_le hk).1
  have con := con S.length <| le_refl S.length
  have := this (S.length - 1) <| Nat.sub_le S.length 1
  exact (con this).2 rfl

theorem toList_nodup (S : TriangularSet σ R) : S.toList.Nodup := by
  refine List.nodup_iff_injective_getElem.mpr ?_
  intro ⟨i, hi⟩ ⟨j, hj⟩ (h : S.toList[i] = S.toList[j])
  rw [toList_getElem, toList_getElem] at h
  exact (Fin.mk.injEq ..) ▸ index_eq_of_apply_eq hi hj h

/-! ### Set-like behavior -/

instance instSetLike : SetLike (TriangularSet σ R) (MvPolynomial σ R) where
  coe := fun S ↦ {p | ∃ n < S.length, S n = p}
  coe_injective' := by
    intro S T (h : (fun p ↦ ∃ n < S.length, S n = p) = (fun p ↦ ∃ n < T.length, T n = p))
    have h (p : MvPolynomial σ R) : p ∈ S.toList ↔ p ∈ T.toList := by
      rw [mem_toList_iff', mem_toList_iff']
      exact Iff.of_eq (congrFun h p)
    rw [← toList_eq_iff_eq]
    exact List.Perm.eq_of_pairwise
      (fun _ _ _ _ h1 h2 ↦ absurd h2 <| Std.not_gt_of_lt h1)
      S.toList_pairwise T.toList_pairwise
      ((List.perm_ext_iff_of_nodup S.toList_nodup T.toList_nodup).mpr h)

theorem mem_def : p ∈ S ↔ ∃ n < S.length, S n = p := Eq.to_iff rfl

@[simp] theorem mem_toList_iff : p ∈ S.toList ↔ p ∈ S := mem_toList_iff'

@[simp] theorem zero_notMem (S : TriangularSet σ R) : 0 ∉ S := fun h ↦
  absurd (mem_toList_iff.mpr h) S.zero_notMem_toList

theorem ne_zero_of_mem : p ∈ S → p ≠ 0 := fun h1 h2 ↦ (h2 ▸ zero_notMem S) h1

theorem apply_mem {n : ℕ} : n < S.length → S n ∈ S := fun h ↦ ⟨n, h, rfl⟩

theorem forall_mem_iff_forall_index {S : TriangularSet σ R} {a : MvPolynomial σ R → Prop} :
    (∀ p ∈ S, a p) ↔ ∀ i < S.length, a (S i) := Set.forall_mem_image

theorem forall_mem_iff_forall_index' {S : TriangularSet σ R} {a : MvPolynomial σ R → Prop} {n : ℕ}
    (h : n = S.length) : (∀ p ∈ S, a p) ↔ ∀ i : Fin n, a (S i) :=
  Iff.trans forall_mem_iff_forall_index (by rw [Fin.forall_iff, h])

theorem exists_mem_iff_exists_index {S : TriangularSet σ R} {a : MvPolynomial σ R → Prop} :
    (∃ p ∈ S, a p) ↔ ∃ i < S.length, a (S i) := Set.exists_mem_image

theorem exists_mem_iff_exists_index' {S : TriangularSet σ R} {a : MvPolynomial σ R → Prop} {n : ℕ}
    (h : n = S.length) : (∃ p ∈ S, a p) ↔ ∃ i : Fin n, a (S i) :=
  Iff.trans exists_mem_iff_exists_index (by simp only [Fin.exists_iff, h, exists_prop])

instance : HasSubset (TriangularSet σ R) where
  Subset S T := ∀ ⦃x⦄, x ∈ S → x ∈ T

instance : HasSSubset (TriangularSet σ R) where
  SSubset S T := S ⊆ T ∧ ¬T ⊆ S

@[simp] theorem Subset.refl (S : TriangularSet σ R) : S ⊆ S := fun _ ↦ id

theorem Subset.trans {U : TriangularSet σ R} : S ⊆ T → T ⊆ U → S ⊆ U :=
  fun h₁ h₂ _ m => h₂ (h₁ m)

theorem subset_def : S ⊆ T ↔ ∀ ⦃x⦄, x ∈ S → x ∈ T := Iff.rfl

theorem mem_of_subset (p : MvPolynomial σ R) (h : S ⊆ T) : p ∈ S → p ∈ T := @h _

theorem ssubset_def : S ⊂ T ↔ S ⊆ T ∧ ¬T ⊆ S := Iff.rfl

/-- Converts a triangular set to a finite set. -/
def toFinset (S : TriangularSet σ R) : Finset (MvPolynomial σ R) :=
  (@Finset.univ (Fin S.length) _).map
    ⟨fun i ↦ S.toList[i], List.nodup_iff_injective_getElem.mp S.toList_nodup⟩

@[simp] theorem card_toFinset (S : TriangularSet σ R) : S.toFinset.card = S.length := by
  simp [toFinset]

@[simp] theorem mem_toFinset_iff : p ∈ S.toFinset ↔ p ∈ S := by
  refine Iff.trans ?_ SetLike.mem_coe
  simp [toFinset, SetLike.coe, Fin.exists_iff, toList_getElem]

@[simp] theorem toFinset_eq_iff_eq : S.toFinset = T.toFinset ↔ S = T := by
  refine ⟨fun h ↦ SetLike.ext fun p ↦ ?_, congrArg _⟩
  rw [← mem_toFinset_iff, ← mem_toFinset_iff]
  aesop

theorem toFinset_eq_coe_set (S : TriangularSet σ R) : S.toFinset = (S : Set (MvPolynomial σ R)) :=
  Set.ext fun _ ↦ ⟨SetLike.mem_coe.mpr ∘ mem_toFinset_iff.mp, mem_toFinset_iff.mpr⟩

theorem length_le_of_subset : S ⊆ T → S.length ≤ T.length := fun h ↦ by
  rw [← card_toFinset, ← card_toFinset]
  exact Finset.card_le_card <| Finset.coe_subset.mp (by simpa [toFinset_eq_coe_set] using h)

theorem length_lt_of_ssubset : S ⊂ T → S.length < T.length := fun h ↦ by
  rw [← card_toFinset, ← card_toFinset]
  exact Finset.card_lt_card <| Finset.coe_ssubset.mp (by simpa [toFinset_eq_coe_set] using h)



/-- The empty triangular set. -/
protected def empty : TriangularSet σ R where
  toList := []
  zero_notMem' := List.not_mem_nil
  isChain_max_vars' := List.IsChain.nil

instance : EmptyCollection (TriangularSet σ R) := ⟨.empty⟩

instance : Inhabited (TriangularSet σ R) := ⟨∅⟩

theorem empty_eq_default : (∅ : TriangularSet σ R) = default := rfl

@[simp] theorem toList_empty : (∅ : TriangularSet σ R).toList = [] := rfl

@[simp] theorem length_empty : (∅ : TriangularSet σ R).length = 0 := rfl

@[simp] theorem empty_apply : (∅ : TriangularSet σ R) n = 0 := rfl

theorem length_eq_zero_iff : S.length = 0 ↔ S = ∅ :=
  ⟨fun h ↦ ext fun i ↦ eq_zero_iff_length_le.mp <| h ▸ Nat.zero_le i, fun h ↦ h ▸ length_empty⟩

theorem length_gt_zero_iff : 0 < S.length ↔ S ≠ ∅ :=
  iff_not_comm.mp <| Iff.trans length_eq_zero_iff.symm
    ⟨fun h ↦ h ▸ Nat.not_add_one_le_zero 0, Nat.eq_zero_of_not_pos⟩

theorem length_ge_one_iff : 1 ≤ S.length ↔ S ≠ ∅ := length_gt_zero_iff

theorem notMem_empty (p : MvPolynomial σ R) : p ∉ (∅ : TriangularSet σ R) := fun h ↦
  Nat.not_succ_le_zero _ (Exists.choose_spec h).1

theorem eq_empty_of_forall_notMem : (∀ p, p ∉ S) → S = ∅ := fun h ↦ by
  contrapose! h
  exact ⟨S 0, apply_mem <| length_gt_zero_iff.mpr h⟩

/-- A triangular set with exactly one non-zero element. -/
def single' (hp : p ≠ 0) : TriangularSet σ R where
  toList := [p]
  zero_notMem' := by simpa only [List.mem_cons, List.not_mem_nil, or_false, ne_eq] using hp.symm
  isChain_max_vars' := List.IsChain.singleton p

theorem toList_single' (hp : p ≠ 0) : (single' hp).toList = [p] := rfl

theorem single'_apply (hp : p ≠ 0) :
    (single' hp) n = if n = 0 then p else 0 := by
  rw [← toList_getElem?_getD, toList_single' hp, List.getElem?_singleton]
  apply apply_ite_left

theorem length_single' (hp : p ≠ 0) : (single' hp).length = 1 := rfl

/-- Takes the first `n` elements of a triangular set. -/
def take (S : TriangularSet σ R) (n : ℕ) : TriangularSet σ R where
  toList := S.toList.take n
  zero_notMem' := fun h ↦ absurd (List.mem_of_mem_take h) S.zero_notMem_toList
  isChain_max_vars' := List.IsChain.take S.toList_isChain n

theorem toList_take (S : TriangularSet σ R) (n : ℕ) : (S.take n).toList = S.toList.take n := rfl

@[simp]
theorem length_take (S : TriangularSet σ R) (n : ℕ) : (S.take n).length = n ⊓ S.length :=
  List.length_take

theorem take_apply (S : TriangularSet σ R) (n m : ℕ) :
    (S.take n) m = if m < n then S m else 0 := by
  rw [← toList_getElem?_getD, toList_take, List.getElem?_take]
  apply apply_ite_left

theorem take_apply' {S : TriangularSet σ R} {n m : ℕ} (h : m < n ⊓ S.length) :
    (S.take n) m = S m := by
  rw [take_apply, if_pos (lt_of_lt_of_le h (Nat.min_le_left ..))]

@[simp] theorem take_zero (S : TriangularSet σ R) : S.take 0 = ∅ := ext fun _ ↦ rfl

@[simp] theorem take_length (S : TriangularSet σ R) : S.take (S.length) = S := ext fun i ↦ by
  rw [take_apply]
  split_ifs with hi
  · exact rfl
  rw [eq_zero_iff_length_le.mp <| Nat.le_of_not_lt hi]

theorem take_subset (S : TriangularSet σ R) (n : ℕ) : S.take n ⊆ S := fun p hp ↦ by
  rw [← mem_toList_iff] at hp ⊢
  exact List.mem_of_mem_take hp

/-- Drops the first `n` elements of a triangular set. -/
def drop (S : TriangularSet σ R) (n : ℕ) : TriangularSet σ R where
  toList := S.toList.drop n
  zero_notMem' := fun h ↦ absurd (List.mem_of_mem_drop h) S.zero_notMem_toList
  isChain_max_vars' := List.IsChain.drop S.toList_isChain n

theorem toList_drop (S : TriangularSet σ R) (n : ℕ) : (S.drop n).toList = S.toList.drop n := rfl

@[simp]
theorem length_drop (S : TriangularSet σ R) (n : ℕ) : (S.drop n).length = S.length - n :=
  List.length_drop

@[simp] theorem drop_apply (S : TriangularSet σ R) (n m : ℕ) : (S.drop n) m = S (n + m) := by
  rw [← toList_getElem?_getD, ← toList_getElem?_getD, toList_drop, List.getElem?_drop]

@[simp] theorem drop_zero (S : TriangularSet σ R) : S.drop 0 = S :=
  ext fun i ↦ by rw [drop_apply, zero_add]

theorem drop_eq_empty_of_ge_length : S.length ≤ n → S.drop n = ∅ := fun h ↦
  ext fun _ ↦ (drop_apply S ..).symm ▸ eq_zero_iff_length_le.mp (Nat.le_add_right_of_le h)

@[simp] theorem drop_length (S : TriangularSet σ R) : S.drop S.length = ∅ :=
  drop_eq_empty_of_ge_length (le_refl _)

/-- The condition required to append `p` to `S` while maintaining the Triangular Set property.
`p` must be non-zero and its main variable must be strictly greater than
the main variable of the last element of `S`. -/
abbrev CanConcat (S : TriangularSet σ R) (p : MvPolynomial σ R) : Prop :=
  p ≠ 0 ∧ (0 < S.length → (S (S.length - 1)).vars.max < p.vars.max)

theorem canConcat_def : S.CanConcat p ↔
    (p ≠ 0 ∧ (0 < S.length → (S (S.length - 1)).vars.max < p.vars.max)) := Iff.rfl

theorem empty_canConcat : p ≠ 0 → (∅ : TriangularSet σ R).CanConcat p :=
  fun h1 ↦ ⟨h1, fun h2 ↦ absurd h2 <| Nat.lt_irrefl 0⟩

theorem not_canConcat_zero : ¬ S.CanConcat 0 := not_and.mpr fun a _ ↦ a rfl

/-- Appends a polynomial `p` to the end of `S`. Requires `S.canConcat p`. -/
def concat (S : TriangularSet σ R) (p : MvPolynomial σ R)
    (h : S.CanConcat p := by assumption) : TriangularSet σ R where
  toList := S.toList.concat p
  zero_notMem' := fun hz ↦ by
    rw [List.concat_eq_append, List.mem_append, List.mem_singleton] at hz
    absurd S.zero_notMem_toList
    exact or_iff_not_imp_right.mp hz h.1.symm
  isChain_max_vars' := by
    rw [List.concat_eq_append]
    apply List.IsChain.append S.toList_isChain (List.IsChain.singleton p)
    intro q hq
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq']
    have : 0 < S.toList.length := List.length_pos_iff.mpr fun h ↦ by aesop
    have hq : q = S (S.length - 1) := by
      rw [← toList_getElem?_getD, ← length_toList]
      grind
    exact hq ▸ h.2 this

theorem toList_concat {p : MvPolynomial σ R} (h : S.CanConcat p) :
    (S.concat p).toList = S.toList.concat p := rfl

@[simp] theorem length_concat {p : MvPolynomial σ R} (h : S.CanConcat p) :
    (S.concat p).length = S.length + 1 := by
  rw [← length_toList, ← length_toList, toList_concat, List.length_concat]

theorem concat_apply {p : MvPolynomial σ R} (h : S.CanConcat p) (n : ℕ) :
    (S.concat p) n = if n < S.length then S n else if n = S.length then p else 0 := by
  rw [← toList_getElem?_getD]
  grind [= toList_concat, = toList_getElem?_getD, = length_toList]

theorem concat_apply_length {p : MvPolynomial σ R} (h : S.CanConcat p) :
    (S.concat p) S.length = p := by
  simp only [concat_apply, lt_self_iff_false, ↓reduceIte]

theorem mem_concat {p : MvPolynomial σ R} (h : S.CanConcat p) : p ∈ S.concat p := by
  use S.length
  rw [length_concat, concat_apply h, if_neg (Nat.lt_irrefl S.length), if_pos rfl]
  simp only [lt_add_iff_pos_right, zero_lt_one, and_self]

theorem subset_concat {p : MvPolynomial σ R} (h : S.CanConcat p) : S ⊆ S.concat p := fun _ ⟨i, hi⟩ ↦
  ⟨i, (length_concat h) ▸ Nat.lt_add_one_of_lt hi.1, (concat_apply h _) ▸ if_pos hi.1 ▸ hi.2⟩

theorem mem_concat_iff {p q : MvPolynomial σ R} (h : S.CanConcat p) :
    q ∈ S.concat p ↔ q = p ∨ q ∈ S := by
  rw [← mem_toList_iff, toList_concat, List.concat_eq_append, List.mem_append, List.mem_singleton,
    mem_toList_iff, Or.comm]

theorem coe_concat_eq_insert {p : MvPolynomial σ R} (h : S.CanConcat p) :
    S.concat p = (S : Set (MvPolynomial σ R)).insert p := Set.ext fun q ↦ by
  simpa using mem_concat_iff h

variable [DecidableEq R] {S T : TriangularSet σ R} {p q : MvPolynomial σ R}

/-- A triangular set with exactly one element. -/
noncomputable def single (p : MvPolynomial σ R) : TriangularSet σ R :=
  if h : p = 0 then ∅ else single' h

@[simp] theorem single_zero : single (0 : MvPolynomial σ R) = ∅ := rfl

theorem length_single : p ≠ 0 → (single p).length = 1 :=
  fun h ↦ by simp only [single, h, reduceDIte]; exact rfl

theorem single_eq_zero_iff : p = 0 ↔ single p = ∅ :=
  ⟨fun h ↦ by simp only [single, h, reduceDIte],
  fun h ↦ by by_contra con; absurd h ▸ length_single con; exact Nat.ne_of_beq_eq_false rfl⟩

theorem length_single_zero : p = 0 → (single p).length = 0 := fun h ↦ single_eq_zero_iff.mp h ▸ rfl

theorem length_single_le_one : (single p).length ≤ 1 :=
  Or.elim (em (p = 0))
    (fun h ↦ le_of_eq_of_le (length_single_zero h) <| Nat.zero_le 1)
    (fun h ↦ (length_single h).symm ▸ le_refl 1)

theorem single_apply_zero (p : MvPolynomial σ R) : single p 0 = p :=
  Or.elim (em (p = 0))
    (fun h ↦ by simp only [single, h, reduceDIte, empty_apply])
    (fun h ↦ by simp only [single, h, reduceDIte, single'_apply h, reduceIte])

theorem single_apply_nonzero (p : MvPolynomial σ R) : n ≠ 0 → single p n = 0 :=
  fun h ↦ Or.elim (em (p = 0))
    (fun hn ↦ by simp only [single, hn, reduceDIte, empty_apply])
    (fun hn ↦ by simp only [single, hn, reduceDIte, single'_apply hn, reduceIte, h])

theorem mem_single_of_ne_zero : p ≠ 0 → p ∈ single p := fun h ↦
  mem_def.mpr ⟨0, length_single h ▸ Nat.one_pos, single_apply_zero p⟩

theorem notMem_single_of_ne {q : MvPolynomial σ R} : q ≠ p → q ∉ single p := mt fun h ↦
  have ⟨_, hi1, hi2⟩ := h
  have hi1 := Nat.lt_one_iff.mp <| lt_of_lt_of_le hi1 length_single_le_one
  (single_apply_zero p) ▸ hi1 ▸ hi2.symm

theorem single_of_length_le_one : S.length ≤ 1 → S = single (S 0) :=
  fun h ↦ ext fun i ↦ by
    match Decidable.em (i = 0) with
    | Or.inl hi => rw [hi, single_apply_zero]
    | Or.inr hi =>
      have : S.length ≤ i := Nat.le_trans h <| Nat.one_le_iff_ne_zero.mpr hi
      rw [eq_zero_iff_length_le.mp this, single_apply_nonzero _ hi]

theorem single_of_last_max_vars_eq_bot :
    (S (S.length - 1)).vars.max = ⊥ → S = single (S 0) := fun h ↦
  have : S.length ≤ 1 := by
    by_cases hl : S.length = 0
    · exact hl ▸ Nat.zero_le 1
    have : S.length - 1 < S.length := Nat.sub_one_lt hl
    exact Nat.le_of_sub_eq_zero <| index_eq_zero_of_max_vars_eq_bot this h
  single_of_length_le_one this

/--
`takeConcat S p` tries to construct a new Triangular Set
by taking a prefix of `S` and appending `p`.
This is a key operation in constructing the Characteristic Set.
If `p` fits naturally at the end of `S`, it behaves like `S.concat p`.
If `p` conflicts with some element in `S` (in terms of main variable order), `takeConcat` finds the
first element in `S` that has a higher or equal main variable than `p`,
truncates `S` before that element, and appends `p`.
-/
noncomputable def takeConcat (S : TriangularSet σ R) (p : MvPolynomial σ R) :
    TriangularSet σ R :=
  if S = ∅ then single p
  else if hc : p.vars.max ≤ (S 0).vars.max then single p
  else
    let k := Nat.find <| exists_index_max_vars_between_of_max_vars_first_lt <| lt_of_not_ge hc
    have hk : k ≤ S.length ∧ (S (k - 1)).vars.max < p.vars.max ∧
        (p.vars.max ≤ (S k).vars.max ∨ k = S.length) :=
      Nat.find_spec <| exists_index_max_vars_between_of_max_vars_first_lt <| lt_of_not_ge hc
    have max_vars_lt : (S.take k).CanConcat p := by
      rw [CanConcat, length_take, min_eq_left hk.1, take_apply]
      refine ⟨fun hp ↦ absurd (LT.lt.ne_bot <| lt_of_not_ge hc) (by simp [hp]), ?_⟩
      exact fun hkz ↦ if_pos (Nat.sub_one_lt_of_lt hkz) ▸ hk.2.1
    (S.take k).concat p

theorem takeConcat_eq_concat_of_canConcat (h : S.CanConcat p) : S.takeConcat p = S.concat p := by
  unfold takeConcat
  split_ifs with h1 hc
  · simp [h1, single, h.1, single', concat]
  repeat' have h1 := length_gt_zero_iff.mpr h1
  · absurd hc
    simp only [not_le]
    refine lt_of_le_of_lt (max_vars_le_of_index_le (Nat.zero_le _) ?_) <| h.2 h1
    exact Nat.sub_one_lt_of_lt h1
  let k := Nat.find <| exists_index_max_vars_between_of_max_vars_first_lt <| lt_of_not_ge hc
  have hk : k = S.length := by
    have : k ≤ S.length ∧ (S (k - 1)).vars.max < p.vars.max ∧
        (p.vars.max ≤ (S k).vars.max ∨ k = S.length) :=
      Nat.find_spec <| exists_index_max_vars_between_of_max_vars_first_lt <| lt_of_not_ge hc
    by_contra con
    simp only [con, or_false] at this
    absurd lt_of_le_of_ne this.1 con
    have := index_lt_of_max_vars_lt (Nat.sub_one_lt_of_lt h1) (lt_of_lt_of_le (h.2 h1) this.2.2)
    exact Nat.not_lt.mpr <| Nat.le_of_pred_lt this
  change (S.take k).concat p _ = S.concat p
  simp only [hk, take_length]

theorem takeConcat_zero_eq_empty (S : TriangularSet σ R) : S.takeConcat 0 = ∅ := by
  have : (0 : MvPolynomial σ R).vars.max = ⊥ := rfl
  simp only [takeConcat, single_zero, this, bot_le, ↓reduceDIte, ite_self]

theorem mem_takeConcat (S : TriangularSet σ R) {p : MvPolynomial σ R} (h : p ≠ 0) :
    p ∈ S.takeConcat p := by
  unfold takeConcat
  split_ifs with _ hc
  repeat' exact mem_single_of_ne_zero h
  exact mem_concat _

theorem takeConcat_subset : ∀ q ∈ S.takeConcat p, q ≠ p → q ∈ S := fun q hq1 hq2 ↦ by
  unfold takeConcat at hq1
  split_ifs at hq1 with hs hc
  repeat exact absurd hq1 <| notMem_single_of_ne hq2
  let k := Nat.find <| exists_index_max_vars_between_of_max_vars_first_lt <| lt_of_not_ge hc
  apply S.take_subset k
  change q ∈ ((S.take k).concat p _ : Set (MvPolynomial σ R)) at hq1
  simpa [coe_concat_eq_insert, Set.insert, hq2] using hq1

end TriangularSet
