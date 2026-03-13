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
such that their main variables (main variables) are strictly increasing:
`max_vars(P₁) < max_vars(P₂) < ... < max_vars(Pₘ)`.

## Main Definitions

* `TriangularSet`: The structure definition.
  It bundles the length, the sequence function,
  and the proofs of non-zero elements and ascending main variables.
* `TriangularSet.order`: A lexicographic order assigned to each triangular set,
  used to prove termination of algorithms (like Wu's Method).
* `TriangularSet.toFinset` / `toList`: Viewing the sequence as a set or list of polynomials.

## Main Results

* `TriangularSet.instWellFoundedLT`: Proof that triangular sets are well-founded
  under the order ordering (assuming finite variables).
  This guarantees termination of characteristic set algorithms.
* `TriangularSet.takeConcat_lt_of_reducedToSet`: Appending a reduced element
  strictly decreases the order, used to prove termination of basic set algorithms.

-/

@[expose] public section

open MvPolynomial

/-- A Triangular Set is a finite sequence of polynomials
with strictly increasing main variables. -/
structure TriangularSet (σ R : Type*) [CommSemiring R] [LinearOrder σ] where
  /-- The number of polynomials in the set. -/
  length' : ℕ
  /-- The sequence of polynomials, indexed by `ℕ`. -/
  seq : ℕ → MvPolynomial σ R
  /-- Elements within the length bound are non-zero. -/
  elements_ne_zero : ∀ n, n < length' ↔ seq n ≠ 0
  /-- The main variables of the polynomials are strictly increasing. -/
  ascending_max_vars : ∀ n < length' - 1, (seq n).vars.max < (seq (n + 1)).vars.max

namespace TriangularSet

variable {R σ : Type*} [CommSemiring R] [LinearOrder σ]

-- Enable treating a TriangularSet as a function `ℕ → MvPolynomial σ R`
instance instFunLike : FunLike (TriangularSet σ R) ℕ (MvPolynomial σ R) :=
  ⟨fun S ↦ S.seq, by
    rintro ⟨S, f, hf⟩ ⟨T, g, hg⟩ (hfg : f = g)
    congr
    rewrite [hfg] at hf
    have (n : ℕ) : ¬n < S ↔ ¬n < T := not_iff_not.mpr (Iff.trans (hf n) (hg n).symm)
    simp only [not_lt] at this
    exact le_antisymm ((this T).mpr <| le_refl T) <| (this S).mp <| le_refl S⟩

/-- The length of the triangular set. -/
def length (S : TriangularSet σ R) : ℕ := S.length'

variable {S T : TriangularSet σ R} {p : MvPolynomial σ R} {m n : ℕ}

@[ext]
theorem ext (h : ∀ i, S i = T i) : S = T := DFunLike.ext _ _ h

theorem elements_ne_zero_iff : n < S.length ↔ S n ≠ 0 := S.elements_ne_zero n

theorem elements_eq_zero_iff : S.length ≤ n ↔ S n = 0 :=
  not_iff_not.mp <| Iff.trans Nat.not_le elements_ne_zero_iff

theorem ext' (h1 : S.length = T.length) (h2 : ∀ i < S.length, S i = T i) : S = T := ext fun i ↦ by
  if h : i < S.length then exact h2 i h
  else
    have h := le_of_not_gt h
    rw [elements_eq_zero_iff.mp h, elements_eq_zero_iff.mp <| h1 ▸ h]

@[simp] theorem apply_length_eq_zero : S S.length = 0 := elements_eq_zero_iff.mp (le_refl _)

theorem max_vars_lt_max_vars_next :
    n < S.length - 1 → (S n).vars.max < (S (n + 1)).vars.max := S.ascending_max_vars n

theorem max_vars_lt_max_vars_next' :
    n + 1 < S.length → (S n).vars.max < (S (n + 1)).vars.max :=
  fun h ↦ max_vars_lt_max_vars_next <| Nat.lt_sub_of_add_lt h

theorem max_vars_lt_max_vars_next'' :
    0 < n → n < S.length → (S (n - 1)).vars.max < (S n).vars.max := fun h1 h2 ↦
  have : n - 1 < S.length - 1 := Nat.sub_lt_sub_right h1 h2
  Nat.sub_add_cancel h1 ▸ max_vars_lt_max_vars_next this

theorem max_vars_lt_of_index_lt (h : n < S.length) :
    m < n → (S m).vars.max < (S n).vars.max := fun hmn ↦ by
  induction n with
  | zero => exact absurd hmn <| Nat.not_lt_zero m
  | succ n hn => match Nat.lt_succ_iff_lt_or_eq.mp hmn with
    | Or.inl hmn =>
      exact lt_trans (hn (Nat.lt_of_succ_lt h) hmn) <| max_vars_lt_max_vars_next' h
    | Or.inr hmn => rewrite [hmn]; exact max_vars_lt_max_vars_next' h

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
  fun hm hn hc ↦ index_eq_of_max_vars_eq hm hn (congrArg (fun p ↦ p.vars.max) hc)

theorem index_eq_zero_of_max_vars_eq_bot :
    n < S.length → (S n).vars.max = ⊥ → n = 0 := fun h1 h2 ↦
  Decidable.byContradiction fun hn ↦
    WithBot.not_lt_bot _ (h2 ▸ max_vars_lt_max_vars_next'' (Nat.zero_lt_of_ne_zero hn) h1)

theorem exists_index_mainVar_between_of_mainVar_first_lt
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

/-! ### Set-like behavior -/

instance instSetLike : SetLike (TriangularSet σ R) (MvPolynomial σ R) where
  coe := fun S ↦ {p | ∃ n < S.length, S n = p}
  coe_injective' := by
    intro S T (h : (fun p ↦ ∃ n < S.length, S n = p) = fun p ↦ ∃ n < T.length, T n = p)
    have h (p) : (∃ n, S n = p) ↔ ∃ n, T n = p := by
      have (S : TriangularSet σ R) : (∃ n, S n = p) ↔ p = 0 ∨ ∃ n < S.length, S n = p :=
        ⟨fun ⟨n, hn⟩ ↦ or_iff_not_imp_left.mpr fun hp ↦ ⟨n, elements_ne_zero_iff.mpr (hn ▸ hp), hn⟩,
          fun hp ↦ Or.elim hp (fun hp ↦ ⟨S.length, hp ▸ apply_length_eq_zero⟩)
            (fun hp ↦ ⟨Exists.choose hp, (Exists.choose_spec hp).2⟩)⟩
      rw [this S, this T, Eq.to_iff (funext_iff.mp h p)]
    refine ext fun i ↦ ?_
    induction i using Nat.strong_induction_on with | h i hi =>
    have {S T : TriangularSet σ R} (h : ∀ p, (∃ n, S n = p) ↔ ∃ n, T n = p)
        (hi : ∀ m < i, S m = T m) : S i = 0 → T i = 0 := fun hs ↦ by
      by_contra ht
      have ⟨j ,hj⟩ := (h (T i)).mpr <| Exists.intro i rfl
      have h1 : i < T.length:= elements_ne_zero_iff.mpr ht
      rewrite [← hj] at ht
      have h2 : j < i := lt_of_lt_of_le (elements_ne_zero_iff.mpr ht) <| elements_eq_zero_iff.mpr hs
      have hj := congrArg (fun p ↦ p.vars.max) (hi j h2 ▸ hj)
      exact False.elim <| Eq.not_lt hj <| max_vars_lt_of_index_lt h1 h2
    have : S i = 0 ↔ T i = 0 :=
      ⟨this h hi, this (fun p ↦ (h p).symm) (fun i hi' ↦ (hi i hi').symm)⟩
    by_cases hst : S i = 0 ∨ T i = 0
    · rewrite [this, or_self] at hst
      rw [hst, this, hst]
    rewrite [not_or] at hst
    have ⟨h1, h2⟩ := And.intro (elements_ne_zero_iff.mpr hst.1) (elements_ne_zero_iff.mpr hst.2)
    have ⟨j ,hj⟩ := (h (S i)).mp <| Exists.intro i rfl
    by_cases hij : j ≤ i
    · match Nat.eq_or_lt_of_le hij with
      | .inl hij => exact (hij ▸ hj).symm
      | .inr hij =>
        absurd (max_vars_lt_of_index_lt h1 hij)
        exact hj.symm ▸ (Eq.not_lt <| congrArg (fun p ↦ p.vars.max) <| hi j hij)
    have ⟨k ,hk⟩ := (h (T i)).mpr <| Exists.intro i rfl
    have : j < T.length := elements_ne_zero_iff.mpr <| ne_of_eq_of_ne hj hst.1
    have : (T i).vars.max < (T j).vars.max :=
      max_vars_lt_of_index_lt this (not_le.mp hij)
    have hs : (S k).vars.max < (S i).vars.max := by rewrite [← hk, hj] at this; exact this
    have : k < S.length := elements_ne_zero_iff.mpr <| ne_of_eq_of_ne hk hst.2
    have klti : k < i := index_lt_of_max_vars_lt this hs
    have : T k = T i := (hi k klti).symm.trans hk
    absurd (congrArg (fun p ↦ p.vars.max) this)
    exact ne_of_lt <| max_vars_lt_of_index_lt h2 klti

theorem mem_def : p ∈ S ↔ ∃ n < S.length, S n = p := Eq.to_iff rfl

@[simp] theorem zero_notMem (S : TriangularSet σ R) : 0 ∉ S := fun h ↦
  have := Exists.choose_spec (mem_def.mp h)
  absurd this.2 <| elements_ne_zero_iff.mp this.1

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
    ⟨fun i ↦ S i.1, fun ⟨_, hi⟩ ⟨_, hj⟩ hij ↦ (Fin.mk.injEq ..) ▸ index_eq_of_apply_eq hi hj hij⟩

@[simp] theorem card_toFinset (S : TriangularSet σ R) : S.toFinset.card = S.length := by
  simp only [toFinset, Finset.card_map, Finset.card_univ, Fintype.card_fin]

@[simp] theorem mem_toFinset_iff : p ∈ S.toFinset ↔ p ∈ S := by
  refine Iff.trans ?_ SetLike.mem_coe
  simp [toFinset, Finset.map, SetLike.coe, Fin.exists_iff]

@[simp] theorem toFinset_eq_iff_eq : S.toFinset = T.toFinset ↔ S = T := by
  refine ⟨fun h ↦ SetLike.ext fun p ↦ ?_, congrArg _⟩
  rewrite [← mem_toFinset_iff, ← mem_toFinset_iff]
  exact Eq.to_iff (congrFun (congrArg Membership.mem h) p)

theorem toFinset_eq_coe_set (S : TriangularSet σ R) : S.toFinset = (S : Set (MvPolynomial σ R)) :=
  Set.ext fun _ ↦ ⟨SetLike.mem_coe.mpr ∘ mem_toFinset_iff.mp, mem_toFinset_iff.mpr⟩

theorem length_le_of_subset : S ⊆ T → S.length ≤ T.length := fun h ↦ by
  rewrite [← card_toFinset, ← card_toFinset]
  exact Finset.card_le_card <| Finset.coe_subset.mp (by simpa [toFinset_eq_coe_set] using h)

theorem length_lt_of_ssubset : S ⊂ T → S.length < T.length := fun h ↦ by
  rewrite [← card_toFinset, ← card_toFinset]
  exact Finset.card_lt_card <| Finset.coe_ssubset.mp (by simpa [toFinset_eq_coe_set] using h)

/-- Converts a triangular set to a list. -/
def toList (S : TriangularSet σ R) : List (MvPolynomial σ R) :=
  List.ofFn fun i : Fin S.length ↦ S i.1

@[simp] theorem length_toList (S : TriangularSet σ R) : S.toList.length = S.length := by
  simp only [toList, List.length_ofFn]

@[simp] theorem mem_toList_iff : p ∈ S.toList ↔ p ∈ S := by
  refine Iff.trans ?_ SetLike.mem_coe
  simp [toList, SetLike.coe, Fin.exists_iff]

@[simp] theorem toList_eq_iff_eq : S.toList = T.toList ↔ S = T := by
  refine ⟨fun h ↦ SetLike.ext fun p ↦ ?_, congrArg _⟩
  simpa [← mem_toList_iff] using Eq.to_iff (congrFun (congrArg Membership.mem h) p)

theorem toList_getElem {n : ℕ} (h : n < S.toList.length) : S.toList[n] = S n := by
  simp only [toList, List.getElem_ofFn]

theorem toList_non_zero : ∀ ⦃p⦄, p ∈ S.toList → p ≠ 0 :=
  fun _ hp ↦ ne_zero_of_mem <| mem_toList_iff.mp hp

theorem toList_pairwise : S.toList.Pairwise fun p q ↦ p.vars.max < q.vars.max :=
  List.pairwise_ofFn.mpr fun _ ⟨_, hn⟩ hmn ↦ max_vars_lt_of_index_lt hn hmn

instance [DecidableEq (MvPolynomial σ R)] : DecidableEq (TriangularSet σ R) :=
  fun _ _ ↦ decidable_of_iff _ toList_eq_iff_eq

/-- The empty triangular set. -/
protected noncomputable def empty : TriangularSet σ R where
  length' := 0
  seq := 0
  elements_ne_zero := fun n ↦ ⟨fun h ↦ absurd h <| Nat.not_lt_zero n, absurd rfl⟩
  ascending_max_vars := fun _ hn ↦ absurd hn <| of_decide_eq_false rfl

noncomputable instance : EmptyCollection (TriangularSet σ R) := ⟨.empty⟩

noncomputable instance : Inhabited (TriangularSet σ R) := ⟨∅⟩

theorem empty_eq_default : (∅ : TriangularSet σ R) = default := rfl

@[simp] theorem length_empty : (∅ : TriangularSet σ R).length = 0 := rfl

@[simp] theorem empty_apply : (∅ : TriangularSet σ R) n = 0 := rfl

theorem length_eq_zero_iff : S.length = 0 ↔ S = ∅ :=
  ⟨fun h ↦ ext fun i ↦ elements_eq_zero_iff.mp <| h ▸ Nat.zero_le i, fun h ↦ h ▸ length_empty⟩

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
noncomputable def single_of_ne_zero (hp : p ≠ 0) : TriangularSet σ R where
  length' := 1
  seq n := if n = 0 then p else 0
  elements_ne_zero := fun _ ↦
    ⟨fun hn ↦ ne_of_eq_of_ne (if_pos <| Nat.lt_one_iff.mp hn) hp,
    fun hn ↦ by by_contra con; exact hn (if_neg <| Nat.ne_zero_of_lt <| Nat.le_of_not_lt con)⟩
  ascending_max_vars n hn := absurd hn <| Nat.not_lt_zero n

theorem single_of_ne_zero_apply (hp : p ≠ 0) :
    (single_of_ne_zero hp) n = if n = 0 then p else 0 := rfl

theorem length_single_of_ne_zero (hp : p ≠ 0) : (single_of_ne_zero hp).length = 1 := rfl

/-- Takes the first `n` elements of a triangular set. -/
noncomputable def take (S : TriangularSet σ R) (n : ℕ) : TriangularSet σ R where
  length' := n ⊓ S.length
  seq m := if m < n then S m else 0
  elements_ne_zero m := by
    simp only [ne_eq, ite_eq_right_iff, Classical.not_imp]
    exact ⟨fun h ↦ ⟨lt_of_lt_of_le h <| Nat.min_le_left ..,
      elements_ne_zero_iff.mp <| lt_of_lt_of_le h <| Nat.min_le_right ..⟩,
      fun h ↦ lt_min h.1 (elements_ne_zero_iff.mpr h.2)⟩
  ascending_max_vars m hm := by
    have : n ⊓ S.length - 1 ≤ n - 1 := Nat.sub_le_sub_right (Nat.min_le_left ..) 1
    have : m + 1 < n := Nat.add_lt_of_lt_sub <| lt_of_lt_of_le hm this
    rewrite [if_pos this, if_pos <| Nat.lt_of_succ_lt this]
    have : n ⊓ S.length - 1 ≤ S.length - 1 := Nat.sub_le_sub_right (Nat.min_le_right ..) 1
    exact max_vars_lt_max_vars_next <| lt_of_lt_of_le hm this

@[simp]
theorem length_take (S : TriangularSet σ R) (n : ℕ) : (S.take n).length = n ⊓ S.length := rfl

theorem take_apply (S : TriangularSet σ R) (n m : ℕ) :
    (S.take n) m = if m < n then S m else 0 := rfl

theorem take_apply' {S : TriangularSet σ R} {n m : ℕ} (h : m < n ⊓ S.length) :
    (S.take n) m = S m := by
  rw [take_apply, if_pos (lt_of_lt_of_le h (Nat.min_le_left ..))]

@[simp] theorem take_zero (S : TriangularSet σ R) : S.take 0 = ∅ := ext fun _ ↦ rfl

@[simp] theorem take_length (S : TriangularSet σ R) : S.take (S.length) = S := ext fun i ↦ by
  rewrite [take_apply]
  split_ifs with hi
  · exact rfl
  rw [elements_eq_zero_iff.mp <| Nat.le_of_not_lt hi]

theorem take_subset (S : TriangularSet σ R) (n : ℕ) : S.take n ⊆ S := fun _ ⟨i, hi1, hi2⟩ ↦
  ⟨i, lt_of_lt_of_le hi1 (Nat.min_le_right ..),
    (@if_pos _ _ (lt_of_lt_of_le hi1 <| Nat.min_le_left ..) _ (S i) 0) ▸ hi2⟩

theorem toList_take_comm (S : TriangularSet σ R) (n : ℕ) :
    (S.take n).toList = S.toList.take n := by
    refine List.ext_getElem (by simp [length_toList, List.length_take]) fun i h1 h2 ↦ ?_
    rw [List.getElem_take, toList_getElem h1,
      toList_getElem (lt_of_lt_of_le (List.length_take ▸ h2) (Nat.min_le_right ..)),
      take_apply' (S.length_toList ▸ List.length_take ▸ h2)]

/-- Drops the first `n` elements of a triangular set. -/
def drop (S : TriangularSet σ R) (n : ℕ) : TriangularSet σ R where
  length' := S.length - n
  seq m := S (m + n)
  elements_ne_zero _ := Iff.trans ⟨Nat.add_lt_of_lt_sub, Nat.lt_sub_of_add_lt⟩ elements_ne_zero_iff
  ascending_max_vars m hm := max_vars_lt_of_index_lt
    ((add_assoc m 1 n).symm ▸ Nat.add_lt_of_lt_sub <| (add_comm n 1) ▸ hm)
    (Nat.add_lt_add_right (lt_add_one m) n)

@[simp]
theorem length_drop (S : TriangularSet σ R) (n : ℕ) : (S.drop n).length = S.length - n := rfl

@[simp] theorem drop_apply (S : TriangularSet σ R) (n m : ℕ) : (S.drop n) m = S (m + n) := rfl

@[simp] theorem drop_zero (S : TriangularSet σ R) : S.drop 0 = S :=
  ext fun i ↦ by rw [drop_apply, add_zero]

theorem drop_eq_empty_of_ge_length : S.length ≤ n → S.drop n = ∅ := fun h ↦
  ext fun _ ↦ (drop_apply S ..).symm ▸ elements_eq_zero_iff.mp (Nat.le_add_left_of_le h)

@[simp] theorem drop_length (S : TriangularSet σ R) : S.drop S.length = ∅ :=
  drop_eq_empty_of_ge_length (le_refl _)

theorem toList_drop_comm (S : TriangularSet σ R) (n : ℕ) :
    (S.drop n).toList = S.toList.drop n := by
  refine List.ext_getElem (by simp [length_toList, List.length_drop]) fun i h1 h2 ↦ ?_
  have h2 : n + i < S.toList.length := by
    rewrite [List.length_drop] at h2
    exact Nat.add_lt_of_lt_sub' h2
  rw [List.getElem_drop, toList_getElem h1, toList_getElem h2, drop_apply, add_comm i n]

/-- The condition required to append `p` to `S` while maintaining the Triangular Set property.
`p` must be non-zero and its main variable must be strictly greater than
the main variable of the last element of `S`. -/
abbrev canConcat (S : TriangularSet σ R) (p : MvPolynomial σ R) : Prop :=
  p ≠ 0 ∧ (0 < S.length → (S (S.length - 1)).vars.max < p.vars.max)

theorem canConcat_def : S.canConcat p ↔
    (p ≠ 0 ∧ (0 < S.length → (S (S.length - 1)).vars.max < p.vars.max)) := Iff.rfl

theorem empty_canConcat : p ≠ 0 → (∅ : TriangularSet σ R).canConcat p :=
  fun h1 ↦ ⟨h1, fun h2 ↦ absurd h2 <| Nat.lt_irrefl 0⟩

theorem not_canConcat_zero : ¬ S.canConcat 0 := not_and.mpr fun a _ ↦ a rfl

/-- Appends a polynomial `p` to the end of `S`. Requires `S.canConcat p`. -/
noncomputable def concat (S : TriangularSet σ R) (p : MvPolynomial σ R)
    (h : S.canConcat p := by assumption) : TriangularSet σ R where
  length' := S.length + 1
  seq n := if n < S.length then S n else if n = S.length then p else 0
  elements_ne_zero n :=
    ⟨fun hn ↦ by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hn with (hn | hn)
      · simp [hn, elements_ne_zero_iff.mp hn]
      · simp [hn, h.1],
    fun hn ↦ by
      by_contra con
      have con := not_lt.mp con
      simp only [Nat.not_lt_of_gt con, reduceIte, ne_eq, ite_eq_right_iff, Classical.not_imp] at hn
      exact (Nat.ne_of_lt con) hn.1.symm⟩
  ascending_max_vars n hn := by
    have hn : n < S.length := hn
    match Decidable.em (n + 1 < S.length) with
    | Or.inl h1 =>
      rewrite [if_pos hn, if_pos h1]
      exact max_vars_lt_max_vars_next <| Nat.lt_sub_of_add_lt h1
    | Or.inr h1 =>
      have h1 : n + 1 = S.length := Nat.le_antisymm hn <| Nat.le_of_not_lt h1
      simp only [hn, h1, lt_self_iff_false, reduceIte]
      exact add_tsub_cancel_right n 1 ▸ h1 ▸ h.2 (h1 ▸ Nat.zero_lt_succ n)

@[simp] theorem length_concat {p : MvPolynomial σ R} (h : S.canConcat p) :
    (S.concat p).length = S.length + 1 := rfl

theorem concat_apply {p : MvPolynomial σ R} (h : S.canConcat p) (n : ℕ) :
    (S.concat p) n = if n < S.length then S n else if n = S.length then p else 0 := rfl

theorem concat_apply_length {p : MvPolynomial σ R} (h : S.canConcat p) :
   (S.concat p) S.length = p := by simp [concat_apply]

theorem mem_concat {p : MvPolynomial σ R} (h : S.canConcat p) : p ∈ S.concat p := by
  use S.length
  rewrite [length_concat, concat_apply h, if_neg (Nat.lt_irrefl S.length), if_pos rfl]
  simp only [lt_add_iff_pos_right, zero_lt_one, and_self]

theorem subset_concat {p : MvPolynomial σ R} (h : S.canConcat p) : S ⊆ S.concat p := fun _ ⟨i, hi⟩ ↦
  ⟨i, (length_concat h) ▸ Nat.lt_add_one_of_lt hi.1, (concat_apply h _) ▸ if_pos hi.1 ▸ hi.2⟩

theorem mem_concat_iff {p q : MvPolynomial σ R} (h : S.canConcat p) :
    q ∈ S.concat p ↔ q = p ∨ q ∈ S := by
  refine ⟨fun ⟨i, (hi1 : i < S.length + 1), hi2⟩ ↦ ?_, fun hp ↦ ?_⟩
  · rewrite [concat_apply h i] at hi2
    if hlt : i < S.length then
      exact Or.inr ⟨i, hlt, by apply if_pos hlt ▸ hi2⟩
    else
      have : i = S.length := Nat.eq_of_lt_succ_of_not_lt hi1 hlt
      exact Or.inl (if_pos this ▸ if_neg hlt ▸ hi2).symm
  exact Or.elim hp (fun hp ↦ hp ▸ mem_concat h) (fun hp ↦ subset_concat h hp)

theorem coe_concat_eq_insert {p : MvPolynomial σ R} (h : S.canConcat p) :
    S.concat p = (S : Set (MvPolynomial σ R)).insert p := Set.ext fun q ↦ by
  simpa using mem_concat_iff h

/-- Converts a list to a TriangularSet.
Requires the list to be non-zero and pairwise strictly ascending in main variable. -/
noncomputable def list (l : List (MvPolynomial σ R)) (h1 : ∀ p ∈ l, p ≠ 0 := by assumption)
    (h2 : l.Pairwise fun p q ↦ p.vars.max < q.vars.max := by assumption) :
    TriangularSet σ R where
  length' := l.length
  seq n := l.getD n 0
  elements_ne_zero n :=
    ⟨fun hn ↦ by simp [hn, List.forall_mem_iff_getElem.mp h1 n hn],
      fun hn ↦ by contrapose! hn; simp [hn]⟩
  ascending_max_vars n hn := by
    have hn1 := Nat.lt_of_lt_pred hn
    have hn2 := Nat.add_lt_of_lt_sub hn
    simp [hn1, hn2, List.pairwise_iff_getElem.mp h2 _ _ hn1 hn2 (lt_add_one n)]

theorem length_list {l : List (MvPolynomial σ R)} (h1 : ∀ p ∈ l, p ≠ 0)
    (h2 : l.Pairwise fun p q ↦ p.vars.max < q.vars.max) : (list l).length = l.length := rfl

theorem list_nil_eq_empty {l : List (MvPolynomial σ R)} (h1 : ∀ p ∈ l, p ≠ 0)
    (h2 : l.Pairwise fun p q ↦ p.vars.max < q.vars.max) (h3 : l = []) : list l = ∅ :=
  length_eq_zero_iff.mp (by rw [length_list, h3, List.length_nil])

theorem list_apply {l : List (MvPolynomial σ R)} (h1 : ∀ p ∈ l, p ≠ 0)
    (h2 : l.Pairwise fun p q ↦ p.vars.max < q.vars.max)
    {n : ℕ} (hn : n < l.length) : (list l) n = l[n] := by
  change l.getD n 0 = l[n]
  simp only [List.getD_eq_getElem?_getD, hn, getElem?_pos, Option.getD_some]

theorem toList_list_eq {l : List (MvPolynomial σ R)} (h1 : ∀ p ∈ l, p ≠ 0)
    (h2 : l.Pairwise fun p q ↦ p.vars.max < q.vars.max) : (list l).toList = l :=
  List.ext_getElem (length_toList (list l) ▸ rfl)
    (fun _ hi1 hi2 ↦ (list_apply _ _ hi2) ▸ toList_getElem hi1)

theorem list_eq_of_eq_toList {l : List (MvPolynomial σ R)} (h1 : ∀ p ∈ l, p ≠ 0)
    (h2 : l.Pairwise fun p q ↦ p.vars.max < q.vars.max) (heq : l = S.toList) :
    list l = S := by
  refine ext' (heq ▸ S.length_toList) fun i (hi : i < l.length) ↦ ?_
  rw [list_apply _ _ hi, ← toList_getElem <| heq ▸ hi, List.getElem_of_eq heq hi]

theorem mem_list_iff {l : List (MvPolynomial σ R)} (h1 : ∀ p ∈ l, p ≠ 0)
    (h2 : l.Pairwise fun p q ↦ p.vars.max < q.vars.max) {p : MvPolynomial σ R} :
    p ∈ list l ↔ p ∈ l := by
  simp only [mem_def, length_list, List.mem_iff_getElem]
  refine ⟨fun ⟨i, hi1, hi2⟩ ↦ ⟨i, hi1, ?_⟩, fun ⟨i, hi1, hi2⟩ ↦ ⟨i, hi1, ?_⟩⟩
  <;> rw [← hi2, list_apply]

variable [DecidableEq R] {S T : TriangularSet σ R} {p q : MvPolynomial σ R}

/-- Unsafely construct a TriangularSet from a list. Panics if preconditions are not met.
This should be used with caution, primarily for computation where inputs are guaranteed correct. -/
noncomputable def list! (l : List (MvPolynomial σ R)) : TriangularSet σ R :=
  if h : (∀ p ∈ l, p ≠ 0) ∧ l.Pairwise fun p q ↦ p.vars.max < q.vars.max then list l h.1 h.2
  else panic "Illegal list input"

theorem list!_eq_list (l : List (MvPolynomial σ R)) (h1 : ∀ p ∈ l, p ≠ 0)
    (h2 : l.Pairwise fun p q ↦ p.vars.max < q.vars.max) : list! l = list l := by
  unfold list!
  split_ifs with h
  · rfl
  exact absurd ⟨h1, h2⟩ h

/-- A triangular set with exactly one element. -/
noncomputable def single (p : MvPolynomial σ R) : TriangularSet σ R :=
  if h : p = 0 then ∅ else single_of_ne_zero h

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
    (fun h ↦ by simp only [single, h, reduceDIte, single_of_ne_zero_apply h, reduceIte])

theorem single_apply_nonzero (p : MvPolynomial σ R) : n ≠ 0 → single p n = 0 :=
  fun h ↦ Or.elim (em (p = 0))
    (fun hn ↦ by simp only [single, hn, reduceDIte, empty_apply])
    (fun hn ↦ by simp only [single, hn, reduceDIte, single_of_ne_zero_apply hn, reduceIte, h])

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
      rw [elements_eq_zero_iff.mp this, single_apply_nonzero _ hi]

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
    let k := Nat.find <| exists_index_mainVar_between_of_mainVar_first_lt <| lt_of_not_ge hc
    have hk : k ≤ S.length ∧ (S (k - 1)).vars.max < p.vars.max ∧
        (p.vars.max ≤ (S k).vars.max ∨ k = S.length) :=
      Nat.find_spec <| exists_index_mainVar_between_of_mainVar_first_lt <| lt_of_not_ge hc
    have max_vars_lt : (S.take k).canConcat p := by
      rewrite [canConcat, length_take, min_eq_left hk.1, take_apply]
      refine ⟨fun hp ↦ absurd (LT.lt.ne_bot <| lt_of_not_ge hc) (by simp [hp]), ?_⟩
      exact fun hkz ↦ if_pos (Nat.sub_one_lt_of_lt hkz) ▸ hk.2.1
    (S.take k).concat p

theorem takeConcat_eq_concat_of_canConcat (h : S.canConcat p) : S.takeConcat p = S.concat p := by
  unfold takeConcat
  split_ifs with h1 hc
  · simp [h1, single, h.1, single_of_ne_zero, concat]
  repeat' have h1 := length_gt_zero_iff.mpr h1
  · absurd hc
    simp only [not_le]
    refine lt_of_le_of_lt (max_vars_le_of_index_le (Nat.zero_le _) ?_) <| h.2 h1
    exact Nat.sub_one_lt_of_lt h1
  let k := Nat.find <| exists_index_mainVar_between_of_mainVar_first_lt <| lt_of_not_ge hc
  have hk : k = S.length := by
    have : k ≤ S.length ∧ (S (k - 1)).vars.max < p.vars.max ∧
        (p.vars.max ≤ (S k).vars.max ∨ k = S.length) :=
      Nat.find_spec <| exists_index_mainVar_between_of_mainVar_first_lt <| lt_of_not_ge hc
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
  let k := Nat.find <| exists_index_mainVar_between_of_mainVar_first_lt <| lt_of_not_ge hc
  apply S.take_subset k
  change q ∈ ((S.take k).concat p _ : Set (MvPolynomial σ R)) at hq1
  simpa [coe_concat_eq_insert, Set.insert, hq2] using hq1

end TriangularSet
