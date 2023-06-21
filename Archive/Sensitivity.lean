/-
Copyright (c) 2019 Reid Barton, Johan Commelin, Jesse Han, Chris Hughes, Robert Y. Lewis,
Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Johan Commelin, Jesse Han, Chris Hughes, Robert Y. Lewis, Patrick Massot

! This file was ported from Lean 3 source module sensitivity
! leanprover-community/mathlib commit 328375597f2c0dd00522d9c2e5a33b6a6128feeb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.FinCases
import Mathbin.Tactic.ApplyFun
import Mathbin.LinearAlgebra.FiniteDimensional
import Mathbin.LinearAlgebra.Dual
import Mathbin.Analysis.NormedSpace.Basic
import Mathbin.Data.Real.Sqrt

/-!
# Huang's sensitivity theorem

A formalization of Hao Huang's sensitivity theorem: in the hypercube of
dimension n ≥ 1, if one colors more than half the vertices then at least one
vertex has at least √n colored neighbors.

A fun summer collaboration by
Reid Barton, Johan Commelin, Jesse Han, Chris Hughes, Robert Y. Lewis, and Patrick Massot,
based on Don Knuth's account of the story
(https://www.cs.stanford.edu/~knuth/papers/huang.pdf),
using the Lean theorem prover (https://leanprover.github.io/),
by Leonardo de Moura at Microsoft Research, and his collaborators
(https://leanprover.github.io/people/),
and using Lean's user maintained mathematics library
(https://github.com/leanprover-community/mathlib).

The project was developed at https://github.com/leanprover-community/lean-sensitivity and is now
archived at https://github.com/leanprover-community/mathlib/blob/master/archive/sensitivity.lean
-/


namespace Sensitivity

/-! The next two lines assert we do not want to give a constructive proof,
but rather use classical logic. -/


noncomputable section

open scoped Classical

/-! We also want to use the notation `∑` for sums. -/


open scoped BigOperators

notation "√" => Real.sqrt

open Function Bool LinearMap Fintype FiniteDimensional Module.DualBases

/-!
### The hypercube

Notations:
- `ℕ` denotes natural numbers (including zero).
- `fin n` = {0, ⋯ , n - 1}.
- `bool` = {`tt`, `ff`}.
-/


/-- The hypercube in dimension `n`. -/
def Q (n : ℕ) :=
  Fin n → Bool
deriving Inhabited, Fintype
#align sensitivity.Q Sensitivity.Q

/-- The projection from `Q (n + 1)` to `Q n` forgetting the first value
(ie. the image of zero). -/
def π {n : ℕ} : Q (n + 1) → Q n := fun p => p ∘ Fin.succ
#align sensitivity.π Sensitivity.π

namespace Q

/-! `n` will always denote a natural number. -/


variable (n : ℕ)

/-- `Q 0` has a unique element. -/
instance : Unique (Q 0) :=
  ⟨⟨fun _ => true⟩, by intro; ext x; fin_cases x⟩

/-- `Q n` has 2^n elements. -/
theorem card : card (Q n) = 2 ^ n := by simp [Q]
#align sensitivity.Q.card Sensitivity.Q.card

/-! Until the end of this namespace, `n` will be an implicit argument (still
a natural number). -/


variable {n}

theorem succ_n_eq (p q : Q (n + 1)) : p = q ↔ p 0 = q 0 ∧ π p = π q :=
  by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h₀, h⟩
    ext x
    by_cases hx : x = 0
    · rwa [hx]
    · rw [← Fin.succ_pred x hx]
      convert congr_fun h (Fin.pred x hx)
#align sensitivity.Q.succ_n_eq Sensitivity.Q.succ_n_eq

/-- The adjacency relation defining the graph structure on `Q n`:
`p.adjacent q` if there is an edge from `p` to `q` in `Q n`. -/
def adjacent {n : ℕ} (p : Q n) : Set (Q n) := fun q => ∃! i, p i ≠ q i
#align sensitivity.Q.adjacent Sensitivity.Q.adjacent

/-- In `Q 0`, no two vertices are adjacent. -/
theorem not_adjacent_zero (p q : Q 0) : ¬p.adjacent q := by rintro ⟨v, _⟩ <;> apply finZeroElim v
#align sensitivity.Q.not_adjacent_zero Sensitivity.Q.not_adjacent_zero

/-- If `p` and `q` in `Q (n+1)` have different values at zero then they are adjacent
iff their projections to `Q n` are equal. -/
theorem adj_iff_proj_eq {p q : Q (n + 1)} (h₀ : p 0 ≠ q 0) : p.adjacent q ↔ π p = π q :=
  by
  constructor
  · rintro ⟨i, h_eq, h_uni⟩
    ext x; by_contra hx
    apply Fin.succ_ne_zero x
    rw [h_uni _ hx, h_uni _ h₀]
  · intro heq
    use 0, h₀
    intro y hy
    contrapose! hy
    rw [← Fin.succ_pred _ hy]
    apply congr_fun HEq
#align sensitivity.Q.adj_iff_proj_eq Sensitivity.Q.adj_iff_proj_eq

/-- If `p` and `q` in `Q (n+1)` have the same value at zero then they are adjacent
iff their projections to `Q n` are adjacent. -/
theorem adj_iff_proj_adj {p q : Q (n + 1)} (h₀ : p 0 = q 0) : p.adjacent q ↔ (π p).adjacent (π q) :=
  by
  constructor
  · rintro ⟨i, h_eq, h_uni⟩
    have h_i : i ≠ 0 := fun h_i => absurd h₀ (by rwa [h_i] at h_eq )
    use i.pred h_i,
      show p (Fin.succ (Fin.pred i _)) ≠ q (Fin.succ (Fin.pred i _)) by rwa [Fin.succ_pred]
    intro y hy
    simp [Eq.symm (h_uni _ hy)]
  · rintro ⟨i, h_eq, h_uni⟩
    use i.succ, h_eq
    intro y hy
    rw [← Fin.pred_inj, Fin.pred_succ]
    · apply h_uni
      change p (Fin.pred _ _).succ ≠ q (Fin.pred _ _).succ
      simp [hy]
    · contrapose! hy
      rw [hy, h₀]
    · apply Fin.succ_ne_zero
#align sensitivity.Q.adj_iff_proj_adj Sensitivity.Q.adj_iff_proj_adj

@[symm]
theorem adjacent.symm {p q : Q n} : p.adjacent q ↔ q.adjacent p := by simp only [adjacent, ne_comm]
#align sensitivity.Q.adjacent.symm Sensitivity.Q.adjacent.symm

end Q

/-! ### The vector space -/


/-- The free vector space on vertices of a hypercube, defined inductively. -/
def V : ℕ → Type
  | 0 => ℝ
  | n + 1 => V n × V n
#align sensitivity.V Sensitivity.V

namespace V

variable (n : ℕ)

/-! `V n` is a real vector space whose equality relation is computable. -/


instance : DecidableEq (V n) := by induction n <;> · dsimp only [V]; skip; infer_instance

instance : AddCommGroup (V n) := by induction n <;> · dsimp only [V]; skip; infer_instance

instance : Module ℝ (V n) := by induction n <;> · dsimp only [V]; skip; infer_instance

end V

/-- The basis of `V` indexed by the hypercube, defined inductively. -/
noncomputable def e : ∀ {n}, Q n → V n
  | 0 => fun _ => (1 : ℝ)
  | n + 1 => fun x => cond (x 0) (e (π x), 0) (0, e (π x))
#align sensitivity.e Sensitivity.e

@[simp]
theorem e_zero_apply (x : Q 0) : e x = (1 : ℝ) :=
  rfl
#align sensitivity.e_zero_apply Sensitivity.e_zero_apply

/-- The dual basis to `e`, defined inductively. -/
noncomputable def ε : ∀ {n : ℕ} (p : Q n), V n →ₗ[ℝ] ℝ
  | 0, _ => LinearMap.id
  | n + 1, p =>
    cond (p 0) ((ε <| π p).comp <| LinearMap.fst _ _ _) ((ε <| π p).comp <| LinearMap.snd _ _ _)
#align sensitivity.ε Sensitivity.ε

variable {n : ℕ}

theorem duality (p q : Q n) : ε p (e q) = if p = q then 1 else 0 :=
  by
  induction' n with n IH
  · rw [show p = q from Subsingleton.elim p q]
    dsimp [ε, e]
    simp
  · dsimp [ε, e]
    cases hp : p 0 <;> cases hq : q 0
    all_goals
      repeat' rw [cond_tt]
      repeat' rw [cond_ff]
      simp only [LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.comp_apply, IH]
      try congr 1; rw [Q.succ_n_eq]; finish
      try
        erw [(ε _).map_zero]
        have : p ≠ q := by intro h; rw [p.succ_n_eq q] at h ; finish
        simp [this]
#align sensitivity.duality Sensitivity.duality

/-- Any vector in `V n` annihilated by all `ε p`'s is zero. -/
theorem epsilon_total {v : V n} (h : ∀ p : Q n, (ε p) v = 0) : v = 0 :=
  by
  induction' n with n ih
  · dsimp [ε] at h ; exact h fun _ => tt
  · cases' v with v₁ v₂
    ext <;> change _ = (0 : V n) <;> simp only <;> apply ih <;> intro p <;>
      [let q : Q (n + 1) := fun i => if h : i = 0 then tt else p (i.pred h);
      let q : Q (n + 1) := fun i => if h : i = 0 then ff else p (i.pred h)]
    all_goals
      specialize h q
      first
      | rw [ε, show q 0 = tt from rfl, cond_tt] at h 
      | rw [ε, show q 0 = ff from rfl, cond_ff] at h 
      rwa [show p = π q by ext; simp [q, Fin.succ_ne_zero, π]]
#align sensitivity.epsilon_total Sensitivity.epsilon_total

open Module

/-- `e` and `ε` are dual families of vectors. It implies that `e` is indeed a basis
and `ε` computes coefficients of decompositions of vectors on that basis. -/
def dualBases_e_ε (n : ℕ) : DualBases (@e n) (@ε n)
    where
  eval := duality
  Total := @epsilon_total _
#align sensitivity.dual_bases_e_ε Sensitivity.dualBases_e_ε

/-! We will now derive the dimension of `V`, first as a cardinal in `dim_V` and,
since this cardinal is finite, as a natural number in `finrank_V` -/


theorem dim_v : Module.rank ℝ (V n) = 2 ^ n :=
  by
  have : Module.rank ℝ (V n) = (2 ^ n : ℕ) := by
    rw [rank_eq_card_basis (dual_bases_e_ε _).Basis, Q.card] <;> infer_instance
  assumption_mod_cast
#align sensitivity.dim_V Sensitivity.dim_v

instance : FiniteDimensional ℝ (V n) :=
  FiniteDimensional.of_fintype_basis (dualBases_e_ε _).Basis

theorem finrank_v : finrank ℝ (V n) = 2 ^ n :=
  by
  have := @dim_v n
  rw [← finrank_eq_rank] at this  <;> assumption_mod_cast
#align sensitivity.finrank_V Sensitivity.finrank_v

/-! ### The linear map -/


/-- The linear operator $f_n$ corresponding to Huang's matrix $A_n$,
defined inductively as a ℝ-linear map from `V n` to `V n`. -/
noncomputable def f : ∀ n, V n →ₗ[ℝ] V n
  | 0 => 0
  | n + 1 =>
    LinearMap.prod (LinearMap.coprod (f n) LinearMap.id) (LinearMap.coprod LinearMap.id (-f n))
#align sensitivity.f Sensitivity.f

/-! The preceding definition uses linear map constructions to automatically
get that `f` is linear, but its values are somewhat buried as a side-effect.
The next two lemmas unbury them. -/


@[simp]
theorem f_zero : f 0 = 0 :=
  rfl
#align sensitivity.f_zero Sensitivity.f_zero

theorem f_succ_apply (v : V (n + 1)) : f (n + 1) v = (f n v.1 + v.2, v.1 - f n v.2) :=
  by
  cases v
  rw [f]
  simp only [LinearMap.id_apply, LinearMap.prod_apply, Pi.prod, Prod.mk.inj_iff,
    LinearMap.neg_apply, sub_eq_add_neg, LinearMap.coprod_apply]
  exact ⟨rfl, rfl⟩
#align sensitivity.f_succ_apply Sensitivity.f_succ_apply

/-! In the next statement, the explicit conversion `(n : ℝ)` of `n` to a real number
is necessary since otherwise `n • v` refers to the multiplication defined
using only the addition of `V`. -/


theorem f_squared : ∀ v : V n, (f n) (f n v) = (n : ℝ) • v :=
  by
  induction' n with n IH <;> intro
  · simpa only [Nat.cast_zero, zero_smul]
  · cases v; simp [f_succ_apply, IH, add_smul, add_assoc]; abel
#align sensitivity.f_squared Sensitivity.f_squared

/-! We now compute the matrix of `f` in the `e` basis (`p` is the line index,
`q` the column index). -/


theorem f_matrix : ∀ p q : Q n, |ε q (f n (e p))| = if q.adjacent p then 1 else 0 :=
  by
  induction' n with n IH
  · intro p q
    dsimp [f]
    simp [Q.not_adjacent_zero]
  · intro p q
    have ite_nonneg : ite (π q = π p) (1 : ℝ) 0 ≥ 0 := by split_ifs <;> norm_num
    have f_map_zero := (show V (n + 0) →ₗ[ℝ] V n from f n).map_zero
    dsimp [e, ε, f]; cases hp : p 0 <;> cases hq : q 0
    all_goals
      repeat' rw [cond_tt]; repeat' rw [cond_ff]
      simp [f_map_zero, hp, hq, IH, duality, abs_of_nonneg ite_nonneg, Q.adj_iff_proj_eq,
        Q.adj_iff_proj_adj]
#align sensitivity.f_matrix Sensitivity.f_matrix

/-- The linear operator $g_m$ corresponding to Knuth's matrix $B_m$. -/
noncomputable def g (m : ℕ) : V m →ₗ[ℝ] V (m + 1) :=
  LinearMap.prod (f m + √ (m + 1) • LinearMap.id) LinearMap.id
#align sensitivity.g Sensitivity.g

/-! In the following lemmas, `m` will denote a natural number. -/


variable {m : ℕ}

/-! Again we unpack what are the values of `g`. -/


theorem g_apply : ∀ v, g m v = (f m v + √ (m + 1) • v, v) := by delta g <;> simp
#align sensitivity.g_apply Sensitivity.g_apply

theorem g_injective : Injective (g m) := by
  rw [g]
  intro x₁ x₂ h
  simp only [LinearMap.prod_apply, LinearMap.id_apply, Prod.mk.inj_iff, Pi.prod] at h 
  exact h.right
#align sensitivity.g_injective Sensitivity.g_injective

theorem f_image_g (w : V (m + 1)) (hv : ∃ v, g m v = w) : f (m + 1) w = √ (m + 1) • w :=
  by
  rcases hv with ⟨v, rfl⟩
  have : √ (m + 1) * √ (m + 1) = m + 1 := Real.mul_self_sqrt (by exact_mod_cast zero_le _)
  simp [this, f_succ_apply, g_apply, f_squared, smul_add, add_smul, smul_smul]
  abel
#align sensitivity.f_image_g Sensitivity.f_image_g

/-!
### The main proof

In this section, in order to enforce that `n` is positive, we write it as
`m + 1` for some natural number `m`. -/


/-! `dim X` will denote the dimension of a subspace `X` as a cardinal. -/


notation "dim " X:70 => Module.rank ℝ ↥X

/-! `fdim X` will denote the (finite) dimension of a subspace `X` as a natural number. -/


notation "fdim" => finrank ℝ

/-! `Span S` will denote the ℝ-subspace spanned by `S`. -/


notation "Span" => Submodule.span ℝ

/-! `Card X` will denote the cardinal of a subset of a finite type, as a
natural number. -/


notation "Card " X:70 => X.toFinset.card

/-! In the following, `⊓` and `⊔` will denote intersection and sums of ℝ-subspaces,
equipped with their subspace structures. The notations come from the general
theory of lattices, with inf and sup (also known as meet and join). -/


/-- If a subset `H` of `Q (m+1)` has cardinal at least `2^m + 1` then the
subspace of `V (m+1)` spanned by the corresponding basis vectors non-trivially
intersects the range of `g m`. -/
theorem exists_eigenvalue (H : Set (Q (m + 1))) (hH : Card H ≥ 2 ^ m + 1) :
    ∃ y ∈ Span (e '' H) ⊓ (g m).range, y ≠ (0 : _) :=
  by
  let W := Span (e '' H)
  let img := (g m).range
  suffices 0 < dim (W ⊓ img) by
    simp only [exists_prop]
    exact_mod_cast exists_mem_ne_zero_of_rank_pos this
  have dim_le : dim (W ⊔ img) ≤ 2 ^ (m + 1) :=
    by
    convert ← rank_submodule_le (W ⊔ img)
    apply dim_V
  have dim_add : dim (W ⊔ img) + dim (W ⊓ img) = dim W + 2 ^ m :=
    by
    convert ← Submodule.rank_sup_add_rank_inf_eq W img
    rw [← rank_eq_of_injective (g m) g_injective]
    apply dim_V
  have dimW : dim W = card H :=
    by
    have li : LinearIndependent ℝ (H.restrict e) :=
      by
      convert (dual_bases_e_ε _).Basis.LinearIndependent.comp _ Subtype.val_injective
      rw [(dual_bases_e_ε _).coe_basis]
    have hdW := rank_span li
    rw [Set.range_restrict] at hdW 
    convert hdW
    rw [← (dual_bases_e_ε _).coe_basis, Cardinal.mk_image_eq (dual_bases_e_ε _).Basis.Injective,
      Cardinal.mk_fintype]
  rw [← finrank_eq_rank ℝ] at dim_le dim_add dimW ⊢
  rw [← finrank_eq_rank ℝ, ← finrank_eq_rank ℝ] at dim_add 
  norm_cast at dim_le dim_add dimW ⊢
  rw [pow_succ'] at dim_le 
  rw [Set.toFinset_card] at hH 
  linarith
#align sensitivity.exists_eigenvalue Sensitivity.exists_eigenvalue

/-- **Huang sensitivity theorem** also known as the **Huang degree theorem** -/
theorem huang_degree_theorem (H : Set (Q (m + 1))) (hH : Card H ≥ 2 ^ m + 1) :
    ∃ q, q ∈ H ∧ √ (m + 1) ≤ Card H ∩ q.adjacent :=
  by
  rcases exists_eigenvalue H hH with ⟨y, ⟨⟨y_mem_H, y_mem_g⟩, y_ne⟩⟩
  have coeffs_support : ((dual_bases_e_ε (m + 1)).coeffs y).support ⊆ H.to_finset :=
    by
    intro p p_in
    rw [Finsupp.mem_support_iff] at p_in 
    rw [Set.mem_toFinset]
    exact (dual_bases_e_ε _).mem_of_mem_span y_mem_H p p_in
  obtain ⟨q, H_max⟩ : ∃ q : Q (m + 1), ∀ q' : Q (m + 1), |(ε q' : _) y| ≤ |ε q y|
  exact Finite.exists_max _
  have H_q_pos : 0 < |ε q y| := by
    contrapose! y_ne
    exact epsilon_total fun p => abs_nonpos_iff.mp (le_trans (H_max p) y_ne)
  refine' ⟨q, (dual_bases_e_ε _).mem_of_mem_span y_mem_H q (abs_pos.mp H_q_pos), _⟩
  let s := √ (m + 1)
  suffices : s * |ε q y| ≤ ↑_ * |ε q y|
  exact (mul_le_mul_right H_q_pos).mp ‹_›
  let coeffs := (dual_bases_e_ε (m + 1)).coeffs
  calc
    s * |ε q y| = |ε q (s • y)| := by
      rw [map_smul, smul_eq_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    _ = |ε q (f (m + 1) y)| := by rw [← f_image_g y (by simpa using y_mem_g)]
    _ = |ε q (f (m + 1) (lc _ (coeffs y)))| := by rw [(dual_bases_e_ε _).lc_coeffs y]
    _ =
        |(coeffs y).Sum fun (i : Q (m + 1)) (a : ℝ) =>
            a • (ε q ∘ f (m + 1) ∘ fun i : Q (m + 1) => e i) i| :=
      by erw [(f <| m + 1).map_finsupp_total, (ε q).map_finsupp_total, Finsupp.total_apply]
    _ ≤ ∑ p in (coeffs y).support, |coeffs y p * (ε q <| f (m + 1) <| e p)| :=
      (norm_sum_le _ fun p => coeffs y p * _)
    _ = ∑ p in (coeffs y).support, |coeffs y p| * ite (q.adjacent p) 1 0 := by
      simp only [abs_mul, f_matrix]
    _ = ∑ p in (coeffs y).support.filterₓ (Q.adjacent q), |coeffs y p| := by
      simp [Finset.sum_filter]
    _ ≤ ∑ p in (coeffs y).support.filterₓ (Q.adjacent q), |coeffs y q| :=
      (Finset.sum_le_sum fun p _ => H_max p)
    _ = (((coeffs y).support.filterₓ (Q.adjacent q)).card : ℝ) * |coeffs y q| := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = (((coeffs y).support ∩ (Q.adjacent q).toFinset).card : ℝ) * |coeffs y q| := by congr with x;
      simp; rfl
    _ ≤ Finset.card (H ∩ Q.adjacent q).toFinset * |ε q y| :=
      by
      refine' (mul_le_mul_right H_q_pos).2 _
      norm_cast
      apply Finset.card_le_of_subset
      rw [Set.toFinset_inter]
      convert Finset.inter_subset_inter_right coeffs_support
#align sensitivity.huang_degree_theorem Sensitivity.huang_degree_theorem

end Sensitivity

