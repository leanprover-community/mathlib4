/-
Copyright (c) 2023 Antoine Chambert-Loir and María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández, Eric Wieser, Bhavik Mehta,
  Yaël Dillies
-/
import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Data.Finset.Sym

/-!
# Antidiagonal of functions as finsets

This file provides the finset of functions summing to a specific value on a finset. Such finsets
should be thought of as the "antidiagonals" in the space of functions.

Precisely, for a commutative monoid `μ` with antidiagonals (see `Finset.HasAntidiagonal`),
`Finset.piAntidiag s n` is the finset of all functions `f : ι → μ` with support contained in `s` and
such that the sum of its values equals `n : μ`.

We define it recursively on `s` using `Finset.HasAntidiagonal.antidiagonal : μ → Finset (μ × μ)`.
Technically, we non-canonically identify `s` with `Fin n` where `n = s.card`, recurse on `n` using
that `(Fin (n + 1) → μ) ≃ (Fin n → μ) × μ`, and show the end result doesn't depend on our
identification. See `Finset.finAntidiag` for the details.

## Main declarations

* `Finset.piAntidiag s n`: Finset of all functions `f : ι → μ` with support contained in `s` and
  such that the sum of its values equals `n : μ`.
* `Finset.finAntidiagonal d n`: Computationally efficient special case of `Finset.piAntidiag` when
  `ι := Fin d`.

## TODO

`Finset.finAntidiagonal` is strictly more general than `Finset.Nat.antidiagonalTuple`. Deduplicate.

## See also

`Finset.finsuppAntidiag` for the `Finset (ι →₀ μ)`-valued version of `Finset.piAntidiag`.
-/

open Function

variable {ι μ μ' : Type*}

namespace Finset
section AddCommMonoid
variable [DecidableEq ι] [AddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ] {n : μ}

/-!
### `Fin d → μ`

In this section, we define the antidiagonals in `Fin d → μ` by recursion on `d`. Note that this is
computationally efficient, although probably not as efficient as `Finset.Nat.antidiagonalTuple`.
-/

/-- `finAntidiagonal d n` is the type of `d`-tuples with sum `n`.

TODO: deduplicate with the less general `Finset.Nat.antidiagonalTuple`. -/
def finAntidiagonal (d : ℕ) (n : μ) : Finset (Fin d → μ) :=
  aux d n
where
  /-- Auxiliary construction for `finAntidiagonal` that bundles a proof of lawfulness
  (`mem_finAntidiagonal`), as this is needed to invoke `disjiUnion`. Using `Finset.disjiUnion` makes
  this computationally much more efficient than using `Finset.biUnion`. -/
  aux (d : ℕ) (n : μ) : {s : Finset (Fin d → μ) // ∀ f, f ∈ s ↔ ∑ i, f i = n} :=
    match d with
    | 0 =>
      if h : n = 0 then
        ⟨{0}, by simp [h, Subsingleton.elim _ ![]]⟩
      else
        ⟨∅, by simp [Ne.symm h]⟩
    | d + 1 =>
      { val := (antidiagonal n).disjiUnion
          (fun ab => (aux d ab.2).1.map {
              toFun := Fin.cons (ab.1)
              inj' := Fin.cons_right_injective _ })
          (fun i _hi j _hj hij => Finset.disjoint_left.2 fun t hti htj => hij <| by
            simp_rw [Finset.mem_map, Embedding.coeFn_mk] at hti htj
            obtain ⟨ai, hai, hij'⟩ := hti
            obtain ⟨aj, haj, rfl⟩ := htj
            rw [Fin.cons_inj] at hij'
            ext
            · exact hij'.1
            · obtain ⟨-, rfl⟩ := hij'
              rw [← (aux d i.2).prop ai |>.mp hai, ← (aux d j.2).prop ai |>.mp haj])
        property := fun f => by
          simp_rw [mem_disjiUnion, mem_antidiagonal, mem_map, Embedding.coeFn_mk, Prod.exists,
            (aux d _).prop, Fin.sum_univ_succ]
          constructor
          · rintro ⟨a, b, rfl, g, rfl, rfl⟩
            simp only [Fin.cons_zero, Fin.cons_succ]
          · intro hf
            exact ⟨_, _, hf, _, rfl, Fin.cons_self_tail f⟩ }

@[simp] lemma mem_finAntidiagonal {d : ℕ} {f : Fin d → μ} :
    f ∈ finAntidiagonal d n ↔ ∑ i, f i = n := (finAntidiagonal.aux d n).prop f

/-!
### `ι → μ`

In this section, we transfer the antidiagonals in `Fin s.card → μ` to antidiagonals in `ι → s` by
choosing an identification `s ≃ Fin s.card` and proving that the end result does not depend on that
choice.
-/

/-- The finset of functions `ι → μ` with support contained in `s` and sum `n`. -/
def piAntidiag (s : Finset ι) (n : μ) : Finset (ι → μ) := by
  refine (Fintype.truncEquivFinOfCardEq <| Fintype.card_coe s).lift
    (fun e ↦ (finAntidiagonal s.card n).map ⟨fun f i ↦ if hi : i ∈ s then f (e ⟨i, hi⟩) else 0, ?_⟩)
    fun e₁ e₂ ↦ ?_
  · rintro f g hfg
    ext i
    simpa using congr_fun hfg (e.symm i)
  · ext f
    simp only [mem_map, mem_finAntidiagonal]
    refine Equiv.exists_congr ((e₁.symm.trans e₂).arrowCongr <| .refl _) fun g ↦ ?_
    have := Fintype.sum_equiv (e₂.symm.trans e₁) _ g fun _ ↦ rfl
    aesop

variable {s : Finset ι} {n : μ} {f : ι → μ}

@[simp] lemma mem_piAntidiag : f ∈ piAntidiag s n ↔ s.sum f = n ∧ ∀ i, f i ≠ 0 → i ∈ s := by
  rw [piAntidiag]
  induction' Fintype.truncEquivFinOfCardEq (Fintype.card_coe s) using Trunc.ind with e
  simp only [Trunc.lift_mk, mem_map, mem_finAntidiagonal, Embedding.coeFn_mk]
  constructor
  · rintro ⟨f, ⟨hf, rfl⟩, rfl⟩
    rw [sum_dite_of_true fun _ ↦ id]
    exact ⟨Fintype.sum_equiv e _ _ (by simp), by simp +contextual⟩
  · rintro ⟨rfl, hf⟩
    refine ⟨f ∘ (↑) ∘ e.symm, ?_, by ext i; have := not_imp_comm.1 (hf i); aesop⟩
    rw [← sum_attach s]
    exact Fintype.sum_equiv e.symm _ _ (by simp)

@[simp] lemma piAntidiag_empty_zero : piAntidiag (∅ : Finset ι) (0 : μ) = {0} := by
  ext; simp [Fintype.sum_eq_zero_iff_of_nonneg, funext_iff, not_imp_comm, ← forall_and]

@[simp] lemma piAntidiag_empty_of_ne_zero (hn : n ≠ 0) : piAntidiag (∅ : Finset ι) n = ∅ :=
  eq_empty_of_forall_notMem (by simp [@eq_comm _ 0, hn.symm])

lemma piAntidiag_empty (n : μ) : piAntidiag (∅ : Finset ι) n = if n = 0 then {0} else ∅ := by
  split_ifs with hn <;> simp [*]

lemma finsetCongr_piAntidiag_eq_antidiag (n : μ) :
    Equiv.finsetCongr (Equiv.boolArrowEquivProd _) (piAntidiag univ n) = antidiagonal n := by
  ext ⟨x₁, x₂⟩
  simp_rw [Equiv.finsetCongr_apply, mem_map, Equiv.toEmbedding, Function.Embedding.coeFn_mk,
    ← Equiv.eq_symm_apply]
  simp [add_comm]

end AddCommMonoid

section AddCancelCommMonoid
variable [DecidableEq ι] [AddCancelCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ] {i : ι}
  {s : Finset ι}

lemma pairwiseDisjoint_piAntidiag_map_addRightEmbedding (hi : i ∉ s) (n : μ) :
    (antidiagonal n : Set (μ × μ)).PairwiseDisjoint fun p ↦
      map (addRightEmbedding fun j ↦ if j = i then p.1 else 0) (s.piAntidiag p.2) := by
  rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd
  simp only [ne_eq, antidiagonal_congr' hab hcd, disjoint_left, mem_map, mem_piAntidiag,
    addRightEmbedding_apply, not_exists, not_and, and_imp, forall_exists_index]
  rintro hfg _ f rfl - rfl g rfl - hgf
  exact hfg <| by simpa [sum_add_distrib, hi] using congr_arg (∑ j ∈ s, · j) hgf.symm

lemma piAntidiag_cons (hi : i ∉ s) (n : μ) :
    piAntidiag (cons i s hi) n = (antidiagonal n).disjiUnion (fun p : μ × μ ↦
      (piAntidiag s p.snd).map (addRightEmbedding fun t ↦ if t = i then p.fst else 0))
        (pairwiseDisjoint_piAntidiag_map_addRightEmbedding hi _) := by
  ext f
  simp only [mem_piAntidiag, sum_cons, ne_eq, mem_cons, mem_disjiUnion, mem_antidiagonal, mem_map,
    addLeftEmbedding_apply, Prod.exists]
  constructor
  · rintro ⟨hn, hf⟩
    refine ⟨_, _, hn, update f i 0, ⟨sum_update_of_notMem hi _ _, fun j ↦ ?_⟩, by aesop⟩
    have := fun h₁ h₂ ↦ (hf j h₁).resolve_left h₂
    aesop (add simp [update])
  · rintro ⟨a, _, hn, g, ⟨rfl, hg⟩, rfl⟩
    have := hg i
    aesop (add simp [sum_add_distrib])

lemma piAntidiag_insert [DecidableEq (ι → μ)] (hi : i ∉ s) (n : μ) :
    piAntidiag (insert i s) n = (antidiagonal n).biUnion fun p : μ × μ ↦ (piAntidiag s p.snd).image
      (fun f j ↦ f j + if j = i then p.fst else 0) := by
  simpa [map_eq_image, addRightEmbedding] using piAntidiag_cons hi n

end AddCancelCommMonoid

section CanonicallyOrderedAddCommMonoid
variable [DecidableEq ι] [AddCommMonoid μ] [PartialOrder μ]
  [CanonicallyOrderedAdd μ] [HasAntidiagonal μ] [DecidableEq μ]

@[simp] lemma piAntidiag_zero (s : Finset ι) : piAntidiag s (0 : μ) = {0} := by
  ext; simp [funext_iff, not_imp_comm, ← forall_and]

end CanonicallyOrderedAddCommMonoid

section Nat
variable [DecidableEq ι]

/-- Local notation for the pointwise operation `n • s := {n • a | a ∈ s}` to avoid conflict with the
pointwise operation `n • s := s + ... + s` (`n` times). -/
local infixr:73 "•ℕ" => @SMul.smul _ _ Finset.smulFinset

lemma piAntidiag_univ_fin_eq_antidiagonalTuple (n k : ℕ) :
    piAntidiag univ n = Nat.antidiagonalTuple k n := by
  ext; simp [Nat.mem_antidiagonalTuple]

lemma nsmul_piAntidiag [DecidableEq (ι → ℕ)] (s : Finset ι) (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    n •ℕ piAntidiag s m = {f ∈ piAntidiag s (n * m) | ∀ i ∈ s, n ∣ f i} := by
  ext f
  refine mem_smul_finset.trans ?_
  simp only [mem_smul_finset, mem_filter, mem_piAntidiag, Function.Embedding.coeFn_mk, exists_prop,
    and_assoc]
  constructor
  · rintro ⟨f, rfl, hf, rfl⟩
    simpa [← mul_sum, hn] using hf
  rintro ⟨hfsum, hfsup, hfdvd⟩
  have (i) : n ∣ f i := by
    by_cases hi : i ∈ s
    · exact hfdvd _ hi
    · rw [not_imp_comm.1 (hfsup _) hi]
      exact dvd_zero _
  refine ⟨fun i ↦ f i / n, ?_⟩
  simp [funext_iff, Nat.mul_div_cancel', ← Nat.sum_div, *]
  aesop

lemma map_nsmul_piAntidiag (s : Finset ι) (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (piAntidiag s m).map
      ⟨(n • ·), fun _ _ h ↦ funext fun i ↦ mul_right_injective₀ hn (congr_fun h i)⟩ =
        {f ∈ piAntidiag s (n * m) | ∀ i ∈ s, n ∣ f i} := by
  classical rw [map_eq_image]; exact nsmul_piAntidiag _ _ hn

lemma nsmul_piAntidiag_univ [Fintype ι] (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    n •ℕ (piAntidiag univ m) = {f ∈ piAntidiag (univ : Finset ι) (n * m) | ∀ i, n ∣ f i} := by
  simpa using nsmul_piAntidiag (univ : Finset ι) m hn

lemma map_nsmul_piAntidiag_univ [Fintype ι] (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (piAntidiag (univ : Finset ι) m).map
        ⟨(n • ·), fun _ _ h ↦ funext fun i ↦ mul_right_injective₀ hn (congr_fun h i)⟩ =
      {f ∈ piAntidiag (univ : Finset ι) (n * m) | ∀ i, n ∣ f i} := by
  simpa using map_nsmul_piAntidiag (univ : Finset ι) m hn

end Nat

lemma map_sym_eq_piAntidiag [DecidableEq ι] (s : Finset ι) (n : ℕ) :
    (s.sym n).map ⟨fun m a ↦ m.1.count a, Multiset.count_injective.comp Sym.coe_injective⟩ =
      piAntidiag s n := by
  ext f
  simp only [Sym.val_eq_coe, mem_map, mem_sym_iff, Embedding.coeFn_mk, funext_iff, Sym.exists,
    Sym.mem_mk, Sym.coe_mk, exists_and_left, exists_prop, mem_piAntidiag, ne_eq]
  constructor
  · rintro ⟨m, hm, rfl, hf⟩
    simpa [← hf, Multiset.sum_count_eq_card hm]
  · rintro ⟨rfl, hf⟩
    refine ⟨∑ a ∈ s, f a • {a}, ?_, ?_⟩
    · simp +contextual
    · simpa [Multiset.count_sum', Multiset.count_singleton, not_imp_comm, eq_comm (a := 0)] using hf

end Finset
