/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.RingTheory.MvPolynomial.Groebner
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
public import Mathlib.Algebra.MonoidAlgebra.Defs

/-! # Alon's Combinatorial Nullstellensatz

This is a formalization of Noga Alon's Combinatorial Nullstellensatz. It follows [Alon_1999].

We consider a family `S : σ → Finset R` of finite subsets of a domain `R`
and a multivariate polynomial `f` in `MvPolynomial σ R`.
The combinatorial Nullstellensatz gives combinatorial constraints for
the vanishing of `f` at any `x : σ → R` such that `x s ∈ S s` for all `s`.

- `MvPolynomial.eq_zero_of_eval_zero_at_prod_finset` :
  if `f` vanishes at any such point and `f.degreeOf s < #(S s)` for all `s`,
  then `f = 0`.

- `combinatorial_nullstellensatz_exists_linearCombination`
  If `f` vanishes at every such point, then it can be written as a linear combination
  `f = linearCombination (MvPolynomial σ R) (fun i ↦ ∏ r ∈ S i, (X i - C r)) h`,
  for some `h : σ →₀ MvPolynomial σ R` such that
  `((∏ r ∈ S s, (X i - C r)) * h i).totalDegree ≤ f.totalDegree` for all `s`.

- `combinatorial_nullstellensatz_exists_eval_nonzero`
  a multi-index `t : σ →₀ ℕ` such that `t s < (S s).card` for all `s`,
  `f.totalDegree = t.degree` and `f.coeff t ≠ 0`,
  there exists a point `x : σ → R` such that `x s ∈ S s` for all `s` and `f.eval s ≠ 0`.

- `combinatorial_nullstellensatz_exists_eval_nonzero_of_maximal`
  The hypothesis `f.totalDegree = t.degree` can be weakened to the requirement that
  `t` is maximal in the support of `f` in the pointwise order on `σ →₀ ℕ`.

## TODO

- Applications
- relation with Schwartz–Zippel lemma, as in [Rote_2023]

## References

- [Alon, *Combinatorial Nullstellensatz*][Alon_1999]

- [Lasoń, *A generalization of Combinatorial Nullstellensatz*][Lason_2013]

- [Rote, *The Generalized Combinatorial Lasoń-Alon-Zippel-Schwartz
  Nullstellensatz Lemma*][Rote_2023]

-/

public section

open Finsupp

open scoped Finset

variable {R : Type*} [CommRing R]

namespace MvPolynomial

open Finsupp Function

/-- A multivariate polynomial that vanishes on a large product finset is the zero polynomial. -/
theorem eq_zero_of_eval_zero_at_prod_finset {σ : Type*} [Finite σ] [IsDomain R]
    (P : MvPolynomial σ R) (S : σ → Finset R)
    (Hdeg : ∀ i, P.degreeOf i < #(S i))
    (Heval : ∀ (x : σ → R), (∀ i, x i ∈ S i) → eval x P = 0) :
    P = 0 := by
  induction σ using Finite.induction_empty_option with
  | @of_equiv σ τ e h =>
    suffices MvPolynomial.rename e.symm P = 0 by
      have that := MvPolynomial.rename_injective (R := R) e.symm (e.symm.injective)
      rw [RingHom.injective_iff_ker_eq_bot] at that
      rwa [← RingHom.mem_ker, that] at this
    apply h _ (fun i ↦ S (e i))
    · intro i
      convert! Hdeg (e i)
      conv_lhs => rw [← e.symm_apply_apply i, degreeOf_rename_of_injective e.symm.injective]
    · intro x hx
      simp only [MvPolynomial.eval_rename]
      apply Heval
      intro s
      simp only [Function.comp_apply]
      convert! hx (e.symm s)
      simp only [Equiv.apply_symm_apply]
  | h_empty =>
    suffices P = C (constantCoeff P) by
      specialize Heval default (fun i ↦ PEmpty.elim i)
      rw [this, eval_C] at Heval
      rw [this, Heval, C_0]
    ext m
    suffices m = 0 by simp [this, constantCoeff_eq]
    ext d; exact PEmpty.elim d
  | @h_option σ _ h =>
    set Q := optionEquivLeft R σ P with hQ
    suffices Q = 0 by
      rw [← AlgEquiv.symm_apply_apply (optionEquivLeft R σ) P, ← hQ, this, map_zero]
    have Heval' (x : σ → R) (hx : ∀ i, x i ∈ S (some i)) : Polynomial.map (eval x) Q = 0 := by
      apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ (S none)
      · intro y hy
        rw [← optionEquivLeft_elim_eval]
        apply Heval
        simp only [Option.forall, Option.elim_none, hy, Option.elim_some, hx, implies_true,
          and_self]
      · apply lt_of_le_of_lt _ (Hdeg none)
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro d hd
        simp only [hQ]
        rw [MvPolynomial.coeff_eval_eq_eval_coeff]
        convert! map_zero (MvPolynomial.eval x)
        ext m
        simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
        set n := (embDomain Function.Embedding.some m).update none d with hn
        rw [eq_option_embedding_update_none_iff] at hn
        rw [← hn.1, ← hn.2, optionEquivLeft_coeff_some_coeff_none]
        by_contra hm
        apply not_le.mpr hd
        rw [MvPolynomial.degreeOf_eq_sup]
        rw [← ne_eq, ← MvPolynomial.mem_support_iff] at hm
        convert! Finset.le_sup hm
        exact hn.1.symm
    ext m d
    suffices Q.coeff m = 0 by simp [this]
    apply h _ (fun i ↦ S (some i))
    · intro i
      apply lt_of_le_of_lt _ (Hdeg (some i))
      simp only [degreeOf_eq_sup, Finset.sup_le_iff, mem_support_iff, ne_eq]
      intro e he
      set n := (embDomain Function.Embedding.some e).update none m with hn
      rw [eq_option_embedding_update_none_iff] at hn
      rw [hQ, ← hn.1, ← hn.2, optionEquivLeft_coeff_some_coeff_none, ← ne_eq,
        ← MvPolynomial.mem_support_iff] at he
      convert! Finset.le_sup he
      rw [← hn.2, some_apply]
    · intro x hx
      specialize Heval' x hx
      rw [Polynomial.ext_iff] at Heval'
      simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using Heval' m

open MonomialOrder

/- Here starts the actual proof of the combinatorial Nullstellensatz -/

variable {σ : Type*}

/-- The polynomial in `X i` that vanishes at all elements of `S`. -/
private noncomputable def Alon.P (S : Finset R) (i : σ) : MvPolynomial σ R :=
  ∏ r ∈ S, (X i - C r)

/-- The degree of `Alon.P S i` with respect to `X i` is the cardinality of `S`,
  and `0` otherwise. -/
private theorem Alon.degree_P [Nontrivial R] (m : MonomialOrder σ) (S : Finset R) (i : σ) :
    m.degree (Alon.P S i) = single i #S := by
  simp only [P]
  rw [degree_prod_of_regular]
  · simp [Finset.sum_congr rfl (fun r _ ↦ m.degree_X_sub_C i r)]
  · intro r _
    rw [m.monic_X_sub_C]
    exact isRegular_one

/-- The leading coefficient of `Alon.P S i` is `1`. -/
private theorem Alon.monic_P (m : MonomialOrder σ) (S : Finset R) (i : σ) :
    m.Monic (P S i) :=
  Monic.prod (fun r _ ↦ m.monic_X_sub_C i r)

/-- The **Combinatorial Nullstellensatz**.

If `f` vanishes at every point `x : σ → R` such that `x s ∈ S s` for all `s`,
then it can be written as a linear combination
`f = linearCombination (MvPolynomial σ R) (fun i ↦ (∏ r ∈ S i, (X i - C r))) h`,
for some `h : σ →₀ MvPolynomial σ R` such that
`((∏ r ∈ S s, (X i - C r)) * h i).totalDegree ≤ f.totalDegree` for all `s`.

[Alon_1999], theorem 1. -/
theorem combinatorial_nullstellensatz_exists_linearCombination
    [IsDomain R] [Finite σ] (S : σ → Finset R) (Sne : ∀ i, (S i).Nonempty)
    (f : MvPolynomial σ R) (Heval : ∀ (x : σ → R), (∀ i, x i ∈ S i) → eval x f = 0) :
    ∃ (h : σ →₀ MvPolynomial σ R),
      (∀ i, ((∏ s ∈ S i, (X i - C s)) * h i).totalDegree ≤ f.totalDegree) ∧
      f = linearCombination (MvPolynomial σ R) (fun i ↦ ∏ r ∈ S i, (X i - C r)) h := by
  let : LinearOrder σ := WellOrderingRel.isWellOrder.linearOrder
  obtain ⟨h, r, hf, hh, hr⟩ := degLex.div (b := fun i ↦ Alon.P (S i) i)
      (fun i ↦ by simp only [(Alon.monic_P ..).leadingCoeff_eq_one, isUnit_one]) f
  suffices hr' : r = 0 by
    rw [hr', add_zero] at hf
    exact ⟨h, fun i ↦ degLex_totalDegree_monotone (hh i), hf⟩
  apply eq_zero_of_eval_zero_at_prod_finset r S
  · intro i
    rw [degreeOf_eq_sup, Finset.sup_lt_iff (by simp [Sne i])]
    aesop (add simp [Alon.degree_P])
  · intro x hx
    rw [Iff.symm sub_eq_iff_eq_add'] at hf
    rw [← hf, map_sub, Heval x hx, zero_sub, neg_eq_zero,
      linearCombination_apply, map_finsuppSum, sum, Finset.sum_eq_zero]
    intro i _
    rw [smul_eq_mul, map_mul]
    convert! mul_zero _
    rw [Alon.P, _root_.map_prod]
    apply Finset.prod_eq_zero (hx i)
    simp

/-- Key recurrence for the coefficients of the quotient `g` in `f = g * (X i - C r) + h`
where `h` does not involve `X i`. -/
private lemma Lason.coeff_recurrence {i : σ} {r : R} {g h f : MvPolynomial σ R}
    (hfgh : f = g * (X i - C r) + h) (hdeg : h.degreeOf i = 0) (m : σ →₀ ℕ) :
    f.coeff (m + single i 1) = g.coeff m - r * g.coeff (m + single i 1) := by
  simp only [hfgh, mul_sub, mul_comm g (C r), AddMonoidAlgebra.coeff_add, coeff_mul_X,
    AddMonoidAlgebra.coeff_sub, coe_add, coe_sub, Pi.add_apply, Pi.sub_apply, coeff_C_mul,
    add_eq_left]
  by_contra! h'
  have := monomial_le_degreeOf i (MvPolynomial.mem_support_iff.mpr h')
  simp only [coe_add, Pi.add_apply, single_eq_same] at this
  lia

/-- If `f.coeff (m + single i c) = 0` for all `c > 0`, then `g.coeff m = 0`, where `g` is the
quotient in `f = g * (X i - C r) + h` and `h` does not involve `X i`. -/
private lemma Lason.coeff_quotient_eq_zero {i : σ} {r : R} {g h f : MvPolynomial σ R}
    (hfgh : f = g * (X i - C r) + h) (hdeg : h.degreeOf i = 0)
    (m : σ →₀ ℕ) (hm : ∀ c, 0 < c → f.coeff (m + single i c) = 0) :
    g.coeff m = 0 := by
  have key (n : ℕ) : g.coeff m = r ^ n * g.coeff (m + single i n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hrec := Lason.coeff_recurrence hfgh hdeg (m + single i n)
      rw [add_assoc, ← single_add, hm (n + 1) n.succ_pos, eq_comm, sub_eq_zero] at hrec
      rw [ih, hrec]
      ring
  rw [key (g.totalDegree + 1)]
  refine mul_eq_zero_of_right _ (coeff_eq_zero_of_totalDegree_lt ?_)
  have hmem : i ∈ (m + single i (g.totalDegree + 1)).support := by simp
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hmem)
  simp only [coe_add, Pi.add_apply, single_eq_same]
  linarith

/-- The **Generalized Combinatorial Nullstellensatz**.

Given a multi-index `t : σ →₀ ℕ` which is maximal in the support of `f`, in the sense that
`f.coeff t ≠ 0` while `f.coeff t' = 0` for every `t' > t` for the pointwise order on `σ →₀ ℕ`, and
such that `t s < (S s).card` for all `s`, there exists a point `x : σ → R` such that `x s ∈ S s` for
all `s` and `f.eval s ≠ 0`.

[Lason_2013], theorem 2 -/
theorem combinatorial_nullstellensatz_exists_eval_nonzero_of_maximal
    [IsDomain R] (f : MvPolynomial σ R) (t : σ →₀ ℕ) (ht : f.coeff t ≠ 0)
    (ht' : ∀ t' : σ →₀ ℕ, t < t' → f.coeff t' = 0) (S : σ → Finset R) (htS : ∀ i, t i < #(S i)) :
    ∃ s : σ → R, (∀ i, s i ∈ S i) ∧ eval s f ≠ 0 := by
  classical
  suffices h : ∀ (n : ℕ) (f : MvPolynomial σ R) (t : σ →₀ ℕ), t.degree = n →
      f.coeff t ≠ 0 → (∀ t' : σ →₀ ℕ, t < t' → f.coeff t' = 0) →
      ∀ (S : σ → Finset R), (∀ i, t i < #(S i)) →
      ∃ s : σ → R, (∀ i, s i ∈ S i) ∧ eval s f ≠ 0 by
    exact h t.degree f t rfl ht ht' S htS
  intro n
  induction n with
  | zero =>
    intro f t ht htc htmax S hScard
    rw [Finsupp.degree_eq_zero_iff] at ht
    subst ht
    simp only [coe_zero, Pi.zero_apply, Finset.card_pos] at hScard
    refine ⟨(hScard · |>.choose), (hScard · |>.choose_spec), ?_⟩
    suffices hf : f = C f.constantCoeff by
      rw [hf]
      simpa only [constantCoeff_eq, eval_C, ne_eq] using htc
    ext t
    by_cases ht : t = 0
    · rw [constantCoeff_eq, coeff_C, ht]
      rfl
    · rw [htmax _ (pos_of_ne_zero ht), coeff_C, right_eq_ite_iff]
      exact fun h ↦ ((h ▸ ht) rfl).elim
  | succ n ih =>
    intro f t ht htc htmax S hScard
    obtain ⟨i, hi⟩ : t.support.Nonempty :=
      support_nonempty_iff.mpr (n.succ_ne_zero <| · ▸ ht |>.symm)
    rw [Finsupp.mem_support_iff] at hi
    obtain ⟨r, hr⟩ := Finset.card_pos.mp (Nat.zero_lt_of_lt (hScard i))
    obtain ⟨g, hg⟩ := X_sub_C_dvd_sub_bind₁_update f i r
    have hdeg : (bind₁ (Function.update X i (C r)) f).degreeOf i = 0 :=
      degreeOf_bind₁_update_self_eq_zero f i r
    set h := bind₁ (Function.update X i (C r)) f with hhdef
    have hfgh : f = g * (X i - C r) + h := mul_comm _ g ▸ eq_add_of_sub_eq hg
    by_cases hy : ∃ y : σ → R, (∀ j, y j ∈ S j) ∧ eval y h ≠ 0
    · obtain ⟨y, _, hy⟩ := hy
      refine ⟨Function.update y i r, by grind, ?_⟩
      rw [hfgh, map_add, map_mul, map_sub, eval_X, eval_C, Function.update_self, sub_self, mul_zero,
        zero_add]
      convert hy using 1
      refine eval₂Hom_congr' rfl (fun _ h _ ↦ Function.update_of_ne ?_ _ _) rfl
      rintro rfl
      exact mem_vars_iff_degreeOf_ne_zero.mp h hdeg
    · simp only [not_exists, not_and, not_not] at hy
      set t₀ := t - single i 1 with ht₀def
      have hcancel : t₀ + single i 1 = t := ht₀def ▸ sub_add_single_one_cancel hi
      have hB : g.coeff t₀ = f.coeff t := by
        have : g.coeff t = 0 := Lason.coeff_quotient_eq_zero hfgh hdeg t fun _ _ ↦ htmax _ <|
          lt_of_le_of_ne le_self_add fun _ ↦ by grind only [Finsupp.add_apply, single_eq_same]
        grind only [Lason.coeff_recurrence]
      have hgmax (u : σ →₀ ℕ) (hu : t₀ < u) : g.coeff u = 0 := by
        refine Lason.coeff_quotient_eq_zero hfgh hdeg u fun c hc ↦ htmax _ ?_
        obtain ⟨hle, hne⟩ := lt_iff_le_and_ne.mp hu
        refine lt_of_le_of_ne (hcancel ▸ add_le_add hle (single_le_single.mpr hc)) ?_
        rintro rfl
        obtain ⟨j, hj⟩ := ne_iff.mp hne
        have : t₀ j < u j := lt_of_le_of_ne (hle _) hj
        have : u j + single i c j = t₀ j + (single i 1) j := by
          rw [← Pi.add_apply, ← coe_add, ← hcancel, add_apply]
        grind only [single_apply]
      set S' : σ → Finset R := Function.update S i ((S i).erase r) with hS'def
      obtain ⟨s, hs, hsg⟩ := ih g t₀ (by grind only [map_add, degree_single]) (hB ▸ htc) hgmax
        (Function.update S i ((S i).erase r)) <| by
          grind only [tsub_apply, Function.update, single_apply, Finset.card_erase_of_mem]
      have hsS : ∀ j, s j ∈ S j := by grind only [Function.update, Finset.mem_erase]
      refine ⟨s, hsS, ?_⟩
      rw [hfgh, map_add, map_mul, map_sub, eval_X, eval_C, hy s hsS, add_zero]
      exact mul_ne_zero hsg (sub_ne_zero.mpr
        (Finset.mem_erase.mp (Function.update_self i _ _ ▸ (hs i))).1)

/-- The **Combinatorial Nullstellensatz**.

Given a multi-index `t : σ →₀ ℕ` such that `t s < (S s).card` for all `s`,
`f.totalDegree = t.degree` and `f.coeff t ≠ 0`,
there exists a point `x : σ → R` such that `x s ∈ S s` for all `s` and `f.eval s ≠ 0`.

[Alon_1999], theorem 2 -/
theorem combinatorial_nullstellensatz_exists_eval_nonzero [IsDomain R]
    (f : MvPolynomial σ R)
    (t : σ →₀ ℕ) (ht₁ : f.coeff t ≠ 0) (ht₂ : f.totalDegree = t.degree)
    (S : σ → Finset R) (htS : ∀ i, t i < #(S i)) :
    ∃ s : σ → R, (∀ i, s i ∈ S i) ∧ eval s f ≠ 0 :=
  combinatorial_nullstellensatz_exists_eval_nonzero_of_maximal f t ht₁
    (fun _ h ↦ coeff_eq_zero_of_totalDegree_lt
      (by rw [ht₂, ← degree_apply]; exact degree_strictMono h)) S htS

end MvPolynomial
