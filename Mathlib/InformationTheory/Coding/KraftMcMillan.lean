/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

public import Mathlib.InformationTheory.Coding.UniquelyDecodable

/-!
# Kraft-McMillan Inequality

This file proves the Kraft-McMillan inequality for uniquely decodable codes.

## Main definitions

* `concatFn`: Concatenation of `r` codewords into a single string.

## Main results

* `kraft_mcmillan_inequality`: For a uniquely decodable code `S` over an alphabet of size
  `D`, `∑_{w ∈ S} D^{-|w|} ≤ 1`.

The proof uses a counting argument: the `r`-th power of the Kraft sum counts concatenations of
`r` codewords, weighted by length. Since the code is uniquely decodable, these concatenations are
distinct, and the count is bounded by the number of strings of each length.

## References

* McMillan, B. (1956), "Two inequalities implied by unique decipherability"
-/

namespace InformationTheory

variable {α : Type*}

section concatFn

variable {S : Finset (List α)} {r : ℕ}

private def concatFn (w : Fin r → S) : List α :=
  (List.ofFn (fun i => (w i).val)).flatten

private lemma concatFn.length (w : Fin r → S) :
    (concatFn w).length = ∑ i : Fin r, ((w i).val).length := by
  simp [List.sum_ofFn, concatFn]

end concatFn

/-- For uniquely decodable codes, the concatenation map is injective.

This is the key property: distinct tuples of codewords produce distinct concatenations. -/
private lemma uniquely_decodable_concatFn_injective {S : Finset (List α)}
    (h : UniquelyDecodable (S : Set (List α))) (r : ℕ) :
    Function.Injective (concatFn (S := S) (r := r)) := by
  intro w1 w2 hflat
  -- package tuples as subtype-lists
  let pack (w: Fin r → S) : {L : List (List α) // ∀ x ∈ L, x ∈ S} :=
    ⟨List.ofFn (fun i : Fin r => (w i).val), by
      intro x hx
      rcases List.mem_ofFn.mp hx with ⟨i, rfl⟩
      exact (w i).prop⟩
  have hpack : pack w1 = pack w2 := by
    apply (UniquelyDecodable.flatten_injective h)
    simpa using hflat
  funext i
  apply Subtype.ext
  simpa using congrArg (fun f => f i) (List.ofFn_injective (congrArg Subtype.val hpack))

private lemma disjoint_filter_eq_of_ne {β γ : Type*} [DecidableEq γ] {S : Finset β}
    (f : β → γ) {a b : γ} (hab : a ≠ b) :
    Disjoint (S.filter (fun x => f x = a)) (S.filter (fun x => f x = b)) := by
  apply Finset.disjoint_left.mpr
  intro x hx1 hx2
  apply hab
  exact (Finset.mem_filter.mp hx1).right ▸ (Finset.mem_filter.mp hx2).right ▸ rfl

private lemma sum_pow_len_filter_le_one_of_card_le [Fintype α] [Nonempty α]
    {T : Finset (List α)} {s : ℕ}
    (h_card : (T.filter (fun x => x.length = s)).card ≤ (Fintype.card α) ^ s) :
    (∑ x ∈ T.filter (fun x => x.length = s),
    (1 / (Fintype.card α : ℕ) : ℝ) ^ x.length) ≤ 1 := by
  let D : ℕ := Fintype.card α
  have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Fintype.card_pos : 0 < D)
  -- rewrite exponents x.length = s on the filter
  have : (∑ x ∈ T.filter (fun x => x.length = s), (1 / (D : ℝ)) ^ x.length)
       = (∑ x ∈ T.filter (fun x => x.length = s), (1 / (D : ℝ)) ^ s) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxlen : x.length = s := (Finset.mem_filter.mp hx).right
    simp [hxlen]
  -- now it is card * (1/D)^s, use card bound
  calc
    (∑ x ∈ T.filter (fun x => x.length = s), (1 / (D : ℝ)) ^ x.length)
        = (T.filter (fun x => x.length = s)).card * (1 / (D : ℝ)) ^ s := by
            simp only [this, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (D ^ s) * (1 / D) ^ s := by
            refine mul_le_mul_of_nonneg_right (by exact_mod_cast h_card) (by positivity)
    _ = 1 := by simp [hD0]

/-- The `r`-th power of the Kraft sum equals the sum over all `r`-tuples of codewords.

This expansion is the key algebraic identity in the Kraft-McMillan proof. -/
private lemma kraft_sum_pow_eq_sum_concatFn {S : Finset (List α)} {D : ℕ} {r : ℕ} :
    (∑ c ∈ S, (1 / (D : ℝ)) ^ c.length) ^ r =
    ∑ w : Fin r → S, (1 / (D : ℝ)) ^ (concatFn w).length := by
  -- Distribute the product of identical sums and reindex into functions `Fin r → S`.
  have h_expand :
      (∏ _i : Fin r, (∑ w ∈ S, (1 / (D : ℝ)) ^ w.length)) =
      ∑ w : Fin r → S, ∏ i : Fin r, (1 / (D : ℝ)) ^ (w i).val.length := by
    -- distribute product over sums (over `Finset.univ`)
    rw [Finset.prod_sum, Finset.sum_bij]
    · intros a ha i
      exact ⟨a i (Finset.mem_univ i), (Finset.mem_pi.mp ha i (Finset.mem_univ i))⟩
    · simp
    · intro a₁ ha₁ a₂ ha₂
      simp [funext_iff]
    · intro b hb
      exact ⟨(fun i _ => (b i).val), (Finset.mem_pi.mpr (by simp)), rfl⟩
    · simp
  have hprod (w : Fin r → S):
      (∏ i : Fin r, (1 / (D : ℝ)) ^ (w i).val.length) =
      (1 / (D : ℝ)) ^ (∑ i : Fin r, (w i).val.length) := by
    simpa using
      (Finset.prod_pow_eq_pow_sum
        (s := (Finset.univ : Finset (Fin r)))
        (f := fun i : Fin r => (w i).val.length)
        (a := (1 / (D : ℝ))))
  have h_term (w : Fin r → S) :
      (∏ i : Fin r, (1 / (D : ℝ)) ^ (w i).val.length) =
      (1 / (D : ℝ)) ^ (concatFn w).length := by
    simpa [concatFn.length w] using (hprod w)
  calc
    (∑ w ∈ S, (1 / (D : ℝ)) ^ w.length) ^ r
        = ∏ _i : Fin r, (∑ w ∈ S, (1 / (D : ℝ)) ^ w.length) := by simp
    _ = ∑ w : Fin r → S, ∏ i : Fin r, (1 / (D : ℝ)) ^ (w i).val.length := h_expand
    _ = ∑ w : Fin r → S, (1 / (D : ℝ)) ^ (concatFn w).length := by
        grind

/-- The number of strings of length `s` in any set is at most `D^s`
(the total number of such strings). -/
private lemma card_filter_length_eq_le [Fintype α] (T : Finset (List α)) (s : ℕ) :
    (T.filter (fun x => x.length = s)).card ≤ (Fintype.card α) ^ s := by
  classical
  let all_words : Finset (List α) := (Finset.univ : Finset (Fin s → α)).image List.ofFn
  have hsub : T.filter (fun x => x.length = s) ⊆ all_words := by
    intro a ha
    have halen : a.length = s := (Finset.mem_filter.mp ha).right
    apply Finset.mem_image.mpr
    refine ⟨(fun j : Fin s => a.get ⟨j.1, by simp [halen]⟩), ?_, ?_⟩
    · exact Finset.mem_univ _
    · exact List.ext_get (by simp [halen]) (by simp)
  have hcard_all : all_words.card = Fintype.card α ^ s := by
    -- `List.ofFn` is injective, so the image has the same cardinality as the domain.
    simpa using
      (Finset.card_image_of_injective
        (s := (Finset.univ : Finset (Fin s → α)))
        (f := (List.ofFn : (Fin s → α) → List α))
        List.ofFn_injective)
  calc
    (T.filter (fun x => x.length = s)).card
        ≤ all_words.card := Finset.card_le_card hsub
    _ = Fintype.card α ^ s := hcard_all

/-- If `S` is uniquely decodable, then `(Σ 2^{-|w|})^r ≤ r·maxLen`
where `maxLen` is the maximum codeword length.

This auxiliary bound is the heart of the Kraft-McMillan proof. The r-th power of the Kraft sum
counts concatenations of r codewords, which by unique decodability are distinct.
Since these concatenations have lengths between r and r·maxLen,
we get at most r·maxLen - r + 1 ≤ r·maxLen terms. -/
private lemma kraft_mcmillan_inequality_aux {S : Finset (List α)} [Fintype α] [Nonempty α]
    (h : UniquelyDecodable (S : Set (List α))) (r : ℕ) (hr : r ≥ 1) :
    (∑ w ∈ S, (1 / (Fintype.card α) : ℝ) ^ w.length) ^ r ≤ r * (Finset.sup S List.length) := by
  classical
  -- Let $maxLen = \max_{w \in S} |w|$.
  set maxLen := (S.sup List.length) with hmaxLen_def
  let D := Fintype.card α
  -- Since the map $(w_1,\dots,w_r) \mapsto w_1 \cdots w_r$ is injective,
  -- the sum $\sum_{w_1,\dots,w_r \in S} 2^{-|w_1 \cdots w_r|}$
  -- is at most $\sum_{s=r}^{r\ell} \sum_{x \in \{0,1\}^s} 2^{-|x|}$.
  let T : Finset (List α) := Finset.image concatFn (Finset.univ : Finset (Fin r → S))
  have h_injective :
    ∑ w : Fin r → S, (1 / D : ℝ) ^ ((concatFn w).length)
      ≤ ∑ s ∈ Finset.Icc r (r * maxLen),
          ∑ x ∈ T.filter (fun x => x.length = s), (1 / D : ℝ) ^ x.length := by
    rw [← Finset.sum_biUnion]
    · apply le_of_eq
      refine Finset.sum_bij (fun w _ => concatFn w) ?_ ?_ (by simp [T]) (by simp)
      · intro a _
        simp only [T, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_filter, Finset.mem_image,
                   Finset.mem_univ, true_and]
        use (concatFn a).length
        refine ⟨⟨?_, ?_⟩, ⟨a, rfl⟩, rfl⟩
        · -- r ≤ (concatFn a).length
          -- Each selected codeword has positive length (since [] ∉ S).
          have h1le (i : Fin r) : (1 : ℕ) ≤ ((a i).val).length := by
            have hlen0 : ((a i).val).length ≠ 0 := by
              intro h0len
              have hnil : (a i).val = ([] : List α) := List.length_eq_zero_iff.mp h0len
              have : ([] : List α) ∈ (S : Set (List α)) := by
                simpa [hnil] using (a i).property
              exact h.epsilon_not_mem this
            have hpos : 0 < ((a i).val).length := Nat.pos_of_ne_zero hlen0
            exact Nat.succ_le_iff.mpr hpos
          -- Sum of r ones ≤ sum of the lengths.
          have hsum :
              (∑ _i : Fin r, (1 : ℕ)) ≤ ∑ i : Fin r, ((a i).val).length := by
            refine Finset.sum_le_sum ?_
            intro i hi
            simpa using h1le i
          -- Rewrite (∑ 1) as r, and RHS as concat length.
          simpa [concatFn.length] using hsum
        · -- Upper bound: |w| ≤ r * maxLen
          rw [concatFn.length]
          calc
            ∑ i : Fin r, (a i).val.length
              ≤ ∑ _i : Fin r, maxLen := by
                apply Finset.sum_le_sum
                intro i _
                -- Each codeword length is bounded by the sup of all lengths
                exact Finset.le_sup (a i).prop
            _ = r * maxLen := by simp
      · intro a₁ _ a₂ _ h_eq
        exact uniquely_decodable_concatFn_injective h r h_eq
    · intro _ _ _ _ hst
      exact disjoint_filter_eq_of_ne _ hst
  -- Since $\sum_{x \in \{0,1\}^s} 2^{-|x|} = 1$ for any $s$, we have
  -- $\sum_{s=r}^{r\ell} \sum_{x \in \{0,1\}^s} 2^{-|x|}
  --   = \sum_{s=r}^{r\ell} 1 = r\ell - r + 1 \le r\ell$.
  have h_sum_one :
      ∀ s ∈ Finset.Icc r (r * maxLen),
        ∑ x ∈ T.filter (fun x => x.length = s), (1 / D : ℝ) ^ x.length ≤ 1 := by
    intro s _
    simpa [sum_pow_len_filter_le_one_of_card_le] using
      (sum_pow_len_filter_le_one_of_card_le (by
        simpa using (card_filter_length_eq_le (T := T) (s := s))))
  refine le_trans kraft_sum_pow_eq_sum_concatFn.le
    <| h_injective.trans
    <| le_trans (Finset.sum_le_sum h_sum_one) ?_
  rcases r with (_ | _ | r) <;> rcases maxLen with (_ | _ | maxLen) <;> norm_num at *
  · positivity
  · rw [Nat.cast_sub] <;> push_cast <;> nlinarith only

open Filter

private lemma tendsto_nat_div_pow_atTop_nhds_0 {K : ℝ} (hK : 1 < K) :
    Tendsto (fun r : ℕ => (r : ℝ) / K ^ r) atTop (nhds 0) := by
  have hK0 : 0 < K := lt_trans (by norm_num) hK
  have hAbs : |1 / K| < 1 := by
    calc
      |1 / K| = 1 / K := abs_of_pos (by positivity)
      _ < 1 := (div_lt_one hK0).mpr hK
  simpa using (tendsto_self_mul_const_pow_of_abs_lt_one hAbs)

private lemma tendsto_mul_const_nat_div_pow_atTop_nhds_0 {K c : ℝ} (hK : 1 < K) :
    Filter.Tendsto (fun r : ℕ => (c * r) / K ^ r) Filter.atTop (nhds 0) := by
  simpa [mul_div_assoc] using
    (tendsto_nat_div_pow_atTop_nhds_0 hK).const_mul c

/-- **Kraft-McMillan Inequality**: If `S` is a finite uniquely decodable code,
then `Σ D^{-|w|} ≤ 1`. -/
public theorem kraft_mcmillan_inequality {S : Finset (List α)} [Fintype α] [Nonempty α]
    (h : UniquelyDecodable (S : Set (List α))) :
    ∑ w ∈ S, (1 / Fintype.card α : ℝ) ^ w.length ≤ 1 := by
  let D : ℝ := Fintype.card α
  have h_kraft := kraft_mcmillan_inequality_aux h
  contrapose! h_kraft
  let K := ∑ w ∈ S, (1 / D) ^ w.length
  have hK1 : 1 < K := by
    simpa [K] using h_kraft
  have hr_exists : Filter.Tendsto (fun r : ℕ =>
        (r * (Finset.sup S List.length) : ℝ) / K ^ r) Filter.atTop (nhds 0) := by
    let maxLen : ℕ := S.sup List.length
    have h0 :
        Tendsto (fun r : ℕ => (maxLen * (r : ℝ)) / K ^ r) atTop (nhds 0) := by
      exact tendsto_mul_const_nat_div_pow_atTop_nhds_0 hK1
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm] using h0
  obtain ⟨r, hr⟩ := Filter.eventually_atTop.mp (hr_exists.eventually (gt_mem_nhds zero_lt_one))
  refine ⟨r + 1, by linarith, ?_⟩
  have := hr (r + 1) (by linarith)
  rw [div_lt_iff₀ (by positivity)] at this
  linarith

end InformationTheory
