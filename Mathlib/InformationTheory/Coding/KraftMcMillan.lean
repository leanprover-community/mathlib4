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

private lemma concatFn_length {w : Fin r → S} :
    (concatFn w).length = ∑ i : Fin r, (w i).val.length := by
  simp [List.sum_ofFn, concatFn]

end concatFn

/-- For uniquely decodable codes, the concatenation map is injective.

This is the key property: distinct tuples of codewords produce distinct concatenations. -/
private lemma concatFn_injective_of_uniquelyDecodable {S : Finset (List α)}
    (h : UniquelyDecodable (S : Set (List α))) (r : ℕ) :
    Function.Injective (concatFn (S := S) (r := r)) := by
  intro w₁ w₂ hflat
  have : (fun i : Fin r => (w₁ i).val) = fun i => (w₂ i).val :=
    List.ofFn_injective (h _ _ (by simp) (by simp) (by simpa using hflat))
  funext i
  exact Subtype.ext (by simpa using congrArg (fun f => f i) this)

/-- The number of strings of length `s` in any set is at most `D^s`
(the total number of such strings). -/
private lemma card_filter_length_eq_le [Fintype α] {T : Finset (List α)} {s : ℕ} :
    (T.filter (fun x => x.length = s)).card ≤ (Fintype.card α) ^ s := by
  classical
  let all_words : Finset (List α) := (Finset.univ : Finset (Fin s → α)).image List.ofFn
  have hsub : T.filter (fun x => x.length = s) ⊆ all_words := by
    intro a ha
    have halen : a.length = s := (Finset.mem_filter.mp ha).right
    apply Finset.mem_image.mpr
    refine ⟨(fun j : Fin s => a.get ⟨j.val, by simp [halen]⟩), Finset.mem_univ _, ?_⟩
    exact List.ext_get (by simp [halen]) (by simp)
  have hcard_all : all_words.card = Fintype.card α ^ s := by
    -- `List.ofFn` is injective, so the image has the same cardinality as the domain.
    simpa using
      (Finset.card_image_of_injective
        (s := (Finset.univ : Finset (Fin s → α)))
        (f := List.ofFn)
        List.ofFn_injective)
  calc
    (T.filter (fun x => x.length = s)).card
        ≤ all_words.card := Finset.card_le_card hsub
    _ = Fintype.card α ^ s := hcard_all

private lemma sum_pow_len_filter_le_one_of_card_le [Fintype α] [Nonempty α]
    {T : Finset (List α)} {s : ℕ} :
    (∑ x ∈ T.filter (fun x => x.length = s),
    (1 / Fintype.card α : ℝ) ^ x.length) ≤ 1 := by
  let D : ℕ := Fintype.card α
  calc
    (∑ x ∈ T.filter (fun x => x.length = s), (1 / (D : ℝ)) ^ x.length)
        = (∑ x ∈ T.filter (fun x => x.length = s), (1 / (D : ℝ)) ^ s) :=
            Finset.sum_congr rfl (fun x hx => by
              simp [(Finset.mem_filter.mp hx).right])
    _   = (T.filter (fun x => x.length = s)).card * (1 / (D : ℝ)) ^ s := by
            simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (D ^ s) * (1 / D) ^ s := by
            gcongr
            exact_mod_cast card_filter_length_eq_le
    _ = 1 := by
            have : (D : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Fintype.card_pos : 0 < D)
            simp [this]

/-- The `r`-th power of the Kraft sum equals the sum over all `r`-tuples of codewords.

This expansion is the key algebraic identity in the Kraft-McMillan proof. -/
private lemma kraft_sum_pow_eq_sum_concatFn
    {S : Finset (List α)} {D : ℝ} {r : ℕ} :
    (∑ c ∈ S, (1 / D) ^ c.length) ^ r =
      ∑ w : Fin r → S, (1 / D) ^ (concatFn w).length := by
  calc
    (∑ c ∈ S, (1 / D) ^ c.length) ^ r
        = ∑ w : Fin r → S, ∏ i : Fin r, (1 / D) ^ (w i).val.length := by
            simpa [(Finset.sum_coe_sort S _).symm] using
              (Fintype.sum_pow (f := fun c : S => (1 / D) ^ c.val.length) r)
    _   = ∑ w : Fin r → S, (1 / D) ^ (concatFn w).length := by
            apply Fintype.sum_congr
            intro w
            simpa [concatFn_length] using (Finset.prod_pow_eq_pow_sum
                  (s := (Finset.univ : Finset (Fin r)))
                  (f := fun i => (w i).val.length)
                  (a := 1 / D))

/-- Auxiliary bound for Kraft–McMillan.

If `S` is uniquely decodable and `1 ≤ r`, then
`(∑ w ∈ S, (1 / D) ^ w.length) ^ r ≤ r * (S.sup List.length)`.

Expand the `r`-th power, use injectivity of concatenation to reindex by the image `T`,
then split by lengths `s ∈ Icc r (r * maxLen)`; each length class contributes at most `1`,
so the total is `≤ r * maxLen`. -/
private lemma kraft_mcmillan_inequality_aux {S : Finset (List α)} [Fintype α] [Nonempty α]
    (h : UniquelyDecodable (S : Set (List α))) (r : ℕ) (hr : r ≥ 1) :
    (∑ w ∈ S, (1 / (Fintype.card α) : ℝ) ^ w.length) ^ r ≤ r * (Finset.sup S List.length) := by
  classical
  -- Let $maxLen = \max_{w \in S} |w|$.
  set maxLen := (S.sup List.length) with hmaxLen_def
  let D := (Fintype.card α : ℝ)
  -- Since `concatFn : (Fin r → S) → List α` is injective, we can sum over its image `T`.
  -- The words in `T` have lengths in `Icc r (r * maxLen)`, so we split the sum by length:
  -- `∑_{w} (1/D)^{|concatFn w|} = ∑_{s=r}^{r*maxLen} ∑_{x ∈ T, |x| = s} (1/D)^{|x|}`.
  -- Each inner sum is ≤ 1 since there are at most `D^s` words of length `s`.
  let T : Finset (List α) := Finset.image concatFn (Finset.univ : Finset (Fin r → S))
  have hsum_image :
      ∑ x ∈ T, (1 / D) ^ x.length =
      ∑ w : Fin r → S, (1 / D) ^ (concatFn w).length := by
    simpa [T] using Finset.sum_image
        (f := fun x => (1 / D) ^ x.length)
        (fun _ _ _ _ hEq => concatFn_injective_of_uniquelyDecodable h r hEq)
  have hlen_maps :
      ∀ x ∈ T, x.length ∈ Finset.Icc r (r * maxLen) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨w, _hw, rfl⟩
    rw [Finset.mem_Icc]
    constructor
    · -- lower bound: r ≤ (concatFn w).length
      have hpos (i) : 1 ≤ (w i).val.length := by
        have hne : (w i).val ≠ [] := by
          intro hnil
          apply h.epsilon_not_mem
          simpa [hnil] using (w i).prop
        have : 0 < (w i).val.length :=
          Nat.pos_of_ne_zero (fun hz => hne (List.length_eq_zero_iff.mp hz))
        simpa using (Nat.succ_le_iff.mpr this)
      have : (∑ _ : Fin r, (1 : ℕ)) ≤ ∑ i, (w i).val.length :=
        Finset.sum_le_sum (fun i _ => hpos i)
      -- `∑ _ : Fin r, 1 = r` and RHS is `concatFn_length`
      simpa [concatFn_length] using this
    · -- upper bound: (concatFn w).length ≤ r * maxLen
      have : (∑ i, (w i).val.length) ≤ ∑ _ : Fin r, maxLen :=
        Finset.sum_le_sum (fun i _ => Finset.le_sup (w i).prop)
      -- `∑ _ : Fin r, maxLen = r * maxLen`
      simpa [concatFn_length] using (this.trans_eq (by simp))
  have hsplit :
    ∑ s ∈ Finset.Icc r (r * maxLen),
        ∑ x ∈ T with x.length = s, (1 / D) ^ x.length
      = ∑ x ∈ T, (1 / D) ^ x.length := by
    simpa using
      (Finset.sum_fiberwise_of_maps_to
        (f := fun x => (1 / D) ^ x.length)
        hlen_maps)
  -- Summing the bound `≤ 1` over all admissible lengths gives
  -- `∑_{s=r}^{r*maxLen} (∑_{x ∈ T, x.length = s} (1/D)^{x.length}) ≤ ∑_{s=r}^{r*maxLen} 1`.
  -- The right-hand side is the number of integers `s` with `r ≤ s ≤ r*maxLen`,
  -- i.e. `r*maxLen - r + 1`, and this is `≤ r*maxLen` since `1 ≤ r`.
  rw [kraft_sum_pow_eq_sum_concatFn, <-hsum_image, <-hsplit]
  apply le_trans (Finset.sum_le_sum
      (fun s _ => sum_pow_len_filter_le_one_of_card_le))
  rcases r with (_ | _ | r) <;> rcases maxLen with (_ | _ | maxLen) <;> norm_num at *
  · positivity
  · rw [Nat.cast_sub] <;> push_cast <;> nlinarith only

open Filter

/-- **Kraft-McMillan Inequality**: If `S` is a finite uniquely decodable code,
then `Σ D^{-|w|} ≤ 1`. -/
public theorem kraft_mcmillan_inequality {S : Finset (List α)} [Fintype α] [Nonempty α]
    (h : UniquelyDecodable (S : Set (List α))) :
    ∑ w ∈ S, (1 / Fintype.card α : ℝ) ^ w.length ≤ 1 := by
  have h_kraft := kraft_mcmillan_inequality_aux h
  contrapose! h_kraft
  let K := ∑ w ∈ S, (1 / (Fintype.card α : ℝ)) ^ w.length
  let maxLen : ℕ := S.sup List.length
  have hAbs : |1 / K| < 1 := by
    grw [abs_of_pos (by positivity), div_lt_one] <;> grind
  have : Tendsto (fun r : ℕ => r * maxLen / K ^ r) atTop (nhds 0) := by
    simpa [mul_comm, mul_left_comm, mul_assoc, mul_div_assoc] using
      ((tendsto_self_mul_const_pow_of_abs_lt_one hAbs).const_mul (maxLen : ℝ))
  obtain ⟨r, hr⟩ := eventually_atTop.mp <| this.eventually <| gt_mem_nhds zero_lt_one
  refine ⟨r + 1, by linarith, ?_⟩
  have := hr (r + 1) (by linarith)
  rw [div_lt_iff₀ (by positivity)] at this
  linarith

end InformationTheory
