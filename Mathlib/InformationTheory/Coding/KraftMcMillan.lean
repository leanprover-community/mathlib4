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
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.InformationTheory.Coding.UniquelyDecodable
import Mathlib.Analysis.SpecificLimits.Normed

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
  funext i
  have := List.ofFn_injective (h _ _ (by simp) (by simp) hflat)
  exact Subtype.ext (congrArg (fun f => f i) this)

private lemma sum_pow_length_filter_eq_le_card_mul [Fintype α] [Nonempty α]
    {T : Finset (List α)} {s : ℕ} :
    (∑ x ∈ T.filter (fun x => x.length = s), (1 / (Fintype.card α : ℝ)) ^ x.length)
      ≤ ((Fintype.card α) ^ s) * (1 / Fintype.card α) ^ s := by
  calc
    _  = ∑ x ∈ T.filter (fun x => x.length = s), (1 / (Fintype.card α : ℝ)) ^ s :=
      Finset.sum_congr rfl fun x hx ↦ by simp [Finset.mem_filter.mp hx]
    _ = (T.filter fun x => x.length = s).card * (1 / Fintype.card α) ^ s := by
      simp only [Finset.sum_const, nsmul_eq_mul]
  gcongr
  exact_mod_cast Finset.card_filter_length_eq_le

/-- Length of a concatenation of `r` codewords lies in `[r, r*sup length]`
assuming `[] ∉ S`. -/
private lemma concatFn_length_mem_Icc {S : Finset (List α)}
    {r : ℕ} {w : Fin r → S} (h0 : ∀ c : S, c.val ≠ []) :
    (concatFn w).length ∈ Finset.Icc r (r * S.sup List.length) := by
  rw [concatFn_length, Finset.mem_Icc]
  constructor
  · -- lower bound
    have : ∑ _, 1 ≤ ∑ i, (w i).val.length :=
      Finset.sum_le_sum (fun i _ => by grind)
    simpa using this
  · -- upper bound
    exact (Finset.sum_le_sum (fun i _ => Finset.le_sup (w i).prop)).trans_eq (by simp)

/-- Auxiliary bound for Kraft–McMillan.

If `S` is a finite uniquely decodable code and `1 ≤ r`, then the `r`-th power of its Kraft sum
is bounded by `r * sup length`:

`(∑ w ∈ S, (1 / D) ^ w.length) ^ r ≤ r * (S.sup List.length)`. -/
private lemma kraft_mcmillan_inequality_aux {S : Finset (List α)} [Fintype α] [Nonempty α]
    (h : UniquelyDecodable (S : Set (List α))) (r : ℕ) (hr : r ≥ 1) :
    (∑ w ∈ S, (1 / (Fintype.card α) : ℝ) ^ w.length) ^ r ≤ r * (Finset.sup S List.length) := by
  classical
  -- We use maxLen to bound lengths of `r`-fold concatenations.
  set maxLen := S.sup List.length
  -- Let `T` be the set of all concatenations of `r` codewords from `S`.
  let T : Finset (List α) := Finset.image concatFn (Finset.univ : Finset (Fin r → S))
  -- Any `x ∈ T` is a concatenation of `r` nonempty codewords, hence `r ≤ |x| ≤ r*maxLen`.
  have hlen_maps (x : List α) (hx : x ∈ T) : x.length ∈ Finset.Icc r (r * maxLen) := by
    rcases Finset.mem_image.mp hx with ⟨_, _, rfl⟩
    exact concatFn_length_mem_Icc
      (fun c hnil => h.epsilon_not_mem (by simpa [hnil] using c.prop))
  let D := (Fintype.card α : ℝ)
  -- Expand the `r`-th power as a sum over `r`-tuples of codewords;
  -- each tuple contributes the weight `(1/D)^{|concatFn w|}`.
  calc (∑ w ∈ S, (1 / (Fintype.card α) : ℝ) ^ w.length) ^ r
    _ = ∑ w : Fin r → S, ∏ i : Fin r, (1 / D) ^ (w i).val.length := by
      simpa [(Finset.sum_coe_sort S _).symm] using
        Fintype.sum_pow (f := fun c : S => (1 / D) ^ c.val.length) r
    -- Each tuple contributes the weight `(1/D)^{|concatFn w|}`.
    _ = ∑ w, (1 / D) ^ (concatFn w).length := by
      apply Fintype.sum_congr
      intro w
      simpa [concatFn_length] using Finset.prod_pow_eq_pow_sum Finset.univ _ _
    -- Unique decodability makes `concatFn` injective, so these concatenations are distinct;
    -- we can reindex the sum by the set `T` of words.
    _ = ∑ x ∈ T, (1 / D) ^ x.length :=
      (Finset.sum_image (f := fun x => (1 / D) ^ x.length)
        (fun _ _ _ _ hEq => concatFn_injective_of_uniquelyDecodable h r hEq)).symm
    -- Group the sum over `T` by the length `s`.
    -- The admissible lengths lie in `[r, r*maxLen]` by `hlen_maps`.
    _ = ∑ s ∈ Finset.Icc r (r * maxLen), ∑ x ∈ T with x.length = s, (1 / D) ^ x.length :=
      (Finset.sum_fiberwise_of_maps_to hlen_maps _).symm
  -- For each length `s`, the `s`-fiber contributes at most `D^s * (1/D)^s`:
  -- there are ≤ `D^s` words of length `s`, and each has weight `(1/D)^s`.
  apply le_trans (Finset.sum_le_sum (fun _ _ => sum_pow_length_filter_eq_le_card_mul))
  -- Summing these bounds over the interval s ∈ [r, r * maxLen] multiplies the term
  -- by the number of lengths. Since r ≥ 1, this count is at most r * maxLen.
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
    simpa [mul_left_comm, mul_div_assoc] using
      (tendsto_self_mul_const_pow_of_abs_lt_one hAbs).const_mul (maxLen : ℝ)
  obtain ⟨r, hr⟩ := eventually_atTop.mp <| this.eventually <| gt_mem_nhds zero_lt_one
  refine ⟨r + 1, by linarith, ?_⟩
  have := hr (r + 1) (by linarith)
  rw [div_lt_iff₀ (by positivity)] at this
  linarith

end InformationTheory
