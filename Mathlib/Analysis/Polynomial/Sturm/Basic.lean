/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.Polynomial.Sturm.Defs
public import Mathlib.Analysis.Polynomial.Order
public import Mathlib.FieldTheory.Perfect

/-!
Sturm's theorem over `Polynomial ℝ`, proved as a five-step chain. Everything
here is a slice over `Polynomial ℝ` with no `HexRealRoots`
dependence.

The three local lemmas (`sturmVar_const_of_no_zero`, `sturmVar_interior_cross`,
`sturmVar_root_cross`) describe the behaviour of `Sturm.sturmVar` across the
finitely many zeros of the chain elements. The two global results
(`sturm_half_open`, `sturm_line`) are the telescoping consequences: the number
of real roots of `p` in a half-open interval `(a, b]` is the drop in
`sturmVar` from `a` to `b`, and the total number of real roots is the drop
from `−∞` to `+∞`.

The half-open form telescopes the three local lemmas over the finitely many
chain zeros in `(a, b]` (helpers `chainZeros`, `exists_left_gap`/`exists_right_gap`,
`sturmVar_eq_right`, `card_filter_Ioc_split`). The line form evaluates the chain
just beyond every root at `±M` and reads the `±∞` variation counts
`Sturm.sturmVarNegInf` / `Sturm.sturmVarPosInf` off the leading coefficients and
degree parities (helpers `eval_sign_pos_inf` / `eval_sign_neg_inf`).
-/

public section

open Filter Topology

namespace Sturm

/-- Sign variations of the chain at `+∞`: the sign of each element there is the
sign of its leading coefficient, so this is the zero-skipping variation count
of the leading coefficients. The zero polynomial contributes leading
coefficient `0`, which the zero-skipping convention drops. -/
@[expose]
noncomputable def sturmVarPosInf (chain : List (Polynomial ℝ)) : ℕ :=
  signVariations (chain.map Polynomial.leadingCoeff)

/-- Sign variations of the chain at `−∞`: the sign of an element there is the
sign of its leading coefficient times `(-1) ^ degree`, so this is the
zero-skipping variation count of `leadingCoeff · (-1) ^ natDegree`. -/
@[expose]
noncomputable def sturmVarNegInf (chain : List (Polynomial ℝ)) : ℕ :=
  signVariations (chain.map (fun q => q.leadingCoeff * (-1) ^ q.natDegree))

/-- **Sign persistence.** A polynomial with no zero on `[a, b]` keeps a constant
sign there: its evaluation signs at the two endpoints agree. If they differed,
the two endpoint values would straddle `0` and the intermediate value theorem
would supply an interior zero. -/
theorem eval_sign_eq_of_no_zero {q : Polynomial ℝ} {a b : ℝ} (hab : a ≤ b)
    (hz : ∀ x ∈ Set.Icc a b, q.eval x ≠ 0) :
    SignType.sign (q.eval a) = SignType.sign (q.eval b) := by
  have hna : q.eval a ≠ 0 := hz a ⟨le_refl a, hab⟩
  have hnb : q.eval b ≠ 0 := hz b ⟨hab, le_refl b⟩
  have hpos : 0 < q.eval a * q.eval b := by
    rcases lt_or_gt_of_ne (mul_ne_zero hna hnb) with hlt | hgt
    · exfalso
      have hmem : (0 : ℝ) ∈ Set.uIcc (q.eval a) (q.eval b) := by
        rcases mul_neg_iff.mp hlt with ⟨hx, hy⟩ | ⟨hx, hy⟩
        · exact Set.mem_uIcc.mpr (Or.inr ⟨hy.le, hx.le⟩)
        · exact Set.mem_uIcc.mpr (Or.inl ⟨hx.le, hy.le⟩)
      have hsub := intermediate_value_uIcc (a := a) (b := b)
        (f := fun x => q.eval x) q.continuousOn
      obtain ⟨c, hc, hc0⟩ := hsub hmem
      rw [Set.uIcc_of_le hab] at hc
      exact hz c hc hc0
    · exact hgt
  rcases mul_pos_iff.mp hpos with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [sign_pos h1, sign_pos h2]
  · rw [sign_neg h1, sign_neg h2]

/-- Build the sign-pattern relation `SVRel` between the evaluations of a
polynomial list at a "generic" point `a` (where every element is nonzero) and a
"special" point `r` (where some interior elements may vanish). The hypotheses
are exactly what an `IsSturmChain` supplies restricted to the relevant interval:
every element is nonzero at `a`; the head and last elements are nonzero at `r`;
whenever an interior element vanishes at `r` its neighbours are nonzero there
with opposite signs; and every element nonzero at `r` has the same sign at `a`
and `r`. -/
private theorem buildSVRel (a r : ℝ) :
    ∀ (cs : List (Polynomial ℝ)),
      (∀ q ∈ cs, q.eval a ≠ 0) →
      (∀ q, cs.head? = some q → q.eval r ≠ 0) →
      (∀ q, cs.getLast? = some q → q.eval r ≠ 0) →
      (∀ (i : ℕ) (q0 q1 q2 : Polynomial ℝ), cs[i]? = some q0 → cs[i + 1]? = some q1 →
        cs[i + 2]? = some q2 → q1.eval r = 0 →
        q0.eval r ≠ 0 ∧ q2.eval r ≠ 0 ∧ q0.eval r * q2.eval r < 0) →
      (∀ q ∈ cs, q.eval r ≠ 0 → SignType.sign (q.eval a) = SignType.sign (q.eval r)) →
      SVRel (cs.map (Polynomial.eval a)) (cs.map (Polynomial.eval r))
  | [], _, _, _, _, _ => SVRel.nil
  | [q0], hne0, hfront, _, _, hsame => by
      have hr : q0.eval r ≠ 0 := hfront q0 rfl
      exact SVRel.same (hne0 q0 (by simp)) hr (hsame q0 (by simp) hr) SVRel.nil
  | q0 :: q1 :: rest, hne0, hfront, hlast, halt, hsame => by
      have hr0 : q0.eval r ≠ 0 := hfront q0 rfl
      have ha0 : q0.eval a ≠ 0 := hne0 q0 (by simp)
      by_cases hq1 : q1.eval r = 0
      · cases rest with
        | nil => exact absurd hq1 (hlast q1 (by simp))
        | cons q2 rest' =>
            obtain ⟨hn0, hn2, hoppR⟩ := halt 0 q0 q1 q2 rfl rfl rfl hq1
            have hsx : SignType.sign (q0.eval a) = SignType.sign (q0.eval r) :=
              hsame q0 (by simp) hn0
            have hsy : SignType.sign (q2.eval a) = SignType.sign (q2.eval r) :=
              hsame q2 (by simp) hn2
            have hoppA : SignType.sign (q0.eval a) * SignType.sign (q2.eval a) = -1 := by
              rw [hsx, hsy, ← sign_mul, sign_eq_neg_one_iff]; exact hoppR
            have hne0' : ∀ q ∈ q2 :: rest', q.eval a ≠ 0 := fun q hq =>
              hne0 q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))
            have hfront' : ∀ q, (q2 :: rest').head? = some q → q.eval r ≠ 0 := by
              intro q hq; rw [List.head?_cons] at hq; cases hq; exact hn2
            have hlast' : ∀ q, (q2 :: rest').getLast? = some q → q.eval r ≠ 0 := by
              intro q hq
              exact hlast q (by rw [List.getLast?_cons_cons, List.getLast?_cons_cons]; exact hq)
            have halt' : ∀ (i : ℕ) (p0 p1 p2 : Polynomial ℝ), (q2 :: rest')[i]? = some p0 →
                (q2 :: rest')[i + 1]? = some p1 → (q2 :: rest')[i + 2]? = some p2 →
                p1.eval r = 0 → p0.eval r ≠ 0 ∧ p2.eval r ≠ 0 ∧ p0.eval r * p2.eval r < 0 := by
              intro i p0 p1 p2 h0 h1 h2 hz
              exact halt (i + 2) p0 p1 p2
                (by rw [List.getElem?_cons_succ, List.getElem?_cons_succ]; exact h0)
                (by rw [List.getElem?_cons_succ, List.getElem?_cons_succ]; exact h1)
                (by rw [List.getElem?_cons_succ, List.getElem?_cons_succ]; exact h2) hz
            have hsame' : ∀ q ∈ q2 :: rest', q.eval r ≠ 0 →
                SignType.sign (q.eval a) = SignType.sign (q.eval r) := fun q hq =>
              hsame q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))
            have IH := buildSVRel a r (q2 :: rest') hne0' hfront' hlast' halt' hsame'
            simp only [List.map_cons] at IH ⊢
            rw [hq1]
            exact SVRel.collapse ha0 (hne0 q1 (by simp)) hn2 hsx hsy hoppA IH
      · have hne0' : ∀ q ∈ q1 :: rest, q.eval a ≠ 0 := fun q hq =>
          hne0 q (List.mem_cons_of_mem _ hq)
        have hfront' : ∀ q, (q1 :: rest).head? = some q → q.eval r ≠ 0 := by
          intro q hq; rw [List.head?_cons] at hq; cases hq; exact hq1
        have hlast' : ∀ q, (q1 :: rest).getLast? = some q → q.eval r ≠ 0 := by
          intro q hq
          exact hlast q (by rw [List.getLast?_cons_cons]; exact hq)
        have halt' : ∀ (i : ℕ) (p0 p1 p2 : Polynomial ℝ), (q1 :: rest)[i]? = some p0 →
            (q1 :: rest)[i + 1]? = some p1 → (q1 :: rest)[i + 2]? = some p2 →
            p1.eval r = 0 → p0.eval r ≠ 0 ∧ p2.eval r ≠ 0 ∧ p0.eval r * p2.eval r < 0 := by
          intro i p0 p1 p2 h0 h1 h2 hz
          exact halt (i + 1) p0 p1 p2
            (by rw [List.getElem?_cons_succ]; exact h0)
            (by rw [List.getElem?_cons_succ]; exact h1)
            (by rw [List.getElem?_cons_succ]; exact h2) hz
        have hsame' : ∀ q ∈ q1 :: rest, q.eval r ≠ 0 →
            SignType.sign (q.eval a) = SignType.sign (q.eval r) := fun q hq =>
          hsame q (List.mem_cons_of_mem _ hq)
        have IH := buildSVRel a r (q1 :: rest) hne0' hfront' hlast' halt' hsame'
        simp only [List.map_cons] at IH ⊢
        exact SVRel.same ha0 hr0 (hsame q0 (by simp) hr0) IH

variable {p : Polynomial ℝ} {chain : List (Polynomial ℝ)}

/-- **Local constancy.** On a closed interval `[a, b]` containing no zero of
any chain element, `sturmVar` takes the same value at the two endpoints.

Proof sketch: each element keeps a constant nonzero sign across
`[a, b]` by continuity of polynomial evaluation (`Polynomial.continuous_aeval`)
and the intermediate value theorem (`intermediate_value_Icc`): a sign change
would force a zero. The list of evaluation signs is therefore the same at `a`
and `b`, so `signVariations` — which depends only on those signs — agrees. -/
theorem sturmVar_const_of_no_zero (_hchain : IsSturmChain p chain)
    (a b : ℝ) (hab : a ≤ b)
    (hz : ∀ q ∈ chain, ∀ x ∈ Set.Icc a b, q.eval x ≠ 0) :
    sturmVar chain a = sturmVar chain b := by
  change signVariations (chain.map (Polynomial.eval a))
    = signVariations (chain.map (Polynomial.eval b))
  apply signVariations_congr
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  intro q hq
  exact eval_sign_eq_of_no_zero hab (fun x hx => hz q hq x hx)

/-- **Interior-element crossing preserves `sturmVar`.** If `r` is not a root of
`p` and the only chain zeros in `[a, b]` occur at `r` (necessarily zeros of
interior elements), then `sturmVar` is unchanged from `a` to `b`.

Proof sketch: away from `r` local constancy applies on `[a, r]`
and `[r, b]`. At `r` the vanishing interior elements sit between neighbours of
opposite sign (`IsSturmChain.interior_alternates`), so each contributes exactly
one variation both immediately before and immediately after `r` regardless of
the sign it passes through, and the head pair (involving `p`, nonzero near `r`)
is unaffected. Hence the count at `a`, at `r`, and at `b` coincide. The value
at `r` itself is part of the statement because the global theorem places no
restriction on its endpoints, so a telescoping step may need the count exactly
at an interior-element zero. -/
theorem sturmVar_interior_cross (hchain : IsSturmChain p chain) (r : ℝ)
    (hpr : ¬ p.IsRoot r) (a b : ℝ) (har : a < r) (hrb : r < b)
    (hz : ∀ q ∈ chain, ∀ x ∈ Set.Icc a b, x ≠ r → q.eval x ≠ 0) :
    sturmVar chain a = sturmVar chain r ∧ sturmVar chain r = sturmVar chain b := by
  have hab : a ≤ b := (har.trans hrb).le
  have hpr' : p.eval r ≠ 0 := hpr
  -- Chain-structure hypotheses at the special point `r`, shared by both calls.
  have hfront : ∀ q, chain.head? = some q → q.eval r ≠ 0 := by
    intro q hq; rw [hchain.head] at hq; cases hq; exact hpr'
  have hlast : ∀ q, chain.getLast? = some q → q.eval r ≠ 0 :=
    fun q hq => hchain.last_no_root q hq r
  have halt : ∀ (i : ℕ) (q0 q1 q2 : Polynomial ℝ), chain[i]? = some q0 →
      chain[i + 1]? = some q1 → chain[i + 2]? = some q2 → q1.eval r = 0 →
      q0.eval r ≠ 0 ∧ q2.eval r ≠ 0 ∧ q0.eval r * q2.eval r < 0 :=
    fun i q0 q1 q2 h0 h1 h2 hz => hchain.interior_alternates i r q0 q1 q2 h0 h1 h2 hz
  constructor
  · change signVariations (chain.map (Polynomial.eval a))
      = signVariations (chain.map (Polynomial.eval r))
    refine (buildSVRel a r chain (fun q hq => hz q hq a ⟨le_refl a, hab⟩ (ne_of_lt har))
      hfront hlast halt (fun q hq hqr => ?_)).signVariations_eq.1
    exact eval_sign_eq_of_no_zero har.le (fun x hx => by
      by_cases hxr : x = r
      · rw [hxr]; exact hqr
      · exact hz q hq x ⟨hx.1, hx.2.trans hrb.le⟩ hxr)
  · change signVariations (chain.map (Polynomial.eval r))
      = signVariations (chain.map (Polynomial.eval b))
    refine ((buildSVRel b r chain
      (fun q hq => hz q hq b ⟨hab, le_refl b⟩ (ne_of_lt hrb).symm)
      hfront hlast halt (fun q hq hqr => ?_)).signVariations_eq.1).symm
    exact (eval_sign_eq_of_no_zero hrb.le (fun x hx => by
      by_cases hxr : x = r
      · rw [hxr]; exact hqr
      · exact hz q hq x ⟨har.le.trans hx.1, hx.2⟩ hxr)).symm

/-- **Simple-zero crossing of `p` drops `sturmVar` by one, registering at `r`.**
If `r` is a (simple, by squarefreeness) root of `p` and the only chain zeros in
`[a, b]` occur at `r`, then `sturmVar` at `a` exceeds the value at `b` by
exactly one, and the drop has already registered at `r`: the value at `r`
equals the value at `b`.

Proof sketch: the head pair `(p, q)` with `q = chain[1]` has
`p * q < 0` just left of `r` and `p * q > 0` just right (`root_flank`), so this
pair contributes one variation for `x < r` and none for `x ≥ r`; with the
zero-skipping convention the zero of `p` at `r` is dropped, so the change
registers at `r` itself. All interior crossings at `r` are variation-neutral by
step 2, and away from `r` `sturmVar` is locally constant by step 1. The
half-open registration is the one design-sensitive point: it is what makes the
executable half-open counts match with no endpoint hypotheses. -/
theorem sturmVar_root_cross (_hp : p ≠ 0) (_hsf : Squarefree p)
    (hchain : IsSturmChain p chain) (r : ℝ) (hr : p.IsRoot r)
    (a b : ℝ) (har : a < r) (hrb : r < b)
    (hz : ∀ q ∈ chain, ∀ x ∈ Set.Icc a b, x ≠ r → q.eval x ≠ 0)
    (hpz : ∀ x ∈ Set.Icc a b, x ≠ r → ¬ p.IsRoot x) :
    sturmVar chain a = sturmVar chain b + 1 ∧ sturmVar chain r = sturmVar chain b := by
  have hab : a ≤ b := (har.trans hrb).le
  obtain ⟨q, hq1, hqr, hflL, hflR⟩ := hchain.root_flank r hr
  -- Split the chain into its head `p` and second element `q`.
  rcases chain with _ | ⟨p0, _ | ⟨q0, tail⟩⟩
  · exact absurd hchain.head (by simp)
  · exact absurd hq1 (by simp)
  have hp0 : p0 = p := by simpa using hchain.head
  subst p0
  have hq0 : q0 = q := by simpa using hq1
  subst q0
  -- Basic nonvanishing facts.
  have hpr0 : p.eval r = 0 := hr
  have hpa : p.eval a ≠ 0 := fun h => hpz a ⟨le_refl a, hab⟩ (ne_of_lt har) h
  have hpb : p.eval b ≠ 0 := fun h => hpz b ⟨hab, le_refl b⟩ (ne_of_lt hrb).symm h
  have hqa : q.eval a ≠ 0 := hz q (by simp) a ⟨le_refl a, hab⟩ (ne_of_lt har)
  have hqb : q.eval b ≠ 0 := hz q (by simp) b ⟨hab, le_refl b⟩ (ne_of_lt hrb).symm
  -- The head pair `p * q` is negative just left of `r` and positive just right,
  -- and (only zero at `r`) this persists to the endpoints.
  have hpqa : (p * q).eval a < 0 := by
    obtain ⟨c, hclt, hcmem⟩ := (hflL.and (Ioo_mem_nhdsLT har)).exists
    have hsg : SignType.sign ((p * q).eval a) = SignType.sign ((p * q).eval c) :=
      eval_sign_eq_of_no_zero hcmem.1.le (fun x hx => by
        have hxr : x ≠ r := ne_of_lt (lt_of_le_of_lt hx.2 hcmem.2)
        have hxab : x ∈ Set.Icc a b := ⟨hx.1, hx.2.trans (hcmem.2.le.trans hrb.le)⟩
        rw [Polynomial.eval_mul]
        exact mul_ne_zero (fun h => hpz x hxab hxr h) (hz q (by simp) x hxab hxr))
    rw [sign_neg hclt] at hsg
    exact sign_eq_neg_one_iff.mp hsg
  have hpqb : 0 < (p * q).eval b := by
    obtain ⟨c, hcgt, hcmem⟩ := (hflR.and (Ioo_mem_nhdsGT hrb)).exists
    have hsg : SignType.sign ((p * q).eval c) = SignType.sign ((p * q).eval b) :=
      eval_sign_eq_of_no_zero hcmem.2.le (fun x hx => by
        have hxr : x ≠ r := (ne_of_lt (lt_of_lt_of_le hcmem.1 hx.1)).symm
        have hxab : x ∈ Set.Icc a b :=
          ⟨har.le.trans (hcmem.1.le.trans hx.1), hx.2⟩
        rw [Polynomial.eval_mul]
        exact mul_ne_zero (fun h => hpz x hxab hxr h) (hz q (by simp) x hxab hxr))
    rw [sign_pos hcgt] at hsg
    exact sign_eq_one_iff.mp hsg.symm
  have hsignA : SignType.sign (p.eval a) * SignType.sign (q.eval a) = -1 := by
    rw [← sign_mul, sign_eq_neg_one_iff, ← Polynomial.eval_mul]; exact hpqa
  have hsignB : ¬ (SignType.sign (p.eval b) * SignType.sign (q.eval b) = -1) := by
    rw [← sign_mul, sign_eq_neg_one_iff, ← Polynomial.eval_mul]
    exact not_lt.mpr hpqb.le
  -- Point-`r` chain hypotheses for the tail `q :: tail`, shared by both calls.
  have hfront_rest : ∀ s, (q :: tail).head? = some s → s.eval r ≠ 0 := by
    intro s hs; rw [List.head?_cons] at hs; cases hs; exact hqr
  have hlast_rest : ∀ s, (q :: tail).getLast? = some s → s.eval r ≠ 0 := by
    intro s hs
    exact hchain.last_no_root s (by rw [List.getLast?_cons_cons]; exact hs) r
  have halt_rest : ∀ (i : ℕ) (s0 s1 s2 : Polynomial ℝ), (q :: tail)[i]? = some s0 →
      (q :: tail)[i + 1]? = some s1 → (q :: tail)[i + 2]? = some s2 → s1.eval r = 0 →
      s0.eval r ≠ 0 ∧ s2.eval r ≠ 0 ∧ s0.eval r * s2.eval r < 0 := by
    intro i s0 s1 s2 h0 h1 h2 hz0
    exact hchain.interior_alternates (i + 1) r s0 s1 s2
      (by rw [List.getElem?_cons_succ]; exact h0)
      (by rw [List.getElem?_cons_succ]; exact h1)
      (by rw [List.getElem?_cons_succ]; exact h2) hz0
  -- Sign persistence for the tail elements, at `a` and at `b`.
  have hsame_a : ∀ s ∈ q :: tail, s.eval r ≠ 0 →
      SignType.sign (s.eval a) = SignType.sign (s.eval r) := fun s hs hsr =>
    eval_sign_eq_of_no_zero har.le (fun x hx => by
      by_cases hxr : x = r
      · rw [hxr]; exact hsr
      · exact hz s (List.mem_cons_of_mem _ hs) x ⟨hx.1, hx.2.trans hrb.le⟩ hxr)
  have hsame_b : ∀ s ∈ q :: tail, s.eval r ≠ 0 →
      SignType.sign (s.eval b) = SignType.sign (s.eval r) := fun s hs hsr =>
    (eval_sign_eq_of_no_zero hrb.le (fun x hx => by
      by_cases hxr : x = r
      · rw [hxr]; exact hsr
      · exact hz s (List.mem_cons_of_mem _ hs) x ⟨har.le.trans hx.1, hx.2⟩ hxr)).symm
  -- The tail's `sturmVar` is the same at `a`, `r`, `b` (interior-crossing).
  have hEqA : sturmVar (q :: tail) a = sturmVar (q :: tail) r :=
    (buildSVRel a r (q :: tail)
      (fun s hs => hz s (List.mem_cons_of_mem _ hs) a ⟨le_refl a, hab⟩ (ne_of_lt har))
      hfront_rest hlast_rest halt_rest hsame_a).signVariations_eq.1
  have hEqB : sturmVar (q :: tail) b = sturmVar (q :: tail) r :=
    (buildSVRel b r (q :: tail)
      (fun s hs => hz s (List.mem_cons_of_mem _ hs) b ⟨hab, le_refl b⟩ (ne_of_lt hrb).symm)
      hfront_rest hlast_rest halt_rest hsame_b).signVariations_eq.1
  -- Head-pair bookkeeping at each point.
  have hSVa : sturmVar (p :: q :: tail) a = 1 + sturmVar (q :: tail) a := by
    change signVariations (p.eval a :: (q :: tail).map (Polynomial.eval a))
      = 1 + signVariations ((q :: tail).map (Polynomial.eval a))
    rw [signVariations_cons_pos _ hpa]
    simp only [List.map_cons]
    rw [firstSign_cons_ne _ hqa, Option.elim_some, ite_eq_left hsignA]
  have hSVb : sturmVar (p :: q :: tail) b = sturmVar (q :: tail) b := by
    change signVariations (p.eval b :: (q :: tail).map (Polynomial.eval b))
      = signVariations ((q :: tail).map (Polynomial.eval b))
    rw [signVariations_cons_pos _ hpb]
    simp only [List.map_cons]
    rw [firstSign_cons_ne _ hqb, Option.elim_some, ite_eq_right hsignB, zero_add]
  have hSVr : sturmVar (p :: q :: tail) r = sturmVar (q :: tail) r := by
    change signVariations (p.eval r :: (q :: tail).map (Polynomial.eval r))
      = signVariations ((q :: tail).map (Polynomial.eval r))
    rw [hpr0]; exact signVariations_cons_zero _
  refine ⟨?_, ?_⟩
  · rw [hSVa, hSVb, hEqA, hEqB]; omega
  · rw [hSVr, hSVb]; exact hEqB.symm

/-- The finite set of real points at which some element of `chain` vanishes.
Every chain element is nonzero (`IsSturmChain.nonzero_mem`), so each contributes
finitely many zeros; their union is the telescope's set of break points. -/
noncomputable def chainZeros (cs : List (Polynomial ℝ)) : Finset ℝ :=
  cs.toFinset.biUnion (fun q => q.roots.toFinset)

/-- Membership in `chainZeros`: a point lies in it exactly when some chain
element vanishes there (using that every chain element is nonzero). -/
theorem mem_chainZeros {cs : List (Polynomial ℝ)} (hne : ∀ q ∈ cs, q ≠ 0) {x : ℝ} :
    x ∈ chainZeros cs ↔ ∃ q ∈ cs, q.eval x = 0 := by
  unfold chainZeros
  simp only [Finset.mem_biUnion, List.mem_toFinset, Multiset.mem_toFinset]
  constructor
  · rintro ⟨q, hq, hx⟩
    exact ⟨q, hq, (Polynomial.mem_roots (hne q hq)).mp hx⟩
  · rintro ⟨q, hq, hx⟩
    exact ⟨q, hq, (Polynomial.mem_roots (hne q hq)).mpr hx⟩

/-- A gap point just below `z` and above `lo`, lying above every element of the
finite set `S` that is below `z`. Used to manufacture the artificial left
neighbour a crossing lemma needs at a break point. -/
theorem exists_left_gap (S : Finset ℝ) (z lo : ℝ) (hlo : lo < z) :
    ∃ a₀, lo < a₀ ∧ a₀ < z ∧ ∀ x ∈ S, x < z → x < a₀ := by
  classical
  set U : Finset ℝ := insert lo (S.filter (fun x => x < z)) with hU
  have hUne : U.Nonempty := ⟨lo, Finset.mem_insert_self _ _⟩
  have hmax_lt : U.max' hUne < z := by
    rw [Finset.max'_lt_iff]
    intro u hu
    rw [hU, Finset.mem_insert] at hu
    rcases hu with h | h
    · rw [h]; exact hlo
    · exact (Finset.mem_filter.mp h).2
  refine ⟨(U.max' hUne + z) / 2, ?_, ?_, ?_⟩
  · have : lo ≤ U.max' hUne := Finset.le_max' U lo (Finset.mem_insert_self _ _)
    linarith
  · linarith
  · intro x hx hxz
    have : x ≤ U.max' hUne :=
      Finset.le_max' U x (Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨hx, hxz⟩)))
    linarith

/-- A gap point just above `z` and below `hi`, lying below every element of the
finite set `S` that is above `z`. Used to manufacture the artificial right
neighbour a crossing lemma needs at a break point. -/
theorem exists_right_gap (S : Finset ℝ) (z hi : ℝ) (hhi : z < hi) :
    ∃ b₀, z < b₀ ∧ b₀ < hi ∧ ∀ x ∈ S, z < x → b₀ < x := by
  classical
  set U : Finset ℝ := insert hi (S.filter (fun x => z < x)) with hU
  have hUne : U.Nonempty := ⟨hi, Finset.mem_insert_self _ _⟩
  have hlt_min : z < U.min' hUne := by
    rw [Finset.lt_min'_iff]
    intro u hu
    rw [hU, Finset.mem_insert] at hu
    rcases hu with h | h
    · rw [h]; exact hhi
    · exact (Finset.mem_filter.mp h).2
  refine ⟨(z + U.min' hUne) / 2, ?_, ?_, ?_⟩
  · linarith
  · have : U.min' hUne ≤ hi := Finset.min'_le U hi (Finset.mem_insert_self _ _)
    linarith
  · intro x hx hxz
    have : U.min' hUne ≤ x :=
      Finset.min'_le U x (Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨hx, hxz⟩)))
    linarith

/-- The head `p` of a Sturm chain is a member of the chain. -/
theorem chain_head_mem (hchain : IsSturmChain p chain) : p ∈ chain := by
  cases chain with
  | nil => exact absurd hchain.head (by simp)
  | cons hd tl =>
    have hhd : hd = p := by simpa using hchain.head
    rw [← hhd]; exact List.mem_cons_self

/-- **Right registration.** If no chain element vanishes anywhere in the
half-open interval `(z, c]` (with `z ≤ c`), then `sturmVar` agrees at `z` and
`c`, even if `z` itself is a chain zero: the value at a break point equals the
value immediately to its right. -/
theorem sturmVar_eq_right (hp : p ≠ 0) (hsf : Squarefree p)
    (hchain : IsSturmChain p chain) {z c : ℝ} (hzc : z ≤ c)
    (hclear : ∀ x, z < x → x ≤ c → x ∉ chainZeros chain) :
    sturmVar chain z = sturmVar chain c := by
  rcases eq_or_lt_of_le hzc with rfl | hlt
  · rfl
  have hne := hchain.nonzero_mem
  by_cases hzZ : z ∈ chainZeros chain
  · obtain ⟨a₀, _, ha₀z, ha₀gap⟩ := exists_left_gap (chainZeros chain) z (z - 1) (by linarith)
    have hz_ex : ∀ q ∈ chain, ∀ x ∈ Set.Icc a₀ c, x ≠ z → q.eval x ≠ 0 := by
      intro q hq x hx hxz hqx
      have hxZ : x ∈ chainZeros chain := (mem_chainZeros hne).mpr ⟨q, hq, hqx⟩
      rcases lt_trichotomy x z with hlt' | heq | hgt'
      · exact absurd (ha₀gap x hxZ hlt') (not_lt.mpr hx.1)
      · exact hxz heq
      · exact hclear x hgt' hx.2 hxZ
    by_cases hroot : p.IsRoot z
    · have hpz : ∀ x ∈ Set.Icc a₀ c, x ≠ z → ¬ p.IsRoot x := by
        intro x hx hxz hpr
        have hxZ : x ∈ chainZeros chain :=
          (mem_chainZeros hne).mpr ⟨p, chain_head_mem hchain, hpr⟩
        rcases lt_trichotomy x z with hlt' | heq | hgt'
        · exact absurd (ha₀gap x hxZ hlt') (not_lt.mpr hx.1)
        · exact hxz heq
        · exact hclear x hgt' hx.2 hxZ
      exact (sturmVar_root_cross hp hsf hchain z hroot a₀ c ha₀z hlt hz_ex hpz).2
    · exact (sturmVar_interior_cross hchain z hroot a₀ c ha₀z hlt hz_ex).2
  · have hz_all : ∀ q ∈ chain, ∀ x ∈ Set.Icc z c, q.eval x ≠ 0 := by
      intro q hq x hx hqx
      have hxZ : x ∈ chainZeros chain := (mem_chainZeros hne).mpr ⟨q, hq, hqx⟩
      rcases eq_or_lt_of_le hx.1 with heq | hgt
      · exact hzZ (by rw [heq]; exact hxZ)
      · exact hclear x hgt hx.2 hxZ
    exact sturmVar_const_of_no_zero hchain z c hzc hz_all

/-- Splitting a half-open interval count: for `a ≤ a' ≤ b`, the number of
multiset entries in `(a, b]` is the sum of those in `(a, a']` and `(a', b]`. -/
private theorem card_filter_Ioc_split (s : Multiset ℝ) {a a' b : ℝ} (h1 : a ≤ a') (h2 : a' ≤ b) :
    (s.filter (fun r => a < r ∧ r ≤ b)).card
      = (s.filter (fun r => a < r ∧ r ≤ a')).card
        + (s.filter (fun r => a' < r ∧ r ≤ b)).card := by
  classical
  have hand : s.filter (fun r => (a < r ∧ r ≤ a') ∧ (a' < r ∧ r ≤ b)) = 0 := by
    rw [Multiset.filter_eq_nil]
    rintro x _ ⟨⟨_, hxa'⟩, ha'x, _⟩
    exact absurd ha'x (not_lt.mpr hxa')
  have hor : s.filter (fun r => (a < r ∧ r ≤ a') ∨ (a' < r ∧ r ≤ b))
      = s.filter (fun r => a < r ∧ r ≤ b) := by
    apply Multiset.filter_congr
    intro x _
    constructor
    · rintro (⟨h, h'⟩ | ⟨h, h'⟩)
      · exact ⟨h, le_trans h' h2⟩
      · exact ⟨lt_of_le_of_lt h1 h, h'⟩
    · rintro ⟨h, h'⟩
      rcases lt_trichotomy x a' with hx | hx | hx
      · exact Or.inl ⟨h, hx.le⟩
      · exact Or.inl ⟨h, hx.le⟩
      · exact Or.inr ⟨hx, h'⟩
  rw [← Multiset.card_add, Multiset.filter_add_filter, hand, Multiset.add_zero, hor]

/-- **Sturm's theorem, half-open form.** For `p ≠ 0` squarefree with a
generalised Sturm chain, the drop in `sturmVar` from `a` to `b` equals the
number of real roots of `p` in the half-open interval `(a, b]`, counted as the
cardinality of the corresponding filtered submultiset of `p.roots`.

Proof sketch: telescope the preceding lemmas over the finitely many zeros of
the chain elements in `(a, b]`. Zeros of interior elements are variation-neutral
(step 2); each root of `p` drops the count by exactly one and registers at the
root under the half-open convention (step 3); between consecutive chain zeros
`sturmVar` is constant (step 1). The signed total is therefore the number of
roots of `p` in `(a, b]`. -/
theorem sturm_half_open (hp : p ≠ 0) (hsf : Squarefree p)
    (hchain : IsSturmChain p chain) {a b : ℝ} (hab : a < b) :
    (sturmVar chain a : ℤ) - sturmVar chain b =
      (p.roots.filter (fun r => a < r ∧ r ≤ b)).card := by
  classical
  have hne := hchain.nonzero_mem
  have hnod : p.roots.Nodup :=
    Polynomial.nodup_roots (PerfectField.separable_iff_squarefree.mpr hsf)
  suffices H : ∀ n : ℕ, ∀ a b : ℝ, a ≤ b →
      ((chainZeros chain).filter (fun x => a < x ∧ x ≤ b)).card = n →
      (sturmVar chain a : ℤ) - sturmVar chain b =
        (p.roots.filter (fun r => a < r ∧ r ≤ b)).card by
    exact H _ a b hab.le rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hab hcard
    set F := (chainZeros chain).filter (fun x => a < x ∧ x ≤ b) with hF
    by_cases hemp : F = ∅
    · -- No break point in `(a, b]`: `sturmVar` is constant and there are no roots.
      have hclear : ∀ x, a < x → x ≤ b → x ∉ chainZeros chain := by
        intro x hx1 hx2 hxZ
        have hxF : x ∈ F := by rw [hF, Finset.mem_filter]; exact ⟨hxZ, hx1, hx2⟩
        rw [hemp] at hxF; exact absurd hxF (Finset.notMem_empty x)
      have heqv : sturmVar chain a = sturmVar chain b :=
        sturmVar_eq_right hp hsf hchain hab hclear
      have hroots0 : p.roots.filter (fun r => a < r ∧ r ≤ b) = 0 := by
        rw [Multiset.filter_eq_nil]
        rintro x hx ⟨h1, h2⟩
        exact hclear x h1 h2
          ((mem_chainZeros hne).mpr
                  ⟨p, chain_head_mem hchain, (Polynomial.mem_roots hp).mp hx⟩)
      rw [heqv, hroots0]; simp
    · -- Peel off the largest break point `z` in `(a, b]`.
      have hFne : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp
      let z := F.max' hFne
      have hzmem : z ∈ F := F.max'_mem hFne
      have hzmax : ∀ x ∈ F, x ≤ z := fun x hx => F.le_max' x hx
      obtain ⟨hzS, haz, hzb⟩ : z ∈ chainZeros chain ∧ a < z ∧ z ≤ b := by
        have h := hzmem; rw [hF, Finset.mem_filter] at h; exact ⟨h.1, h.2.1, h.2.2⟩
      obtain ⟨a', ha_a', ha'z, ha'gap⟩ := exists_left_gap (chainZeros chain) z a haz
      obtain ⟨b', hzb', _, hb'gap⟩ := exists_right_gap (chainZeros chain) z (z + 1) (by linarith)
      -- Only break point in `(a', b]` is `z`.
      have honly : ∀ x, a' < x → x ≤ b → x ∈ chainZeros chain → x = z := by
        intro x hx1 hx2 hxZ
        rcases lt_trichotomy x z with hlt' | heq | hgt'
        · exact absurd (ha'gap x hxZ hlt') (not_lt.mpr hx1.le)
        · exact heq
        · have hxF : x ∈ F := by rw [hF, Finset.mem_filter]; exact ⟨hxZ, lt_trans ha_a' hx1, hx2⟩
          exact absurd (hzmax x hxF) (not_le.mpr hgt')
      -- `[a', b']` has no break point except `z`.
      have hz_ex : ∀ q ∈ chain, ∀ x ∈ Set.Icc a' b', x ≠ z → q.eval x ≠ 0 := by
        intro q hq x hx hxz hqx
        have hxZ : x ∈ chainZeros chain := (mem_chainZeros hne).mpr ⟨q, hq, hqx⟩
        rcases lt_trichotomy x z with hlt' | heq | hgt'
        · exact absurd (ha'gap x hxZ hlt') (not_lt.mpr hx.1)
        · exact hxz heq
        · exact absurd (hb'gap x hxZ hgt') (not_lt.mpr hx.2)
      have hpz : ∀ x ∈ Set.Icc a' b', x ≠ z → ¬ p.IsRoot x := fun x hx hxz hpr =>
        hz_ex p (chain_head_mem hchain) x hx hxz hpr
      -- Right registration: `sturmVar z = sturmVar b`.
      have hzeqb : sturmVar chain z = sturmVar chain b := by
        apply sturmVar_eq_right hp hsf hchain hzb
        intro x hx1 hx2 hxZ
        have hxF : x ∈ F := by rw [hF, Finset.mem_filter]; exact ⟨hxZ, lt_trans haz hx1, hx2⟩
        exact absurd (hzmax x hxF) (not_le.mpr hx1)
      -- Inductive hypothesis on `(a, a']`.
      have hsub : (chainZeros chain).filter (fun x => a < x ∧ x ≤ a') ⊆ F := by
        rw [hF]; intro x hx; rw [Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, hx.2.1, le_trans hx.2.2 (le_trans ha'z.le hzb)⟩
      have hznotin : z ∉ (chainZeros chain).filter (fun x => a < x ∧ x ≤ a') := by
        rw [Finset.mem_filter]; rintro ⟨_, _, hza'⟩; exact absurd hza' (not_le.mpr ha'z)
      have hlt_card : ((chainZeros chain).filter (fun x => a < x ∧ x ≤ a')).card < n := by
        rw [← hcard]
        exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨z, hzmem, hznotin⟩)
      have IHres := ih _ hlt_card a a' ha_a'.le rfl
      have hsplitZ : ((p.roots.filter (fun r => a < r ∧ r ≤ b)).card : ℤ)
          = ((p.roots.filter (fun r => a < r ∧ r ≤ a')).card : ℤ)
            + ((p.roots.filter (fun r => a' < r ∧ r ≤ b)).card : ℤ) := by
        exact_mod_cast card_filter_Ioc_split p.roots ha_a'.le (le_trans ha'z.le hzb)
      by_cases hzroot : p.IsRoot z
      · obtain ⟨hcrossL, hcrossR⟩ :=
          sturmVar_root_cross hp hsf hchain z hzroot a' b' ha'z hzb' hz_ex hpz
        have ha'bZ : (sturmVar chain a' : ℤ) = sturmVar chain b + 1 := by
          have : sturmVar chain a' = sturmVar chain b + 1 := by
            rw [hcrossL, ← hcrossR, hzeqb]
          exact_mod_cast this
        have hRZ : ((p.roots.filter (fun r => a' < r ∧ r ≤ b)).card : ℤ) = 1 := by
          have hzrootmem : z ∈ p.roots := (Polynomial.mem_roots hp).mpr hzroot
          have hfeq : p.roots.filter (fun r => a' < r ∧ r ≤ b)
              = p.roots.filter (fun r => r = z) := by
            apply Multiset.filter_congr
            intro x hx
            constructor
            · rintro ⟨h1, h2⟩
              exact honly x h1 h2
                ((mem_chainZeros hne).mpr
                  ⟨p, chain_head_mem hchain, (Polynomial.mem_roots hp).mp hx⟩)
            · rintro rfl; exact ⟨ha'z, hzb⟩
          rw [hfeq, Multiset.filter_eq', Multiset.card_replicate,
            Multiset.count_eq_one_of_mem hnod hzrootmem]
          rfl
        linarith [hsplitZ, hRZ, ha'bZ, IHres]
      · obtain ⟨hcrossL, _⟩ :=
          sturmVar_interior_cross hchain z hzroot a' b' ha'z hzb' hz_ex
        have ha'bZ : (sturmVar chain a' : ℤ) = sturmVar chain b := by
          have : sturmVar chain a' = sturmVar chain b := by rw [hcrossL, hzeqb]
          exact_mod_cast this
        have hRZ : ((p.roots.filter (fun r => a' < r ∧ r ≤ b)).card : ℤ) = 0 := by
          have hfeq : p.roots.filter (fun r => a' < r ∧ r ≤ b) = 0 := by
            rw [Multiset.filter_eq_nil]
            rintro x hx ⟨h1, h2⟩
            have hxz : x = z := honly x h1 h2
              ((mem_chainZeros hne).mpr
                  ⟨p, chain_head_mem hchain, (Polynomial.mem_roots hp).mp hx⟩)
            rw [hxz] at hx
            exact hzroot ((Polynomial.mem_roots hp).mp hx)
          rw [hfeq]; rfl
        linarith [hsplitZ, hRZ, ha'bZ, IHres]

/-- **Sign at `+∞`.** Past all its real roots, a nonzero real polynomial has the
sign of its leading coefficient. -/
theorem eval_sign_pos_inf {q : Polynomial ℝ} (hq : q ≠ 0) {x : ℝ}
    (hbeyond : ∀ y, q.IsRoot y → y < x) :
    SignType.sign (q.eval x) = SignType.sign q.leadingCoeff := by
  have hlc : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
  rcases lt_or_gt_of_ne hlc with h | h
  · rw [sign_neg (Polynomial.eval_lt_zero_of_roots_lt_of_leadingCoeff_nonpos hbeyond h.le),
      sign_neg h]
  · rw [sign_pos (Polynomial.zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg hbeyond h.le),
      sign_pos h]

/-- **Sign at `−∞`.** Below all its real roots, a nonzero real polynomial has the
sign of `leadingCoeff · (-1) ^ natDegree`. -/
theorem eval_sign_neg_inf {q : Polynomial ℝ} (hq : q ≠ 0) {x : ℝ}
    (hbeyond : ∀ y, q.IsRoot y → x < y) :
    SignType.sign (q.eval x) = SignType.sign (q.leadingCoeff * (-1) ^ q.natDegree) := by
  set r := q.comp (-Polynomial.X) with hr
  have hlcr : r.leadingCoeff = q.leadingCoeff * (-1) ^ q.natDegree := by
    rw [hr, Polynomial.leadingCoeff_comp (by simp)]; simp
  have hrne : r ≠ 0 := by
    intro h; rw [h, Polynomial.leadingCoeff_zero] at hlcr
    exact (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hq)
      (pow_ne_zero _ (by norm_num))) hlcr.symm
  have heval : r.eval (-x) = q.eval x := by rw [hr, Polynomial.eval_comp]; simp
  have hbeyond' : ∀ y, r.IsRoot y → y < -x := by
    intro y hy
    have hqy : q.IsRoot (-y) := by
      rw [hr, Polynomial.IsRoot, Polynomial.eval_comp] at hy; simpa using hy
    have := hbeyond (-y) hqy
    linarith
  have hsign := eval_sign_pos_inf hrne hbeyond'
  rw [heval, hlcr] at hsign
  exact hsign

/-- **Sturm's theorem, line form.** For `p ≠ 0` squarefree with a generalised
Sturm chain, the total number of real roots of `p` equals the drop in `sturmVar`
from `−∞` to `+∞`.

Proof sketch: take `a` below and `b` above every real root
(e.g. beyond a Cauchy bound). Then `sturmVar chain a = sturmVarNegInf chain` and
`sturmVar chain b = sturmVarPosInf chain`, because each chain element has
constant sign past its largest real zero equal to its sign at the corresponding
infinity, and `(a, b]` contains every real root. Apply `sturm_half_open`; the
filtered multiset is all of `p.roots`. -/
theorem sturm_line (hp : p ≠ 0) (hsf : Squarefree p)
    (hchain : IsSturmChain p chain) :
    (sturmVarNegInf chain : ℤ) - sturmVarPosInf chain = p.roots.card := by
  classical
  have hne := hchain.nonzero_mem
  -- A bound `M > 0` strictly beyond every chain zero (hence every root of every element).
  obtain ⟨M, hMpos, hM⟩ : ∃ M : ℝ, 0 < M ∧ ∀ x ∈ chainZeros chain, |x| < M := by
    set B := insert (0 : ℝ) ((chainZeros chain).image (fun x => |x|)) with hB
    have hBne : B.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
    refine ⟨B.max' hBne + 1, ?_, ?_⟩
    · have : (0 : ℝ) ≤ B.max' hBne := Finset.le_max' B 0 (Finset.mem_insert_self _ _)
      linarith
    · intro x hx
      have : |x| ≤ B.max' hBne :=
        Finset.le_max' B |x| (Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨x, hx, rfl⟩)))
      linarith
  -- Sign of each element at `±M` is its sign at the corresponding infinity.
  have hpos : ∀ q ∈ chain, SignType.sign (q.eval M) = SignType.sign q.leadingCoeff := by
    intro q hq
    apply eval_sign_pos_inf (hne q hq)
    intro y hy
    have hyz : y ∈ chainZeros chain := (mem_chainZeros hne).mpr ⟨q, hq, hy⟩
    have hya := hM y hyz; rw [abs_lt] at hya; exact hya.2
  have hneg : ∀ q ∈ chain,
      SignType.sign (q.eval (-M)) = SignType.sign (q.leadingCoeff * (-1) ^ q.natDegree) := by
    intro q hq
    apply eval_sign_neg_inf (hne q hq)
    intro y hy
    have hyz : y ∈ chainZeros chain := (mem_chainZeros hne).mpr ⟨q, hq, hy⟩
    have hya := hM y hyz; rw [abs_lt] at hya; exact hya.1
  -- Hence `sturmVar` at `±M` equals the `±∞` counts.
  have hMposEq : sturmVar chain M = sturmVarPosInf chain := by
    change signVariations (chain.map (Polynomial.eval M))
      = signVariations (chain.map Polynomial.leadingCoeff)
    apply signVariations_congr
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    exact hpos
  have hMnegEq : sturmVar chain (-M) = sturmVarNegInf chain := by
    change signVariations (chain.map (Polynomial.eval (-M)))
      = signVariations (chain.map (fun q => q.leadingCoeff * (-1) ^ q.natDegree))
    apply signVariations_congr
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    exact hneg
  -- Apply the half-open form on `(-M, M]`, which catches every root.
  have hkey := sturm_half_open hp hsf hchain (a := -M) (b := M) (by linarith)
  have hfilter : p.roots.filter (fun r => -M < r ∧ r ≤ M) = p.roots := by
    rw [Multiset.filter_eq_self]
    intro r hr
    have hroot : p.eval r = 0 := (Polynomial.mem_roots hp).mp hr
    have hrz : r ∈ chainZeros chain := (mem_chainZeros hne).mpr ⟨p, chain_head_mem hchain, hroot⟩
    have hra := hM r hrz; rw [abs_lt] at hra
    exact ⟨hra.1, hra.2.le⟩
  rw [← hMnegEq, ← hMposEq, hkey, hfilter]

end Sturm
