/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.Polynomial.Sturm.Defs
public import Mathlib.Analysis.Polynomial.Order
public import Mathlib.Topology.Instances.Sign.Connected

/-!
# Sturm's theorem

For a real polynomial with no repeated real roots admitting a Sturm chain, the number of roots
in `(a, b]` is the decrease in sign variations from `a` to `b`. Evaluating the
signs at infinity gives the total number of real roots.

## Main results

* `Sturm.IsSturmChain.sturm_Ioc`: the root count on a half-open interval.
* `Sturm.IsSturmChain.sturm`: the root count on the real line.

The proof first establishes local constancy away from chain zeros. Crossing an
interior entry's zero preserves the variation count; crossing a root of the
first entry decreases it by one. The value at a root equals the value just to
its right, accounting for the half-open interval convention. Induction over the
finite set of chain zeros then gives the interval theorem.

## References

* Basu, Pollack and Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  [§2.2.2](https://doi.org/10.1007/3-540-33099-2).
-/

public section

open Filter Topology

namespace Sturm

/-- A local sign-pattern relation between two real lists: they agree entry by
entry except that a nonzero entry flanked by two opposite-sign neighbours may
collapse to `0`. Such a collapse is variation-neutral, so `signVariations` and
the leading sign are preserved (`SignRelation.signVariations_eq`). -/
private inductive SignRelation : List ℝ → List ℝ → Prop
  | nil : SignRelation [] []
  | same {x y : ℝ} {l m : List ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
      (hs : SignType.sign x = SignType.sign y) (h : SignRelation l m) :
      SignRelation (x :: l) (y :: m)
  | collapse {x X x' : ℝ} {l m : List ℝ} {y y' : ℝ}
      (hx : x ≠ 0) (hX : X ≠ 0) (hy' : y' ≠ 0)
      (hsx : SignType.sign x = SignType.sign x')
      (hsy : SignType.sign y = SignType.sign y')
      (hopp : SignType.sign x * SignType.sign y = -1)
      (h : SignRelation (y :: l) (y' :: m)) :
      SignRelation (x :: X :: y :: l) (x' :: 0 :: y' :: m)

private theorem sign_changes_of_opposite (u v w : SignType) (huw : u * w = -1) (hv : v ≠ 0) :
    (if u * v = -1 then (1 : ℕ) else 0) + (if v * w = -1 then 1 else 0) = 1 := by
  revert huw hv; revert u v w; decide

/-- Lists related by `SignRelation` have equal sign variations and equal leading signs. -/
private theorem SignRelation.signVariations_eq {L M : List ℝ} (h : SignRelation L M) :
    signVariations L = signVariations M ∧ firstSign L = firstSign M := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | @same x y l m hx hy hs h ih =>
    refine ⟨?_, ?_⟩
    · rw [signVariations_cons l hx, signVariations_cons m hy, ih.1, ih.2, hs]
    · rw [firstSign_cons_ne l hx, firstSign_cons_ne m hy, hs]
  | @collapse x X x' l m y y' hx hX hy' hsx hsy hopp h ih =>
    have hy : y ≠ 0 := by
      intro hy0; rw [hy0, sign_zero, mul_zero] at hopp; exact absurd hopp (by decide)
    have hx' : x' ≠ 0 := by
      intro hx0; rw [hx0, sign_zero] at hsx; exact hx (sign_eq_zero_iff.mp hsx)
    refine ⟨?_, ?_⟩
    · -- signVariations L
      rw [signVariations_cons (X :: y :: l) hx,
        firstSign_cons_ne (y :: l) hX, signVariations_cons (y :: l) hX,
        firstSign_cons_ne l hy]
      rw [signVariations_cons (0 :: y' :: m) hx',
        firstSign_cons_zero (y' :: m) rfl, firstSign_cons_ne m hy',
        signVariations_cons_zero]
      simp only [Option.elim_some]
      rw [← add_assoc, ih.1]
      congr 1
      rw [← hsx, ← hsy, ite_eq_left hopp]
      exact sign_changes_of_opposite _ _ _ hopp (fun h => hX (sign_eq_zero_iff.mp h))
    · rw [firstSign_cons_ne (X :: y :: l) hx, firstSign_cons_ne (0 :: y' :: m) hx', hsx]


/-- A real polynomial with no roots on an interval has equal signs at its endpoints. -/
private theorem eval_sign_eq_of_no_zero {q : Polynomial ℝ} {a b : ℝ} (hab : a ≤ b)
    (hz : ∀ x ∈ Set.Icc a b, q.eval x ≠ 0) :
    SignType.sign (q.eval a) = SignType.sign (q.eval b) :=
  isPreconnected_Icc.sign_eq_of_continuousOn q.continuousOn hz
    ⟨le_refl a, hab⟩ ⟨hab, le_refl b⟩

/-- Build the sign-pattern relation `SignRelation` between the evaluations of a
polynomial list at a "generic" point `a` (where every element is nonzero) and a
"special" point `r` (where some interior elements may vanish). The hypotheses
are exactly what an `IsSturmChain` supplies restricted to the relevant interval:
every element is nonzero at `a`; the head and last elements are nonzero at `r`;
whenever an interior element vanishes at `r` its neighbours are nonzero there
with opposite signs; and every element nonzero at `r` has the same sign at `a`
and `r`. -/
private theorem signRelation_eval (a r : ℝ) :
    ∀ (cs : List (Polynomial ℝ)),
      (∀ q ∈ cs, q.eval a ≠ 0) →
      (∀ q, cs.head? = some q → q.eval r ≠ 0) →
      (∀ q, cs.getLast? = some q → q.eval r ≠ 0) →
      (∀ (i : ℕ) (q0 q1 q2 : Polynomial ℝ), cs[i]? = some q0 → cs[i + 1]? = some q1 →
        cs[i + 2]? = some q2 → q1.eval r = 0 →
        q0.eval r ≠ 0 ∧ q2.eval r ≠ 0 ∧ q0.eval r * q2.eval r < 0) →
      (∀ q ∈ cs, q.eval r ≠ 0 → SignType.sign (q.eval a) = SignType.sign (q.eval r)) →
      SignRelation (cs.map (Polynomial.eval a)) (cs.map (Polynomial.eval r))
  | [], _, _, _, _, _ => SignRelation.nil
  | [q0], hne0, hfront, _, _, hsame => by
      have hr : q0.eval r ≠ 0 := hfront q0 rfl
      exact SignRelation.same (hne0 q0 (by simp)) hr (hsame q0 (by simp) hr) SignRelation.nil
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
            have IH := signRelation_eval a r (q2 :: rest') hne0' hfront' hlast' halt' hsame'
            simp only [List.map_cons] at IH ⊢
            rw [hq1]
            exact SignRelation.collapse ha0 (hne0 q1 (by simp)) hn2 hsx hsy hoppA IH
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
        have IH := signRelation_eval a r (q1 :: rest) hne0' hfront' hlast' halt' hsame'
        simp only [List.map_cons] at IH ⊢
        exact SignRelation.same ha0 hr0 (hsame q0 (by simp) hr0) IH

variable {p : Polynomial ℝ} {chain : List (Polynomial ℝ)}

/-- Sign variations are constant on an interval containing no zero of any chain entry. -/
theorem sturmVar_const_of_no_zero
    (a b : ℝ) (hab : a ≤ b)
    (hz : ∀ q ∈ chain, ∀ x ∈ Set.Icc a b, q.eval x ≠ 0) :
    sturmVar chain a = sturmVar chain b := by
  change signVariations (chain.map (Polynomial.eval a))
    = signVariations (chain.map (Polynomial.eval b))
  apply signVariations_congr
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  intro q hq
  exact eval_sign_eq_of_no_zero hab (fun x hx => hz q hq x hx)

/-- Crossing a zero of an interior entry preserves the variation count. -/
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
    refine (signRelation_eval a r chain (fun q hq => hz q hq a ⟨le_refl a, hab⟩ (ne_of_lt har))
      hfront hlast halt (fun q hq hqr => ?_)).signVariations_eq.1
    exact eval_sign_eq_of_no_zero har.le (fun x hx => by
      by_cases hxr : x = r
      · rw [hxr]; exact hqr
      · exact hz q hq x ⟨hx.1, hx.2.trans hrb.le⟩ hxr)
  · change signVariations (chain.map (Polynomial.eval r))
      = signVariations (chain.map (Polynomial.eval b))
    refine ((signRelation_eval b r chain
      (fun q hq => hz q hq b ⟨hab, le_refl b⟩ (ne_of_lt hrb).symm)
      hfront hlast halt (fun q hq hqr => ?_)).signVariations_eq.1).symm
    exact (eval_sign_eq_of_no_zero hrb.le (fun x hx => by
      by_cases hxr : x = r
      · rw [hxr]; exact hqr
      · exact hz q hq x ⟨har.le.trans hx.1, hx.2⟩ hxr)).symm

/-- Crossing a root of the first entry decreases the variation count by one.
The count at the root equals the count just to its right. -/
theorem sturmVar_root_cross (hchain : IsSturmChain p chain) (r : ℝ) (hr : p.IsRoot r)
    (a b : ℝ) (har : a < r) (hrb : r < b)
    (hz : ∀ q ∈ chain, ∀ x ∈ Set.Icc a b, x ≠ r → q.eval x ≠ 0) :
    sturmVar chain a = sturmVar chain b + 1 ∧ sturmVar chain r = sturmVar chain b := by
  have hpz : ∀ x ∈ Set.Icc a b, x ≠ r → ¬ p.IsRoot x :=
    fun x hx hxr => hz p hchain.head_mem x hx hxr
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
    (signRelation_eval a r (q :: tail)
      (fun s hs => hz s (List.mem_cons_of_mem _ hs) a ⟨le_refl a, hab⟩ (ne_of_lt har))
      hfront_rest hlast_rest halt_rest hsame_a).signVariations_eq.1
  have hEqB : sturmVar (q :: tail) b = sturmVar (q :: tail) r :=
    (signRelation_eval b r (q :: tail)
      (fun s hs => hz s (List.mem_cons_of_mem _ hs) b ⟨hab, le_refl b⟩ (ne_of_lt hrb).symm)
      hfront_rest hlast_rest halt_rest hsame_b).signVariations_eq.1
  -- Head-pair bookkeeping at each point.
  have hSVa : sturmVar (p :: q :: tail) a = 1 + sturmVar (q :: tail) a := by
    change signVariations (p.eval a :: (q :: tail).map (Polynomial.eval a))
      = 1 + signVariations ((q :: tail).map (Polynomial.eval a))
    rw [signVariations_cons _ hpa]
    simp only [List.map_cons]
    rw [firstSign_cons_ne _ hqa, Option.elim_some, ite_eq_left hsignA]
  have hSVb : sturmVar (p :: q :: tail) b = sturmVar (q :: tail) b := by
    change signVariations (p.eval b :: (q :: tail).map (Polynomial.eval b))
      = signVariations ((q :: tail).map (Polynomial.eval b))
    rw [signVariations_cons _ hpb]
    simp only [List.map_cons]
    rw [firstSign_cons_ne _ hqb, Option.elim_some, ite_eq_right hsignB, zero_add]
  have hSVr : sturmVar (p :: q :: tail) r = sturmVar (q :: tail) r := by
    change signVariations (p.eval r :: (q :: tail).map (Polynomial.eval r))
      = signVariations ((q :: tail).map (Polynomial.eval r))
    rw [hpr0]; exact signVariations_cons_zero _
  refine ⟨?_, ?_⟩
  · rw [hSVa, hSVb, hEqA, hEqB]; omega
  · rw [hSVr, hSVb]; exact hEqB.symm

/-- The union of the real root sets of the chain entries. -/
noncomputable def chainZeros (cs : List (Polynomial ℝ)) : Finset ℝ :=
  cs.toFinset.biUnion (fun q => q.roots.toFinset)

/-- Membership in `chainZeros`: a point lies in it exactly when some chain
element vanishes there (using that every chain element is nonzero). -/
theorem mem_chainZeros {cs : List (Polynomial ℝ)} (hne : ∀ q ∈ cs, q ≠ 0) {x : ℝ} :
    x ∈ chainZeros cs ↔ ∃ q ∈ cs, q.eval x = 0 := by
  simp only [chainZeros, Finset.mem_biUnion, List.mem_toFinset, Multiset.mem_toFinset]
  exact exists_congr fun q => and_congr_right fun hq => Polynomial.mem_roots (hne q hq)

/-- Choose a point between `lo` and `z` above every element of `S` below `z`. -/
private theorem exists_left_gap (S : Finset ℝ) (z lo : ℝ) (hlo : lo < z) :
    ∃ a, lo < a ∧ a < z ∧ ∀ x ∈ S, x < z → x < a := by
  have h : ∀ᶠ a in 𝓝[<] z, ∀ x ∈ S, x < z → x < a := by
    rw [S.eventually_all]
    intro x _
    by_cases hx : x < z
    · exact ((eventually_gt_nhds hx).filter_mono nhdsWithin_le_nhds).mono fun _ ha _ => ha
    · simp [hx]
  obtain ⟨a, ha, hla, haz⟩ := (h.and (Ioo_mem_nhdsLT hlo)).exists
  exact ⟨a, hla, haz, ha⟩

/-- Choose a point between `z` and `hi` below every element of `S` above `z`. -/
private theorem exists_right_gap (S : Finset ℝ) (z hi : ℝ) (hhi : z < hi) :
    ∃ b, z < b ∧ b < hi ∧ ∀ x ∈ S, z < x → b < x := by
  have h : ∀ᶠ b in 𝓝[>] z, ∀ x ∈ S, z < x → b < x := by
    rw [S.eventually_all]
    intro x _
    by_cases hx : z < x
    · exact ((eventually_lt_nhds hx).filter_mono nhdsWithin_le_nhds).mono fun _ hb _ => hb
    · simp [hx]
  obtain ⟨b, hb, hzb, hbh⟩ := (h.and (Ioo_mem_nhdsGT hhi)).exists
  exact ⟨b, hzb, hbh, hb⟩

/-- The variation count agrees with its value immediately to the right,
including at zeros of chain entries. -/
theorem sturmVar_eq_right (hchain : IsSturmChain p chain) {z c : ℝ} (hzc : z ≤ c)
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
    · exact (sturmVar_root_cross hchain z hroot a₀ c ha₀z hlt hz_ex).2
    · exact (sturmVar_interior_cross hchain z hroot a₀ c ha₀z hlt hz_ex).2
  · have hz_all : ∀ q ∈ chain, ∀ x ∈ Set.Icc z c, q.eval x ≠ 0 := by
      intro q hq x hx hqx
      have hxZ : x ∈ chainZeros chain := (mem_chainZeros hne).mpr ⟨q, hq, hqx⟩
      rcases eq_or_lt_of_le hx.1 with heq | hgt
      · exact hzZ (by rw [heq]; exact hxZ)
      · exact hclear x hgt hx.2 hxZ
    exact sturmVar_const_of_no_zero z c hzc hz_all

/-- Splitting a half-open interval count: for `a ≤ a' ≤ b`, the number of
multiset entries in `(a, b]` is the sum of those in `(a, a']` and `(a', b]`. -/
private theorem card_filter_Ioc_split (s : Multiset ℝ) {a a' b : ℝ} (h1 : a ≤ a') (h2 : a' ≤ b) :
    (s.filter (fun r => a < r ∧ r ≤ b)).card
      = (s.filter (fun r => a < r ∧ r ≤ a')).card
        + (s.filter (fun r => a' < r ∧ r ≤ b)).card := by
  classical
  rw [← Multiset.card_add, ← Multiset.filter_add_not (fun r => r ≤ a')
    (s.filter (fun r => a < r ∧ r ≤ b)), Multiset.filter_filter, Multiset.filter_filter]
  congr 2 <;> apply Multiset.filter_congr <;> intro x _ <;> constructor
  · rintro ⟨h, hax, hxb⟩
    exact ⟨hax, h⟩
  · rintro ⟨hax, hxa⟩
    exact ⟨hxa, hax, hxa.trans h2⟩
  · rintro ⟨h, hax, hxb⟩
    exact ⟨lt_of_not_ge h, hxb⟩
  · rintro ⟨hax, hxb⟩
    exact ⟨hax.not_ge, h1.trans_lt hax, hxb⟩

/-- **Sturm's theorem** on a half-open interval.

The decrease in sign variations from `a` to `b` counts the roots in `(a, b]`.
The hypothesis on `p.roots` ensures each real root has multiplicity one. -/
theorem IsSturmChain.sturm_Ioc (hchain : IsSturmChain p chain) (hnod : p.roots.Nodup)
    {a b : ℝ} (hab : a ≤ b) :
    sturmVar chain b + (p.roots.filter (fun r => r ∈ Set.Ioc a b)).card =
      sturmVar chain a := by
  classical
  have hne := hchain.nonzero_mem
  suffices H : ∀ n : ℕ, ∀ a b : ℝ, a ≤ b →
      ((chainZeros chain).filter (fun x => a < x ∧ x ≤ b)).card = n →
      sturmVar chain b + (p.roots.filter (fun r => a < r ∧ r ≤ b)).card =
        sturmVar chain a by
    simpa only [Set.mem_Ioc] using H _ a b hab rfl
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
        sturmVar_eq_right hchain hab hclear
      have hroots0 : p.roots.filter (fun r => a < r ∧ r ≤ b) = 0 := by
        rw [Multiset.filter_eq_nil]
        rintro x hx ⟨h1, h2⟩
        exact hclear x h1 h2
          ((mem_chainZeros hne).mpr
                  ⟨p, hchain.head_mem, (Polynomial.mem_roots hchain.ne_zero).mp hx⟩)
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
      -- Right registration: `sturmVar z = sturmVar b`.
      have hzeqb : sturmVar chain z = sturmVar chain b := by
        apply sturmVar_eq_right hchain hzb
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
      have hsplit := card_filter_Ioc_split p.roots ha_a'.le (ha'z.le.trans hzb)
      by_cases hzroot : p.IsRoot z
      · obtain ⟨hcrossL, hcrossR⟩ :=
          sturmVar_root_cross hchain z hzroot a' b' ha'z hzb' hz_ex
        have ha'b : sturmVar chain a' = sturmVar chain b + 1 := by
          rw [hcrossL, ← hcrossR, hzeqb]
        have hRZ : (p.roots.filter (fun r => a' < r ∧ r ≤ b)).card = 1 := by
          have hzrootmem : z ∈ p.roots := (Polynomial.mem_roots hchain.ne_zero).mpr hzroot
          have hfeq : p.roots.filter (fun r => a' < r ∧ r ≤ b)
              = p.roots.filter (fun r => r = z) := by
            apply Multiset.filter_congr
            intro x hx
            constructor
            · rintro ⟨h1, h2⟩
              exact honly x h1 h2
                ((mem_chainZeros hne).mpr
                  ⟨p, hchain.head_mem, (Polynomial.mem_roots hchain.ne_zero).mp hx⟩)
            · rintro rfl; exact ⟨ha'z, hzb⟩
          rw [hfeq, Multiset.filter_eq', Multiset.card_replicate,
            Multiset.count_eq_one_of_mem hnod hzrootmem]
        omega
      · obtain ⟨hcrossL, _⟩ :=
          sturmVar_interior_cross hchain z hzroot a' b' ha'z hzb' hz_ex
        have ha'b : sturmVar chain a' = sturmVar chain b := by
          rw [hcrossL, hzeqb]
        have hRZ : (p.roots.filter (fun r => a' < r ∧ r ≤ b)).card = 0 := by
          have hfeq : p.roots.filter (fun r => a' < r ∧ r ≤ b) = 0 := by
            rw [Multiset.filter_eq_nil]
            rintro x hx ⟨h1, h2⟩
            have hxz : x = z := honly x h1 h2
              ((mem_chainZeros hne).mpr
                  ⟨p, hchain.head_mem, (Polynomial.mem_roots hchain.ne_zero).mp hx⟩)
            rw [hxz] at hx
            exact hzroot ((Polynomial.mem_roots hchain.ne_zero).mp hx)
          rw [hfeq]; rfl
        omega

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

/-- **Sturm's theorem** on the real line: the decrease in sign variations from
`-∞` to `+∞` counts all real roots. -/
theorem IsSturmChain.sturm (hchain : IsSturmChain p chain) (hnod : p.roots.Nodup) :
    sturmVarPosInf chain + p.roots.card = sturmVarNegInf chain := by
  classical
  have hne := hchain.nonzero_mem
  -- A bound `M > 0` strictly beyond every chain zero (hence every root of every element).
  obtain ⟨M, hMpos, hM⟩ : ∃ M : ℝ, 0 < M ∧ ∀ x ∈ chainZeros chain, |x| < M := by
    have h : ∀ᶠ M : ℝ in atTop, ∀ x ∈ chainZeros chain, |x| < M := by
      rw [Finset.eventually_all]
      exact fun x _ => eventually_gt_atTop |x|
    exact ((eventually_gt_atTop 0).and h).exists
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
  have hkey := hchain.sturm_Ioc hnod (a := -M) (b := M) (by linarith)
  have hfilter : p.roots.filter (fun r => r ∈ Set.Ioc (-M) M) = p.roots := by
    rw [Multiset.filter_eq_self]
    intro r hr
    have hroot : p.eval r = 0 := (Polynomial.mem_roots hchain.ne_zero).mp hr
    have hrz : r ∈ chainZeros chain := (mem_chainZeros hne).mpr ⟨p, hchain.head_mem, hroot⟩
    have hra := hM r hrz; rw [abs_lt] at hra
    exact ⟨hra.1, hra.2.le⟩
  simpa only [hMnegEq, hMposEq, hfilter] using hkey

end Sturm
