/-
Copyright (c) 2023 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
import Mathlib.Algebra.ContinuedFractions.Computation.ApproximationCorollaries
import Mathlib.Data.Nat.Parity
import Mathlib.Topology.List
import Mathlib.Topology.Instances.Irrational
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Correspondence between integer continued fractions and real numbers

This file proves that integer continued fractions converge to a real number.
-/

universe u v

open Nat Int Real Equiv Stream' Seq' Set Filter Topology TopologicalSpace FCF

open CF (of)

noncomputable section

namespace FCF

variable {K : Type u} [LinearOrderedField K]

theorem convergents_sub_convergents_succ {c : CF K} {n : ℕ} (hg : ¬c.s.TerminatedAt n) :
    c.convergents n - c.convergents (n + 1) =
      (-1) ^ (n + 1) * (↑(c.take (n + 1)).denominator)⁻¹ * (↑(c.take n).denominator)⁻¹ := by
  have hnz₁ : (↑(c.take (n + 1)).denominator : K) ≠ 0 :=
    mod_cast Nat.ne_of_gt (c.take (n + 1)).denominator.pos
  have hnz₂ : (↑(c.take n).denominator : K) ≠ 0 :=
    mod_cast Nat.ne_of_gt (c.take n).denominator.pos
  apply mul_left_injective₀ hnz₂
  apply mul_left_injective₀ hnz₁
  simp [convergents, FCF.eval, Rat.mkRat_eq_div]
  convert g.determinant hg using 1 <;> field_simp <;> ring

theorem convergents_lt_convergents_succ_of_even
    {g : GeneralizedContinuedFraction K} [g.IsIntegerContinuedFraction] {n : ℕ} (hne : Even n)
    (hg : ¬g.TerminatedAt n) : convergents g n < convergents g (n + 1) := by
  rw [← sub_neg, convergents_sub_convergents_succ hg]
  apply mul_neg_of_neg_of_pos
  · apply mul_neg_of_neg_of_pos
    · rw [(hne.add_odd odd_one).neg_one_pow]; exact neg_one_lt_zero
    · rw [inv_pos]; exact zero_lt_denom n
  · rw [inv_pos]; exact zero_lt_denom (n + 1)

theorem convergents_gt_convergents_succ_of_odd
    {g : GeneralizedContinuedFraction K} [g.IsIntegerContinuedFraction] {n : ℕ} (hno : Odd n)
    (hg : ¬g.TerminatedAt n) : convergents g (n + 1) < convergents g n := by
  rw [← sub_pos, convergents_sub_convergents_succ hg]
  apply mul_pos
  · apply mul_pos
    · rw [(hno.add_odd odd_one).neg_one_pow]; exact zero_lt_one
    · rw [inv_pos]; exact zero_lt_denom n
  · rw [inv_pos]; exact zero_lt_denom (n + 1)

theorem convergents_sub_convergents_add_two
    {g : GeneralizedContinuedFraction K} [g.IsContinuedFraction] {n : ℕ}
    (hg : ¬g.TerminatedAt (n + 1)) :
    convergents g n - convergents g (n + 2) =
      (-1) ^ (n + 1) * (denominators g (n + 1))⁻¹ *
        ((denominators g n)⁻¹ - (denominators g (n + 2))⁻¹) :=
  have hg' : ¬g.TerminatedAt n := mt (terminated_stable (le_of_lt n.lt_succ_self)) hg
  calc
    convergents g n - convergents g (n + 2)
      = (convergents g n - convergents g (n + 1)) +
          (convergents g (n + 1) - convergents g (n + 2)) := by ring
    _ = (-1) ^ (n + 1) * (denominators g n)⁻¹ * (denominators g (n + 1))⁻¹ +
          (-1) ^ (n + 2) * (denominators g (n + 1))⁻¹ * (denominators g (n + 2))⁻¹ :=
      congr_arg₂ (· + ·)
        (convergents_sub_convergents_succ hg') (convergents_sub_convergents_succ hg)
    _ = (-1) ^ (n + 1) * (denominators g (n + 1))⁻¹ *
          ((denominators g n)⁻¹ - (denominators g (n + 2))⁻¹) := by ring

theorem lt_of_succ_succ_get?_continuantsAux_b
    {g : GeneralizedContinuedFraction K} [g.IsContinuedFraction] {n : ℕ} {b : K} (hn : 1 ≤ n)
    (nth_partDenom_eq : g.partialDenominators.get? n = some b) :
    b * (g.continuantsAux (n + 1)).b < (g.continuantsAux (n + 2)).b := by
  obtain ⟨gp_n, nth_s_eq, rfl⟩ : ∃ gp_n, g.s.get? n = some gp_n ∧ gp_n.b = b
  exact exists_s_b_of_partDenom nth_partDenom_eq
  simp [IsSimpleContinuedFraction.partNum_eq_one (partNum_eq_s_a nth_s_eq),
    continuantsAux_recurrence nth_s_eq rfl rfl]
  exact g.zero_lt_continuantsAux_b hn

/-- Shows that `bₙ * Bₙ < Bₙ₊₁`, where `bₙ` is the `n`th partial denominator and `Bₙ₊₁` and `Bₙ` are
the `n + 1`th and `n`th denominator of the continued fraction, and `1 ≤ n`. -/
theorem lt_of_succ_get?_denom
    {g : GeneralizedContinuedFraction K} [g.IsContinuedFraction] {n : ℕ} {b : K} (hn : 1 ≤ n)
    (nth_partDenom_eq : g.partialDenominators.get? n = some b) :
    b * g.denominators n < g.denominators (n + 1) := by
  rw [denom_eq_conts_b, nth_cont_eq_succ_nth_contAux]
  exact lt_of_succ_succ_get?_continuantsAux_b hn nth_partDenom_eq

theorem denom_lt_denom_succ_of_one_le
    {g : GeneralizedContinuedFraction K} [g.IsIntegerContinuedFraction] {n : ℕ} (hn : 1 ≤ n)
    (not_terminatedAt_n : ¬g.TerminatedAt n) :
    g.denominators n < g.denominators (n + 1) := by
  obtain ⟨cp, hcp⟩ : ∃ cp, g.s.get? n = some cp :=
    Option.ne_none_iff_exists'.mp not_terminatedAt_n
  have hcpb : 1 ≤ cp.b := by
    rcases IsIntegerContinuedFraction.partDenom_eq_int (partDenom_eq_s_b hcp)
      with ⟨m, hm⟩
    have hgpb := IsContinuedFraction.zero_lt_partDenom (partDenom_eq_s_b hcp)
    rw [hm] at hgpb ⊢; norm_cast0 at hgpb ⊢; rwa [← Int.sub_one_lt_iff, Int.sub_self]
  have hd := lt_of_succ_get?_denom hn (partDenom_eq_s_b hcp)
  nlinarith only [hcpb, hd, g.zero_lt_denom n]

theorem denom_lt_denom_add_two
    {g : GeneralizedContinuedFraction K} [g.IsIntegerContinuedFraction] {n : ℕ}
    (hg : ¬g.TerminatedAt (n + 1)) :
    g.denominators n < g.denominators (n + 2) :=
  calc
    g.denominators n ≤ g.denominators (n + 1) := denom_mono
    _                < g.denominators (n + 2) :=
      denom_lt_denom_succ_of_one_le (by linarith only) hg

theorem convergents_lt_convergents_add_two_of_even
    {g : GeneralizedContinuedFraction K} [g.IsIntegerContinuedFraction] {n : ℕ} (hne : Even n)
    (hg : ¬g.TerminatedAt (n + 1)) : convergents g n < convergents g (n + 2) := by
  rw [← sub_neg, convergents_sub_convergents_add_two hg]
  apply mul_neg_of_neg_of_pos
  · apply mul_neg_of_neg_of_pos
    · rw [(hne.add_odd odd_one).neg_one_pow]; exact neg_one_lt_zero
    · rw [inv_pos]; exact zero_lt_denom (n + 1)
  · rw [sub_pos]; exact inv_lt_inv_of_lt (zero_lt_denom n) (denom_lt_denom_add_two hg)

theorem convergents_gt_convergents_add_two_of_odd
    {g : GeneralizedContinuedFraction K} [g.IsIntegerContinuedFraction] {n : ℕ} (hno : Odd n)
    (hg : ¬g.TerminatedAt (n + 1)) : convergents g (n + 2) < convergents g n := by
  rw [← sub_pos, convergents_sub_convergents_add_two hg]
  apply mul_pos
  · apply mul_pos
    · rw [(hno.add_odd odd_one).neg_one_pow]; exact zero_lt_one
    · rw [inv_pos]; exact zero_lt_denom (n + 1)
  · rw [sub_pos]; exact inv_lt_inv_of_lt (zero_lt_denom n) (denom_lt_denom_add_two hg)

theorem convergents_lt_convergents_of_even
    {g : GeneralizedContinuedFraction K} [g.IsIntegerContinuedFraction]
    {m n : ℕ} (hg : ¬g.TerminatedAt (n - 1)) (hme : Even m) (hmn : m < n) :
    g.convergents m < g.convergents n := by
  replace hmn := exists_eq_add_of_lt hmn; rcases hmn with ⟨k, rfl⟩
  rw [Nat.add_sub_cancel] at hg
  wlog hk : Odd k generalizing k hg
  · rw [← even_iff_not_odd, even_iff_exists_two_mul] at hk; rcases hk with ⟨k', rfl⟩
    apply lt_of_le_of_lt (b := g.convergents (m + 2 * k'))
    · cases k' using Nat.casesAuxOn with
      | zero     => rfl
      | succ k'' =>
        simp only [mul_add, mul_one, ← add_assoc] at hg ⊢
        have hg' : ¬g.TerminatedAt (m + 2 * k'' + 1) :=
          mt (terminated_stable ((m + 2 * k'' + 1).le_add_right 1)) hg
        exact le_of_lt (this (2 * k'' + 1) hg' (odd_two_mul_add_one k''))
    · exact convergents_lt_convergents_succ_of_even (hme.add (even_two_mul k')) hg
  rcases hk with ⟨k', rfl⟩
  simp only [← add_assoc] at hg ⊢
  induction k' using Nat.recAuxOn with
  | zero        => exact convergents_lt_convergents_add_two_of_even hme hg
  | succ k'' ih =>
    simp only [mul_add, mul_one, ← add_assoc] at hg ⊢
    trans g.convergents (m + 2 * k'' + 2)
    · exact ih (mt (terminated_stable ((m + 2 * k'' + 1).le_add_right 2)) hg)
    · exact convergents_lt_convergents_add_two_of_even
        ((hme.add (even_two_mul k'')).add even_two) hg

theorem convergents_gt_convergents_of_odd
    {g : GeneralizedContinuedFraction K} [g.IsIntegerContinuedFraction]
    {m n : ℕ} (hg : ¬g.TerminatedAt (n - 1)) (hmo : Odd m) (hmn : m < n) :
    g.convergents n < g.convergents m := by
  replace hmn := exists_eq_add_of_lt hmn; rcases hmn with ⟨k, rfl⟩
  rw [Nat.add_sub_cancel] at hg
  wlog hk : Odd k generalizing k hg
  · rw [← even_iff_not_odd, even_iff_exists_two_mul] at hk; rcases hk with ⟨k', rfl⟩
    apply lt_of_lt_of_le (b := g.convergents (m + 2 * k'))
    · exact convergents_gt_convergents_succ_of_odd (hmo.add_even (even_two_mul k')) hg
    · cases k' using Nat.casesAuxOn with
      | zero     => rfl
      | succ k'' =>
        simp only [mul_add, mul_one, ← add_assoc] at hg ⊢
        have hg' : ¬g.TerminatedAt (m + 2 * k'' + 1) :=
          mt (terminated_stable ((m + 2 * k'' + 1).le_add_right 1)) hg
        exact le_of_lt (this (2 * k'' + 1) hg' (odd_two_mul_add_one k''))
  rcases hk with ⟨k', rfl⟩
  simp only [← add_assoc] at hg ⊢
  induction k' using Nat.recAuxOn with
  | zero        => exact convergents_gt_convergents_add_two_of_odd hmo hg
  | succ k'' ih =>
    simp only [mul_add, mul_one, ← add_assoc] at hg ⊢
    trans g.convergents (m + 2 * k'' + 2)
    · exact convergents_gt_convergents_add_two_of_odd
        ((hmo.add_even (even_two_mul k'')).add_even even_two) hg
    · exact ih (mt (terminated_stable ((m + 2 * k'' + 1).le_add_right 2)) hg)

theorem convergents_le_convergents_of_even
    {g : GeneralizedContinuedFraction K} [g.IsIntegerContinuedFraction]
    {m n : ℕ} (hme : Even m) (hmn : m ≤ n) : g.convergents m ≤ g.convergents n := by
  rw [le_iff_eq_or_lt] at hmn; rcases hmn with rfl | hmn
  · rfl
  · by_cases hg : g.TerminatedAt (n - 1)
    · by_cases hg' : g.TerminatedAt m
      · exact ge_of_eq (convergents_stable_of_terminated (le_of_lt hmn) hg')
      · have het : ∃ l, g.TerminatedAt l := ⟨n - 1, hg⟩
        trans g.convergents (Nat.find het)
        · have hmf : m < Nat.find het :=
            lt_of_not_le (fun hfm => hg' (terminated_stable hfm (Nat.find_spec het)))
          have hg'' : ¬g.TerminatedAt (Nat.find het - 1) :=
            Nat.find_min het (Nat.sub_lt (Nat.zero_lt_of_lt hmf) Nat.zero_lt_one)
          exact le_of_lt (convergents_lt_convergents_of_even hg'' hme hmf)
        · exact ge_of_eq (convergents_stable_of_terminated
            (le_trans (Nat.find_min' het hg) (Nat.sub_le n 1)) (Nat.find_spec het))
    · exact le_of_lt (convergents_lt_convergents_of_even hg hme hmn)

theorem convergents_ge_convergents_of_odd
    {g : GeneralizedContinuedFraction K} [g.IsIntegerContinuedFraction]
    {m n : ℕ} (hme : Odd m) (hmn : m ≤ n) : g.convergents n ≤ g.convergents m := by
  rw [le_iff_eq_or_lt] at hmn; rcases hmn with rfl | hmn
  · rfl
  · by_cases hg : g.TerminatedAt (n - 1)
    · by_cases hg' : g.TerminatedAt m
      · exact le_of_eq (convergents_stable_of_terminated (le_of_lt hmn) hg')
      · have het : ∃ l, g.TerminatedAt l := ⟨n - 1, hg⟩
        trans g.convergents (Nat.find het)
        · exact le_of_eq (convergents_stable_of_terminated
            (le_trans (Nat.find_min' het hg) (Nat.sub_le n 1)) (Nat.find_spec het))
        · have hmf : m < Nat.find het :=
            lt_of_not_le (fun hfm => hg' (terminated_stable hfm (Nat.find_spec het)))
          have hg'' : ¬g.TerminatedAt (Nat.find het - 1) :=
            Nat.find_min het (Nat.sub_lt (Nat.zero_lt_of_lt hmf) Nat.zero_lt_one)
          exact le_of_lt (convergents_gt_convergents_of_odd hg'' hme hmf)
    · exact le_of_lt (convergents_gt_convergents_of_odd hg hme hmn)

theorem eval_bounded_by_inv_fib (f : FCF K) (l : List ℕ+) :
      |f.eval - (f ++ l).eval| ≤ (↑(fib (f.l.length + 1)) : ℚ)⁻¹ * (↑(fib (f.l.length + 2)))⁻¹ := by
  sorry

end FCF

namespace CF

variable {K : Type u} [LinearOrderedField K]

theorem take_add (m n : ℕ) (c : CF K) :
    c.take (m + n) = c.take m ++ (c.s.drop m).take n :=
  sorry

@[simp]
theorem _root_.Seq'.take_ofStream {α : Type u} (n : ℕ) (s : Stream' α) :
    (↑s : Seq' α).take n = s.take n :=
  sorry

theorem cauchySeq_convergents {c : CF ℝ} : CauchySeq c.convergents := by
  by_cases hct : c.s.Terminates
  · lift c to FCF ℝ using hct with f
    have hf : (↑f : CF ℝ).convergents =ᶠ[atTop] (fun _ => f.eval) := by
      rw [EventuallyEq, eventually_atTop]
      use f.l.length
      intro n hn
      simp [convergents, CF.take]
      rw [Seq'.take_stable ?_ hn]
      · congr
        ext1
        simp [eq_comm (a := none)]
      · simp [Seq'.TerminatedAt]
    apply Filter.Tendsto.cauchySeq
    rw [Filter.tendsto_congr' hf, tendsto_const_nhds_iff]
  · apply cauchySeq_of_le_tendsto_0'
      (fun n => (↑(c.take (n + 1)).denominator)⁻¹ * (↑(c.take n).denominator)⁻¹)
    · sorry
    · sorry

/-- Convert integer continued fraction to a real number by considering limit. -/
def toReal (c : CF ℝ) : ℝ :=
  limUnder atTop c.convergents

theorem convergents_tendsTo_toReal (c : CF ℝ) : Tendsto c.convergents atTop (nhds c.toReal) :=
  cauchySeq_convergents.tendsto_limUnder

theorem toReal_eq_of_terminatedAt {n} (hg : g.TerminatedAt n) : g.toReal = g.convergents n :=
  Tendsto.limUnder_eq <| tendsto_atTop_of_eventually_const
    fun (i) (hi : n ≤ i) => convergents_stable_of_terminated hi hg

theorem convergents_le_toReal_of_even {n : ℕ} (hn : Even n) : g.convergents n ≤ g.toReal :=
  ge_of_tendsto convergents_tendsTo_toReal
    (Filter.eventually_atTop.mpr
      ⟨n, fun _ h => convergents_le_convergents_of_even hn h⟩)

theorem convergents_ge_toReal_of_odd {n : ℕ} (hn : Odd n) : g.toReal ≤ g.convergents n :=
  le_of_tendsto convergents_tendsTo_toReal
    (Filter.eventually_atTop.mpr
      ⟨n, fun _ h => convergents_ge_convergents_of_odd hn h⟩)

theorem floor_toReal
    (hg : g.partialDenominators.get? 0 = some 1 → g.partialDenominators.get? 1 ≠ none) :
    (⌊g.toReal⌋ : ℝ) = g.h := by
  obtain ⟨gh, hgh⟩ := ‹g.IsIntegerContinuedFraction›.h_eq_int
  rw [hgh, Int.cast_inj, Int.floor_eq_iff, ← hgh]
  constructor
  · rw [← zeroth_convergent_eq_h]
    exact convergents_le_toReal_of_even even_zero
  · by_cases hgt : g.TerminatedAt 0
    · simp [toReal_eq_of_terminatedAt hgt]
    · rw [terminatedAt_iff_s_none, ← Ne.def, Option.ne_none_iff_exists'] at hgt
      rcases hgt with ⟨gp, hgp⟩
      have hgpa := partNum_eq_s_a hgp; have hgpb := partDenom_eq_s_b hgp
      by_cases hgpb' : gp.b = 1
      · suffices hgl : g.toReal < g.convergents 1
        · convert hgl using 1
          simp [convergents_eq_convergents'_of_isContinuedFraction, convergents',
            convergents'Aux, Stream'.Seq.head, hgp,
            IsSimpleContinuedFraction.partNum_eq_one hgpa, hgpb']
        rw [hgpb'] at hgpb; replace hg := hg hgpb
        rw [Ne.def, ← terminatedAt_iff_partDenom_none] at hg
        by_cases hgt : g.TerminatedAt 2
        · rw [toReal_eq_of_terminatedAt hgt]
          exact convergents_gt_convergents_succ_of_odd odd_one hg
        · apply lt_of_le_of_lt (b := g.convergents 3)
          · apply convergents_ge_toReal_of_odd; decide
          · exact convergents_gt_convergents_add_two_of_odd odd_one hgt
      · apply lt_of_le_of_lt (b := g.convergents 1)
        · exact convergents_ge_toReal_of_odd odd_one
        · simp [convergents_eq_convergents'_of_isContinuedFraction, convergents',
            convergents'Aux, Stream'.Seq.head, hgp,
            IsSimpleContinuedFraction.partNum_eq_one hgpa]
          apply inv_lt_one
          obtain ⟨n, hn⟩ := IsIntegerContinuedFraction.partDenom_eq_int hgpb
          rw_mod_cast [hn, Int.lt_iff_le_and_ne]
          constructor
          · rw [← Int.sub_one_lt_iff, Int.sub_self]
            have hgpb'' := IsContinuedFraction.zero_lt_partDenom hgpb
            rw [hn] at hgpb''; exact_mod_cast hgpb''
          · symm; rw [hn] at hgpb'; exact_mod_cast hgpb'

def IsC0' (c : CF K) : Prop :=
  (none, some 1) ∉ c.s.tail.toStream'.zip c.s.toStream'

theorem of_isC0' [FloorRing K] (v : K) : (of v).IsC0' :=
  sorry

instance : TopologicalSpace ℕ+ := ⊥
instance : DiscreteTopology ℕ+ := ⟨rfl⟩

instance {α : Type u} [TopologicalSpace α] [DiscreteTopology α] : DiscreteTopology (List α) :=
  sorry

@[simps]
def toRealE : { c : CF ℝ // c.IsC0' } ≃ ℝ where
  toFun s := s.1.toReal
  invFun r := ⟨of r, of_isC0' r⟩
  left_inv := sorry
  right_inv := sorry

@[simps ! apply_coe symm_apply_coe]
def toIrrE : { c : CF ℝ // ¬c.s.Terminates } ≃ { x // Irrational x } :=
  ((subtypeSubtypeEquivSubtype sorry).symm).trans (toRealE.subtypeEquiv sorry)

@[simps apply symm_apply_coe]
def toIrrH.equiv : { c : CF ℝ // ¬c.s.Terminates } ≃ ℤ × (ℕ → ℕ+) where
  toFun s := (s.1.1, get (s.1.2.toStream s.2))
  invFun p := ⟨⟨p.1, ↑(⟨p.2⟩ : Stream' ℕ+)⟩, sorry⟩
  left_inv s := sorry
  right_inv p := sorry

theorem _root_.Nat.fib_tendsto_atTop : Tendsto fib atTop atTop :=
  tendsto_atTop_mono' _ (eventually_atTop.mpr ⟨5, λ _n hn => le_fib_self hn⟩) tendsto_id

def toIrrH : ℤ × (ℕ → ℕ+) ≃ₜ { x // Irrational x } where
  toEquiv := toIrrH.equiv.symm.trans toIrrE
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hctt : TendstoUniformly
        (λ (n : ℕ) (p : ℤ × (ℕ → ℕ+)) => convergents (⟨p.1, ↑(⟨p.2⟩ : Stream' ℕ+)⟩ : CF ℝ) n)
        (λ (p : ℤ × (ℕ → ℕ+)) => toReal ⟨p.1, ↑(⟨p.2⟩ : Stream' ℕ+)⟩) atTop
    · simp_rw [tendstoUniformly_iff_tendsto, tendsto_uniformity_iff_dist_tendsto_zero, Real.dist_eq,
        abs_sub_comm]
      refine squeeze_zero
        (g := λ (p : ℕ × (ℤ × (ℕ → ℕ+))) => (↑(fib (p.1 + 1)) : ℝ)⁻¹ * (↑(fib (p.1 + 2)))⁻¹)
        (λ _ => by positivity) ?hb ?ht
      case ht =>
        suffices ht : Tendsto (λ n => (↑(fib (n + 1)) : ℝ)⁻¹ * (↑(fib (n + 2)))⁻¹) atTop (𝓝 0)
        · exact Tendsto.comp ht tendsto_fst
        have ht₁ := (tendsto_add_atTop_iff_nat 1).mpr fib_tendsto_atTop
        replace ht₁ := (tendsto_nat_cast_atTop_atTop (R := ℝ)).comp ht₁
        replace ht₁ := ht₁.inv_tendsto_atTop
        have ht₂ := (tendsto_add_atTop_iff_nat 2).mpr fib_tendsto_atTop
        replace ht₂ := (tendsto_nat_cast_atTop_atTop (R := ℝ)).comp ht₂
        replace ht₂ := ht₂.inv_tendsto_atTop
        convert ht₁.mul ht₂; simp
      case hb =>
        rintro ⟨n, h, f⟩
        let c : CF ℝ := ⟨h, ↑(⟨f⟩ : Stream' ℕ+)⟩
        have hb := λ m => eval_bounded_by_inv_fib (c.take n) ((c.s.drop n).take m)
        simp_rw (config := { proj := false, zeta := false })
          [← take_add, ← Rat.cast_le (K := ℝ)] at hb
        simp at hb; simp_rw [← take_ofStream] at hb
        have ht := (((tendsto_add_atTop_iff_nat n).mpr (convergents_tendsTo_toReal c)).const_sub
          (convergents c n)).abs
        conv at ht => enter [1, m]; rw [add_comm]
        exact le_of_tendsto' ht hb
    have hcc : ∀ n, Continuous
        (λ (p : ℤ × (ℕ → ℕ+)) => convergents (⟨p.1, ↑(⟨p.2⟩ : Stream' ℕ+)⟩ : CF ℝ) n)
    · intro n
      have hcc₁ : Continuous
          (λ (f : ℕ → ℕ+) => (↑(⟨f⟩ : Stream' ℕ+) : Seq' ℕ+).take n)
      · refine (isTopologicalBasis_singletons _).continuous _ ?_
        rintro _ ⟨l, rfl⟩
        refine (PiNat.isTopologicalBasis_cylinders _).isOpen_iff.mpr ?_
        rintro f rfl
        refine ⟨_, ⟨f, n, rfl⟩, ?_⟩
        simp [PiNat.cylinder, subset_def]
        intro g hg
        apply List.ext_get
        · simp
        · intro m hm₁ hm₂
          simp only [get_take]; simp only [length_take] at hm₁; exact hg m hm₁
      have hcc₂ : Continuous (λ p : ℤ × List ℕ+ => (↑(⟨p.1, p.2⟩ : FCF ℝ).eval : ℝ))
      · exact continuous_of_discreteTopology
      exact hcc₂.comp (continuous_id.prod_map hcc₁)
    exact hctt.continuous (eventually_of_forall hcc)
  continuous_invFun := by
    apply Continuous.prod_mk
    · change Continuous (restrict { r | Irrational r } Int.floor)
      apply ContinuousOn.restrict; apply ContinuousAt.continuousOn
      intro r hr
      refine ((continuousOn_congr (floor_eq_on_Ico ⌊r⌋)).mpr continuousOn_const).continuousAt ?_
      exact Ico_mem_nhds (lt_of_le_of_ne (Int.floor_le r) (hr.ne_int _).symm)
        (Int.lt_floor_add_one r)
    · simp
      sorry

end CF

end
