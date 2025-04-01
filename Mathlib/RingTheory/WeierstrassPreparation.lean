/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/

import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Trunc
/-!

# Weierstrass Preparation Theorem for Formal Power Series

In this file we proved the Weierstrass prepation theorem for formal power series.

# Main results

* `CompleteLocalRing.weierstrass_preparation` : The Weierstrass preparation theorem for complete
  local ring, stating that every formal power series with some coefficient not in the unique
  maximal ideal can be uniquely written as the product of a distinguish polynomial and an unit.

-/

open scoped Polynomial
open PowerSeries Ideal Quotient

variable {R : Type*} [CommRing R] {m : Ideal R}

open IsDistinguishedAt

lemma preparation_lift_triv {n : ℕ} (neq0 : n = 0) [hmax : m.IsMaximal] (f : (R ⧸ m ^ (n + 1))⟦X⟧)
    (ntriv : f.map (Ideal.Quotient.mk (m.map (Ideal.Quotient.mk (m ^ (n + 1))))) ≠ 0) :
    ∃! (h : (R ⧸ m ^ (n + 1))⟦X⟧ˣ), ∃ (g : Polynomial (R ⧸ m ^ (n + 1))),
    g.IsDistinguishedAt (m.map (Ideal.Quotient.mk (m ^ (n + 1)))) ∧  f = g * h := by
  have ne0 : f ≠ 0 := by
    by_contra h
    simp [h] at ntriv
  have eq_bot' : m.map (Ideal.Quotient.mk (m ^ (n + 1))) = ⊥ := map_mk_eq_bot_of_le (by simp [neq0])
  let k := (f.map (Ideal.Quotient.mk (m.map (Ideal.Quotient.mk (m ^ (n + 1)))))).order
  let k' := k.lift (order_finite_iff_ne_zero.mpr ntriv)
  have order_eq : f.order = k := by
    rw [Eq.comm, PowerSeries.order_eq]
    refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩
    · have : i = f.order.lift (order_finite_iff_ne_zero.mpr ne0) := by simp [← hi]
      simpa [eq_zero_iff_mem, eq_bot', this] using coeff_order (order_finite_iff_ne_zero.mpr ne0)
    · simpa [eq_zero_iff_mem, eq_bot'] using coeff_of_lt_order i hi
  let max' : (m ^ (n + 1)).IsMaximal := by simpa only [neq0, zero_add, pow_one] using hmax
  let hField : Field (R ⧸ m ^ (n + 1)) := Ideal.Quotient.field (m ^ (n + 1))
  have muleq : f = ((Polynomial.X (R := (R ⧸ m ^ (n + 1))) ^ k') : (R ⧸ m ^ (n + 1))[X]) *
    f.Unit_of_divided_by_X_pow_order := by
    rw [Unit_of_divided_by_X_pow_order_nonzero ne0]
    convert (self_eq_X_pow_order_mul_divided_by_X_pow_order ne0).symm
    simp [order_eq, k']
  use Unit_of_divided_by_X_pow_order f
  constructor
  · use Polynomial.X ^ k'
    refine ⟨⟨⟨?_⟩, Polynomial.monic_X_pow k'⟩, muleq⟩
    simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one, Polynomial.coeff_X_pow]
    intro i hi
    simp [Nat.ne_of_lt hi]
  · rintro h' ⟨g', distinguish, eq⟩
    have : g' = Polynomial.X ^ k' := by
      ext i
      simp only [Polynomial.coeff_X_pow]
      have : constantCoeff _ h' ∉ m.map (Ideal.Quotient.mk (m ^ (n + 1))) := by
        simpa only [eq_bot', mem_bot] using (h'.1.isUnit_constantCoeff h'.isUnit).ne_zero
      have deg_eq : g'.degree = k := degree_eq_order_map f h' g' distinguish this eq
      have deg_eq' : g'.natDegree = k' := by
        simp [← deg_eq, Polynomial.degree_eq_natDegree distinguish.monic.ne_zero,
          ENat.lift_coe _, k']
      by_cases H' : i = k'
      · rw [if_pos H', H', ← deg_eq', distinguish.monic.coeff_natDegree]
      · rcases Nat.lt_or_gt_of_ne H' with gt|lt
        · rw [if_neg (Nat.ne_of_lt gt), ← Ideal.mem_bot, ← eq_bot']
          exact distinguish.mem (deg_eq' ▸ gt)
        · rw [if_neg (Nat.ne_of_gt lt), g'.coeff_eq_zero_of_natDegree_lt (deg_eq' ▸ lt)]
    rw [muleq, this] at eq
    exact Units.eq_iff.mp ((mul_right_inj' (by simp)).mp eq.symm)

lemma map_order_eq {n : ℕ} (npos : n > 0) (f : PowerSeries (R ⧸ m ^ (n + 1))) :
    (f.map (Ideal.Quotient.mk (m.map (Ideal.Quotient.mk (m ^ (n + 1)))))).order =
    ((f.map (factorPow m n.le_succ)).map
      (Ideal.Quotient.mk (m.map (Ideal.Quotient.mk (m ^ n))))).order := by
  rw [Eq.comm, PowerSeries.order_eq]
  refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩
  · have : (f.map (Ideal.Quotient.mk (m.map (Ideal.Quotient.mk (m ^ (n + 1)))))).order < ⊤ := by
      simp [← hi]
    by_contra h
    absurd PowerSeries.coeff_order this
    simp only [coeff_map, eq_zero_iff_mem, ← Ideal.map_mk_comap_factorPow m npos n.le_succ,
      Nat.succ_eq_add_one, mem_comap]
    simp [← eq_zero_iff_mem, ← coeff_map, ← hi, h]
  · have := PowerSeries.coeff_of_lt_order i hi
    simp only [coeff_map, eq_zero_iff_mem, ← Ideal.map_mk_comap_factorPow m npos n.le_succ,
      Nat.succ_eq_add_one, mem_comap] at this
    exact eq_zero_iff_mem.mpr this

lemma ne_top {n : ℕ} (npos : n > 0) (mne : m ≠ ⊤): m.map (Ideal.Quotient.mk (m ^ n)) ≠ ⊤ := by
  apply (Ideal.ne_top_iff_one _).mpr
  by_contra mem
  rcases Ideal.mem_image_of_mem_map_of_surjective (Ideal.Quotient.mk (m ^ n))
    Ideal.Quotient.mk_surjective mem with ⟨r, rmem, hr⟩
  have : r - 1 ∈ m ^ n := by simp only [← mk_eq_mk_iff_sub_mem r 1, hr, map_one]
  absurd (Ideal.ne_top_iff_one m).mp mne
  rw [← (sub_sub_self r 1), m.sub_mem_iff_left (pow_le_self (Nat.ne_zero_of_lt npos) this)]
  exact rmem

lemma preparation_lift {n : ℕ} (npos : n > 0) [hmax : m.IsMaximal] (f : PowerSeries (R ⧸ m ^ n))
    (ntriv : f.map (Ideal.Quotient.mk (m.map (Ideal.Quotient.mk (m ^ n)))) ≠ 0) :
    ∃! (h : (R ⧸ m ^ n)⟦X⟧ˣ), ∃ (g : (R ⧸ m ^ n)[X]),
    g.IsDistinguishedAt (m.map (Ideal.Quotient.mk (m ^ n))) ∧ f = g * h := by
    let nontriv_all {k : ℕ} (pos : k > 0): Nontrivial (R ⧸ m ^ k) :=
      Submodule.Quotient.nontrivial_of_lt_top (m ^ k) (lt_of_le_of_lt
      (Ideal.pow_le_self (Nat.ne_zero_of_lt pos)) (Ne.lt_top (Ideal.IsMaximal.ne_top hmax)))
    induction' n with n ih
    · exact ((Nat.not_lt_zero 0) npos).elim
    · by_cases neq0 : n = 0
      · exact preparation_lift_triv neq0 f ntriv
      · have : ¬ (f.map (factorPow m n.le_succ)).map
          (Ideal.Quotient.mk (m.map (Ideal.Quotient.mk (m ^ n)))) = 0 := by
          rw [← order_eq_top.not, ← map_order_eq (Nat.zero_lt_of_ne_zero neq0), order_eq_top.not]
          exact ntriv
        rcases ih (Nat.zero_lt_of_ne_zero neq0) (map (factorPow m n.le_succ) f) this with
          ⟨h, ⟨g, distinguish, eq⟩, uniq⟩
        rcases map_surjective _ (factor_surjective (pow_le_pow_right n.le_succ)) h.val with
          ⟨h'', hh''⟩
        have : IsUnit h'' := by
          apply isUnit_iff_constantCoeff.mpr
          have := isUnit_iff_constantCoeff.mp h.isUnit
          rw [← hh'', ← coeff_zero_eq_constantCoeff_apply] at this
          simp only [coeff_map, coeff_zero_eq_constantCoeff] at this
          exact factorPowSucc.isUnit_of_isUnit_image (Nat.zero_lt_of_ne_zero neq0) this
        let h' : (R ⧸ m ^ (n + 1))⟦X⟧ˣ := IsUnit.unit this
        have val : h'.1 = h'' := rfl
        let nontriv : Nontrivial (R ⧸ m ^ n) := nontriv_all (Nat.zero_lt_of_ne_zero neq0)
        let nontriv' : Nontrivial (R ⧸ m ^ (n + 1)) := nontriv_all npos
        rcases Polynomial.lifts_and_degree_eq_and_monic (g.map_surjective _
          (factor_surjective (pow_le_pow_right n.le_succ))) distinguish.monic with
          ⟨g', hg', deg, mon⟩
        let k := (f.map (Ideal.Quotient.mk (m.map (Ideal.Quotient.mk (m ^ (n + 1)))))).order
        let k' := k.lift (order_finite_iff_ne_zero.mpr ntriv)
        have : (f - g' * h').map (factorPow m n.le_succ) = 0 := by
          simp [← Polynomial.polynomial_map_coe, hg', val, hh'', eq]
        set c : (R ⧸ m ^ (n + 1))⟦X⟧ := h'.inv * (f - g' * h')
        have map0 : c.map (factorPow m n.le_succ) = 0 := by rw [_root_.map_mul, this, mul_zero]
        let α := trunc k' c
        let γ := (mk fun i ↦ coeff (R ⧸ m ^ (n + 1)) (i + k') c)
        have hu1 : IsUnit (1 + γ) := by
          apply isUnit_iff_constantCoeff.mpr
          apply factorPowSucc.isUnit_of_isUnit_image (Nat.zero_lt_of_ne_zero neq0)
          simp [γ, ← coeff_map, map0]
        have hu2 : IsUnit (h'.1 * (1 + γ)) := h'.isUnit.mul hu1
        have heq : (α : (R ⧸ m ^ (n + 1))⟦X⟧) + (X ^ k') * γ = c := by
          ext k
          simp only [coeff_trunc, ne_eq, Set.coe_setOf, Set.mem_setOf_eq, map_add,
            Polynomial.coeff_coe, Polynomial.coeff_ofFinsupp, Finsupp.coe_mk, α,
            coeff_X_pow_mul', coeff_mk, γ]
          by_cases lt : k < k'
          · rw [if_pos lt, if_neg (Nat.not_le_of_lt lt), add_zero]
          · rw [if_neg lt, if_pos (Nat.le_of_not_lt lt), zero_add,
              Nat.sub_add_cancel (Nat.le_of_not_lt lt)]
        have : (constantCoeff (R ⧸ m ^ n)) h ∉ m.map (Ideal.Quotient.mk (m ^ n)) := by
          by_contra mem
          absurd (Ideal.eq_top_of_isUnit_mem _ mem (isUnit_iff_constantCoeff.mp h.isUnit))
          exact ne_top (Nat.zero_lt_of_ne_zero neq0) Ideal.IsPrime.ne_top'
        have deg' : g.degree = k := by
          rw [degree_eq_order_map (f.map (factorPow m n.le_succ)) h g distinguish this eq,
            ← map_order_eq (Nat.zero_lt_of_ne_zero neq0)]
        have deg' : g.degree = k' := by rw [deg', ENat.coe_lift]
        have deg'' : g'.degree = k' := by rw [deg, deg']
        have deg''' : (g' + α).degree = k' := by
          rw [Polynomial.degree_add_eq_left_of_degree_lt (deg'' ▸ (degree_trunc_lt c k')), deg'']
        have mon' : (g' + α).Monic := mon.add_of_left (deg'' ▸ (degree_trunc_lt c k'))
        have αcoeff (l : ℕ) : (factorPow m n.le_succ) (α.coeff l) = 0 := by
          simp only [coeff_trunc, Set.coe_setOf, Set.mem_setOf_eq,
            Polynomial.coeff_ofFinsupp, Finsupp.coe_mk, α]
          by_cases lt : l < k'
          · rw [if_pos lt, ← coeff_map, map0, map_zero]
          · rw [if_neg lt, map_zero]
        have hgα {i : ℕ} (hi : i < (g' + α).natDegree) :
          (g' + α).coeff i ∈ m.map (Ideal.Quotient.mk (m ^ (n + 1))) := by
          simp only [← map_mk_comap_factorPow m (Nat.zero_lt_of_ne_zero neq0) n.le_succ,
            Polynomial.coeff_add, mem_comap, map_add, αcoeff, add_zero]
          rw [← (Polynomial.coeff_map (factorPow m n.le_succ) i), hg']
          apply distinguish.mem
          rw [← Polynomial.coe_lt_degree, deg', ← deg''', Polynomial.coe_lt_degree]
          exact hi
        have hgcoeff (l : ℕ): (g.coeff l - if l = k' then 1 else 0) ∈
          m.map (Ideal.Quotient.mk (m ^ n)) := by
          by_cases leq : l = k'
          · simp [leq, ← Polynomial.natDegree_eq_of_degree_eq_some deg', distinguish.monic]
          · simp only [leq, ↓reduceIte, sub_zero]
            rcases lt_or_gt_of_ne leq with lt|gt
            · apply distinguish.mem
              simpa [← Polynomial.coe_lt_degree, deg'] using lt
            · convert Submodule.zero_mem _
              apply Polynomial.coeff_eq_zero_of_degree_lt
              simpa [← Polynomial.coe_lt_degree, deg'] using gt
        have hcoeff (l : ℕ): ((((g' + α) : (R ⧸ m ^ (n + 1))⟦X⟧) - X ^ k').coeff _ l) ∈
          m.map (Ideal.Quotient.mk (m ^ (n + 1))) := by
          simpa [← map_mk_comap_factorPow m (Nat.zero_lt_of_ne_zero neq0) n.le_succ, coeff_X_pow,
            αcoeff, ← (Polynomial.coeff_map (factorPow m n.le_succ) l), hg'] using hgcoeff l
        have mul0 : (((g' + α)  : (R ⧸ m ^ (n + 1))⟦X⟧) - (X ^ k')) * γ = 0 := by
          ext
          simp only [coeff_mul, map_zero]
          apply Finset.sum_eq_zero fun x _ => ?_
          rcases mem_image_of_mem_map_of_surjective _ mk_surjective (hcoeff x.1) with ⟨r, hr, eqr⟩
          have : γ.coeff _ x.2  ∈ (m ^ n).map (Ideal.Quotient.mk (m ^ (n + 1))) := by
            simp [← factor_ker (pow_le_pow_right n.le_succ), RingHom.mem_ker, γ, ← coeff_map, map0]
          rcases mem_image_of_mem_map_of_surjective _ mk_surjective this with ⟨s, hs, eqs⟩
          rw [← eqr, ← eqs, ← _root_.map_mul, Ideal.Quotient.eq_zero_iff_mem, add_comm,
            pow_add, pow_one]
          exact Submodule.mul_mem_mul hr hs
        have muleq : (g' + α) * (h'.1 * (1 + γ)) = f := by
          calc
          _ = (g' : (R ⧸ m ^ (n + 1))⟦X⟧) * h'.1 + h'.1 * ((α : (R ⧸ m ^ (n + 1))⟦X⟧) +
              X ^ k' * γ) + (((g' + α)  : (R ⧸ m ^ (n + 1))⟦X⟧) - X ^ k') * γ * h'.1 := by ring
          _ = f := by simp [mul0, heq, c]
        use hu2.unit
        refine ⟨⟨g' + α, ⟨⟨hgα⟩, mon'⟩, by simp [muleq]⟩, ?_⟩
        rintro H ⟨G, distinguishG, eq'⟩
        have : (constantCoeff (R ⧸ m ^ (n + 1))) H ∉ m.map (Ideal.Quotient.mk (m ^ (n + 1))) := by
          by_contra mem
          absurd (Ideal.eq_top_of_isUnit_mem _ mem (isUnit_iff_constantCoeff.mp H.isUnit))
          exact ne_top n.zero_lt_succ Ideal.IsPrime.ne_top'
        have degG : G.degree = k := degree_eq_order_map f H G distinguishG this eq'
        have degG' : G.degree = k' := by rw [degG, ENat.coe_lift]
        have mapHu: IsUnit (H.1.map (factorPow m n.le_succ)) := RingHom.isUnit_map _ H.isUnit
        have mapeq : mapHu.unit = h := by
          apply uniq
          use G.map (factorPow m n.le_succ)
          constructor
          · refine ⟨⟨?_⟩, distinguishG.monic.map _⟩
            intro i hi
            simp only [Polynomial.coeff_map, ← mem_comap]
            rw [map_mk_comap_factorPow m (Nat.zero_lt_of_ne_zero neq0) n.le_succ]
            apply distinguishG.mem
            have : (G.map (factorPow m n.le_succ)).natDegree = G.natDegree := by
              simp [Polynomial.natDegree_map_eq_iff, distinguishG.monic]
            simpa [← this] using hi
          · simp [eq', Polynomial.polynomial_map_coe]
        have mapeq' : G.map (factorPow m n.le_succ) = g := by
          apply Polynomial.coe_inj.mp
          calc
          _= G.map (factorPow m n.le_succ) * mapHu.unit.1 * mapHu.unit.inv := by
            rw [mul_assoc, mapHu.unit.val_inv, mul_one]
          _= f.map (factorPow m n.le_succ) * mapHu.unit.inv := by simp [eq']
          _= _ := by rw [congrArg Units.inv mapeq, eq, mul_assoc, h.val_inv, mul_one]
        have :  H.1.map (factorPow m n.le_succ) = h.1 := by simp [← mapeq]
        have map0' : (H.1 - h'.1).map (factorPow m n.le_succ) = 0 := by simp [val, this, hh'']
        have hcoeff' (l : ℕ): ((G  : (R ⧸ m ^ (n + 1))⟦X⟧) - X ^ k').coeff _ l ∈
          m.map (Ideal.Quotient.mk (m ^ (n + 1))) := by
          simpa [← map_mk_comap_factorPow m (Nat.zero_lt_of_ne_zero neq0) n.le_succ, coeff_X_pow,
            ← (Polynomial.coeff_map (factorPow m n.le_succ) l), mapeq'] using hgcoeff l
        have mul0' : ((G  : (R ⧸ m ^ (n + 1))⟦X⟧) - (X ^ k')) * (H.1 - h'.1) = 0 := by
          ext
          simp only [coeff_mul, map_zero]
          apply Finset.sum_eq_zero fun x _ => ?_
          rcases Ideal.mem_image_of_mem_map_of_surjective (Ideal.Quotient.mk (m ^ (n + 1)))
            Ideal.Quotient.mk_surjective (hcoeff' x.1) with ⟨r, hr, eqr⟩
          have : (H.1 - h'.1).coeff _ x.2  ∈ (m ^ n).map (Ideal.Quotient.mk (m ^ (n + 1))) := by
            simp only [← factor_ker (pow_le_pow_right n.le_succ), RingHom.mem_ker, ← coeff_map,
              map0', map_zero]
          rcases Ideal.mem_image_of_mem_map_of_surjective (Ideal.Quotient.mk (m ^ (n + 1)))
            Ideal.Quotient.mk_surjective this with ⟨s, hs, eqs⟩
          rw [← eqr, ← eqs, ← _root_.map_mul, eq_zero_iff_mem, add_comm, pow_add, pow_one]
          exact Submodule.mul_mem_mul hr hs
        have eq'' : f = (g'  : (R ⧸ m ^ (n + 1))⟦X⟧) * h'.1 + (X ^ k') * (H.1 - h'.1) +
          ((G - g') : (R ⧸ m ^ (n + 1))⟦X⟧) * h'.1 := by
          calc
          _= G * H.1 := by rw [eq']
          _= (g' : (R ⧸ m ^ (n + 1))⟦X⟧) * h'.1 +
             ((G : (R ⧸ m ^ (n + 1))⟦X⟧) - (X ^ k')) * (H.1 - h'.1) + (X ^ k') * (H.1 - h'.1) +
              ((G - g') : (R ⧸ m ^ (n + 1))⟦X⟧) * h'.1 := by ring
          _= _ := by simp [mul0']
        have c_decomp : c = X ^ k' * ((H.1 - h'.1) * h'.inv) +
          ((G - g') : (R ⧸ m ^ (n + 1))⟦X⟧) := by
          calc
          _= h'.inv * (f - ↑g' * h'.1) := rfl
          _= h'.inv * ((g'  : (R ⧸ m ^ (n + 1))⟦X⟧) * h'.1 + (X ^ k') * (H.1 - h'.1) +
            ((G - g') : (R ⧸ m ^ (n + 1))⟦X⟧) * h'.1 - (g' : (R ⧸ m ^ (n + 1))⟦X⟧) * h'.1) := by
              simpa using  eq''
          _= X ^ k' * ((H.1 - h'.1) * h'.inv) +
            ((G - g') : (R ⧸ m ^ (n + 1))⟦X⟧) * h'.1 * h'.inv := by ring
          _= _ := by rw [mul_assoc, h'.val_inv, mul_one]
        have coeff_ge {l : ℕ} (lge : l ≥ k'): G.coeff l - g'.coeff l = 0 := by
          have h1 := Polynomial.natDegree_eq_of_degree_eq_some degG'
          have h2 := Polynomial.natDegree_eq_of_degree_eq_some deg''
          by_cases leq : l = k'
          · simp only [leq]
            nth_rw 1 [← h1, ← h2]
            simp [distinguishG.monic, mon]
          · have lgt : l > k' := Nat.lt_of_le_of_ne lge fun a ↦ leq a.symm
            simp [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_eq_of_lt h1 lgt),
              Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_eq_of_lt h2 lgt)]
        have eqγ : ((H.1 - h'.1) * h'.inv) = γ := by
          ext i
          rw [coeff_mk, c_decomp, map_add, coeff_X_pow_mul]
          simp [coeff_ge (Nat.le_add_left k' i)]
        simp [← Units.eq_iff, mul_add, ← eqγ, mul_comm (H.1 - h'.1) _, ← mul_assoc, h'.val_inv]

lemma map_order_eq' {n : ℕ} (npos : n > 0) {f : PowerSeries R} :
    ((f.map (Ideal.Quotient.mk (m ^ n))).map
      (Ideal.Quotient.mk (m.map (Ideal.Quotient.mk (m ^ n))))).order =
      (f.map (Ideal.Quotient.mk m)).order:= by
  rw [Eq.comm, PowerSeries.order_eq]
  refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩
  · have : ((f.map (Ideal.Quotient.mk (m ^ n))).map
      (Ideal.Quotient.mk (m.map (Ideal.Quotient.mk (m ^ n))))).order < ⊤ := by simp [← hi]
    by_contra h
    absurd PowerSeries.coeff_order this
    simp only [coeff_map, eq_zero_iff_mem] at h
    simpa [eq_zero_iff_mem, pow_le_self (Nat.ne_zero_of_lt npos), ← hi] using h
  · have := PowerSeries.coeff_of_lt_order i hi
    simp only [coeff_map, eq_zero_iff_mem, mem_quotient_iff_mem_sup,
      pow_le_self (Nat.ne_zero_of_lt npos), sup_of_le_left] at this
    simpa [eq_zero_iff_mem] using this

theorem CompleteLocalRing.weierstrass_preparation [hmax : m.IsMaximal] [comp : IsAdicComplete m R]
    (f : PowerSeries R) (ntriv : f.map (Ideal.Quotient.mk m) ≠ 0) :
    ∃! (h : R⟦X⟧ˣ), ∃ (g : R[X]), g.IsDistinguishedAt m ∧ f = g * h := by
  let R_ntriv : Nontrivial R := nontrivial_of_ne 0 1 (ne_of_mem_of_not_mem (Submodule.zero_mem m)
    ((Ideal.ne_top_iff_one m).mp (Ideal.IsMaximal.ne_top hmax)))
  let R_ntriv' {k : ℕ} (kpos : k > 0): Nontrivial (R ⧸ m ^ k) :=
    Submodule.Quotient.nontrivial_of_lt_top (m ^ k) (lt_of_le_of_lt
      (Ideal.pow_le_self (Nat.ne_zero_of_lt kpos)) hmax.ne_top.lt_top)
  have (n : ℕ+) : ((f.map (Ideal.Quotient.mk (m ^ n.1))).map
      (Ideal.Quotient.mk (m.map (Ideal.Quotient.mk (m ^ n.1))))) ≠ 0 := by
    rw [← order_finite_iff_ne_zero, map_order_eq' n.2, order_finite_iff_ne_zero]
    exact ntriv
  choose h_series' hh series_uniq using fun (n : ℕ+) ↦
    preparation_lift n.2 (f.map (Ideal.Quotient.mk (m ^ n.1))) (this n)
  dsimp at hh series_uniq
  choose g_series' series_distinguish series_eq using hh
  let k := (f.map (Ideal.Quotient.mk m)).order
  let k' := k.lift (order_finite_iff_ne_zero.mpr ntriv)
  have series_deg (n : ℕ+) : (g_series' n).degree = k := by
    let _ : Nontrivial (R ⧸ m ^ n.1) := R_ntriv' n.2
    have : (constantCoeff (R ⧸ m ^ n.1)) (h_series' n) ∉ m.map (Ideal.Quotient.mk (m ^ n.1)) := by
      by_contra mem
      absurd (Ideal.eq_top_of_isUnit_mem _ mem (isUnit_iff_constantCoeff.mp (h_series' n).isUnit))
      exact ne_top n.2 Ideal.IsPrime.ne_top'
    rw [degree_eq_order_map _ _ _ (series_distinguish n) this (series_eq n), map_order_eq' n.2]
  have series_deg' (n : ℕ+) : (g_series' n).degree = k' := by rw [series_deg, ENat.coe_lift]
  have factorPow_h_IsUnit {a b : ℕ} (bpos : b > 0) (le : a ≤ b) :
    IsUnit ((h_series' ⟨b, bpos⟩).1.map (factorPow m le)) :=
    RingHom.isUnit_map _ (h_series' ⟨b, bpos⟩).isUnit
  have h_series_factorPoweq' {a b : ℕ} (apos : a > 0) (bpos : b > 0) (le : a ≤ b) :
    (factorPow_h_IsUnit bpos le).unit = (h_series' ⟨a, apos⟩) := by
    apply series_uniq ⟨a, apos⟩ (factorPow_h_IsUnit bpos le).unit
    simp only [IsUnit.unit_spec]
    use (g_series' ⟨b, bpos⟩).map (factorPow m le)
    constructor
    · refine ⟨⟨fun {i} hi ↦ ?_⟩, (series_distinguish ⟨b, bpos⟩).monic.map (factorPow m le)⟩
      let _ : Nontrivial (R ⧸ m ^ a) := R_ntriv' apos
      rw [(series_distinguish ⟨b, bpos⟩).monic.natDegree_map] at hi
      simpa [← mem_comap,  Ideal.map_mk_comap_factorPow m apos le] using
        (series_distinguish ⟨b, bpos⟩).mem hi
    · rw [Polynomial.polynomial_map_coe, ← _root_.map_mul,← series_eq ⟨b, bpos⟩]
      ext
      simp
  have h_series_factorPoweq {a b : ℕ} (apos : a > 0) (bpos : b > 0) (le : a ≤ b) :
    (h_series' ⟨b, bpos⟩).1.map (factorPow m le) = (h_series' ⟨a, apos⟩) :=
    Units.eq_iff.mpr <| h_series_factorPoweq' apos bpos le
  have g_series_factorPoweq {a b : ℕ} (apos : a > 0) (bpos : b > 0) (le : a ≤ b) :
    (g_series' ⟨a, apos⟩) = (g_series' ⟨b, bpos⟩).map (factorPow m le)  := by
    apply Polynomial.coe_inj.mp
    calc
      _= f.map (Ideal.Quotient.mk (m ^ a)) * (h_series' ⟨a, apos⟩).inv := by
        simp only [series_eq ⟨a, apos⟩, Units.inv_eq_val_inv, Units.mul_inv_cancel_right]
      _= f.map (Ideal.Quotient.mk (m ^ a)) * (factorPow_h_IsUnit bpos le).unit.inv := by
        rw [h_series_factorPoweq' apos bpos le]
      _= ((g_series' ⟨b, bpos⟩).map (factorPow m le)) *
         (factorPow_h_IsUnit bpos le).unit * (factorPow_h_IsUnit bpos le).unit.inv := by
        simp only [IsUnit.unit_spec, Units.inv_eq_val_inv, Units.mul_left_inj,
          Polynomial.polynomial_map_coe, ← _root_.map_mul, ← series_eq ⟨b, bpos⟩]
        ext
        simp
      _= _ := by simp only [Units.inv_eq_val_inv, Units.mul_inv_cancel_right]
  let h_series : ℕ → R⟦X⟧ := fun k ↦ if h : k = 0 then 1 else
    Classical.choose <| map_surjective (Ideal.Quotient.mk (m ^ k))
    Ideal.Quotient.mk_surjective (h_series' ⟨k, Nat.zero_lt_of_ne_zero h⟩)
  have h_series_spec {k : ℕ} (kpos : k > 0) :
    (h_series k).map (Ideal.Quotient.mk (m ^ k)) = (h_series' ⟨k, kpos⟩) := by
    simpa only [Nat.ne_zero_of_lt kpos, ↓reduceDIte, h_series]
      using Classical.choose_spec <| map_surjective (Ideal.Quotient.mk (m ^ k))
        Ideal.Quotient.mk_surjective (h_series' ⟨k, kpos⟩)
  let g_series : ℕ → R[X] := fun k ↦ if h : k = 0 then 0 else
    let _ := R_ntriv' (Nat.zero_lt_of_ne_zero h)
    Classical.choose <| Polynomial.lifts_and_degree_eq_and_monic (Polynomial.map_surjective _
      Ideal.Quotient.mk_surjective _) (series_distinguish ⟨k, Nat.zero_lt_of_ne_zero h⟩).monic
  have g_series_spec {k : ℕ} (kpos : k > 0) : (g_series k).map (Ideal.Quotient.mk (m ^ k)) =
    (g_series' ⟨k, kpos⟩) ∧ (g_series k).degree = (g_series' ⟨k, kpos⟩).degree ∧
    (g_series k).Monic := by
    let _ := R_ntriv' kpos
    simpa [Nat.ne_zero_of_lt kpos, g_series]
      using Classical.choose_spec <| Polynomial.lifts_and_degree_eq_and_monic
      (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective _)
      (series_distinguish ⟨k, kpos⟩).monic
  have h_series_mod {a b : ℕ} (apos : a > 0) (le : a ≤ b) : (h_series a).map
    (Ideal.Quotient.mk (m ^ a))  = (h_series b).map (Ideal.Quotient.mk (m ^ a)) := by
    have bpos : b > 0 := Nat.lt_of_lt_of_le apos le
    ext t
    simp only [coeff_map]
    nth_rw 2 [← factor_mk (pow_le_pow_right le)]
    simp [← coeff_map, h_series_spec apos, h_series_spec bpos, h_series_factorPoweq apos bpos le]
  have g_series_mod {a b : ℕ} (apos : a > 0) (le : a ≤ b) : (g_series a).map
    (Ideal.Quotient.mk (m ^ a)) = (g_series b).map (Ideal.Quotient.mk (m ^ a)) := by
    have bpos : b > 0 := Nat.lt_of_lt_of_le apos le
    ext t
    simp only [Polynomial.coeff_map]
    nth_rw 2 [← factor_mk (pow_le_pow_right le)]
    simp [← Polynomial.coeff_map, (g_series_spec apos).1, (g_series_spec bpos).1,
      g_series_factorPoweq apos bpos le]
  have h_coeff_series_mod (i : ℕ): ∀ {a b : ℕ}, a ≤ b → (h_series a).coeff R i  ≡
    (h_series b).coeff R i [SMOD m ^ a • (⊤ : Submodule R R)] := by
    intro a b le
    by_cases apos : a > 0
    · simp [SModEq.sub_mem, ← eq_zero_iff_mem, ← coeff_map, h_series_mod apos le]
    · simp [Nat.eq_zero_of_not_pos apos]
  let h : R⟦X⟧ := mk fun i ↦ Classical.choose
    (IsAdicComplete.toIsPrecomplete.prec (h_coeff_series_mod i))
  have h_spec (i : ℕ) : ∀ n : ℕ, (h_series n).coeff R i ≡ h.coeff R i
    [SMOD m ^ n • (⊤ : Submodule R R)]:= by
    simpa only [coeff_mk, h] using Classical.choose_spec
      (IsAdicComplete.toIsPrecomplete.prec (h_coeff_series_mod i))
  have h_spec' {n : ℕ} (npos : n > 0) : h.map (Ideal.Quotient.mk (m ^ n)) =
    h_series' ⟨n, npos⟩ := by
    rw [← h_series_spec npos]
    ext i
    simpa [mk_eq_mk_iff_sub_mem, ← SModEq.sub_mem] using (h_spec i n).symm
  have hu : IsUnit h := by
    rw [isUnit_iff_constantCoeff, isUnit_iff_nmem_of_isAdicComplete_maximal m]
    by_contra mem
    rw [← pow_one m, ← Ideal.Quotient.eq_zero_iff_mem, ← coeff_zero_eq_constantCoeff_apply,
      ← coeff_map, h_spec' Nat.one_pos, coeff_zero_eq_constantCoeff_apply] at mem
    absurd isUnit_iff_constantCoeff.mp (h_series' ⟨1, Nat.one_pos⟩).isUnit
    let _ : Nontrivial (R ⧸ m ^ 1) := R_ntriv' Nat.one_pos
    dsimp at mem
    simp [mem]
  have g_coeff_series_mod (i : ℕ) : ∀ {a b : ℕ}, a ≤ b → (g_series a).coeff i ≡
    (g_series b).coeff i [SMOD m ^ a • (⊤ : Submodule R R)] := by
    intro a b le
    by_cases apos : a > 0
    · simp [SModEq.sub_mem, ← eq_zero_iff_mem, ← Polynomial.coeff_map, g_series_mod apos le]
    · simp [Nat.eq_zero_of_not_pos apos]
  let g_coeff : ℕ → R := fun i ↦ if i = k' then 1 else if i > k' then 0
    else Classical.choose (IsPrecomplete.prec IsAdicComplete.toIsPrecomplete (g_coeff_series_mod i))
  have lt {i : ℕ}: g_coeff i ≠ 0 → i < k' + 1 := by
    intro ne0
    by_contra gt
    have gt := Nat.lt_of_succ_le (Nat.le_of_not_lt gt)
    simp only [Nat.ne_of_lt' gt, ↓reduceIte, gt, ne_eq, not_true_eq_false, g_coeff] at ne0
  let g : R[X] := {
    toFinsupp := {
      support :=
        have : Fintype {i | g_coeff i ≠ 0} :=
          Fintype.ofInjective (fun i ↦ (⟨i.1, lt i.2⟩ : Fin (k' + 1))) (fun i j hij ↦
            Subtype.val_inj.mp <| Fin.mk.inj_iff.mp hij)
        {i | g_coeff i ≠ 0}.toFinset
      toFun := g_coeff
      mem_support_toFun := by simp }}
  have g_spec {i : ℕ} (hi : i < k') : ∀ n : ℕ, (g_series n).coeff i ≡ g_coeff i
    [SMOD m ^ n • (⊤ : Submodule R R)] := by
    simpa only [gt_iff_lt, Nat.ne_of_lt hi, g_coeff, Nat.not_lt_of_gt hi]
      using Classical.choose_spec (IsAdicComplete.toIsPrecomplete.prec (g_coeff_series_mod i))
  have g_spec' {n : ℕ} (npos : n > 0) : g.map (Ideal.Quotient.mk (m ^ n)) =
    g_series' ⟨n, npos⟩ := by
    rw [← (g_series_spec npos).1]
    have deg : (g_series n).degree = k' := by rw [← series_deg' ⟨n, npos⟩, (g_series_spec npos).2.1]
    have ndeg := Polynomial.natDegree_eq_of_degree_eq_some deg
    ext i
    simp only [Polynomial.coeff_map]
    by_cases ne : i = k'
    · simp [ne, g, g_coeff, ← ndeg, (g_series_spec npos).2.2]
    · rcases lt_or_gt_of_ne ne with lt|gt
      · rw [mk_eq_mk_iff_sub_mem]
        convert SModEq.sub_mem.mp (g_spec lt n).symm
        simp only [smul_eq_mul, Ideal.mul_top]
      · have : (g_series n).coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (ndeg ▸ gt)
        simp [gt_iff_lt.mp gt, ne, ↓reduceIte, g, g_coeff, this]
  use hu.unit
  constructor
  · use g
    have degeq : g.natDegree = k' := by
      apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ (by simp [g, g_coeff])
      rw [g.natDegree_le_iff_degree_le,  g.degree_le_iff_coeff_zero k']
      intro i hi
      have lt : k' < i := WithBot.coe_lt_coe.mp hi
      simp only [gt_iff_lt, ne_eq, Set.coe_setOf, Polynomial.coeff_ofFinsupp, Finsupp.coe_mk,
        (Nat.ne_of_lt lt).symm, ↓reduceIte, g, g_coeff, lt]
    have mon : g.coeff g.natDegree = 1 := by
      simp only [degeq, Polynomial.coeff_ofFinsupp, Finsupp.coe_mk, g, ↓reduceIte, g_coeff]
    constructor
    · refine ⟨⟨fun {i} hi ↦ ?_⟩, mon⟩
      rw [← pow_one m, ← eq_zero_iff_mem, ← Polynomial.coeff_map, g_spec' Nat.one_pos]
      rw [degeq, ← Polynomial.natDegree_eq_of_degree_eq_some (series_deg' ⟨1, Nat.one_pos⟩)] at hi
      have := (series_distinguish ⟨1, Nat.one_pos⟩).mem hi
      have map_bot: m.map (Ideal.Quotient.mk (m ^ 1)) = ⊥ := by simp [map_eq_bot_iff_le_ker]
      simpa [map_bot] using this
    · simp only [IsUnit.unit_spec]
      have {n : ℕ} (npos : n > 0): f.map (Ideal.Quotient.mk (m ^ n)) =
        (g * h).map (Ideal.Quotient.mk (m ^ n)) := by
        simp [← Polynomial.polynomial_map_coe, h_spec' npos, g_spec' npos, ← series_eq]
      ext i
      have modeq (n : ℕ) : f.coeff R i - (g * h).coeff R i ≡ 0
        [SMOD m ^ n • (⊤ : Submodule R R)] := by
        by_cases npos : n > 0
        · simp [← (mk_eq_mk_iff_sub_mem _ _), ← coeff_map, this npos, SModEq.zero]
        · simp [Nat.eq_zero_of_not_pos npos]
      rw [← sub_eq_zero,
        (IsAdicComplete.toIsHausdorff.haus (f.coeff R i - (g * h).coeff R i) modeq)]
  · rintro H ⟨G, distinguishG, eq⟩
    have Hu (n : ℕ) : IsUnit (H.1.map (Ideal.Quotient.mk (m ^ n))) := RingHom.isUnit_map _ H.isUnit
    have modeq' {n : ℕ} (npos : n > 0) : (Hu n).unit = (h_series' ⟨n, npos⟩) := by
      apply series_uniq ⟨n, npos⟩
      use G.map (Ideal.Quotient.mk (m ^ n))
      have degeq : G.degree = k' := by
        have : (constantCoeff R) H ∉ m := by
          by_contra mem
          absurd (Ideal.eq_top_of_isUnit_mem _ mem (isUnit_iff_constantCoeff.mp H.isUnit))
          exact IsPrime.ne_top'
        rw [degree_eq_order_map f H G distinguishG this eq, ENat.coe_lift]
      have degmapeq : (G.map (Ideal.Quotient.mk (m ^ n))).degree = k' := by
        let _ : Nontrivial (R ⧸ m ^ n) := R_ntriv' npos
        rw [distinguishG.monic.degree_map (Ideal.Quotient.mk (m ^ n)), degeq]
      constructor
      · refine ⟨⟨?_⟩, distinguishG.monic.map _⟩
        intro i hi
        rw [Polynomial.natDegree_eq_of_degree_eq_some degmapeq,
          ← Polynomial.natDegree_eq_of_degree_eq_some degeq] at hi
        simp [Submodule.mem_sup_left (distinguishG.mem hi)]
      · simp [Polynomial.polynomial_map_coe, eq]
    have modeq {n : ℕ} (npos : n > 0) : H.1.map (Ideal.Quotient.mk (m ^ n)) =
      (h_series n).map (Ideal.Quotient.mk (m ^ n))  := by simp [h_series_spec npos, ← modeq' npos]
    apply Units.eq_iff.mp
    ext i
    simp only [IsUnit.unit_spec]
    have coeff_modeq' (n : ℕ): H.1.coeff R i  ≡ h.coeff R i [SMOD m ^ n • (⊤ : Submodule R R)] := by
      by_cases npos : n > 0
      · apply SModEq.trans (SModEq.sub_mem.mpr _) (h_spec i n)
        simp [← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map, ← coeff_map, modeq npos]
      · simp [Nat.eq_zero_of_not_pos npos]
    exact sub_eq_zero.mp <| IsHausdorff.haus IsAdicComplete.toIsHausdorff
      (H.1.coeff R i - h.coeff R i) (fun n ↦ SModEq.zero.mpr (SModEq.sub_mem.mp (coeff_modeq' n)))
