/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Prod.Integral

/-!
# Integration with respect to a finite product of measures
-/

open BigOperators Fintype MeasureTheory MeasureTheory.Measure

theorem MeasureTheory.integral_finset_prod_eq_prod' {E : Type*} {n : ℕ} (f : (Fin n) → E → ℝ)
    [MeasureSpace E] [SigmaFinite (volume : Measure E)] :
    ∫ x : (Fin n) → E, ∏ i, f i (x i) = ∏ i, ∫ x, f i x := by
  induction n with
  | zero =>
      simp only [Nat.zero_eq, volume_pi, Finset.univ_eq_empty, Finset.prod_empty, integral_const,
        pi_empty_univ, ENNReal.one_toReal, smul_eq_mul, mul_one, pow_zero]
  | succ n n_ih =>
      calc
        _ = ∫ x : E × (Fin n → E), f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i) := by
          rw [volume_pi, ← ((measurePreserving_piFinSuccAboveEquiv
            (fun _ => (volume : Measure E)) 0).symm).integral_comp']
          simp_rw [MeasurableEquiv.piFinSuccAboveEquiv_symm_apply, Fin.insertNth_zero',
            Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
          rfl
        _ = (∫ x, f 0 x) *  ∏ i : Fin n, ∫ (x : E), f (Fin.succ i) x := by
          rw [← n_ih, ← integral_prod_mul, volume_eq_prod]
        _ =  ∏ i, ∫ x, f i x := by rw [Fin.prod_univ_succ]

theorem MeasureTheory.integral_finset_prod_eq_prod {E : Type*} (ι : Type*) [Fintype ι]
    (f : ι → E → ℝ) [MeasureSpace E] [SigmaFinite (volume : Measure E)] :
    ∫ x : ι → E, ∏ i, f i (x i) = ∏ i, ∫ x, f i x := by
  let e := (equivFin ι)
  let p := measurePreserving_piCongrLeft (fun _ => (volume : Measure E)) e
  rw [volume_pi, ← (p.symm).integral_comp', Fintype.prod_equiv e _ (fun j => ∫ x, f (e.symm j) x)
    (fun _ => by simp_rw [e.symm_apply_apply]), ← integral_finset_prod_eq_prod'
    (fun j => f (e.symm j))]
  congr!
  rw [Fintype.prod_equiv e]
  exact fun _ => by simp [Equiv.symm_apply_apply]; rfl

theorem MeasureTheory.integral_finset_prod_eq_pow {E : Type*} (ι : Type*) [Fintype ι] (f : E → ℝ)
    [MeasureSpace E] [SigmaFinite (volume : Measure E)] :
    ∫ x : ι → E, ∏ i, f (x i) = (∫ x, f x) ^ (card ι) := by
  rw [integral_finset_prod_eq_prod, Finset.prod_const, Fintype.card]
