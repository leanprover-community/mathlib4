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

variable {𝕜 : Type*} [IsROrC 𝕜]

/-- A version of **Fubini's theorem** in `n` variables, for a natural number `n`. -/
theorem MeasureTheory.integral_fin_nat_prod_eq_prod {n : ℕ} {E : Fin n → Type*}
    [∀ i, MeasureSpace (E i)] [∀ i, SigmaFinite (volume : Measure (E i))]
    (f : (i : Fin n) → E i → 𝕜) :
    ∫ x : (i : Fin n) → E i, ∏ i, f i (x i) = ∏ i, ∫ x, f i x := by
  induction n with
  | zero =>
      simp only [Nat.zero_eq, volume_pi, Finset.univ_eq_empty, Finset.prod_empty, integral_const,
        pi_empty_univ, ENNReal.one_toReal, smul_eq_mul, mul_one, pow_zero, one_smul]
  | succ n n_ih =>
      calc
        _ = ∫ x : E 0 × ((i : Fin n) → E (Fin.succ i)),
            f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i) := by
          rw [volume_pi, ← ((measurePreserving_piFinSuccAboveEquiv
            (fun i => (volume : Measure (E i))) 0).symm).integral_comp']
          simp_rw [MeasurableEquiv.piFinSuccAboveEquiv_symm_apply,
            Fin.prod_univ_succ, Fin.insertNth_zero, Fin.cons_succ]
          rfl
        _ = (∫ x, f 0 x) *  ∏ i : Fin n, ∫ (x : E (Fin.succ i)), f (Fin.succ i) x := by
          rw [← n_ih, ← integral_prod_mul, volume_eq_prod]
        _ =  ∏ i, ∫ x, f i x := by rw [Fin.prod_univ_succ]

/-- A version of **Fubini's theorem** with the variables indexed by a general finite type. -/
theorem MeasureTheory.integral_fintype_prod_eq_prod (ι : Type*) [Fintype ι] {E : ι → Type*}
    (f : (i : ι) → E i → 𝕜) [∀ i, MeasureSpace (E i)] [∀ i, SigmaFinite (volume : Measure (E i))] :
    ∫ x : (i : ι) → E i, ∏ i, f i (x i) = ∏ i, ∫ x, f i x := by
  let n := Fintype.card ι
  let e : Fin n ≃ ι := (equivFin ι).symm
  rw [← MeasurePreserving.integral_comp' (μ := volume) (ν := volume)
    (measurePreserving_piCongrLeft (fun i => (volume : Measure (E i))) e)]
  have h0 : ∀ (x : (m : Fin n) → E (e m)) (m : Fin n),
      (MeasurableEquiv.piCongrLeft E e) x (e m) = x m
  · intro x m
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  have h1 : ∫ x, ∏ i, f i ((MeasurableEquiv.piCongrLeft E e) x i) =
      ∫ (x : (m : Fin n) → E (e m)), ∏ m, f (e m) (x m)
  · congr 1 with v : 1
    exact (Fintype.prod_equiv e _ _ (fun m ↦ by rw [h0 v m])).symm
  rw [h1, MeasureTheory.integral_fin_nat_prod_eq_prod]
  exact Fintype.prod_equiv e _ _ (fun i ↦ by rfl)

theorem MeasureTheory.integral_fintype_prod_eq_pow {E : Type*} (ι : Type*) [Fintype ι] (f : E → 𝕜)
    [MeasureSpace E] [SigmaFinite (volume : Measure E)] :
    ∫ x : ι → E, ∏ i, f (x i) = (∫ x, f x) ^ (card ι) := by
  rw [integral_fintype_prod_eq_prod, Finset.prod_const, Fintype.card]
