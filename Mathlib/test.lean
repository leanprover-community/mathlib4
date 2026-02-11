import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.RCLike.Basic

open Filter Bornology

variable {R : Type*} [NormedRing R] [NormOneClass R] [NormMulClass R]

theorem Asymptotics.isLittleO_pow_pow_cobounded_of_lt {p q : ℕ} (hpq : p < q) :
    (fun x : R ↦ x ^ p) =o[cobounded R] fun x ↦ x ^ q := by
  refine isLittleO_iff_nat_mul_le.mpr fun n ↦ ?_
  rw [← (Nat.sub_add_cancel hpq.le)]
  simp_rw [pow_add, norm_mul, norm_pow]
  refine eventually_iff_exists_mem.mpr ?_
  refine ⟨{y | n ≤ ‖y‖ ^ (q - p)}, ?_, fun y my ↦ ?_⟩
  · simp_rw [← isCobounded_def, ← isBounded_compl_iff, Set.compl_setOf, not_le]
    rw [isBounded_iff_forall_norm_le]
    refine ⟨n, fun a ma ↦ ?_⟩
    simp only [Set.mem_setOf_eq] at ma
    contrapose! ma
    rcases le_or_gt ‖a‖ 1 with ha | ha
    · replace ma := ma.trans_le ha
      rw [Nat.cast_lt_one] at ma
      simp [ma]
    · exact ma.le.trans (le_self_pow₀ ha.le (Nat.sub_ne_zero_iff_lt.mpr hpq))
  · gcongr
    exact my
