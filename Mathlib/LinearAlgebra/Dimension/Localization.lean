/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.OreLocalization.OreSet

/-!
# Rank of localization

## Main statements

- `IsLocalizedModule.lift_rank_eq`: `rank_Rₚ Mₚ = rank R M`.
- `rank_quotient_add_rank_of_isDomain`: The **rank-nullity theorem** for commutative domains.
-/

open Cardinal Module nonZeroDivisors

section CommRing

universe uR uS uT uM uN uP

variable {R : Type uR} (S : Type uS) {M : Type uM} {N : Type uN}
variable [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N] [Algebra R S] [Module S N] [IsScalarTower R S N]
variable (p : Submonoid R) [IsLocalization p S] (f : M →ₗ[R] N) [IsLocalizedModule p f]
variable (hp : p ≤ R⁰)

section
include hp

section
include f

lemma IsLocalizedModule.lift_rank_eq :
    Cardinal.lift.{uM} (Module.rank R N) = Cardinal.lift.{uN} (Module.rank R M) := by
  cases subsingleton_or_nontrivial R
  · simp only [rank_subsingleton, lift_one]
  apply le_antisymm <;>
    rw [Module.rank_def, lift_iSup (bddAbove_range _)] <;>
    apply ciSup_le' <;>
    intro ⟨s, hs⟩
  exacts [(IsLocalizedModule.linearIndependent_lift p f hs).choose_spec.cardinal_lift_le_rank,
    hs.of_isLocalizedModule_of_isRegular p f (le_nonZeroDivisors_iff_isRegular.mp hp)
      |>.cardinal_lift_le_rank]

lemma IsLocalizedModule.finrank_eq : finrank R N = finrank R M := by
  simpa using congr_arg toNat (lift_rank_eq p f hp)

end

lemma IsLocalizedModule.rank_eq {N : Type uM} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    [IsLocalizedModule p f] : Module.rank R N = Module.rank R M := by
  simpa using lift_rank_eq p f hp

lemma IsLocalization.rank_eq : Module.rank S N = Module.rank R N := by
  cases subsingleton_or_nontrivial R
  · have := (algebraMap R S).codomain_trivial; simp only [rank_subsingleton, lift_one]
  have inj := IsLocalization.injective S hp
  apply le_antisymm <;> (rw [Module.rank]; apply ciSup_le'; intro ⟨s, hs⟩)
  · have := (faithfulSMul_iff_algebraMap_injective R S).mpr inj
    exact (hs.restrict_scalars' R).cardinal_le_rank
  · have := inj.nontrivial
    exact (hs.localization S p).cardinal_le_rank

end

variable (R M) in
theorem exists_set_linearIndependent_of_isDomain [IsDomain R] :
    ∃ s : Set M, #s = Module.rank R M ∧ LinearIndepOn R id s := by
  obtain ⟨w, hw⟩ :=
    IsLocalizedModule.linearIndependent_lift R⁰ (LocalizedModule.mkLinearMap R⁰ M) <|
      Module.Free.chooseBasis (FractionRing R) (LocalizedModule R⁰ M)
        |>.linearIndependent.restrict_scalars' _
  refine ⟨Set.range w, ?_, (linearIndepOn_id_range_iff hw.injective).mpr hw⟩
  apply Cardinal.lift_injective.{max uR uM}
  rw [Cardinal.mk_range_eq_of_injective hw.injective, ← Module.Free.rank_eq_card_chooseBasisIndex,
    IsLocalization.rank_eq (FractionRing R) R⁰ le_rfl,
    IsLocalizedModule.lift_rank_eq R⁰ (LocalizedModule.mkLinearMap R⁰ M) le_rfl]

/-- The **rank-nullity theorem** for commutative domains. Also see `rank_quotient_add_rank`. -/
theorem rank_quotient_add_rank_of_isDomain [IsDomain R] (M' : Submodule R M) :
    Module.rank R (M ⧸ M') + Module.rank R M' = Module.rank R M := by
  apply lift_injective.{max uR uM}
  simp_rw [lift_add, ← IsLocalizedModule.lift_rank_eq R⁰ (M'.toLocalized R⁰) le_rfl,
    ← IsLocalizedModule.lift_rank_eq R⁰ (LocalizedModule.mkLinearMap R⁰ M) le_rfl,
    ← IsLocalizedModule.lift_rank_eq R⁰ (M'.toLocalizedQuotient R⁰) le_rfl,
    ← IsLocalization.rank_eq (FractionRing R) R⁰ le_rfl,
    ← lift_add, rank_quotient_add_rank_of_divisionRing]

universe w in
instance IsDomain.hasRankNullity [IsDomain R] : HasRankNullity.{w} R where
  rank_quotient_add_rank := rank_quotient_add_rank_of_isDomain
  exists_set_linearIndependent M := exists_set_linearIndependent_of_isDomain R M

namespace IsBaseChange

open Cardinal TensorProduct

section

variable {p} [Free S N] [StrongRankCondition S] {T : Type uT} [CommRing T] [Algebra R T]
  (hpT : Algebra.algebraMapSubmonoid T p ≤ T⁰) [StrongRankCondition (S ⊗[R] T)]
  {P : Type uP} [AddCommGroup P] [Module R P] [Module T P] [IsScalarTower R T P]
  {g : M →ₗ[R] P} (bc : IsBaseChange T g)

include S hp hpT f bc

theorem lift_rank_eq_of_le_nonZeroDivisors :
    Cardinal.lift.{uM} (Module.rank T P) = Cardinal.lift.{uP} (Module.rank R M) := by
  rw [← lift_inj.{_, max uS uT uN}, lift_lift, lift_lift]
  let ST := S ⊗[R] T
  conv_rhs => rw [← lift_lift.{uN, max uS uT uP}, ← IsLocalizedModule.lift_rank_eq p f hp,
    ← IsLocalization.rank_eq S p hp, lift_lift, ← lift_lift.{max uS uT, max uM uP},
    ← rank_baseChange (R := ST), ← lift_id'.{max uS uT, max uS uT uN} (Module.rank ..),
    lift_lift, ← lift_lift.{max uS uT uP, uM}]
  let _ : Algebra T ST := Algebra.TensorProduct.rightAlgebra
  set pT := Algebra.algebraMapSubmonoid T p
  have : IsLocalization pT ST := isLocalizedModule_iff_isLocalization.mp
    (IsLocalization.tensorProduct_isLocalizedModule ..)
  rw [← lift_lift.{max uS uT, max uM uN}, ← lift_umax.{uP},
    ← IsLocalizedModule.lift_rank_eq pT (mk T ST P 1) hpT,
    ← IsLocalization.rank_eq ST pT hpT, lift_id'.{uP, max uS uT},
    ← lift_id'.{max uS uT, max uS uT uP} (Module.rank ..), lift_lift,
    ← lift_lift.{max uS uT uN, uM}, lift_inj]
  exact LinearEquiv.lift_rank_eq <| AlgebraTensorModule.congr (.refl ST ST) bc.equiv.symm ≪≫ₗ
    AlgebraTensorModule.cancelBaseChange .. ≪≫ₗ (AlgebraTensorModule.cancelBaseChange ..).symm ≪≫ₗ
    AlgebraTensorModule.congr (.refl ..) ((isLocalizedModule_iff_isBaseChange p S f).mp ‹_›).equiv

theorem finrank_eq_of_le_nonZeroDivisors : finrank T P = finrank R M := by
  simpa using congr_arg toNat (lift_rank_eq_of_le_nonZeroDivisors S f hp hpT bc)

omit bc
theorem rank_eq_of_le_nonZeroDivisors {P : Type uM} [AddCommGroup P] [Module R P] [Module T P]
    [IsScalarTower R T P] {g : M →ₗ[R] P} (bc : IsBaseChange T g) :
    Module.rank T P = Module.rank R M := by
  simpa using lift_rank_eq_of_le_nonZeroDivisors S f hp hpT bc

end

variable {p} {T : Type uT} [CommRing T] [NoZeroDivisors T] [Algebra R T] [FaithfulSMul R T]
  {P : Type uP} [AddCommGroup P] [Module R P] [Module T P] [IsScalarTower R T P]
  {g : M →ₗ[R] P} (bc : IsBaseChange T g)

include bc
theorem lift_rank_eq :
    Cardinal.lift.{uM} (Module.rank T P) = Cardinal.lift.{uP} (Module.rank R M) := by
  have inj := FaithfulSMul.algebraMap_injective R T
  have := inj.noZeroDivisors _ (map_zero _) (map_mul _)
  cases subsingleton_or_nontrivial R
  · have := (algebraMap R T).codomain_trivial; simp only [rank_subsingleton, lift_one]
  have := (isDomain_iff_noZeroDivisors_and_nontrivial T).mpr
    ⟨‹_›, (FaithfulSMul.algebraMap_injective R T).nontrivial⟩
  let FR := FractionRing R
  let FT := FractionRing T
  replace inj : Function.Injective (algebraMap R FT) := (IsFractionRing.injective T _).comp inj
  let g := TensorProduct.mk T FT P 1
  have : IsLocalizedModule R⁰ (TensorProduct.mk R FR FT 1) := inferInstance
  let _ : Algebra FT (FR ⊗[R] FT) := Algebra.TensorProduct.rightAlgebra
  let _ := isLocalizedModule_iff_isLocalization.mp this |>.atUnits _ _ ?_ |>.symm.isField
    _ (Field.toIsField FT) |>.toField
  on_goal 2 => rintro _ ⟨_, mem, rfl⟩; exact (map_ne_zero_of_mem_nonZeroDivisors _ inj mem).isUnit
  have := bc.comp_iff.2 ((isLocalizedModule_iff_isBaseChange T⁰ FT g).1 inferInstance)
  rw [← lift_inj.{_, max uT uP}, lift_lift, lift_lift, ← lift_lift.{max uT uP, uM},
    ← IsLocalizedModule.lift_rank_eq T⁰ g le_rfl, lift_lift, ← lift_lift.{uM},
    ← IsLocalization.rank_eq FT T⁰ le_rfl,
    lift_rank_eq_of_le_nonZeroDivisors FR (LocalizedModule.mkLinearMap R⁰ M) le_rfl
      (map_le_nonZeroDivisors_of_injective _ inj le_rfl) this, lift_lift]

theorem finrank_eq : finrank T P = finrank R M := by simpa using congr_arg toNat bc.lift_rank_eq

omit bc
theorem rank_eq {P : Type uM} [AddCommGroup P] [Module R P] [Module T P] [IsScalarTower R T P]
    {g : M →ₗ[R] P} (bc : IsBaseChange T g) : Module.rank T P = Module.rank R M := by
  simpa using bc.lift_rank_eq

end IsBaseChange

end CommRing

section Ring

variable {R} [Ring R] [IsDomain R]

/-- A domain that is not (left) Ore is of infinite rank.
See [cohn_1995] Proposition 1.3.6 -/
lemma aleph0_le_rank_of_isEmpty_oreSet (hS : IsEmpty (OreLocalization.OreSet R⁰)) :
    ℵ₀ ≤ Module.rank R R := by
  classical
  rw [← not_nonempty_iff, OreLocalization.nonempty_oreSet_iff_of_noZeroDivisors] at hS
  push_neg at hS
  obtain ⟨r, s, h⟩ := hS
  refine Cardinal.aleph0_le.mpr fun n ↦ ?_
  suffices LinearIndependent R (fun (i : Fin n) ↦ r * s ^ (i : ℕ)) by
    simpa using this.cardinal_lift_le_rank
  suffices ∀ (g : ℕ → R) (x), (∑ i ∈ Finset.range n, g i • (r * s ^ (i + x))) = 0 →
      ∀ i < n, g i = 0 by
    refine Fintype.linearIndependent_iff.mpr fun g hg i ↦ ?_
    simpa only [dif_pos i.prop] using this (fun i ↦ if h : i < n then g ⟨i, h⟩ else 0) 0
      (by simp [← Fin.sum_univ_eq_sum_range, ← hg]) i i.prop
  intro g x hg i hin
  induction n generalizing g x i with
  | zero => exact (hin.not_ge (zero_le i)).elim
  | succ n IH =>
    rw [Finset.sum_range_succ'] at hg
    by_cases hg0 : g 0 = 0
    · simp only [hg0, zero_smul, add_zero, add_assoc] at hg
      cases i; exacts [hg0, IH _ _ hg _ (Nat.succ_lt_succ_iff.mp hin)]
    simp only [MulOpposite.smul_eq_mul_unop, zero_add, ← add_comm _ x, pow_add _ _ x,
      ← mul_assoc, pow_succ, ← Finset.sum_mul, pow_zero, one_mul, smul_eq_mul] at hg
    rw [← neg_eq_iff_add_eq_zero, ← neg_mul, ← neg_mul] at hg
    have := mul_right_cancel₀ (mem_nonZeroDivisors_iff_ne_zero.mp (s ^ x).prop) hg
    exact (h _ ⟨(g 0), mem_nonZeroDivisors_iff_ne_zero.mpr (by simpa)⟩ this.symm).elim

-- TODO: Upgrade this to an iff. See [lam_1999] Exercise 10.21
lemma nonempty_oreSet_of_strongRankCondition [StrongRankCondition R] :
    Nonempty (OreLocalization.OreSet R⁰) := by
  by_contra h
  have := aleph0_le_rank_of_isEmpty_oreSet (not_nonempty_iff.mp h)
  rw [rank_self] at this
  exact this.not_gt one_lt_aleph0

end Ring
