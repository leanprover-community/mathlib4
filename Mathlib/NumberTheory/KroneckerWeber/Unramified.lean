import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Invariant
import Mathlib.RingTheory.Unramified.LocalRing

section IsUnramifiedAt

variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]

open IsLocalRing

noncomputable
instance (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    Algebra p.ResidueField q.ResidueField :=
  (Ideal.ResidueField.mapₐ p q Ideal.LiesOver.over).toAlgebra

/-- Let `A` be an essentially of finite type `R`-algebra, `q` be a prime over `p`.
Then `A` is unramified at `p` if and only if `κ(q)/κ(p)` is separable, and `pS_q = qS_q`. -/
lemma Algebra.isUnramifiedAt_iff_map_eq2 [EssFiniteType R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    Algebra.IsUnramifiedAt R q ↔
      Algebra.IsSeparable p.ResidueField q.ResidueField ∧
      p.map (algebraMap R (Localization.AtPrime q)) = maximalIdeal _ := by
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    (Localization.localRingHom p q (algebraMap R S) Ideal.LiesOver.over).toAlgebra
  have : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q) := .of_algebraMap_eq
    fun x ↦ (Localization.localRingHom_to_map p q (algebraMap R S) Ideal.LiesOver.over x).symm
  letI : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) :=
    Localization.isLocalHom_localRingHom _ _ _ Ideal.LiesOver.over
  have : EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) := .of_comp R _ _
  trans Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q)
  · exact ⟨fun _ ↦ .of_comp R _ _, fun _ ↦ .comp _ (Localization.AtPrime p) _⟩
  rw [FormallyUnramified.iff_map_maximalIdeal_eq]
  congr!
  rw [RingHom.algebraMap_toAlgebra, ← Localization.AtPrime.map_eq_maximalIdeal,
    Ideal.map_map, Localization.localRingHom,
    IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq]

end IsUnramifiedAt

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

namespace Algebra

instance (p : Ideal S) (P : Ideal T) [P.LiesOver p] [p.IsPrime] [P.IsPrime] :
    IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime P) :=  .of_algebraMap_eq (by
  simp [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply R S (Localization.AtPrime p),
  Localization.localRingHom_to_map, IsScalarTower.algebraMap_apply R T (Localization.AtPrime P),
  IsScalarTower.algebraMap_apply R S T])

variable (R) in
lemma IsUnramifiedAt.comp (p : Ideal S) (P : Ideal T) [P.LiesOver p] [p.IsPrime] [P.IsPrime]
    [IsUnramifiedAt R p] [IsUnramifiedAt S P] : IsUnramifiedAt R P := by
  have : FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime P) :=
    .of_comp S _ _
  exact FormallyUnramified.comp R (Localization.AtPrime p) _

variable (R) in
lemma IsUnramifiedAt.of_restrictScalars (P : Ideal T) [P.IsPrime]
    [IsUnramifiedAt R P] : IsUnramifiedAt S P :=
  FormallyUnramified.of_comp R _ _

instance {R : Type*} [CommRing R] (S : Submonoid R) [IsNoetherianRing R] :
    IsNoetherianRing (Localization S) :=
  IsLocalization.isNoetherianRing S _ ‹_›


scoped[NumberTheory] notation3 "e("P"|"R")" =>
  Ideal.ramificationIdx (algebraMap _ _) (Ideal.under R P) P

open scoped NumberTheory in
lemma _root_.Ideal.ramificationIdx_ne_one_iff {p : Ideal S} :
    e(p|R) ≠ 1 ↔ (p.under R).map (algebraMap R S) ≤ p ^ 2 := by
  classical
  by_cases H : ∀ n : ℕ, ∃ k, (p.under R).map (algebraMap R S) ≤ p ^ k ∧ n < k
  · obtain ⟨k, hk, h2k⟩ := H 2
    simp [Ideal.ramificationIdx_eq_zero H, hk.trans (Ideal.pow_le_pow_right h2k.le)]
  push_neg at H
  rw [Ideal.ramificationIdx_eq_find H]
  constructor
  · intro he
    have : 1 ≤ Nat.find H := Nat.find_spec H 1 (by simp [Ideal.map_le_iff_le_comap])
    have := Nat.find_min H (m := 1) (by omega)
    push_neg at this
    obtain ⟨k, hk, h1k⟩ := this
    exact hk.trans (Ideal.pow_le_pow_right (Nat.succ_le.mpr h1k))
  · intro he
    have := Nat.find_spec H 2 he
    omega

open scoped NumberTheory in
open IsLocalRing in
lemma _root_.Ideal.ramificationIdx_eq_one_of_map_localization
    {p : Ideal S} [p.IsPrime] [IsNoetherianRing S]
    (hp : p ≠ ⊥) (hp' : p.primeCompl ≤ nonZeroDivisors S)
    (H : Ideal.map (algebraMap R (Localization.AtPrime p)) (p.under R) =
      IsLocalRing.maximalIdeal (Localization.AtPrime p)) :
  e(p|R) = 1 := by
  rw [← not_ne_iff (b := 1), Ideal.ramificationIdx_ne_one_iff]
  intro h₂
  replace h₂ := Ideal.map_mono (f := algebraMap S (Localization.AtPrime p)) h₂
  rw [Ideal.map_pow, Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq, H, pow_two] at h₂
  have := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ (IsNoetherian.noetherian _) h₂
    (maximalIdeal_le_jacobson _)
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_eq_bot_iff_of_injective] at this
  · exact hp this
  · exact IsLocalization.injective _ hp'

open scoped NumberTheory in
open IsLocalRing in
lemma _root_.Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
    {p : Ideal S} [p.IsPrime] [IsNoetherianRing S] [IsUnramifiedAt R p]
    (hp : p ≠ ⊥) [IsDomain S] [EssFiniteType R S] :
    e(p|R) = 1 :=
  (Ideal.ramificationIdx_eq_one_of_map_localization hp p.primeCompl_le_nonZeroDivisors
    ((isUnramifiedAt_iff_map_eq2 R (p.under R) p).mp ‹_›).2)

open scoped NumberTheory in
open IsLocalRing in
lemma _root_.Ideal.ramificationIdx_eq_one_iff_of_isDedekindDomain
    {p : Ideal S} [p.IsPrime] [IsDedekindDomain S]
    (hp : p ≠ ⊥) :
    e(p|R) = 1 ↔ Ideal.map (algebraMap R (Localization.AtPrime p)) (p.under R) =
      IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
  refine ⟨?_, Ideal.ramificationIdx_eq_one_of_map_localization hp
    (Ideal.primeCompl_le_nonZeroDivisors _)⟩
  let Sₚ := Localization.AtPrime p
  rw [← not_ne_iff (b := 1), Ideal.ramificationIdx_ne_one_iff, pow_two]
  intro H₁
  have H₀ : (p.under R).map (algebraMap R S) ≤ p := Ideal.map_comap_le
  obtain ⟨a, ha⟩ : p ∣ (p.under R).map (algebraMap R S) := Ideal.dvd_iff_le.mpr Ideal.map_comap_le
  have ha' : ¬ a ≤ p := fun h ↦ H₁ (ha.trans_le (Ideal.mul_mono_right h))
  rw [IsScalarTower.algebraMap_eq _ S, ← Ideal.map_map, ha, Ideal.map_mul,
    Localization.AtPrime.map_eq_maximalIdeal]
  convert Ideal.mul_top _
  rw [← not_ne_iff, IsLocalization.map_algebraMap_ne_top_iff_disjoint p.primeCompl]
  simpa [Ideal.primeCompl, Set.disjoint_compl_left_iff_subset]

lemma EssFiniteType.IsNoetherianRing (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [EssFiniteType R S] [IsNoetherianRing R] : IsNoetherianRing S := by
  exact IsLocalization.isNoetherianRing (EssFiniteType.submonoid R S) _
    (Algebra.FiniteType.isNoetherianRing R _)

variable (R) in
/--
Note: `IsDomain S` can be replaced by "`P` contains all zero-divisors",
and `NoZeroSMulDivisors S T` can be replaced by `P ≠ ⊥`.
-/
lemma IsUnramifiedAt.of_liesOver_of_ne_bot
    (p : Ideal S) (P : Ideal T) [P.LiesOver p] [p.IsPrime] [P.IsPrime]
    [IsUnramifiedAt R P] [EssFiniteType R S] [EssFiniteType R T]
    [IsDedekindDomain S] (hP₁ : P.primeCompl ≤ nonZeroDivisors T) (hP₂ : p ≠ ⊥ → P ≠ ⊥) :
    IsUnramifiedAt R p := by
  let p₀ : Ideal R := p.under R
  have : P.LiesOver p₀ := .trans P p p₀
  have hp₀ : p₀ = P.under R := Ideal.LiesOver.over
  have : EssFiniteType S T := .of_comp R S T
  have := EssFiniteType.IsNoetherianRing S T
  rw [isUnramifiedAt_iff_map_eq2 R p₀ p]
  have ⟨h₁, h₂⟩ := (isUnramifiedAt_iff_map_eq2 R p₀ P).mp ‹_›
  -- todo: move me out
  have : IsScalarTower p₀.ResidueField p.ResidueField P.ResidueField := by
    refine .of_algebraMap_eq fun x ↦ ?_
    simp only [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Ideal.ResidueField.mapₐ_apply, Ideal.ResidueField.map, IsLocalRing.ResidueField.map_map,
      ← IsLocalRing.ResidueField.map_comp, IsScalarTower.algebraMap_eq R S T,
      ← Localization.localRingHom_comp]
  refine ⟨Algebra.isSeparable_tower_bot_of_isSeparable _ _ P.ResidueField, ?_⟩
  by_cases hp : p = ⊥
  · have : p₀.map (algebraMap R S) = p := by
      subst hp
      exact le_bot_iff.mp (Ideal.map_comap_le)
    rw [IsScalarTower.algebraMap_eq _ S, ← Ideal.map_map, this,
      Localization.AtPrime.map_eq_maximalIdeal]
  rw [← Ideal.ramificationIdx_eq_one_iff_of_isDedekindDomain hp,
    ← not_ne_iff, Ideal.ramificationIdx_ne_one_iff]
  intro H
  have := Ideal.ramificationIdx_eq_one_of_map_localization (hP₂ hp) hP₁ (hp₀ ▸ h₂)
  · rw [← not_ne_iff, Ideal.ramificationIdx_ne_one_iff, ← hp₀] at this
    replace H := Ideal.map_mono (f := algebraMap S T) H
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq, Ideal.map_pow] at H
    refine this (H.trans (Ideal.pow_right_mono ?_ _))
    exact Ideal.map_le_iff_le_comap.mpr Ideal.LiesOver.over.le

variable (R) in
lemma IsUnramifiedAt.of_liesOver (p : Ideal S) (P : Ideal T) [P.LiesOver p] [p.IsPrime] [P.IsPrime]
    [IsUnramifiedAt R P] [EssFiniteType R S] [EssFiniteType R T]
    [IsDedekindDomain S] [IsDomain T] [NoZeroSMulDivisors S T] : IsUnramifiedAt R p :=
  IsUnramifiedAt.of_liesOver_of_ne_bot R p P P.primeCompl_le_nonZeroDivisors
    (Ideal.ne_bot_of_liesOver_of_ne_bot · P)

open IsLocalization in
lemma _root_.IsLocalization.finite
    {R S : Type*} [CommRing R] (M : Submonoid R) [CommRing S] [Algebra R S]
    [IsLocalization M S] [Finite R] : Finite S := by
  have : Function.Surjective (Function.uncurry (mk' (M := M) S)) := fun x ↦ by
    simpa using IsLocalization.mk'_surjective M x
  exact .of_surjective _ this

instance {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] :
    Algebra.IsAlgebraic (R ⧸ p) p.ResidueField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (R ⧸ p))

instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) (P : Ideal S)
    [p.IsPrime] [P.IsPrime] [P.LiesOver p] [Algebra.IsIntegral R S] :
    Algebra.IsAlgebraic p.ResidueField P.ResidueField := by
  have : Algebra.IsIntegral (R ⧸ p) (S ⧸ P) :=
    .tower_top R
  have : Algebra.IsAlgebraic (R ⧸ p) (S ⧸ P) := Algebra.IsIntegral.isAlgebraic
  letI := ((algebraMap (S ⧸ P) P.ResidueField).comp (algebraMap (R ⧸ p) (S ⧸ P))).toAlgebra
  haveI : IsScalarTower (R ⧸ p) (S ⧸ P) P.ResidueField := .of_algebraMap_eq' rfl
  haveI : Algebra.IsAlgebraic (R ⧸ p) P.ResidueField := .trans _ (S ⧸ P) _
  haveI : IsScalarTower (R ⧸ p) p.ResidueField P.ResidueField := by
    refine .of_algebraMap_eq fun x ↦ ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [RingHom.algebraMap_toAlgebra, Algebra.ofId_apply]
    rfl
  refine .extendScalars (Ideal.injective_algebraMap_quotient_residueField p)

open scoped NumberTheory in
open IsLocalRing in
lemma isUnramifiedAt_iff_of_isDedekindDomain
    {p : Ideal S} [p.IsPrime] [IsDedekindDomain S] [EssFiniteType R S] [IsDomain R]
    [Module.Finite ℤ R] [CharZero R] [Algebra.IsIntegral R S] [NoZeroSMulDivisors R S]
    (hp : p ≠ ⊥) :
    Algebra.IsUnramifiedAt R p ↔ e(p|R) = 1 := by
  rw [isUnramifiedAt_iff_map_eq2 R (p.under R) p, and_iff_right,
    Ideal.ramificationIdx_eq_one_iff_of_isDedekindDomain hp]
  have : Fintype (R ⧸ p.under R) :=
    Ideal.fintypeQuotientOfFreeOfNeBot _ (mt Ideal.eq_bot_of_comap_eq_bot hp)
  have : Finite ((p.under R).ResidueField) := IsLocalization.finite
    (nonZeroDivisors (R ⧸ p.under R))
  infer_instance

end Algebra
