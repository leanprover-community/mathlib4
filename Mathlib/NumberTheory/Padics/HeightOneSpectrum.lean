import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.NumberTheory.Padics.WithVal
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Int.Basic
import Mathlib.NumberTheory.Padics.ProperSpace

open IsDedekindDomain

open scoped NumberField WithZero

noncomputable
def IsDedekindDomain.HeightOneSpectrum.natGenerator {R : Type*} [CommRing R]
    [h : Nonempty (R ≃+* ℤ)] (v : HeightOneSpectrum R) : ℕ :=
  Submodule.IsPrincipal.generator (v.asIdeal.map h.some) |>.natAbs

namespace IsDedekindDomain.HeightOneSpectrum

noncomputable instance {R : Type*} [CommRing R] [Nonempty (R ≃+* ℤ)] :
    CoeOut (HeightOneSpectrum R) ℕ where
  coe := natGenerator

theorem span_natGenerator {R : Type*} [CommRing R] [h : Nonempty (R ≃+* ℤ)]
    (v : HeightOneSpectrum R) :
    Ideal.span {↑v} = v.asIdeal.map h.some := by
  simp [natGenerator]

theorem natGenerator_dvd_iff {R : Type*} [CommRing R] [h : Nonempty (R ≃+* ℤ)]
    (v : HeightOneSpectrum R) {n : ℕ} :
    ↑v ∣ n ↔ ↑n ∈ v.asIdeal.map h.some := by
  rw [← span_natGenerator, Ideal.mem_span_singleton]
  exact Int.ofNat_dvd.symm

instance {R : Type*} [CommRing R] [h : Nonempty (R ≃+* ℤ)]
    (v : HeightOneSpectrum R) : Fact (Nat.Prime v) :=
  ⟨Int.prime_iff_natAbs_prime.1 <| Submodule.IsPrincipal.prime_generator_of_isPrime _
    ((Ideal.map_eq_bot_iff_of_injective h.some.injective).not.2 v.ne_bot)⟩

theorem valuation_equiv_padicValuation {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra R ℚ] [IsFractionRing R ℚ] [Nonempty (R ≃+* ℤ)] (𝔭 : HeightOneSpectrum R) :
    (𝔭.valuation ℚ).IsEquiv (Rat.padicValuation 𝔭) := by
  simp [Valuation.isEquiv_iff_val_le_one, Rat.padicValuation_le_one_iff,
    Rat.valuation_le_one_iff_den, natGenerator_dvd_iff,
    ← Ideal.apply_mem_of_equiv_iff (f := Classical.arbitrary (R ≃+* ℤ))]

noncomputable def valuationEquivPadicValuation {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra R ℚ] [IsFractionRing R ℚ] [Nonempty (R ≃+* ℤ)] (𝔭 : HeightOneSpectrum R) :
    WithVal (𝔭.valuation ℚ) ≃ᵤ WithVal (Rat.padicValuation 𝔭) :=
  Valuation.IsEquiv.uniformEquiv (𝔭.valuation_surjective ℚ) (Rat.surjective_padicValuation _)
    𝔭.valuation_equiv_padicValuation

noncomputable def adicCompletion.padicUniformEquiv {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra R ℚ] [IsFractionRing R ℚ] [Nonempty (R ≃+* ℤ)] (𝔭 : HeightOneSpectrum R) :
    𝔭.adicCompletion ℚ ≃ᵤ ℚ_[𝔭] :=
  (UniformSpace.Completion.mapEquiv 𝔭.valuationEquivPadicValuation).trans Padic.withValUniformEquiv

noncomputable def adicCompletion.padicRingEquiv {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra R ℚ] [IsFractionRing R ℚ] [Nonempty (R ≃+* ℤ)] (𝔭 : HeightOneSpectrum R) :
    𝔭.adicCompletion ℚ ≃+* ℚ_[𝔭] :=
  (UniformSpace.Completion.mapRingEquiv _ 𝔭.valuationEquivPadicValuation.uniformContinuous
    𝔭.valuationEquivPadicValuation.symm.uniformContinuous).trans
  Padic.withValRingEquiv

noncomputable def adicCompletion.padicAlgEquiv {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra R ℚ] [IsFractionRing R ℚ] [Nonempty (R ≃+* ℤ)] (𝔭 : HeightOneSpectrum R) :
    𝔭.adicCompletion ℚ ≃ₐ[ℚ] ℚ_[𝔭] where
  __ := adicCompletion.padicRingEquiv 𝔭
  commutes' q := by simp

open UniformSpace.Completion in
theorem _root_.Valuation.IsEquiv.valuedCompletion_le_one_iff {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀} {Γ₀' : Type*}
    [LinearOrderedCommGroupWithZero Γ₀'] {v' : Valuation K Γ₀'} (h : v.IsEquiv v')
    (hv : Function.Surjective v) (hv' : Function.Surjective v') {x : v.Completion} :
    Valued.v x ≤ 1 ↔ Valued.v (mapEquiv (h.uniformEquiv hv hv') x) ≤ 1 := by
  induction x using induction_on with
  | hp =>
    exact (mapEquiv (h.uniformEquiv hv hv')).toHomeomorph.isClosed_setOf_iff
      (Valued.isClopen_closedBall _ one_ne_zero) (Valued.isClopen_closedBall _ one_ne_zero)
  | ih a =>
    rw [Valued.valuedCompletion_apply, ← WithVal.apply_equiv, mapEquiv_coe]
    simpa using h.le_one_iff_le_one

noncomputable def adicCompletionIntegers.padicIntUniformEquiv {R : Type*} [CommRing R]
    [IsDedekindDomain R] [Algebra R ℚ] [IsFractionRing R ℚ] [Nonempty (R ≃+* ℤ)]
    (𝔭 : HeightOneSpectrum R) :
    𝔭.adicCompletionIntegers ℚ ≃ᵤ ℤ_[𝔭] :=
  let e : 𝔭.adicCompletionIntegers ℚ ≃ᵤ
      (Valued.v.valuationSubring : ValuationSubring (Rat.padicValuation 𝔭).Completion) :=
    (UniformSpace.Completion.mapEquiv 𝔭.valuationEquivPadicValuation).subtype fun _ ↦ by
      simpa using 𝔭.valuation_equiv_padicValuation.valuedCompletion_le_one_iff
        (𝔭.valuation_surjective ℚ) (Rat.surjective_padicValuation _)
  e.trans PadicInt.withValIntegersUniformEquiv

universe u v

-- TODO : move
@[simps!]
def _root_.RingEquiv.restrict {R : Type u} {S : Type v} [NonAssocSemiring R] [NonAssocSemiring S]
    {σR : Type*} {σS : Type*} [SetLike σR R] [SetLike σS S] [SubsemiringClass σR R]
    [SubsemiringClass σS S] (f : R ≃+* S) (s' : σR) (s : σS) (h : ∀ x, x ∈ s' ↔ f x ∈ s) :
    s' ≃+* s where
  __ := RingHom.restrict f _ _ fun _ ↦ (h _).1
  invFun := RingHom.restrict f.symm _ _ fun y hy ↦ by
    obtain ⟨x, rfl⟩ := f.surjective y; simp [(h _).2 hy]
  left_inv y := by simp [← Subtype.val_inj]
  right_inv x := by simp [← Subtype.val_inj]

-- TODO : move
open scoped Valued in
noncomputable def _root_.PadicInt.withValIntegersRingEquiv {p : ℕ} [Fact p.Prime] :
    𝒪[(Rat.padicValuation p).Completion] ≃+* ℤ_[p] :=
  Padic.withValRingEquiv.restrict _ (PadicInt.subring p) fun _ ↦
    (Padic.withValUniformEquiv_norm_le_one_iff _).symm

noncomputable def adicCompletionIntegers.padicIntRingEquiv {R : Type*} [CommRing R]
    [IsDedekindDomain R] [Algebra R ℚ] [IsFractionRing R ℚ] [Nonempty (R ≃+* ℤ)]
    (𝔭 : HeightOneSpectrum R) :
    𝔭.adicCompletionIntegers ℚ ≃+* ℤ_[𝔭] :=
  let e : 𝔭.adicCompletionIntegers ℚ ≃+*
      (Valued.v.valuationSubring : ValuationSubring (Rat.padicValuation 𝔭).Completion) :=
    (UniformSpace.Completion.mapRingEquiv _ 𝔭.valuationEquivPadicValuation.uniformContinuous
      𝔭.valuationEquivPadicValuation.symm.uniformContinuous).restrict _ _ fun _ ↦ by
      simpa using 𝔭.valuation_equiv_padicValuation.valuedCompletion_le_one_iff
        (𝔭.valuation_surjective ℚ) (Rat.surjective_padicValuation _)
  e.trans PadicInt.withValIntegersRingEquiv

theorem adicCompletion.padicAlgEquiv_bijOn {R : Type*} [CommRing R]
    [IsDedekindDomain R] [Algebra R ℚ] [IsFractionRing R ℚ] [Nonempty (R ≃+* ℤ)]
    (𝔭 : HeightOneSpectrum R) :
    Set.BijOn (padicAlgEquiv 𝔭) (𝔭.adicCompletionIntegers ℚ) (PadicInt.subring 𝔭) := by
  refine ⟨?_, (padicAlgEquiv 𝔭).injective.injOn, ?_⟩
  · intro x hx
    simp
    change ‖(adicCompletionIntegers.padicIntRingEquiv 𝔭 ⟨x, hx⟩)‖ ≤ 1
    exact PadicInt.norm_le_one ((adicCompletionIntegers.padicIntRingEquiv 𝔭) ⟨x, hx⟩)
  · have := (adicCompletionIntegers.padicIntRingEquiv 𝔭).surjective
    intro y hy
    obtain ⟨x, hx⟩ := this ⟨y, hy⟩
    use x
    use x.2
    change (adicCompletionIntegers.padicIntRingEquiv 𝔭 x) = y
    rw [hx]

instance : Nonempty (𝓞 ℚ ≃+* ℤ) := ⟨Rat.ringOfIntegersEquiv⟩

instance {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation ℚ Γ₀} :
    Nonempty (𝓞 (WithVal v) ≃+* ℤ) := ⟨Rat.ringOfIntegersWithValEquiv v⟩

noncomputable example (𝔭 : HeightOneSpectrum (𝓞 ℚ)) : 𝔭.adicCompletion ℚ ≃ᵤ ℚ_[𝔭] :=
  adicCompletion.padicUniformEquiv 𝔭

noncomputable example (𝔭 : HeightOneSpectrum (𝓞 ℚ)) : CompactSpace (𝔭.adicCompletionIntegers ℚ) :=
  (adicCompletionIntegers.padicIntUniformEquiv 𝔭).toHomeomorph.symm.compactSpace

end IsDedekindDomain.HeightOneSpectrum
