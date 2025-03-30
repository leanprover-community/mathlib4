/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Int.Basic
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.WithZeroMulInt
import Mathlib.Topology.IsLocalHomeomorph

/-!
# The height one spectrum of `ℤ`

## Main results
- `Int.heightOneSpectrumEquiv`: The height one spectrum of `ℤ` is in bijection with primes in `ℕ`.
- `Padic.ofAdicCompletion`: The canonical map from the completion of `ℚ` at a finite place
  corresponding to `p : ℕ` to `ℚ_[p]`.
- `Padic.isHomeomorph_ofAdicCompletion`: The map above is a homeomorphism.
- `Padic.comap_ofAdicCompletion_subring`: The map above maps `𝒪` onto `ℤ_[p]`.

-/

open IsDedekindDomain HeightOneSpectrum

/-- The height one spectrum of `ℤ` is in bijection with primes in `ℕ`. -/
@[simps]
noncomputable
def Int.heightOneSpectrumEquiv : HeightOneSpectrum ℤ ≃ { p : ℕ // p.Prime } where
  toFun p := ⟨(Submodule.IsPrincipal.generator p.asIdeal).natAbs, by
    rw [← Int.prime_iff_natAbs_prime, ← Ideal.span_singleton_prime, Ideal.span_singleton_generator]
    · infer_instance
    · rw [ne_eq, ← Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero]
      exact p.3⟩
  invFun n := ⟨Ideal.span {(n : ℤ)}, by
    rw [Ideal.span_singleton_prime (by exact_mod_cast n.2.ne_zero), ← Nat.prime_iff_prime_int]
    exact n.2, by simpa using n.2.ne_zero⟩
  left_inv p := by
    ext1
    simp only [span_natAbs, Ideal.span_singleton_generator]
  right_inv n := by
    ext
    simpa only [Ideal.span_singleton_eq_span_singleton, Int.associated_iff_natAbs] using
      Ideal.span_singleton_generator (Ideal.span {(n : ℤ)})

/-- The maximal ideal (`span {n}`) associated to a prime `p : ℕ`. -/
@[simps! asIdeal]
noncomputable
def Nat.toHeightOneSpectrum (p : ℕ) [Fact p.Prime] : HeightOneSpectrum ℤ :=
  Int.heightOneSpectrumEquiv.symm ⟨p, Fact.out⟩

lemma Nat.intValuation_toHeightOneSpectrum (p : ℕ) [Fact p.Prime] {n : ℤ} (hn : n ≠ 0) :
    p.toHeightOneSpectrum.intValuation n = Multiplicative.ofAdd (-padicValInt p n : ℤ) := by
  classical
  rw [intValuation_apply, intValuationDef_if_neg _ hn,
    count_associates_factors_eq (by simpa) inferInstance p.toHeightOneSpectrum.3,
    Nat.toHeightOneSpectrum_asIdeal,
    count_span_normalizedFactors_eq hn (by rw [← Nat.prime_iff_prime_int]; exact Fact.out),
    padicValInt.of_ne_one_ne_zero ‹Fact p.Prime›.out.ne_one hn]
  congr 4
  apply ENat.coe_inj.mp
  rw [← UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors _ hn,
    FiniteMultiplicity.emultiplicity_eq_multiplicity]
  · exact padicValRat.finite_int_prime_iff.mpr hn
  · rw [UniqueFactorizationMonoid.irreducible_iff_prime, ← Nat.prime_iff_prime_int]; exact Fact.out

lemma Nat.valuation_toHeightOneSpectrum (p : ℕ) [Fact p.Prime] {r : ℚ} (hr : r ≠ 0) :
    p.toHeightOneSpectrum.valuation ℚ r = Multiplicative.ofAdd (-padicValRat p r) := by
  trans p.toHeightOneSpectrum.valuation ℚ (algebraMap ℤ ℚ r.num / algebraMap ℤ ℚ r.den)
  · simp [Rat.num_div_den]
  rw [map_div₀, valuation_of_algebraMap, valuation_of_algebraMap,
    intValuation_toHeightOneSpectrum, intValuation_toHeightOneSpectrum, ← WithZero.coe_div,
    ← ofAdd_sub, padicValRat_def, padicValInt, padicValInt, Int.natAbs_cast]
  · ring_nf
  · simp
  · simpa

@[simp]
lemma WithZero.coe_unitsWithZeroEquiv_symm {α : Type*} [Group α] (γ : α) :
    (WithZero.unitsWithZeroEquiv.symm γ : WithZero α) = (γ : WithZero α) := rfl

@[simp]
lemma WithVal.v_equiv {R Γ₀ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation R Γ₀) (x : R) :
    Valued.v ((WithVal.equiv v).symm x) = v x := rfl

/-- The canonical map from the abstract completion of `ℚ` at `p` to `ℚ_[p]`.
This is a homeomorphism, see `Padic.isHomeomorph_ofAdicCompletion`. -/
noncomputable
def Padic.ofAdicCompletion (p : ℕ) [Fact p.Prime] :
    p.toHeightOneSpectrum.adicCompletion ℚ →+* ℚ_[p] := by
  letI := p.toHeightOneSpectrum.adicValued (K := ℚ)
  refine UniformSpace.Completion.extensionHom (Rat.castHom _) ?_
  apply continuous_of_continuousAt_zero
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff Metric.nhds_basis_ball]
  intro ε hε
  obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p hε
  refine ⟨WithZero.unitsWithZeroEquiv.symm (Multiplicative.ofAdd (-k)), trivial, ?_⟩
  intro x hx
  obtain ⟨x, rfl⟩ := (WithVal.equiv _).symm.surjective x
  simp only [eq_ratCast, Metric.mem_ball, dist_zero_right, map_ratCast, padicNormE.eq_padicNorm]
  refine lt_of_le_of_lt ?_ hk
  rw [padicNorm]
  split_ifs with h
  · simp
  rw [Set.mem_setOf, WithVal.v_equiv, WithZero.coe_unitsWithZeroEquiv_symm,
    Nat.valuation_toHeightOneSpectrum _ h, WithZero.coe_lt_coe,
      Multiplicative.ofAdd_lt, neg_lt_neg_iff] at hx
  simp only [Rat.cast_inv, Rat.cast_zpow, Rat.cast_natCast, zpow_natCast]
  gcongr
  exact_mod_cast ‹Fact p.Prime›.1.one_le

@[fun_prop]
lemma Padic.continuous_ofAdicCompletion (p : ℕ) [Fact p.Prime] :
    Continuous (Padic.ofAdicCompletion p) :=
  letI := p.toHeightOneSpectrum.adicValued (K := ℚ)
  UniformSpace.Completion.continuous_extension

open Filter in
open WithZeroTopology in
lemma Padic.valuation_ofAdicCompletionofAdicCompletion (p : ℕ) [Fact p.Prime] (x) :
    ‖Padic.ofAdicCompletion p x‖ = WithZeroMulInt.toNNReal
      (Nat.cast_ne_zero.mpr ‹Fact p.Prime›.1.ne_zero) (Valued.v x) := by
  letI := p.toHeightOneSpectrum.adicValued (K := ℚ)
  have H : IsDenseEmbedding (Rat.cast (K := p.toHeightOneSpectrum.adicCompletion ℚ)) := by
    convert UniformSpace.Completion.isDenseEmbedding_coe (α := ℚ)
    ext
    exact (eq_ratCast UniformSpace.Completion.coeRingHom _).symm
  refine H.dense.induction ?_ ?_ x
  · rintro _ ⟨x, rfl⟩
    simp only [map_ratCast, padicNormE.eq_padicNorm, valuedAdicCompletion_def]
    rw [← eq_ratCast UniformSpace.Completion.coeRingHom x]
    simp only [padicNorm, WithZeroMulInt.toNNReal, WithVal, UniformSpace.Completion.coeRingHom,
      RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Valued.extension_extends, adicValued_apply,
      MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, map_eq_zero]
    split_ifs with h
    · simp
    · simp only [Rat.cast_zpow, Rat.cast_natCast, NNReal.coe_zpow, NNReal.coe_natCast]
      congr 1
      apply Multiplicative.ofAdd.injective
      apply WithZero.coe_inj.mp
      simp only [WithZero.coe_inv, ofAdd_toAdd, WithZero.coe_unzero,
        ← Nat.valuation_toHeightOneSpectrum _ h, adicValued_apply]
  · apply isClosed_eq
    · fun_prop
    · refine continuous_subtype_val.comp ?_
      refine (WithZeroMulInt.continuous_toNNReal ?_).comp Valued.continuous_extension
      exact_mod_cast ‹Fact p.Prime›.1.one_lt

lemma Padic.isHomeomorph_ofAdicCompletion (p : ℕ) [Fact p.Prime] :
    IsHomeomorph (Padic.ofAdicCompletion p) := by
  letI := p.toHeightOneSpectrum.adicValued (K := ℚ)
  have := algebraRat.charZero (adicCompletion ℚ p.toHeightOneSpectrum)
  letI h : (Valued.v (R := p.toHeightOneSpectrum.adicCompletion ℚ)).RankOne :=
  { hom := WithZeroMulInt.toNNReal (Nat.cast_ne_zero.mpr ‹Fact p.Prime›.1.ne_zero)
    strictMono' := WithZeroMulInt.toNNReal_strictMono (by simpa using ‹Fact p.Prime›.1.one_lt)
    nontrivial' :=
    ⟨UniformSpace.Completion.coeRingHom (α := ℚ) p,
    by simpa using ‹Fact p.Prime›.1.ne_zero, by
      simp only [UniformSpace.Completion.coeRingHom,
        RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, valuedAdicCompletion_def,
        Valued.extension_extends]
      show p.toHeightOneSpectrum.valuation ℚ (p : ℚ) ≠ 1
      rw [p.valuation_toHeightOneSpectrum (by exact_mod_cast ‹Fact p.Prime›.1.ne_zero)]
      simp only [padicValRat.of_nat, padicValNat_self, Nat.cast_one, Int.reduceNeg, ←
        WithZero.coe_one, ne_eq, WithZero.coe_inj]
      rw [← Multiplicative.toAdd.injective.eq_iff]
      simp⟩ }
  letI := Valued.toNormedField (p.toHeightOneSpectrum.adicCompletion ℚ) _
  have : Isometry (Padic.ofAdicCompletion p) := by
    apply AddMonoidHomClass.isometry_of_norm
    exact fun _ ↦ Padic.valuation_ofAdicCompletionofAdicCompletion _ _
  refine (this.isEmbedding.toHomeomorph_of_surjective ?_).isHomeomorph
  rw [← Set.range_eq_univ, ← Set.univ_subset_iff, ← (Padic.denseRange_ratCast p).closure_eq,
    this.isClosedEmbedding.isClosed_range.closure_subset_iff]
  rintro _ ⟨x, rfl⟩
  exact ⟨x, by simp⟩

lemma Padic.comap_ofAdicCompletion_subring (p : ℕ) [Fact p.Prime] :
    (PadicInt.subring p).comap (Padic.ofAdicCompletion p) =
      (p.toHeightOneSpectrum.adicCompletionIntegers ℚ).toSubring := by
  have : 1 < (p : NNReal) := by simpa using ‹Fact p.Prime›.1.one_lt
  ext x
  simp [mem_adicCompletionIntegers, Padic.valuation_ofAdicCompletionofAdicCompletion,
    WithZeroMulInt.toNNReal_le_one_iff this]

/-- The canonical map from the abstract adic completion of `ℤ` at `p` to `ℚ_[p]`.
This is a homeomorphism, see `PadicInt.isHomeomorph_adicCompletionIntegers`. -/
noncomputable
def PadicInt.ofAdicCompletionIntegers (p : ℕ) [Fact p.Prime] :
    p.toHeightOneSpectrum.adicCompletionIntegers ℚ →+* ℤ_[p] :=
  (Padic.ofAdicCompletion p).restrict _ (PadicInt.subring p)
    (Padic.comap_ofAdicCompletion_subring p).ge

lemma PadicInt.isHomeomorph_adicCompletionIntegers (p : ℕ) [Fact p.Prime] :
    IsHomeomorph (ofAdicCompletionIntegers p) := by
  refine (Topology.IsEmbedding.toHomeomorph_of_surjective ?_ ?_).isHomeomorph
  · refine .of_comp ?_ continuous_subtype_val ?_
    · dsimp; fun_prop
    · exact (Padic.isHomeomorph_ofAdicCompletion p).isEmbedding.comp .subtypeVal
  · intro ⟨x, hx⟩
    obtain ⟨x, rfl⟩ := (Padic.isHomeomorph_ofAdicCompletion p).surjective x
    exact ⟨⟨x, (Padic.comap_ofAdicCompletion_subring p).le hx⟩, Subtype.ext rfl⟩
