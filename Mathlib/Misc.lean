import Mathlib.Data.Int.Star
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.NumberTheory.Cyclotomic.Rat
import Mathlib.Algebra.Group.NatPowAssoc
import Mathlib.Riccardo

theorem ZMod.orderOf_mod_self_pow_sub_one {n k : ℕ} (hn : 1 < n) (hk : 0 < k) :
    orderOf (n : ZMod (n ^ k - 1)) = k := by
  have : NeZero n := NeZero.of_gt hn
  refine (orderOf_eq_iff hk).mpr ⟨?_, fun m hm₁ hm₂ ↦ ?_⟩
  · rw [← Nat.cast_npow, ← sub_eq_zero, ← Nat.cast_one (R := ZMod (n ^ k - 1)),
      ← Nat.cast_sub NeZero.one_le]
    exact ZMod.natCast_self _
  · rw [ne_eq, ← Nat.cast_npow, ← sub_eq_zero, ← Nat.cast_one (R := ZMod (n ^ k - 1)),
      ← Nat.cast_sub NeZero.one_le, ZMod.natCast_eq_zero_iff]
    refine (Nat.le_of_dvd ?_).mt (not_le.mpr ?_)
    · exact Nat.zero_lt_sub_of_lt <| Nat.one_lt_pow hm₂.ne' hn
    · exact Nat.sub_lt_sub_iff_right NeZero.one_le (c := 1).mpr <| Nat.pow_lt_pow_right hn hm₁

open Polynomial in
theorem Polynomial.cyclotomic_eq_minpoly' (n : ℕ) (R : Type*) [CommRing R] [IsDomain R]
    [CharZero R] {μ : R} (h : IsPrimitiveRoot μ n) (hpos : 0 < n) :
    cyclotomic n ℤ = minpoly ℤ μ := by
  have h' : IsPrimitiveRoot (algebraMap R (FractionRing R) μ) n :=
    h.map_of_injective <| FaithfulSMul.algebraMap_injective R _
  apply map_injective (algebraMap ℤ ℚ) <| RingHom.injective_int _
  rw [← @minpoly.isIntegrallyClosed_eq_field_fractions ℤ R _ _ _ _ ℚ (FractionRing R) _ _
    _ _ _ _ _ _ ?_ _ _ _ μ (h.isIntegral hpos), ← cyclotomic_eq_minpoly_rat h' hpos, map_cyclotomic]
  -- We need to do that because of the `zsmul` diamond, see the discussion
  -- "Instance diamond in `OreLocalization`" on Zulip
  convert AddCommGroup.intIsScalarTower (R := ℚ) (M := FractionRing R) using 1
  ext n x
  exact OreLocalization.zsmul_eq_zsmul n x

@[simp]
lemma RingHom.rangeRestrict_injective_iff {R S : Type*} [Ring R] [Ring S] {f : R →+* S} :
    Function.Injective f.rangeRestrict ↔ Function.Injective f := by
  convert Set.injective_codRestrict _

@[to_additive]
theorem MonoidAlgebra.single_sub {R M : Type*} [Ring R] (a : M) (b₁ b₂ : R) :
    single a (b₁ - b₂) = single a b₁ - single a b₂ :=
  Finsupp.single_sub _ _ _

@[to_additive (attr := simp)]
theorem MonoidAlgebra.fintype_sum_single {k G : Type*} [Fintype G] [Semiring k]
    (f : MonoidAlgebra k G) : ∑ g : G, single g (f g) = f := by
  classical
  rw [← sum_single f, Finsupp.sum_fintype]
  · conv_lhs =>
      enter [2, g, 2]
      rw [Finset.sum_apply']
      simp [single_apply]
  · intro _
    simp

open NumberField RingOfIntegers in
theorem IsCyclotomicExtension.Rat.inertiaDeg_of_coprime (m : ℕ) [NeZero m] {K : Type*}
    [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K] (p : ℕ) [hp : Fact (p.Prime)]
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] (hm : p.Coprime m) :
    (Ideal.span {(p : ℤ)}).inertiaDeg P = orderOf (p : ZMod m) := by
  let ζ := (IsCyclotomicExtension.zeta_spec m ℚ K).toInteger
  have h₁ : exponent ζ = 1 := by
    rw [exponent_eq_one_iff]
    exact IsCyclotomicExtension.Rat.adjoin_singleton_eq_top m K _
  have h₂ : ¬ p ∣ exponent ζ := by
    rw [h₁]
    exact hp.out.not_dvd_one
  let hQ := Ideal.primesOverSpanEquivMonicFactorsMod h₂ ⟨P, ⟨inferInstance, inferInstance⟩⟩
  have := Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' h₂ hQ.2
  simp only [Subtype.coe_eta, Equiv.symm_apply_apply, hQ] at this
  rw [this]
  have h := hQ.2
  rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff] at h
  · rw [foo (p := p) (f := 1)]
    · simp
      exact (orderOf_injective _ Units.coeHom_injective (ZMod.unitOfCoprime p hm)).symm
    · simp
    · simpa
    · have := h.2.2
      refine dvd_trans this ?_
      rw [← Polynomial.map_cyclotomic_int]
      rw [← Polynomial.cyclotomic_eq_minpoly' m (𝓞 K) _ (NeZero.pos _)]
      exact IsPrimitiveRoot.toInteger_isPrimitiveRoot _
    · exact h.1
    · exact h.2.1
  · exact Polynomial.map_monic_ne_zero (minpoly.monic ζ.isIntegral)
