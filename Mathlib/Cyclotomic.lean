module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
public import Mathlib.Misc
public import Mathlib.NumberTheory.Cyclotomic.Gal

@[expose] public section

noncomputable section

variable (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
  [hK : IsCyclotomicExtension {n} ℚ K]

-- abbrev galChar := MulChar Gal(K/ℚ) ℂ

-- def galPairing : Gal(K/ℚ) → galChar K → ℂ := fun σ χ ↦ χ σ

-- def galPairing_left_perp (L : IntermediateField ℚ K) : Subgroup (galChar K) := by

--   let G := L.fixingSubgroup




namespace IsCyclotomicExtension.Rat

open NumberField Ideal Pointwise RingOfIntegers

include hK in
def galEquiv : Gal(K/ℚ) ≃* (ZMod n)ˣ :=
  IsCyclotomicExtension.autEquivPow K <|
      Polynomial.cyclotomic.irreducible_rat (NeZero.pos n)

theorem galEquiv_apply_of_pow_eq (σ : Gal(K/ℚ)) {x : K} (hx : x ^ n = 1) :
    σ x = x ^ (galEquiv n K σ).val.val := by
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ K
  obtain ⟨a, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
  rw [map_pow, pow_right_comm, galEquiv, IsCyclotomicExtension.autEquivPow_apply,
    OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, IsPrimitiveRoot.autToPow_spec]

theorem galEquiv_smul_of_pow_eq (σ : Gal(K/ℚ)) {x : 𝓞 K} (hx : x ^ n = 1) :
    σ • x = x ^ (galEquiv n K σ).val.val := by
  apply FaithfulSMul.algebraMap_injective (𝓞 K) K
  apply galEquiv_apply_of_pow_eq n K σ <| by rw [← Subalgebra.coe_pow, hx, OneMemClass.coe_one]

example (p : ℕ) [hp : Fact (Nat.Prime p)] (hp' : p.Coprime n) (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (span {(p : ℤ)})] (σ : Gal(K/ℚ)) :
    σ • P = P ↔ galEquiv n K σ ∈ Subgroup.zpowers (ZMod.unitOfCoprime p hp') := by
  let ζ := (zeta_spec n ℚ K).toInteger
  have h₁ : ¬ p ∣ exponent ζ := by
    rw [exponent_eq_one_iff.mpr <| adjoin_singleton_eq_top (zeta_spec n ℚ K)]
    exact hp.out.not_dvd_one
  have h₂ := (primesOverSpanEquivMonicFactorsMod h₁ ⟨P, ⟨inferInstance, inferInstance⟩⟩).2

  have h₃ := primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span h₁ h₂
  simp only [Subtype.coe_eta, Equiv.symm_apply_apply] at h₃

  rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff
    (map_monic_ne_zero (minpoly.monic ζ.isIntegral))] at h₂
  rw [h₃, natDegree_of_dvd_cyclotomic_of_irreducible (by simp) hm (f := 1) _ h₂.1]
  · simpa using (orderOf_injective _ Units.coeHom_injective (ZMod.unitOfCoprime p hm)).symm
  · refine dvd_trans h₂.2.2 ?_
    rw [← map_cyclotomic_int, cyclotomic_eq_minpoly (zeta_spec m ℚ K) (NeZero.pos _),
      ← (zeta_spec m ℚ K).coe_toInteger, ← RingOfIntegers.minpoly_coe ζ]
    rfl
  sorry

variable {m : ℕ} [NeZero m] (F : Type*) [Field F] [NumberField F]
  [hF : IsCyclotomicExtension {m} ℚ F] [Algebra F K]

theorem galEquiv_restrictNormal_apply [IsGalois ℚ F] (h : m ∣ n) (σ : Gal(K/ℚ)) :
    galEquiv m F (σ.restrictNormal F) = ZMod.unitsMap h (galEquiv n K σ) := by
  let ζ := IsCyclotomicExtension.zeta m ℚ F
  have hζ := IsCyclotomicExtension.zeta_spec m ℚ F
  have : ζ ^ (galEquiv m F (σ.restrictNormal F)).val.val = ζ ^ (galEquiv n K σ).val.val := by
    apply FaithfulSMul.algebraMap_injective F K
    rw [map_pow, map_pow, ← galEquiv_apply_of_pow_eq, ← AlgEquiv.restrictNormal_commutes,
      galEquiv_apply_of_pow_eq m, map_pow]
    · exact hζ.pow_eq_one
    · rw [← map_pow, orderOf_dvd_iff_pow_eq_one.mp, map_one]
      rwa [← hζ.eq_orderOf]
  rw [hζ.isOfFinOrder.pow_inj_mod, ← hζ.eq_orderOf, ← ZMod.natCast_eq_natCast_iff'] at this
  simp only [ZMod.natCast_val, ZMod.cast_id', id_eq] at this
  rwa [Units.ext_iff]

theorem galEquiv_restrictNormal [IsGalois ℚ F] (h : m ∣ n) :
    (galEquiv m F).toMonoidHom.comp (AlgEquiv.restrictNormalHom F) =
      (ZMod.unitsMap h).comp (galEquiv n K).toMonoidHom :=
  MonoidHom.ext fun σ ↦ galEquiv_restrictNormal_apply n K F h σ



end IsCyclotomicExtension.Rat

#exit

theorem IsCyclotomicExtension_single_iff_single_two_mul_of_odd (n : ℕ) (hn : Odd n)
    (A B : Type*) [CommRing A] [CommRing B] [Nontrivial B] [NoZeroDivisors B] [Algebra A B]
    (hB : ringChar B ≠ 2) :
    IsCyclotomicExtension {n} A B ↔ IsCyclotomicExtension {2 * n} A B := by
  have : NeZero n := by
    refine ⟨?_⟩
    exact Nat.ne_of_odd_add hn
  have h : orderOf (-1 : B) = 2 := by
    rw [orderOf_neg_one, if_neg hB]
  rw [IsCyclotomicExtension.iff_singleton, IsCyclotomicExtension.iff_singleton]
  congr! 1
  · refine ⟨?_, ?_⟩
    · intro ⟨ζ, hζ⟩
      refine ⟨-ζ, ?_⟩
      convert IsPrimitiveRoot.orderOf (-ζ)
      rw [neg_eq_neg_one_mul, (Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime]
      · rw [h, hζ.eq_orderOf]
      · rw [h, ← hζ.eq_orderOf]
        exact Nat.coprime_two_left.mpr hn
    · intro ⟨ζ, hζ⟩
      exact ⟨ζ ^ 2, hζ.pow (NeZero.pos _) rfl⟩
  · suffices Algebra.adjoin A {b : B | b ^ n = 1} = Algebra.adjoin A {b : B | b ^ (2 * n) = 1} by
      rw [SetLike.ext_iff] at this
      exact forall_congr' this
    apply le_antisymm
    · apply Algebra.adjoin_mono
      intro b hb
      rw [Set.mem_setOf_eq, mul_comm, pow_mul, hb, one_pow]
    · apply Algebra.adjoin_le
      intro b hb
      rw [Set.mem_setOf_eq, mul_comm, pow_mul, sq_eq_one_iff] at hb
      obtain hb | hb := hb
      · apply Algebra.subset_adjoin
        exact hb
      · simp only [SetLike.mem_coe]
        rw [show b = - - b by exact Eq.symm (InvolutiveNeg.neg_neg b)]
        apply Subalgebra.neg_mem
        apply Algebra.subset_adjoin
        rw [Set.mem_setOf_eq, neg_pow, Odd.neg_one_pow hn, neg_mul, one_mul, hb, neg_neg]

-- Golf `IsCyclotomicExtension.of_union_of_dvd` using this
theorem IsCyclotomicExtension.exists_isPrimitiveRoot_of_dvd {n : ℕ} [NeZero n] {S : Set ℕ}
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] (h : ∃ s ∈ S, s ≠ 0 ∧ n ∣ s)
    [H : IsCyclotomicExtension S A B] :
    ∃ (r : B), IsPrimitiveRoot r n := by
  obtain ⟨m, hm, hm', ⟨x, rfl⟩⟩ := h
  obtain ⟨ζ, hζ⟩ := H.exists_isPrimitiveRoot hm hm'
  refine ⟨ζ ^ x, ?_⟩
  have h_xnz : x ≠ 0 := Nat.ne_zero_of_mul_ne_zero_right hm'
  have := hζ.pow_of_dvd h_xnz (dvd_mul_left x n)
  rwa [mul_div_cancel_right₀ _ h_xnz] at this

open NumberField Units

theorem NumberField.Units.mem_torsion' (K : Type*) [Field K] [NumberField K]
    {x : (𝓞 K)ˣ} :
    x ∈ torsion K ↔ IsOfFinOrder x := CommGroup.mem_torsion _ _

theorem NumberField.dvd_torsionOrder_of_isPrimitiveRoot {n : ℕ} [NeZero n] {K : Type*} [Field K]
    [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    n ∣ torsionOrder K := by
  sorry
  -- rw [torsionOrder, Fintype.card_eq_nat_card]
  -- replace hζ := (hζ.toInteger_isPrimitiveRoot).isUnit_unit (NeZero.ne n)
  -- have hζ' := CommGroup.mem_torsion_of_isPrimitiveRoot n hζ
  -- convert orderOf_dvd_natCard (⟨_, hζ'⟩ : torsion K)
  -- rw [Subgroup.orderOf_mk]
  -- exact hζ.eq_orderOf

theorem NumberField.Units.torsionOrder_eq_of_isCyclotomicExtension (n : ℕ) [NeZero n] {K : Type*}
    [Field K] [NumberField K] [hK : IsCyclotomicExtension {n} ℚ K] :
    torsionOrder K = if Even n then n else 2 * n := by
  sorry
  -- have hζ := hK.zeta_spec
  -- obtain ⟨μ, hμ⟩ : ∃ μ : torsion K, orderOf μ = torsionOrder K := by
  --   rw [torsionOrder, Fintype.card_eq_nat_card]
  --   exact IsCyclic.exists_ofOrder_eq_natCard
  -- rw [← IsPrimitiveRoot.iff_orderOf, ← IsPrimitiveRoot.coe_submonoidClass_iff,
  --   ← IsPrimitiveRoot.coe_units_iff] at hμ
  -- replace hμ := hμ.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  -- have h := IsPrimitiveRoot.pow_mul_pow_lcm hζ hμ (NeZero.ne _) (torsionOrder_ne_zero K)
  -- have : NeZero (n.lcm (torsionOrder K)) :=
  --   NeZero.of_pos <| Nat.lcm_pos_iff.mpr ⟨NeZero.pos n, torsionOrder_pos K⟩
  -- have : IsCyclotomicExtension {n.lcm (torsionOrder K)} ℚ K := by
  --   have := hK.union_of_isPrimitiveRoot _ _ _ h
  --   rwa [Set.union_comm, ← IsCyclotomicExtension.iff_union_of_dvd] at this
  --   exact ⟨n.lcm (torsionOrder K), by simp, NeZero.ne _, Nat.dvd_lcm_left _ _⟩
  -- have hmain := (IsCyclotomicExtension.Rat.finrank n K).symm.trans <|
  --   (IsCyclotomicExtension.Rat.finrank (n.lcm (torsionOrder K)) K)
  -- obtain hn | hn := Nat.even_or_odd n
  -- · rw [if_pos hn]
  --   apply dvd_antisymm
  --   · have := Nat.eq_of_totient_eq_totient (Nat.dvd_lcm_left _ _) hn hmain
  --     rwa [eq_comm, Nat.lcm_eq_left_iff_dvd] at this
  --   · exact NumberField.dvd_torsionOrder_of_isPrimitiveRoot hζ
  -- · rw [if_neg (Nat.not_even_iff_odd.mpr hn)]
  --   have := (Nat.eq_or_eq_of_totient_eq_totient (Nat.dvd_lcm_left _ _) hmain).resolve_left ?_
  --   · rw [this, eq_comm, Nat.lcm_eq_right_iff_dvd]
  --     exact NumberField.dvd_torsionOrder_of_isPrimitiveRoot hζ
  --   · rw [eq_comm, Nat.lcm_eq_left_iff_dvd]
  --     intro h
  --     exact Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hn h) (even_torsionOrder K)
