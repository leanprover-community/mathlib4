module

public import Mathlib.Misc
public import Mathlib.GalCyclotomic
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.NumberTheory.NumberField.Ideal.Basic

section IsPrimitiveRoot

open NumberField Ideal

theorem IsPrimitiveRoot.idealQuotient_mk {K : Type*} [Field K] {I : Ideal (𝓞 K)} [NumberField K]
    {n : ℕ} [NeZero n] {ζ : (𝓞 K)} (hζ : IsPrimitiveRoot ζ n) (hI₁ : absNorm I ≠ 1)
    (hI₂ : (absNorm I).Coprime n) : IsPrimitiveRoot (Ideal.Quotient.mk I ζ) n := by
  have h : IsPrimitiveRoot hζ.toRootsOfUnity n :=
    IsPrimitiveRoot.coe_submonoidClass_iff.mp <| IsPrimitiveRoot.coe_units_iff.mp hζ
  exact IsPrimitiveRoot.coe_units_iff.mpr <|
    h.map_of_injective <| Ideal.rootsOfUnityMapQuot_injective n hI₁ hI₂

end IsPrimitiveRoot
section FiniteField

open FiniteField

@[simp]
theorem FiniteField.Extension.frob_iterate_apply (k : Type*) [Field k] [Finite k] (p : ℕ)
    [Fact (Nat.Prime p)] [CharP k p] (n i : ℕ) [NeZero n] {x : Extension k p n} :
    (frob k p n)^[i] x = x ^ (Nat.card k ^ i) := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [Function.iterate_add_apply, Function.iterate_one, frob_apply, iterate_map_pow, ih,
        ← pow_mul, ← Nat.pow_succ]

variable (k : Type*) [Field k] [Finite k] (p : ℕ) [Fact (Nat.Prime p)] [CharP k p] (l : Type*)
    [Field l] [Algebra k l] [Finite l]

include p in
theorem toto (g : Gal(l/k)) :
    ∃ i, ∀ x, g x = x ^ (Nat.card k ^ i) := by
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank k l = n := exists_eq'
  have : NeZero n := hn ▸ NeZero.of_pos Module.finrank_pos
  let τ := (algEquivExtension k p n l hn).symm.trans (g.trans (algEquivExtension k p n l hn))
  obtain ⟨i, _, hi⟩ := Extension.exists_frob_pow_eq k p n τ
  refine ⟨i, fun x ↦ ?_⟩
  convert (AlgEquiv.congr_arg (f := (algEquivExtension k p n l hn).symm) <|
    AlgEquiv.congr_fun hi (algEquivExtension k p n l hn x)).symm
  · simp [τ]
  · simp

end FiniteField

open NumberField IsCyclotomicExtension Rat RingOfIntegers Pointwise Ideal

variable {m : ℕ} (p : ℕ) [hp : Fact (Nat.Prime p)] (K : Type*) [Field K] [NumberField K]
  (P : Ideal (𝓞 K)) [hP₁ : P.IsMaximal] [hP₂ : P.LiesOver (Ideal.span {(p : ℤ)})] [NeZero m]
  [hK : IsCyclotomicExtension {m} ℚ K] (hm : p.Coprime m)

attribute [local instance] Ideal.Quotient.field

theorem step1 (σ : Gal(K/ℚ)) (hσ : σ • P = P) :
    galEquiv m K σ ∈ Subgroup.zpowers (ZMod.unitOfCoprime p hm) := by
  have hζ := IsCyclotomicExtension.zeta_spec m ℚ K
  let 𝕜 := (𝓞 K) ⧸ P
  let τ := IsFractionRing.stabilizerHom Gal(K/ℚ) (Ideal.span {(p : ℤ)}) P
     (ℤ ⧸ span {(p : ℤ)}) 𝕜 ⟨σ, hσ⟩
  obtain ⟨i, hi⟩ := toto (ℤ ⧸ span {(p : ℤ)}) p 𝕜 τ
  refine ⟨i, ?_⟩
  dsimp only
  have t₁ := hi (Ideal.Quotient.mk P hζ.toInteger)
  simp only [τ] at t₁
  have t₂ := IsFractionRing.stabilizerHom_apply_apply_mk Gal(K/ℚ) (Ideal.span {(p : ℤ)}) P
    (ℤ ⧸ span {(p : ℤ)}) 𝕜 ⟨σ, hσ⟩ hζ.toInteger
  simp only [Algebra.algebraMap_self, RingHomCompTriple.comp_apply, 𝕜] at t₂
  have t₃ := hζ.toInteger_isPrimitiveRoot.idealQuotient_mk (I := P) ?_ ?_
  · rw [t₂] at t₁
    rw [galEquiv_smul_of_pow_eq m, map_pow, IsOfFinOrder.pow_inj_mod] at t₁
    · rw [zpow_natCast]
      rw [Units.ext_iff]
      simp only [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime]
      rw [← t₃.eq_orderOf] at t₁
      rw [Int.card_ideal_quot] at t₁
      rw [← ZMod.natCast_eq_natCast_iff'] at t₁
      simp at t₁
      exact t₁.symm
    · apply IsPrimitiveRoot.isOfFinOrder t₃
    · exact hζ.toInteger_isPrimitiveRoot.pow_eq_one
  · rw [Ne.eq_def, absNorm_eq_one_iff]
    exact IsPrime.ne_top'
  · rw [Ideal.absNorm_eq_pow_inertiaDeg' _ hp.out]
    apply Nat.Coprime.pow_left
    exact hm

theorem galEquiv_stabilizer :
    (galEquiv m K).mapSubgroup (MulAction.stabilizer Gal(K/ℚ) P) =
      Subgroup.zpowers (ZMod.unitOfCoprime p hm) := by
  classical
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {m} ℚ K
  rw [SetLike.ext'_iff]
  apply Set.eq_of_subset_of_card_le
  · rintro _ ⟨σ, hσ, rfl⟩
    exact step1 p K P hm σ hσ
  · rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
    erw [Nat.card_zpowers]
    rw [MulEquiv.mapSubgroup_apply, Subgroup.coe_map]
    erw [Nat.card_image_equiv]
    have := Ideal.card_stabilizer (span {(p : ℤ)}) P Gal(K/ℚ) (by simp [hp.out.ne_zero])
    erw [this]
    rw [inertiaDegIn_eq_of_not_dvd p K (m := m), ramificationIdxIn_eq_of_not_dvd p K (m := m),
      one_mul]
    rw [← orderOf_injective _ Units.coeHom_injective]
    simp only [Units.coeHom_apply, ZMod.coe_unitOfCoprime, le_refl]
    · rwa [← Nat.Prime.coprime_iff_not_dvd hp.out]
    · rwa [← Nat.Prime.coprime_iff_not_dvd hp.out]








#exit


  have := IsFractionRing.stabilizerHom_surjective Gal(K/ℚ) (Ideal.span {(p : ℤ)}) P
    (ℤ ⧸ span {(p : ℤ)}) 𝕜


  have :=  Ideal.Quotient.exists_algEquiv_fixedPoint_quotient_under Gal(K/ℚ)
    (Ideal.span {(p : ℤ)}) P

  let 𝕜 := (𝓞 K) ⧸ P
  let : Field 𝕜 := Ideal.Quotient.field P
  have : CharP 𝕜 p := by
    refine ringChar.of_eq ?_
    convert Ideal.ringChar_quot P
    rw [liesOver_iff] at hP₂
    rw [← hP₂]
    simp
  let : Algebra (ZMod p) 𝕜 := ZMod.algebra 𝕜 p
  let τ : Gal(𝕜/(ZMod p)) := sorry
  have {x} : τ x = x ^ (galEquiv m K σ).val.val := sorry


#exit

open Polynomial in
example : (galEquiv m K).symm (ZMod.unitOfCoprime p hm) • P = P := by
  let ζ := (zeta_spec m ℚ K).toInteger
  have h₁ : ¬ p ∣ exponent ζ := by
    rw [exponent_eq_one_iff.mpr <| adjoin_singleton_eq_top (zeta_spec m ℚ K)]
    exact hp.out.not_dvd_one
  let zQ := ↑((primesOverSpanEquivMonicFactorsMod h₁) ⟨P, ⟨inferInstance, inferInstance⟩⟩).1
  let Q := zQ.sum fun i r ↦ C (ZMod.cast r) * (X : Polynomial ℤ) ^ i
  have h₂ : Q.map (Int.castRingHom (ZMod p)) = zQ := sorry
  have h₃ : map (Int.castRingHom (ZMod p)) Q ∈ monicFactorsMod ζ p := by
    unfold Q
    rw [sum, Polynomial.map_sum]
    simp_rw [Polynomial.map_mul, map_C, Polynomial.map_pow, map_X, eq_intCast, ZMod.intCast_cast,
      ZMod.cast_id, ← as_sum_support_C_mul_X_pow]
    exact (primesOverSpanEquivMonicFactorsMod h₁ ⟨P, ⟨inferInstance, inferInstance⟩⟩).2
  have h₄ := primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span h₁ h₃
  simp [h₂, zQ] at h₄
  rw [h₄]




#exit

variable (α : Type*) {β : Type*} [Group α] [MulAction α β] (b : β)

@[to_additive (attr := simp)]
theorem MulAction.orbitProdStabilizerEquivGroup_symm_apply_fst (α : Type*) {β : Type*} [Group α]
    [MulAction α β] (b : β) (a : α) :
    ((MulAction.orbitProdStabilizerEquivGroup α b).symm a).1 = a • b := rfl

@[to_additive (attr := simp)]
theorem MulAction.orbitProdStabilizerEquivGroup_apply_smul (x : orbit α b) (y : stabilizer α b) :
    MulAction.orbitProdStabilizerEquivGroup α b (x, y) • b = x := by
  rw [← MulAction.orbitProdStabilizerEquivGroup_symm_apply_fst, Equiv.symm_apply_apply]
