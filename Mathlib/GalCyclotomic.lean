module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
public import Mathlib.Duality
public import Mathlib.Misc
public import Mathlib.NumberTheory.Cyclotomic.Gal
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.FieldTheory.PrimeField

@[expose] public section

noncomputable section

namespace IsCyclotomicExtension.Rat

variable (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
  [hK : IsCyclotomicExtension {n} ℚ K] (R : Type*) [CommRing R] [IsDomain R]
  [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ)] -- replace by φ n ?

open NumberField Ideal Pointwise RingOfIntegers MulChar

def subgroupGalEquivDirichletCharSubgroup :
    Subgroup Gal(K/ℚ) ≃o (Subgroup (DirichletCharacter R n))ᵒᵈ :=
  (galEquivZMod n K).mapSubgroup.trans <| subgroupOrderIsoSubgroupMulChar (ZMod n) R

@[simp]
theorem mem_subgroupGalEquivDirichletCharSubgroup_iff (χ : DirichletCharacter R n)
    (H : Subgroup Gal(K/ℚ)) :
    χ ∈ (subgroupGalEquivDirichletCharSubgroup n K R H).ofDual ↔
      ∀ σ ∈ H, χ (galEquivZMod n K σ) = 1 := by simp [subgroupGalEquivDirichletCharSubgroup]

@[simp]
theorem mem_subgroupGalEquivDirichletCharSubgroup_symm_iff (σ : Gal(K/ℚ))
    (Y : Subgroup (DirichletCharacter R n)) :
    σ ∈ (subgroupGalEquivDirichletCharSubgroup n K R).symm (OrderDual.toDual Y) ↔
      ∀ χ ∈ Y, χ (galEquivZMod n K σ) = 1 := by
  unfold subgroupGalEquivDirichletCharSubgroup
  simp only [OrderIso.symm_trans_apply, MulEquiv.symm_mapSubgroup, MulEquiv.coe_mapSubgroup,
    Subgroup.mem_map_equiv, MulEquiv.symm_symm, mem_subgroupOrderIsoSubgroupMulChar_symm_iff]

variable [IsGalois ℚ K]

def intermediateFieldEquivSubgroupChar :
    IntermediateField ℚ K ≃o Subgroup (DirichletCharacter R n) :=
  IsGalois.intermediateFieldEquivSubgroup.trans <|
      (subgroupGalEquivDirichletCharSubgroup n K R).dual.trans (OrderIso.dualDual _).symm

theorem mem_intermediateFieldEquivSubgroupChar {F : IntermediateField ℚ K}
    {χ : DirichletCharacter R n} :
    χ ∈ intermediateFieldEquivSubgroupChar n K R F ↔
      ∀ σ : Gal(K/ℚ), (∀ x ∈ F, σ x = x) → χ (galEquivZMod n K σ) = 1 := by
  simp [← IntermediateField.mem_fixingSubgroup_iff, intermediateFieldEquivSubgroupChar]

theorem intermediateFieldEquivSubgroupChar_of_isCyclotomicExtension (F : IntermediateField ℚ K)
    {m : ℕ} [NeZero m] [IsGalois ℚ F] [IsCyclotomicExtension {m} ℚ F] (hdiv : m ∣ n) :
    intermediateFieldEquivSubgroupChar n K R F =
      (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod n) R (ZMod.unitsMap hdiv).ker).ofDual := by
  ext χ
  sorry
  -- simp [mem_intermediateFieldEquivSubgroupChar, mem_subgroupOrderIsoSubgroupMulChar_iff,
  --   MonoidHom.mem_ker, ← (galEquivZMod n K).forall_congr_right, MulEquiv.toEquiv_eq_coe,
  --   EquivLike.coe_coe, (galEquivZMod_restrictNormal_apply n K F hdiv _).symm,
  --   EmbeddingLike.map_eq_one_iff, AlgEquiv.restrictNormal_eq_one_iff]

example (F : IntermediateField ℚ K) {p k : ℕ} [hp : Fact (p.Prime)] [IsGalois ℚ F]
    [IsCyclotomicExtension {p ^ (k + 1)} ℚ F] (hdiv : p ^ (k + 1) ∣ n) :
    intermediateFieldEquivSubgroupChar n K R F =
      {χ : DirichletCharacter R n | p ∣ χ.conductor} := by
  rw [intermediateFieldEquivSubgroupChar_of_isCyclotomicExtension n K R F hdiv]
  ext χ
  simp only [SetLike.mem_coe, mem_subgroupOrderIsoSubgroupMulChar_iff, Set.mem_setOf_eq]
  have : p ∣ χ.conductor ↔ χ.FactorsThrough (p ^ (k + 1)) := by
    refine ⟨?_, ?_⟩
    · intro h
      sorry
    · intro h
      rw [← DirichletCharacter.mem_conductorSet_iff] at h

      sorry
  rw [this]
  have := DirichletCharacter.factorsThrough_iff_ker_unitsMap (χ := χ) hdiv
  simp_rw [this, ← MulChar.coe_toUnitHom, Units.val_eq_one, ← MonoidHom.mem_ker, SetLike.le_def]

#exit

def intermediateFieldEquivSubgroupChar [IsGalois ℚ K] :
    IntermediateField ℚ K ≃o Subgroup (DirichletCharacter R n) :=
  IsGalois.intermediateFieldEquivSubgroup.trans <|
    (subgroupGalEquivDirichletCharSubgroup n K R).dual.trans (OrderIso.dualDual _).symm





theorem forall_mem_intermediateFieldEquivSubgroupChar_iff [IsAbelianGalois ℚ K] (σ : Gal(K/ℚ))
    (L : IntermediateField ℚ K) :
    (∀ χ ∈ intermediateFieldEquivSubgroupChar n K R L, χ (galEquiv n K σ) = 1) ↔
      σ ∈ L.fixingSubgroup := by
  unfold intermediateFieldEquivSubgroupChar
  simp [- IntermediateField.mem_fixingSubgroup_iff]

  simp_rw [OrderIso.trans_apply, OrderIso.dual_apply, OrderIso.dualDual_symm_apply,
    OrderDual.ofDual_toDual, mem_subgroupGalEquivDirichletCharSubgroup_iff]
  rw [@IsGalois.ofDual_intermediateFieldEquivSubgroup_apply]

  simp only [OrderIso.dualDual_symm_apply, OrderDual.ofDual_toDual,
    mem_subgroupGalEquivDirichletCharSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
  have := fun χ ↦ mem_subgroupGalEquivDirichletCharSubgroup_iff n K R χ
  simp only [OrderIso.trans_apply, OrderIso.dual_apply, OrderDual.ofDual_toDual,
    OrderIso.dualDual_symm_apply, mem_subgroupGalEquivDirichletCharSubgroup_iff]


#exit

  have : HasEnoughRootsOfUnity R (Monoid.exponent Gal(K/ℚ)) := sorry
  have : HasEnoughRootsOfUnity R (Monoid.exponent (DirichletCharacter R n)) := sorry
  have t₀ := CommGroup.forall_monoidHom_apply_eq_one_iff R L.fixingSubgroup
  rw [← (galEquiv n K).symm.forall_congr_right] at t₀

#exit

  have t₁ := CommGroup.forall_monoidHom_apply_eq_one_iff R
    (intermediateFieldEquivSubgroupChar n K R L)
  simp_rw (config := {singlePass := true}) [← t₁]


  have := CommGroup.forall_monoidHom_apply_eq_one_iff R L.fixingSubgroup
  rw [← this]

  unfold intermediateFieldEquivSubgroupChar



  dsimp only [intermediateFieldEquivSubgroupChar, MulEquiv.symm_mapSubgroup, OrderIso.trans_apply,
    IsGalois.intermediateFieldEquivSubgroup_apply, OrderIso.dual_apply, OrderDual.ofDual_toDual,
    OrderIso.dualDual_symm_apply]
  simp_rw [MulEquiv.coe_mapSubgroup, Subgroup.mem_map_equiv]
  simp_rw [CommGroup.mem_subgroupOrderIsoSubgroupMonoidHom_iff]
  simp_rw [Subgroup.mem_map_equiv]
  rw [MulEquiv.symm_symm]
  simp_rw [← (galEquiv n K).forall_congr_right]
  rw [← MulChar.mulEquivToUnitHom.symm.forall_congr_right]




-- theorem mem_fixingSubgroup_iff_forall [IsGalois ℚ K] (σ : Gal(K/ℚ)) (L : IntermediateField ℚ K) :
--     σ ∈ L.fixingSubgroup ↔ ∀ χ ∈ intermediateFieldEquivSubgroupChar n K R L,
--       χ (galEquiv n K σ) = 1 := by
--   unfold intermediateFieldEquivSubgroupChar
--   simp only [OrderIso.trans_apply, MulEquiv.symm_mapSubgroup, OrderIso.dual_apply,
--     OrderDual.ofDual_toDual, IsGalois.ofDual_intermediateFieldEquivSubgroup_apply,
--     OrderIso.dualDual_symm_apply, CommGroup.subgroupOrderIsoSubgroupMonoidHom_apply,
--     MulEquiv.coe_mapSubgroup, Subgroup.mem_map_equiv, MulEquiv.symm_symm]
--   rw [← mulEquivToUnitHom.symm.forall_congr_right]
--   simp only [MulEquiv.toMonoidHom_eq_coe, MulEquiv.toEquiv_eq_coe, MulEquiv.toEquiv_symm,
--     MulEquiv.coe_toEquiv_symm, MulEquiv.apply_symm_apply, mulEquivToUnitHom_symm_apply_apply,
--     Units.isUnit, reduceDIte, IsUnit.unit_of_val_units, Units.val_eq_one]
--   rw [CommGroup.forall_mem_restrictHom_ker_apply_eq_one_iff]
--   simp only [IntermediateField.mem_fixingSubgroup_iff, Subgroup.mem_map, MonoidHom.coe_coe,
--     EmbeddingLike.apply_eq_iff_eq, exists_eq_right]

-- example [IsGalois ℚ K] (χ : DirichletCharacter R n) (L : IntermediateField ℚ K) :
--     χ ∈ intermediateFieldEquivSubgroupChar n K R L ↔ ∀ σ ∈ L.fixingSubgroup,
--       χ (galEquiv n K σ)= 1 := by
--   simp_rw [mem_fixingSubgroup_iff_forall n K R]
--   rw [← (galEquiv n K).symm.forall_congr_right]
--   have := MulChar.forall_mem_subgroupOrderIsoSubgroupMulChar_apply_eq_one_iff (ZMod n) R
--     (intermediateFieldEquivSubgroupChar n K R L) χ
--   rw [← this]
--   simp

--  have := CommGroup.forall_mem_restrictHom_ker_apply_eq_one_iff
--    (intermediateFieldEquivSubgroupChar n K R L)











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
