import Mathlib
import Mathlib.NumberTheory.KroneckerWeber.IsInvariant

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] --[IsDiscreteValuationRing R] [I]

def Ideal.oneAdd (I : Ideal R) : Submonoid R where
  carrier := { x | x - 1 ∈ I }
  mul_mem' {a b} ha hb := by simpa [mul_sub] using add_mem (I.mul_mem_left a hb) ha
  one_mem' := by simp

lemma Ideal.oneAdd_le_isUnit (I : Ideal R) (hI : I ≤ jacobson ⊥) :
    I.oneAdd ≤ IsUnit.submonoid R := by
  intro x hx
  simpa using mem_jacobson_bot.mp (hI hx) 1

def Ideal.oneAddUnits (I : Ideal R) : Subgroup Rˣ where
  __ := I.oneAdd.comap (Units.coeHom R)
  inv_mem' {x} hx := by
    simpa [-unit_mul_mem_iff_mem, mul_sub, ← sub_eq_neg_add] using I.mul_mem_left (-x⁻¹).1 hx

lemma Ideal.mem_oneAddUnits {I : Ideal R} {x : Rˣ} : x ∈ I.oneAddUnits ↔ x.1 - 1 ∈ I := Iff.rfl

lemma Ideal.oneAddUnits_mono : Monotone (oneAddUnits (R := R)) := fun _ _ h _ ↦ (h ·)

def Ideal.quotientOneAddUnits (I : Ideal R) : Rˣ ⧸ I.oneAddUnits →* (R ⧸ I)ˣ :=
  QuotientGroup.lift _ (Units.map (Ideal.Quotient.mk I).toMonoidHom) fun x hx ↦ by
    ext
    simp only [RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe, Units.val_one]
    rwa [← (Ideal.Quotient.mk I).map_one, Ideal.Quotient.eq]

@[simp]
lemma Ideal.coe_quotientOneAddUnits_mk (I : Ideal R) (x : Rˣ) :
    (I.quotientOneAddUnits x).1 = x.1 := rfl

lemma Ideal.quotientOneAddUnits_injective (I : Ideal R) :
    Function.Injective I.quotientOneAddUnits := by
  rw [injective_iff_map_eq_one]
  intro a ha
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  simp only [Units.ext_iff, coe_quotientOneAddUnits_mk, Units.val_one] at ha
  rw [← (Ideal.Quotient.mk I).map_one, Ideal.Quotient.eq] at ha
  rwa [QuotientGroup.eq_one_iff]

lemma Ideal.quotientOneAddUnits_bijective (I : Ideal R) (hI : I ≤ jacobson ⊥) :
    Function.Bijective I.quotientOneAddUnits := by
  refine ⟨I.quotientOneAddUnits_injective, ?_⟩
  rintro ⟨a, b, ha, -⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← _root_.map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq] at ha
  have : IsUnit a ∧ IsUnit b := by simpa using mem_jacobson_bot.mp (hI ha) 1
  refine ⟨QuotientGroup.mk this.1.unit, ?_⟩
  ext
  simp

noncomputable
def Ideal.toOneAddUnitsQuot {I J : Ideal R} {ϖ : R}
    (hϖ₁ : ϖ ∈ I) (hϖ₂ : ϖ ∈ jacobson ⊥) (hϖ₃ : ϖ ^ 2 ∈ J) :
    R →+ Additive (I.oneAddUnits ⧸ J.oneAddUnits.subgroupOf I.oneAddUnits) where
  toFun x :=
    letI : IsUnit (ϖ * x + 1) := mem_jacobson_bot.mp hϖ₂ x
    .ofMul <| QuotientGroup.mk ⟨this.unit, show _ ∈ I by simpa using I.mul_mem_right _ hϖ₁⟩
  map_zero' := by simpa using one_mem _
  map_add' x y := by
    simp only [← ofMul_mul, Additive.ofMul.injective.eq_iff,
      ← QuotientGroup.mk_mul, QuotientGroup.eq]
    show _ ∈ J
    simp only [Subgroup.coeSubtype, Subgroup.coe_mul, InvMemClass.coe_inv, Units.coeHom_apply,
      Units.val_mul, IsUnit.unit_spec]
    generalize_proofs h
    rw [← unit_mul_mem_iff_mem _ h, mul_sub, mul_one, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
    convert J.mul_mem_right (x * y) hϖ₃ using 1
    ring

lemma Ideal.toOneAddUnitsQuot_surjective {I J : Ideal R} {ϖ : R}
    (hϖ₁ : Ideal.span {ϖ} = I) (hϖ₂ : ϖ ∈ jacobson ⊥) (hϖ₃ : ϖ ^ 2 ∈ J) :
    Function.Surjective (toOneAddUnitsQuot (hϖ₁.le (mem_span_singleton_self ϖ)) hϖ₂ hϖ₃) := by
  intro x
  obtain ⟨x, rfl⟩ := Additive.ofMul.surjective x
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y, hy⟩ := mem_span_singleton.mp (hϖ₁.ge hx)
  use y
  rw [eq_comm]
  simp only [toOneAddUnitsQuot, AddMonoidHom.coe_mk, ZeroHom.coe_mk, EmbeddingLike.apply_eq_iff_eq,
    QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, InvMemClass.coe_inv,
    mem_oneAddUnits, Units.val_mul, IsUnit.unit_spec]
  simp_rw [← unit_mul_mem_iff_mem _ (x := (_ - _)) x.isUnit, mul_sub, mul_one,
    Units.mul_inv_cancel_left, ← hy]
  simp

lemma Ideal.ker_toOneAddUnitsQuot [IsDomain R] {I J : Ideal R} {x y : R} (hx0 : x ≠ 0) (hy : y ∣ x)
    (hxI : x ∈ I) (hx : x ∈ jacobson ⊥) (hJ : Ideal.span {x * y} = J) :
    (toOneAddUnitsQuot hxI hx
      (hJ.le (mem_span_singleton.mpr (by simpa [pow_two] using mul_dvd_mul_left x hy)))).ker =
    (Ideal.span {y}).toAddSubgroup := by
  ext
  simp [toOneAddUnitsQuot, Subgroup.mem_subgroupOf, mem_oneAddUnits, ← hJ,
    mem_span_singleton, pow_succ, mul_dvd_mul_iff_left hx0]

variable {G : Type*} [Group G] [MulSemiringAction G R]

open nonZeroDivisors

noncomputable
def Ideal.inertiaToOneAddUnitsToFun (I J : Ideal R) (ϖ : R) (hϖ : ϖ ∈ R⁰) (hI : I ≤ span {ϖ})
    (H : I.colon (span {ϖ}) ≤ J) (σ : I.toAddSubgroup.inertia G) :
    J.oneAddUnits :=
  letI h := Ideal.mem_span_singleton.mp (hI (σ.2 ϖ))
  letI x := h.choose
  haveI h₁ : IsUnit (x + 1) := by
    obtain ⟨y, e⟩ := Ideal.mem_span_singleton.mp (hI (σ⁻¹.2 ϖ))
    rw [sub_eq_iff_eq_add, ← mul_add_one, Subgroup.coe_inv, inv_smul_eq_iff, smul_mul'] at e
    refine isUnit_iff_exists_inv.mpr ⟨σ.1 • (y + 1), ?_⟩
    rw [← sub_eq_zero]
    apply hϖ
    rw [mul_comm, mul_sub, ← mul_assoc, mul_add_one, ← h.choose_spec, sub_add_cancel,
      ← e, mul_one, sub_self]
  haveI h₂ : x + 1 ∈ J.oneAdd := by
    refine H ?_
    rw [add_sub_cancel_right, span, Submodule.mem_colon_singleton,
      smul_eq_mul, mul_comm, ← h.choose_spec]
    exact σ.2 ϖ
  ⟨h₁.unit, h₂⟩

lemma Ideal.inertiaToOneAddUnitsToFun_spec
    (I J : Ideal R) (ϖ : R) (hϖ : ϖ ∈ R⁰) (hI : I ≤ Ideal.span {ϖ})
    (H : I.colon (span {ϖ}) ≤ J) (σ : I.toAddSubgroup.inertia G) :
    ϖ * (inertiaToOneAddUnitsToFun I J ϖ hϖ hI H σ).1.1 = σ.1 • ϖ := by
  letI h := Ideal.mem_span_singleton.mp ((hI (σ.2 ϖ)))
  letI x := h.choose
  have hx : _ = ϖ * x := h.choose_spec
  show ϖ * (x + 1) = _
  rw [mul_add, mul_one, ← hx, sub_add_cancel]

lemma QuotientGroup.eq_iff_exists {G : Type*} [Group G] {H : Subgroup G} {x y : G} :
    (x : G ⧸ H) = y ↔ ∃ z ∈ H, x = y * z := by
  simp_rw [← inv_mul_eq_iff_eq_mul, eq_comm, exists_eq_right, eq_comm (a := mk x), QuotientGroup.eq]

noncomputable
def Ideal.inertiaToOneAddUnits [IsDomain R] (I J : Ideal R) (ϖ : R) (hϖ : ϖ ≠ 0)
    (hI : I ≤ span {ϖ}) (H : I.colon (span {ϖ}) ≤ J) :
    I.toAddSubgroup.inertia G →* J.oneAddUnits ⧸ I.oneAddUnits.subgroupOf J.oneAddUnits where
  toFun σ := QuotientGroup.mk (Ideal.inertiaToOneAddUnitsToFun I J ϖ (by simpa using hϖ) hI H σ)
  map_one' := by
    simp only [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Ideal.mem_oneAddUnits]
    convert zero_mem I using 1
    apply mul_left_cancel₀ hϖ
    simp only [mul_sub, inertiaToOneAddUnitsToFun_spec, Subgroup.coe_one, one_smul, mul_one,
      sub_self, mul_zero]
  map_mul' σ τ := by
    simp only [← QuotientGroup.mk_mul, QuotientGroup.eq_iff_exists]
    let s := I.inertiaToOneAddUnitsToFun J ϖ (by simpa using hϖ) hI H τ
    have hsu : IsUnit ((s.1⁻¹).1 * σ.1 • s.1.1) := by
      simp only [IsUnit.mul_iff, Units.isUnit, true_and]
      exact s.1.isUnit.map (MulSemiringAction.toRingHom _ R σ.1)
    have hs : (s.1⁻¹).1 * σ.1 • s.1.1 ∈ J.oneAdd := by
      refine H ?_
      simp only [mem_colon_singleton]
      refine Ideal.mul_mem_right _ _ ((unit_mul_mem_iff_mem _ s.1.isUnit).mp ?_)
      simpa only [mul_sub, Units.mul_inv_cancel_left, mul_one] using σ.2 _
    refine ⟨⟨hsu.unit, hs⟩, ?_, ?_⟩
    · simpa [Subgroup.mem_subgroupOf, mem_oneAddUnits,
        ← unit_mul_mem_iff_mem I (x := _ - 1) s.1.isUnit, mul_sub] using σ.2 _
    ext
    apply mul_left_cancel₀ hϖ
    simp only [inertiaToOneAddUnitsToFun_spec, Subgroup.coe_mul, mul_smul, Units.val_mul,
      IsUnit.unit_spec, ← mul_assoc, Units.mul_inv_cancel_right, s]
    rw [← inertiaToOneAddUnitsToFun_spec I J ϖ (by simpa using hϖ) hI H, MulSemiringAction.smul_mul]

noncomputable
abbrev Ideal.inertiaToOneAddUnitsOfEqPow [IsDomain R] [IsDiscreteValuationRing R] (I J : Ideal R)
    (ϖ : R) (hϖ : Irreducible ϖ) (n : ℕ)
    (hI : I = span {ϖ ^ (n + 1)}) (hJ : J = span {ϖ ^ n}) :
    I.toAddSubgroup.inertia G →* J.oneAddUnits ⧸ I.oneAddUnits.subgroupOf J.oneAddUnits :=
  inertiaToOneAddUnits I J ϖ hϖ.ne_zero
    (by rw [hI, span_singleton_le_span_singleton, pow_succ']; exact ⟨_, rfl⟩)
    (by simp [hI, hJ, SetLike.le_def, mem_span_singleton,
      pow_succ, mul_dvd_mul_iff_right hϖ.ne_zero])

instance {R S : Type*} [CommRing R] [Field S] [Algebra R S] [FaithfulSMul R S] [Finite S] :
    Algebra.IsSeparable R S := by
  have : Finite R := .of_injective _ (FaithfulSMul.algebraMap_injective R S)
  have : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain
  letI := (Finite.isField_of_domain R).toField
  infer_instance

attribute [local instance] Ideal.Quotient.field in
lemma Ideal.ker_inertiaToOneAddUnits [Finite G]
    [IsDomain R] [IsDiscreteValuationRing R] (I J : Ideal R)
    (ϖ : R) (hϖ : Irreducible ϖ) [Finite (IsLocalRing.ResidueField R)] (n : ℕ)
    (hI : I = span {ϖ ^ (n + 1)}) (hJ : J = span {ϖ ^ n}) :
    (Ideal.inertiaToOneAddUnitsOfEqPow I J ϖ hϖ n hI hJ).ker =
      ((span {ϖ ^ (n + 2)}).toAddSubgroup.inertia G).subgroupOf _ := by
  ext σ
  simp only [inertiaToOneAddUnits, MonoidHom.mem_ker, MonoidHom.coe_mk, OneHom.coe_mk,
    QuotientGroup.eq_one_iff, hI, Subgroup.mem_subgroupOf, mem_oneAddUnits, mem_span_singleton,
    ← mul_dvd_mul_iff_left hϖ.ne_zero (b := ϖ ^ (n + 1)), ← pow_succ', add_assoc,
    one_add_one_eq_two, mul_sub, inertiaToOneAddUnitsToFun_spec, mul_one, AddSubgroup.mem_inertia,
    Submodule.mem_toAddSubgroup]
  refine ⟨fun H x ↦ ?_, fun H ↦ H _⟩
  have : (span {ϖ}).IsMaximal := hϖ.maximalIdeal_eq ▸ inferInstance
  have : Finite (R ⧸ Ideal.span {ϖ}) := by rwa [← hϖ.maximalIdeal_eq]
  obtain ⟨y, hy, e⟩ := exists_mem_fixedPoints_inertia_sub_mem R G (span {ϖ}) x
  simp only [Ideal.mem_span_singleton', eq_sub_iff_add_eq] at e
  obtain ⟨x, rfl⟩ := e
  have : I ≤ span {ϖ} := by rw [hI, ← span_singleton_pow]; exact pow_le_self (by simp)
  have h₁ : σ.1 • y = y := hy ⟨σ, fun x ↦ this (σ.2 x)⟩
  simp only [smul_add, smul_mul', h₁, add_sub_add_right_eq_sub]
  convert_to ϖ ^ (n + 2) ∣ σ.1 • x * (σ.1 • ϖ - ϖ) + (σ.1 • x - x) * ϖ
  · ring
  refine dvd_add (dvd_mul_of_dvd_right H _) ?_
  rw [pow_succ]
  refine mul_dvd_mul ?_ dvd_rfl
  rw [← Ideal.mem_span_singleton, ← hI]
  exact σ.2 x

/-

lemma Ideal.toOneAddUnitsQuot_surjective {I J : Ideal R} {ϖ : R}
    (hϖ₁ : Ideal.span {ϖ} = I) (hϖ₂ : ϖ ∈ jacobson ⊥) (hϖ₃ : ϖ ^ 2 ∈ J) :
    Function.Surjective (toOneAddUnitsQuot (hϖ₁.le (mem_span_singleton_self ϖ)) hϖ₂ hϖ₃) := by
  intro x
  obtain ⟨x, rfl⟩ := Additive.ofMul.surjective x
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y, hy⟩ := mem_span_singleton.mp (hϖ₁.ge hx)
  use y
  rw [eq_comm]
  simp only [toOneAddUnitsQuot, AddMonoidHom.coe_mk, ZeroHom.coe_mk, EmbeddingLike.apply_eq_iff_eq,
    QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, InvMemClass.coe_inv,
    mem_oneAddUnits, Units.val_mul, IsUnit.unit_spec]
  simp_rw [← unit_mul_mem_iff_mem _ (x := (_ - _)) x.isUnit, mul_sub, mul_one,
    Units.mul_inv_cancel_left, ← hy]
  simp

lemma Ideal.ker_toOneAddUnitsQuot [IsDomain R] {I J : Ideal R} {x y : R} (hx0 : x ≠ 0) (hy : y ∣ x)
    (hxI : x ∈ I) (hx : x ∈ jacobson ⊥) (hJ : Ideal.span {x * y} = J) :
-/

noncomputable
def Ideal.equivOneAddUnitsQuot [IsDomain R] {I J : Ideal R} {x y : R} (hx0 : x ≠ 0) (hy : y ∣ x)
    (hxI : Ideal.span {x} = I) (hx : x ∈ jacobson ⊥) (hJ : Ideal.span {x * y} = J) :
    R ⧸ Ideal.span {y} ≃+ Additive (I.oneAddUnits ⧸ J.oneAddUnits.subgroupOf I.oneAddUnits) :=
  (QuotientAddGroup.quotientAddEquivOfEq (by rw [Ideal.ker_toOneAddUnitsQuot hx0 hy _ hx hJ])).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (H := Additive (I.oneAddUnits ⧸ J.oneAddUnits.subgroupOf I.oneAddUnits))
      (toOneAddUnitsQuot (hxI.le (mem_span_singleton_self _)) hx (hJ.le (mem_span_singleton.mpr
      (by simpa [pow_two] using mul_dvd_mul_left x hy)))) <| by
      exact Ideal.toOneAddUnitsQuot_surjective hxI hx _)

open IsLocalRing

open scoped Pointwise in
instance (I : Ideal R) (n : ℕ) :
    (((I ^ (n + 2)).toAddSubgroup.inertia G).subgroupOf
      ((I ^ (n + 1)).toAddSubgroup.inertia G)).Normal := by
  constructor
  intro σ hσ τ r
  have := Ideal.smul_mem_pointwise_smul τ.1 _ _  (hσ (τ.1⁻¹ • r))
  simp only [smul_pow', Subgroup.coeSubtype, smul_sub, smul_inv_smul, Subgroup.coe_mul,
    InvMemClass.coe_inv, mul_smul, Submodule.mem_toAddSubgroup] at this ⊢
  refine Ideal.pow_right_mono ?_ _ this
  simp only [SetLike.le_def, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  intro x hx
  simpa using I.add_mem hx (Ideal.pow_le_self (by simp) (τ.2 (τ.1⁻¹ • x)))

open scoped Pointwise in
instance (I : Ideal R) :
    (((I ^ 2).toAddSubgroup.inertia G).subgroupOf (I.toAddSubgroup.inertia G)).Normal := by
  convert (inferInstanceAs ((((I ^ (0 + 2)).toAddSubgroup.inertia G).subgroupOf
      ((I ^ (0 + 1)).toAddSubgroup.inertia G)).Normal)) <;> simp

lemma card_relIndex_inertia_dvd_card_quotient [Finite G]
    [IsDomain R] [IsDiscreteValuationRing R] [Finite (ResidueField R)]
    (n : ℕ) (hn : 2 ≤ n) :
    ((maximalIdeal R ^ (n + 1)).toAddSubgroup.inertia G).relindex
      ((maximalIdeal R ^ n).toAddSubgroup.inertia G) ∣ Nat.card (ResidueField R) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  simp only [ResidueField, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  cases n with
  | zero => simp at hn
  | succ n =>
    replace hn : 0 < n := by nlinarith
    let e := Ideal.equivOneAddUnitsQuot (x := ϖ ^ n) (y := ϖ) (J := .span {ϖ ^ (n + 1)})
      (by simpa [hn.ne'] using hϖ.ne_zero) (dvd_pow_self _ hn.ne') rfl
      (by simpa [hn.ne', IsLocalRing.jacobson_eq_maximalIdeal] using hϖ.not_unit)
      (by rw [← pow_succ])
    rw [Nat.card_congr (e.toEquiv.trans Additive.toMul)]
    let f := QuotientGroup.kerLift (Ideal.inertiaToOneAddUnitsOfEqPow (G := G) _ _ ϖ hϖ n rfl rfl)
    convert Subgroup.card_dvd_of_injective f (QuotientGroup.kerLift_injective _) using 1
    · rw [Ideal.ker_inertiaToOneAddUnits]
      rfl

lemma card_inertia_dvd_card_quotient_pow [Finite G] [FaithfulSMul G R]
    [IsDomain R] [IsDiscreteValuationRing R] [Finite (ResidueField R)] :
    ∃ k, Nat.card ((maximalIdeal R ^ 2).toAddSubgroup.inertia G) ∣
      (Nat.card (ResidueField R)) ^ k := by
  let Γ (i) := (maximalIdeal R ^ i).toAddSubgroup.inertia G
  have hΓ {i j} (h : j ≤ i) : Γ i ≤ Γ j := fun σ hσ x ↦ Ideal.pow_le_pow_right h (hσ x)
  show ∃ k, Nat.card (Γ 2) ∣ _
  have H (σ : G) (hσ : σ ≠ 1) : ∃ n, σ ∉ Γ n := by
    contrapose! hσ
    refine FaithfulSMul.eq_of_smul_eq_smul (α := R) fun r ↦ ?_
    rw [← sub_eq_zero, one_smul, ← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing _
      (maximalIdeal.isMaximal R).ne_top, Ideal.mem_iInf]
    exact (hσ · r)
  choose! n hn using H
  cases nonempty_fintype G
  let N := Finset.univ.sup n
  have : Γ (N + 2) = ⊥ := le_bot_iff.mp fun σ hσ ↦
    not_imp_not.mp (hn σ) (hΓ ((Finset.le_sup (Finset.mem_univ _)).trans (N.le_add_right _)) hσ)
  rw [← Subgroup.relindex_bot_left, ← this]
  use N
  induction N with
  | zero => simp
  | succ n IH =>
    rw [← Subgroup.relindex_mul_relindex (Γ (n + 1 + 2)) (Γ (n + 2)) (Γ 2)
      (hΓ (by linarith)) (hΓ (by linarith)), pow_succ']
    exact mul_dvd_mul (card_relIndex_inertia_dvd_card_quotient _ (by linarith)) IH

lemma isPGroup_maximalIdeal_sq_inertia [Finite G] [FaithfulSMul G R]
    [IsDomain R] [IsDiscreteValuationRing R] [Finite (ResidueField R)]
    (p : ℕ) [CharP (ResidueField R) p] :
    IsPGroup p ((maximalIdeal R ^ 2).toAddSubgroup.inertia G) := by
  cases nonempty_fintype (ResidueField R)
  obtain ⟨n, hp, e⟩ := FiniteField.card (ResidueField R) p
  obtain ⟨k, hk⟩ := card_inertia_dvd_card_quotient_pow (R := R) (G := G)
  rw [Nat.card_eq_fintype_card (α := ResidueField R), e, ← pow_mul] at hk
  obtain ⟨i, hi, H⟩ := (dvd_prime_pow hp.prime _).mp hk
  exact .of_card (associated_iff_eq.mp H)

instance [Finite G] [FaithfulSMul G R]
    [IsDomain R] [IsDiscreteValuationRing R] [Finite (ResidueField R)] :
    Group.IsNilpotent ((maximalIdeal R ^ 2).toAddSubgroup.inertia G) := by
  obtain ⟨p, hc⟩ := CharP.exists (ResidueField R)
  cases nonempty_fintype (ResidueField R)
  have : Fact (Nat.Prime p) := ⟨(FiniteField.card (ResidueField R) p).choose_spec.1⟩
  exact (isPGroup_maximalIdeal_sq_inertia p).isNilpotent

noncomputable
def maximalIdealInertiaQuotient
    [Finite G] [IsDomain R] [IsDiscreteValuationRing R] [Finite (ResidueField R)]
    (ϖ : R) (hϖ : Irreducible ϖ) :
    ((maximalIdeal R).toAddSubgroup.inertia G ⧸
      ((maximalIdeal R ^ 2).toAddSubgroup.inertia G).subgroupOf
      ((maximalIdeal R).toAddSubgroup.inertia G)) →* (ResidueField R)ˣ :=
  letI f := Ideal.inertiaToOneAddUnitsOfEqPow (G := G)
    (maximalIdeal R) ⊤ ϖ hϖ 0 (by simp [hϖ.maximalIdeal_eq]) (by simp)
  letI g := (QuotientGroup.kerLift f).comp (QuotientGroup.quotientMulEquivOfEq
    (M := ((maximalIdeal R ^ 2).toAddSubgroup.inertia G).subgroupOf
      ((maximalIdeal R).toAddSubgroup.inertia G)) (N := MonoidHom.ker f) (by
      rw [Ideal.ker_inertiaToOneAddUnits, ← Ideal.span_singleton_pow,
        hϖ.maximalIdeal_eq, zero_add])).toMonoidHom
  (Ideal.quotientOneAddUnits (maximalIdeal R)).comp
    (.comp (QuotientGroup.map _ _ (Subgroup.subtype _) (by simp)) g)

lemma maximalIdealInertiaQuotient_injective
    [Finite G] [IsDomain R] [IsDiscreteValuationRing R] [Finite (ResidueField R)]
    (ϖ : R) (hϖ : Irreducible ϖ) :
    Function.Injective (maximalIdealInertiaQuotient (G := G) ϖ hϖ) := by
  letI f := Ideal.inertiaToOneAddUnitsOfEqPow (G := G)
    (maximalIdeal R) ⊤ ϖ hϖ 0 (by simp [hϖ.maximalIdeal_eq]) (by simp)
  refine (Ideal.quotientOneAddUnits_injective (maximalIdeal R)).comp
    (.comp (g := QuotientGroup.map _ _ _ (by simp)) ?_
    ((QuotientGroup.kerLift_injective f).comp (MulEquiv.injective _)))
  rw [← MonoidHom.ker_eq_bot_iff]
  simp [SetLike.ext_iff, QuotientGroup.mk_surjective.forall, Subgroup.mem_subgroupOf]

instance isCyclic_maximalIdeal_inertia_quotient
    [Finite G] [IsDomain R] [IsDiscreteValuationRing R] [Finite (ResidueField R)] :
    IsCyclic ((maximalIdeal R).toAddSubgroup.inertia G ⧸
      ((maximalIdeal R ^ 2).toAddSubgroup.inertia G).subgroupOf
      ((maximalIdeal R).toAddSubgroup.inertia G)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  exact isCyclic_of_injective _ (maximalIdealInertiaQuotient_injective (G := G) ϖ hϖ)

lemma relindex_maximalIdeal_inertia_quotient_dvd
    [Finite G] [IsDomain R] [IsDiscreteValuationRing R] [Finite (ResidueField R)] :
    ((maximalIdeal R ^ 2).toAddSubgroup.inertia G).relindex
      ((maximalIdeal R).toAddSubgroup.inertia G) ∣ Nat.card (ResidueField R) - 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [← Nat.card_units (ResidueField R)]
  exact Subgroup.card_dvd_of_injective _ (maximalIdealInertiaQuotient_injective (G := G) ϖ hϖ)

instance isSolvable_maximalIdeal_inertia
    [Finite G] [FaithfulSMul G R] [IsDomain R] [IsDiscreteValuationRing R]
    [Finite (ResidueField R)] :
    IsSolvable ((maximalIdeal R).toAddSubgroup.inertia G) :=
  solvable_of_ker_le_range
    (G' := (maximalIdeal R ^ 2).toAddSubgroup.inertia G)
    (G := (maximalIdeal R).toAddSubgroup.inertia G)
    (G'' := ((maximalIdeal R).toAddSubgroup.inertia G ⧸
      ((maximalIdeal R ^ 2).toAddSubgroup.inertia G).subgroupOf
      ((maximalIdeal R).toAddSubgroup.inertia G)))
    (Subgroup.inclusion fun σ hσ x ↦ Ideal.pow_le_self (by simp) (hσ x))
    (QuotientGroup.mk' _)
    (by simp)
