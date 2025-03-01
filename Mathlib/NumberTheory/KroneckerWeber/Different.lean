
-- import Mathlib.Algebra.GroupWithZero.Action.Faithful
-- import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.KroneckerWeber.Unramified
-- import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib

open nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra


theorem differentIdeal_ne_bot (A : Type*) {B : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [IsDomain A]
    [IsIntegrallyClosed A] [IsDedekindDomain B] [NoZeroSMulDivisors A B] [Module.Finite A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)] :
    differentIdeal A B ≠ ⊥ := by
  let K := FractionRing A
  let L := FractionRing B
  have : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization _ K _ _
  have : FiniteDimensional K L :=
    Module.Finite_of_isLocalization A B _ _ A⁰
  rw [ne_eq, ← FractionalIdeal.coeIdeal_inj (K := L), coeIdeal_differentIdeal (K := K)]
  simp

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra in
theorem not_dvd_differentIdeal_of_intTrace_not_mem (A : Type*) {B : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [IsDomain A]
    [IsIntegrallyClosed A] [IsDedekindDomain B] [NoZeroSMulDivisors A B] [Module.Finite A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)] {p : Ideal A}
    (P Q : Ideal B) (hP : P * Q = Ideal.map (algebraMap A B) p)
    (x : B) (hxQ : x ∈ Q) (hx : Algebra.intTrace A B x ∉ p) :
    ¬ P ∣ differentIdeal A B := by
  by_cases hp : p = ⊥
  · subst hp
    simp only [Ideal.map_bot, Ideal.mul_eq_bot] at hP
    obtain (rfl|rfl) := hP
    · rw [← Ideal.zero_eq_bot, zero_dvd_iff]
      exact differentIdeal_ne_bot A (B := B)
    · obtain rfl := hxQ
      simp at hx
  letI : Algebra (A ⧸ p) (B ⧸ Q) := Ideal.Quotient.algebraQuotientOfLEComap (by
      rw [← Ideal.map_le_iff_le_comap, ← hP]
      exact Ideal.mul_le_left)
  let K := FractionRing A
  let L := FractionRing B
  have : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization _ K _ _
  have : FiniteDimensional K L :=
    Module.Finite_of_isLocalization A B _ _ A⁰
  have hp' := (Ideal.map_eq_bot_iff_of_injective
    (FaithfulSMul.algebraMap_injective A B)).not.mpr hp
  have hPbot : P ≠ ⊥ := fun e ↦ hp' (by simpa [e] using hP.symm)
  have hQbot : Q ≠ ⊥ := fun e ↦ hp' (by simpa [e] using hP.symm)
  rw [Ideal.dvd_iff_le]
  intro H
  replace H := (mul_le_mul_right' H Q).trans_eq hP
  replace H := (FractionalIdeal.coeIdeal_le_coeIdeal' _ (P := L) le_rfl).mpr H
  rw [FractionalIdeal.coeIdeal_mul, coeIdeal_differentIdeal A K] at H
  replace H := FractionalIdeal.mul_le_mul_left H (FractionalIdeal.dual A K 1)
  simp only [ne_eq, FractionalIdeal.dual_eq_zero_iff, one_ne_zero, not_false_eq_true,
    mul_inv_cancel_left₀] at H
  apply hx
  suffices Algebra.trace K L (algebraMap B L x) ∈ (p : FractionalIdeal A⁰ K) by
    obtain ⟨y, hy, e⟩ := this
    rw [← Algebra.algebraMap_intTrace (A := A), Algebra.linearMap_apply,
      (IsLocalization.injective _ le_rfl).eq_iff] at e
    exact e ▸ hy
  have := @H (algebraMap _ _ x) ⟨_, hxQ, rfl⟩
  refine FractionalIdeal.mul_induction_on (H ⟨_, hxQ, rfl⟩) ?_ ?_
  · rintro x hx _ ⟨y, hy, rfl⟩
    induction hy using Submodule.span_induction generalizing x with
    | mem y h =>
      obtain ⟨y, hy, rfl⟩ := h
      obtain ⟨z, hz⟩ :=
        (FractionalIdeal.mem_dual (by simp)).mp hx 1 ⟨1, trivial, (algebraMap B L).map_one⟩
      simp only [Algebra.traceForm_apply, mul_one] at hz
      refine ⟨z * y, Ideal.mul_mem_left _ _ hy, ?_⟩
      rw [Algebra.linearMap_apply, Algebra.linearMap_apply, mul_comm x,
        ← IsScalarTower.algebraMap_apply,
        ← Algebra.smul_def, LinearMap.map_smul_of_tower, ← hz,
        Algebra.smul_def, map_mul, mul_comm]
    | zero => simp
    | add y z _ _ hy hz =>
      simp only [map_add, mul_add]
      exact Submodule.add_mem _ (hy x hx) (hz x hx)
    | smul y z hz IH =>
      simpa [Algebra.smul_def, mul_assoc, -FractionalIdeal.mem_coeIdeal, mul_left_comm x] using
        IH _ (Submodule.smul_mem _ y hx)
  · simp only [map_add, forall_exists_index, and_imp]
    exact fun _ _ h₁ h₂ ↦ Submodule.add_mem _ h₁ h₂

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra Ideal.Quotient.field in
theorem not_dvd_differentIdeal_of_isCoprime_of_isSeparable
    (A : Type*) {B : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [IsDomain A]
    [IsDedekindDomain B] [NoZeroSMulDivisors A B] [Module.Finite A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [IsDedekindDomain A]
    {p : Ideal A} [p.IsMaximal]
    (P Q : Ideal B) (hPQ : IsCoprime P Q)
    (hP : P * Q = Ideal.map (algebraMap A B) p) [P.IsMaximal] [P.LiesOver p]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)] :
    ¬ P ∣ differentIdeal A B := by
  letI : Algebra (A ⧸ p) (B ⧸ Q) := Ideal.Quotient.algebraQuotientOfLEComap (by
      rw [← Ideal.map_le_iff_le_comap, ← hP]
      exact Ideal.mul_le_left)
  have : IsScalarTower A (A ⧸ p) (B ⧸ Q) := .of_algebraMap_eq' rfl
  have : Module.Finite (A ⧸ p) (B ⧸ Q) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ Q)
  letI e : (B ⧸ p.map (algebraMap A B)) ≃ₐ[A ⧸ p] ((B ⧸ P) × B ⧸ Q) :=
    { __ := (Ideal.quotEquivOfEq hP.symm).trans (Ideal.quotientMulEquivQuotientProd P Q hPQ),
      commutes' := Quotient.ind fun _ ↦ rfl }
  obtain ⟨x, hx⟩ : ∃ x, Algebra.trace (A ⧸ p) (B ⧸ P) x ≠ 0 := by
    simpa [LinearMap.ext_iff] using Algebra.trace_ne_zero (A ⧸ p) (B ⧸ P)
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (e.symm (x, 0))
  refine not_dvd_differentIdeal_of_intTrace_not_mem A P Q hP y ?_ ?_
  · simpa [e, Ideal.Quotient.eq_zero_iff_mem] using congr((e $hy).2)
  · rw [← Ideal.Quotient.eq_zero_iff_mem, ← Algebra.trace_quotient_eq_of_isDedekindDomain,
      hy, Algebra.trace_eq_of_algEquiv, Algebra.trace_prod_apply]
    simpa

-- attribute [local instance 9999] IntermediateField.module' Module.Free.of_divisionRing in
-- lemma Subfield.relfinrank_eq_one_iff {E : Type*} [Field E] {E₁ E₂ : Subfield E} :
--     E₁.relfinrank E₂ = 1 ↔ E₂ ≤ E₁ := by
--   refine ⟨fun h x hx ↦ ?_, relfinrank_eq_one_of_le⟩
--   obtain ⟨⟨v, h⟩, hv, H⟩ := _root_.finrank_eq_one_iff'.mp h
--   obtain ⟨⟨c, hc⟩, e⟩ := H ⟨x, hx⟩
--   replace e : c * v = x := congr_arg Subtype.val e
--   obtain ⟨⟨c', hc'⟩, e'⟩ := H 1
--   replace e' : c' * v = 1 := congr_arg Subtype.val e'
--   have hc'' : c' ≠ 0 := fun e ↦ by simp [e] at e'
--   rw [show x = c'⁻¹ * c by rw [eq_inv_mul_iff_mul_eq₀ hc'', ← e, mul_left_comm, e', mul_one]]
--   exact mul_mem (inv_mem hc'.1) hc.1

-- lemma IntermediateField.relfinrank_eq_one_iff {F E : Type*} [Field F] [Field E] [Algebra F E]
--     {E₁ E₂ : IntermediateField F E} :
--     E₁.relfinrank E₂ = 1 ↔ E₂ ≤ E₁ :=
--   Subfield.relfinrank_eq_one_iff

-- attribute [local instance 9999] IntermediateField.module' Module.Free.of_divisionRing in
-- lemma IntermediateField.one_lt_relfinrank {F E : Type*} [Field F] [Field E] [Algebra F E]
--     [FiniteDimensional F E]
--     {E₁ E₂ : IntermediateField F E} (h : E₁ < E₂) :
--     1 < E₁.relfinrank E₂ := by
--   by_contra H
--   have : FiniteDimensional (E₁.toSubfield ⊓ E₂.toSubfield :) E :=
--     inferInstanceAs (FiniteDimensional (E₁ ⊓ E₂ :) E)
--   have := (not_lt.mp H).antisymm (Nat.one_le_iff_ne_zero.mpr Module.finrank_pos.ne')
--   exact not_le_of_lt h (relfinrank_eq_one_iff.mp this)

-- lemma foobar :

open IntermediateField in
universe u in
lemma IsPurelyInseparable.finrank_eq
    (F : Type*) (E : Type u) [Field F] [Field E] [Algebra F E] (q : ℕ) [hF : ExpChar F q]
    [IsPurelyInseparable F E] [FiniteDimensional F E] :
    ∃ n, Module.finrank F E = q ^ n := by
  suffices ∀ (F E : Type u) [Field F] [Field E] [Algebra F E] (q : ℕ) [hF : ExpChar F q]
      [IsPurelyInseparable F E] [FiniteDimensional F E], ∃ n, Module.finrank F E = q ^ n by
    simpa using this (⊥ : IntermediateField F E) E q
  intros F E _ _ _ q _ _ _
  generalize hd : Module.finrank F E = d
  induction d using Nat.strongRecOn generalizing F with
  | ind d IH =>
    by_cases h : (⊥ : IntermediateField F E) = ⊤
    · rw [← finrank_top', ← h, IntermediateField.finrank_bot] at hd
      exact ⟨0, ((pow_zero q).trans hd).symm⟩
    obtain ⟨x, -, hx⟩ := SetLike.exists_of_lt (lt_of_le_of_ne bot_le h:)
    obtain ⟨m, y, e⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C F q x
    have : Module.finrank F F⟮x⟯ = q ^ m := by
      rw [adjoin.finrank (Algebra.IsIntegral.isIntegral x), e, Polynomial.natDegree_sub_C,
        Polynomial.natDegree_X_pow]
    obtain ⟨n, hn⟩ := IH _ (by
      rw [← hd, ← Module.finrank_mul_finrank F F⟮x⟯, Nat.lt_mul_iff_one_lt_left Module.finrank_pos,
        this]
      by_contra! H
      refine hx (finrank_adjoin_simple_eq_one_iff.mp (le_antisymm (this ▸ H) ?_))
      exact Nat.one_le_iff_ne_zero.mpr Module.finrank_pos.ne') (F⟮x⟯) rfl
    exact ⟨m + n, by rw [← hd, ← Module.finrank_mul_finrank F F⟮x⟯, hn, pow_add, this]⟩

lemma Algebra.finrank_eq_one_iff {R S : Type*} [CommRing R] [Nontrivial R]
    [Ring S] [Algebra R S] [Module.Free R S] :
    Module.finrank R S = 1 ↔ Function.Bijective (algebraMap R S) := by
  constructor
  · intro H
    cases subsingleton_or_nontrivial S
    · simp [Module.finrank_zero_of_subsingleton] at H
    obtain ⟨v, hv, h⟩ := finrank_eq_one_iff'.mp H
    simp_rw [Algebra.smul_def] at h
    obtain ⟨c1, e1⟩ := h 1
    have hv : IsUnit v := isUnit_iff_exists.mpr ⟨_, Algebra.commutes c1 v ▸ e1, e1⟩
    obtain ⟨v', e⟩ := h (v * v)
    obtain rfl := hv.mul_right_cancel e
    refine ⟨FaithfulSMul.algebraMap_injective R S, fun x ↦ ?_⟩
    obtain ⟨cx, ex⟩ := h x
    refine ⟨cx * v', by rw [map_mul, ex]⟩
  · intro H
    rw [← (LinearEquiv.ofBijective (Algebra.linearMap R S) H).finrank_eq, Module.finrank_self R]

lemma IntermediateField.finrank_eq_one_iff'
    {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E] {K : IntermediateField F E} :
    Module.finrank K E = 1 ↔ K = ⊤ := by
  constructor
  · rw [Algebra.finrank_eq_one_iff, ← top_le_iff]
    intro H x _
    obtain ⟨⟨x, hx⟩, rfl⟩ := H.2 x
    exact hx
  · rintro rfl; simp

lemma Algebra.trace_eq_zero_of_not_isSeparable {K L : Type*}
    [Field K] [Field L] [Algebra K L] (H : ¬ Algebra.IsSeparable K L) :
    Algebra.trace K L = 0 := by
  obtain ⟨p, hp⟩ := ExpChar.exists K
  have := expChar_ne_zero K p
  ext x
  by_cases h₀ : FiniteDimensional K L; swap
  · rw [Algebra.trace_eq_zero_of_not_exists_basis]
    rintro ⟨s, ⟨b⟩⟩
    exact h₀ (Module.Finite.of_basis b)
  by_cases hx : IsSeparable K x
  · lift x to separableClosure K L using hx
    rw [← IntermediateField.algebraMap_apply, ← Algebra.trace_trace (S := separableClosure K L),
      Algebra.trace_algebraMap]
    obtain ⟨n, hn⟩ := IsPurelyInseparable.finrank_eq (separableClosure K L) L p
    cases n with
    | zero =>
      rw [pow_zero, IntermediateField.finrank_eq_one_iff', separableClosure.eq_top_iff] at hn
      cases H hn
    | succ n =>
      cases hp with
      | zero =>
        rw [one_pow, IntermediateField.finrank_eq_one_iff', separableClosure.eq_top_iff] at hn
        cases H hn
      | prime hprime =>
        rw [hn, pow_succ', mul_smul, LinearMap.map_smul_of_tower, nsmul_eq_mul,
          CharP.cast_eq_zero, zero_mul, LinearMap.zero_apply]
  · rw [trace_eq_finrank_mul_minpoly_nextCoeff]
    obtain ⟨g, hg₁, m, hg₂⟩ := (minpoly.irreducible
      (Algebra.IsIntegral.isIntegral (R := K) x)).hasSeparableContraction p
    cases m with
    | zero =>
      obtain rfl : g = minpoly K x := by simpa using hg₂
      cases hx hg₁
    | succ n =>
      rw [Polynomial.nextCoeff, if_neg, ← hg₂, Polynomial.coeff_expand (by positivity),
        if_neg, neg_zero, mul_zero, LinearMap.zero_apply]
      · rw [Polynomial.natDegree_expand]
        intro h
        have := Nat.dvd_sub (Nat.sub_le _ _) (dvd_mul_left (p ^ (n + 1)) g.natDegree) h
        rw [tsub_tsub_cancel_of_le, Nat.dvd_one] at this
        · obtain rfl : g = minpoly K x := by simpa [this] using hg₂
          cases hx hg₁
        · rw [Nat.one_le_iff_ne_zero]
          have : g.natDegree ≠ 0 := fun e ↦ by
            have := congr(Polynomial.natDegree $hg₂)
            rw [Polynomial.natDegree_expand, e, zero_mul] at this
            exact (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral (R := K) x)).ne this
          positivity
      · exact (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral (R := K) x)).ne'

attribute [local instance] Ideal.Quotient.field in
instance (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] (p : Ideal A)
    [p.IsMaximal] (P : Ideal B) [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)] :
    Algebra.IsSeparable p.ResidueField P.ResidueField := by
  refine Algebra.IsSeparable.of_equiv_equiv
    (.ofBijective _ p.bijective_algebraMap_quotient_residueField)
    (.ofBijective _ P.bijective_algebraMap_quotient_residueField) ?_
  ext x
  simp [RingHom.algebraMap_toAlgebra, Algebra.ofId_apply]
  rfl

attribute [local instance] Ideal.Quotient.field in
instance Algebra.isSeparable_quotient_of_isSeparable_residueField
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] (p : Ideal A)
    [p.IsMaximal] (P : Ideal B) [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable p.ResidueField P.ResidueField] :
    Algebra.IsSeparable (A ⧸ p) (B ⧸ P) := by
  refine Algebra.IsSeparable.of_equiv_equiv
    (.symm <| .ofBijective _ p.bijective_algebraMap_quotient_residueField)
    (.symm <| .ofBijective _ P.bijective_algebraMap_quotient_residueField) ?_
  ext x
  obtain ⟨x, rfl⟩ :=
    (RingEquiv.ofBijective _ p.bijective_algebraMap_quotient_residueField).surjective x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply (RingEquiv.ofBijective _ P.bijective_algebraMap_quotient_residueField).injective
  simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, RingEquiv.symm_apply_apply,
    RingEquiv.apply_symm_apply]
  simp [RingHom.algebraMap_toAlgebra, Algebra.ofId_apply]
  rfl

set_option maxHeartbeats 0 in
attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra Ideal.Quotient.field in
lemma dvd_differentIdeal_of_not_isSeparable
    (A : Type*) {B : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [IsDomain A]
    [IsDedekindDomain B] [NoZeroSMulDivisors A B] [Module.Finite A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [IsDedekindDomain A]
    {p : Ideal A} [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal B) [P.IsMaximal] [P.LiesOver p]
    (H : ¬ Algebra.IsSeparable (A ⧸ p) (B ⧸ P)) : P ∣ differentIdeal A B := by
  obtain ⟨a, ha⟩ : P ∣ p.map (algebraMap A B) :=
    Ideal.dvd_iff_le.mpr (Ideal.map_le_iff_le_comap.mpr Ideal.LiesOver.over.le)
  by_cases hPa : P ∣ a
  · simpa using pow_sub_one_dvd_differentIdeal A P 2 hp
      (by rw [pow_two, ha]; exact mul_dvd_mul_left _ hPa)
  let K := FractionRing A
  let L := FractionRing B
  have : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization _ K _ _
  have : FiniteDimensional K L :=
    Module.Finite_of_isLocalization A B _ _ A⁰
  have hp' := (Ideal.map_eq_bot_iff_of_injective
    (FaithfulSMul.algebraMap_injective A B)).not.mpr hp
  have habot : a ≠ ⊥ := fun ha' ↦ hp' (by simpa [ha'] using ha)
  have hPbot : P ≠ ⊥ := by
    rintro rfl; apply hp'
    rwa [Ideal.bot_mul] at ha
  suffices ∀ x ∈ a, Algebra.intTrace A B x ∈ p by
    have hP : ((P :)⁻¹ : FractionalIdeal B⁰ L) = a / p.map (algebraMap A B) := by
      apply inv_involutive.injective
      simp only [ha, FractionalIdeal.coeIdeal_mul, inv_div, mul_div_assoc]
      rw [div_self (by simpa), mul_one, inv_inv]
    rw [Ideal.dvd_iff_le, differentialIdeal_le_iff (K := K) (L := L) hPbot, hP,
      Submodule.map_le_iff_le_comap]
    intro x hx
    rw [Submodule.restrictScalars_mem, FractionalIdeal.mem_coe,
      FractionalIdeal.mem_div_iff_of_nonzero (by simpa using hp')] at hx
    rw [Submodule.mem_comap, LinearMap.coe_restrictScalars, ← FractionalIdeal.coe_one,
      ← div_self (G₀ := FractionalIdeal A⁰ K) (a := p) (by simpa using hp),
      FractionalIdeal.mem_coe, FractionalIdeal.mem_div_iff_of_nonzero (by simpa using hp)]
    simp only [FractionalIdeal.mem_coeIdeal, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at hx
    intro y hy'
    obtain ⟨y, hy, rfl : algebraMap A K _ = _⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy'
    obtain ⟨z, hz, hz'⟩ := hx _ (Ideal.mem_map_of_mem _ hy)
    have : Algebra.trace K L (algebraMap B L z) ∈ (p : FractionalIdeal A⁰ K) := by
      rw [← Algebra.algebraMap_intTrace (A := A)]
      exact ⟨Algebra.intTrace A B z, this z hz, rfl⟩
    rwa [mul_comm, ← smul_eq_mul, ← LinearMap.map_smul, Algebra.smul_def, mul_comm,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B L, ← hz']
  intros x hx
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Algebra.trace_quotient_eq_of_isDedekindDomain]
  letI : Algebra (A ⧸ p) (B ⧸ a) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.mp
      (Ideal.dvd_iff_le.mp ⟨_, ha.trans (mul_comm _ _)⟩))
  have : IsScalarTower A (A ⧸ p) (B ⧸ a) := .of_algebraMap_eq' rfl
  have : Module.Finite (A ⧸ p) (B ⧸ a) := .of_restrictScalars_finite A _ _
  have := ((Ideal.prime_iff_isPrime hPbot).mpr inferInstance)
  rw [← this.irreducible.gcd_eq_one_iff, ← Ideal.isCoprime_iff_gcd] at hPa
  letI e : (B ⧸ p.map (algebraMap A B)) ≃ₐ[A ⧸ p] ((B ⧸ P) × B ⧸ a) :=
    { __ := (Ideal.quotEquivOfEq ha).trans (Ideal.quotientMulEquivQuotientProd P a hPa),
      commutes' := Quotient.ind fun _ ↦ rfl }
  have hx' : (e (Ideal.Quotient.mk _ x)).2 = 0 := by
    simpa [e, Ideal.Quotient.eq_zero_iff_mem]
  rw [← Algebra.trace_eq_of_algEquiv e, Algebra.trace_prod_apply,
    Algebra.trace_eq_zero_of_not_isSeparable H, LinearMap.zero_apply, zero_add, hx', map_zero]

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra Ideal.Quotient.field in
theorem not_dvd_differentIdeal_of_isCoprime
    (A : Type*) {B : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [IsDomain A]
    [IsDedekindDomain B] [NoZeroSMulDivisors A B] [Module.Finite A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [IsDedekindDomain A]
    {p : Ideal A} [p.IsMaximal]
    (P Q : Ideal B) (hPQ : IsCoprime P Q)
    (hP : P * Q = Ideal.map (algebraMap A B) p) [P.IsMaximal]
    [Finite (A ⧸ p)] :
    ¬ P ∣ differentIdeal A B := by
  have : P.LiesOver p := by
    constructor
    refine ‹p.IsMaximal›.eq_of_le ?_ ?_
    · simpa using ‹P.IsMaximal›.ne_top
    · rw [← Ideal.map_le_iff_le_comap, ← hP]
      exact Ideal.mul_le_right
  refine not_dvd_differentIdeal_of_isCoprime_of_isSeparable A P Q hPQ hP

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra Ideal.Quotient.field in
theorem not_dvd_differentIdeal_iff
    (A : Type*) {B : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [IsDomain A]
    [IsDedekindDomain B] [NoZeroSMulDivisors A B] [Module.Finite A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [IsDedekindDomain A] (P : Ideal B) [P.IsPrime] :
    ¬ P ∣ differentIdeal A B ↔ Algebra.IsUnramifiedAt A P := by
  classical
  by_cases hPbot : P = ⊥
  · subst hPbot
    simp_rw [← Ideal.zero_eq_bot, zero_dvd_iff]
    simp only [Submodule.zero_eq_bot, differentIdeal_ne_bot, not_false_eq_true, true_iff]
    let K := FractionRing A
    let L := FractionRing B
    have : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
      IsIntegralClosure.isLocalization _ K _ _
    have : FiniteDimensional K L :=
      Module.Finite_of_isLocalization A B _ _ A⁰
    have : IsLocalization B⁰ (Localization.AtPrime (⊥ : Ideal B)) := by
      convert (inferInstanceAs
        (IsLocalization (⊥ : Ideal B).primeCompl (Localization.AtPrime (⊥ : Ideal B))))
      ext; simp [Ideal.primeCompl]
    refine (Algebra.FormallyUnramified.iff_of_equiv (A := L)
      ((IsLocalization.algEquiv B⁰ _ _).restrictScalars A)).mp ?_
    have : Algebra.FormallyUnramified K L := by
      rwa [Algebra.FormallyUnramified.iff_isSeparable]
    refine .comp A K L
  have hp : P.under A ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hPbot
  have hp' := (Ideal.map_eq_bot_iff_of_injective
    (FaithfulSMul.algebraMap_injective A B)).not.mpr hp
  have := Ideal.IsPrime.isMaximal inferInstance hPbot
  constructor
  · intro H
    · rw [Algebra.isUnramifiedAt_iff_map_eq2 (p := P.under A)]
      constructor
      · suffices Algebra.IsSeparable (A ⧸ P.under A) (B ⧸ P) by infer_instance
        contrapose! H
        exact dvd_differentIdeal_of_not_isSeparable A hp P H
      · rw [← Ideal.ramificationIdx_eq_one_iff_of_isDedekindDomain hPbot]
        apply Ideal.ramificationIdx_spec
        · simp [Ideal.map_le_iff_le_comap]
        · contrapose! H
          rw [← pow_one P, show 1 = 2 - 1 by norm_num]
          apply pow_sub_one_dvd_differentIdeal _ _ _ hp
          simpa [Ideal.dvd_iff_le] using H
  · intro H
    obtain ⟨Q, h₁, h₂⟩ := Ideal.eq_prime_pow_mul_coprime hp' P
    rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hp' ‹_› hPbot,
      Ideal.ramificationIdx_eq_one_of_isUnramifiedAt hPbot, pow_one] at h₂
    obtain ⟨h₃, h₄⟩ := (Algebra.isUnramifiedAt_iff_map_eq2 (p := P.under A) _ _).mp H
    have := Algebra.isSeparable_quotient_of_isSeparable_residueField A B (P.under A) P
    exact not_dvd_differentIdeal_of_isCoprime_of_isSeparable
      A P Q (Ideal.isCoprime_iff_sup_eq.mpr h₁) h₂.symm

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra Ideal.Quotient.field in
theorem dvd_differentIdeal_iff
    (A : Type*) {B : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [IsDomain A]
    [IsDedekindDomain B] [NoZeroSMulDivisors A B] [Module.Finite A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [IsDedekindDomain A]
    (P : Ideal B) (hP : P ≠ ⊥) [P.IsPrime] [Module.Finite ℤ A] [CharZero A] :
    P ∣ differentIdeal A B ↔ 1 < Ideal.ramificationIdx (algebraMap A B) (P.under A) P := by
  rw [← not_iff_not, not_dvd_differentIdeal_iff A P, not_lt,
    Algebra.isUnramifiedAt_iff_of_isDedekindDomain hP, le_antisymm_iff,
    and_iff_left]
  rw [Nat.one_le_iff_ne_zero]
  refine Ideal.IsDedekindDomain.ramificationIdx_ne_zero ?_ ‹_› Ideal.map_comap_le
  exact (Ideal.map_eq_bot_iff_of_injective
    (FaithfulSMul.algebraMap_injective A B)).not.mpr (mt Ideal.eq_bot_of_comap_eq_bot hP)
