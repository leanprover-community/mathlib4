import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.Int
import Mathlib.NumberTheory.KroneckerWeber.DedekindDomain
import Mathlib.NumberTheory.KroneckerWeber.Different
import Mathlib.NumberTheory.KroneckerWeber.Unramified
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Tactic.Qify

variable {K 𝒪 : Type*} [Field K] [NumberField K] [CommRing 𝒪] [Algebra 𝒪 K]
variable [IsFractionRing 𝒪 K] [IsIntegralClosure 𝒪 ℤ K] [IsDedekindDomain 𝒪] [CharZero 𝒪]
variable [Module.Finite ℤ 𝒪]

open nonZeroDivisors

-- @[simp]
-- lemma Int.card_quotient_span_singleton (n : ℤ) :
--     Nat.card (ℤ ⧸ Ideal.span {n}) = n.natAbs := by
--   simp [Nat.card_congr (Int.quotientSpanEquivZMod n).toEquiv]

-- @[simp]
-- noncomputable
-- def Int.idealEquiv : Ideal ℤ ≃ ℕ where
--   toFun I := Nat.card (ℤ ⧸ I)
--   invFun n := Ideal.span {(n : ℤ)}
--   left_inv I := by
--     dsimp only
--     obtain ⟨n, rfl⟩ : ∃ n : ℕ, I = .span {(n : ℤ)} :=
--       ⟨(Submodule.IsPrincipal.generator I).natAbs, by
--         rw [Int.span_natAbs, Ideal.span_singleton_generator]⟩
--     simp
--   right_inv n := by simp

lemma Algebra.toMatrix_dualBasis {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L) :
    LinearMap.toMatrix b ((traceForm K L).dualBasis (traceForm_nondegenerate K L) b) .id =
      traceMatrix K b := by
  ext; simp [Basis.toMatrix_apply, mul_comm]

lemma AddSubgroup.toIntSubmodule_closure {E : Type*} [AddCommGroup E] (s : Set E) :
    (closure s).toIntSubmodule = .span ℤ s := by
  apply le_antisymm
  · show closure s ≤ (Submodule.span ℤ s).toAddSubgroup
    rw [closure_le]
    exact Submodule.subset_span
  · rw [Submodule.span_le]
    exact subset_closure

lemma Basis.det_comp_eq_det_toMatrix
    {R M N ι : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [DecidableEq ι] [Fintype ι] (f : M →ₗ[R] N) (bM : Basis ι R M) (bN : Basis ι R N) :
    bN.det (f ∘ bM) = (LinearMap.toMatrix bM bN f).det := by
  rw [Basis.det_comp_basis]
  rw [← LinearMap.det_toMatrix bN, LinearMap.toMatrix_comp _ bM]
  simp

lemma AddSubfroup.index_eq_natAbs_det {E : Type*} [AddCommGroup E] (N : AddSubgroup E)
    {ι : Type*} [DecidableEq ι] [Fintype ι] (bN : Basis ι ℤ N) (bE : Basis ι ℤ E) :
    N.index = (bE.det (bN ·)).natAbs := by
  obtain ⟨n, B⟩ := N.toIntSubmodule.smithNormalForm bE
  refine B.toAddSubgroup_index_eq_ite.trans ?_
  have : Fintype.card ι = n := by
    simpa [← Module.finrank_eq_card_basis bN] using Module.finrank_eq_card_basis B.bN
  let e : Fin n ≃ ι := .ofBijective B.f (B.f.2.bijective_of_nat_card_le (by simp [this]))
  have hf : ⇑B.f = e := rfl
  rw [if_pos this.symm]
  simp only [Ideal.span_singleton_toAddSubgroup_eq_zmultiples, Int.index_zmultiples]
  trans (B.bM.det (B.bN <| e.symm ·)).natAbs
  · zify
    simp_rw [B.snf, ← AlternatingMap.coe_multilinearMap, MultilinearMap.map_smul_univ, hf]
    simp only [Equiv.apply_symm_apply, AlternatingMap.coe_multilinearMap, smul_eq_mul,
      Basis.det_self, mul_one, Finset.abs_prod, e.symm.prod_comp]
  · have : bE.det (LinearMap.id (R := ℤ) ∘ B.bM) *
      B.bM.det (N.subtype.toIntLinearMap ∘ B.bN.reindex (M := N) e) *
        (B.bN.reindex (M := N) e).det (LinearMap.id (R := ℤ) ∘ bN) =
        bE.det (N.subtype.toIntLinearMap ∘ bN) := by
      simp_rw [Basis.det_comp_eq_det_toMatrix, ← Matrix.det_mul, ← LinearMap.toMatrix_comp]
      rfl
    simp only [LinearMap.id_coe, CompTriple.comp_eq, AddMonoidHom.coe_toIntLinearMap,
      AddSubgroup.coeSubtype, Basis.coe_reindex, Function.comp_def] at this
    zify
    rw [← this]
    simp only [abs_mul, Int.isUnit_iff_abs_eq.mp (Basis.isUnit_det _ _), one_mul, mul_one]
    rfl

lemma AddSubgroup.relIndex_eq_det
    {E : Type*} [AddCommGroup E] [Module ℚ E] (L₁ L₂ : AddSubgroup E) (H : L₁ ≤ L₂)
    {ι : Type*} [DecidableEq ι] [Fintype ι] (b₁ b₂ : Basis ι ℚ E)
    (h₁ : L₁ = .closure (Set.range b₁)) (h₂ : L₂ = .closure (Set.range b₂)) :
    L₁.relindex L₂ = |b₂.det b₁| := by
  let b₁' : Basis ι ℤ L₁ := .mk (v := fun i ↦ ⟨b₁ i, h₁.ge (AddSubgroup.subset_closure (by simp))⟩)
    (.of_comp L₁.subtype.toIntLinearMap
      (.restrict_scalars_algebras (S := ℚ) Int.cast_injective b₁.linearIndependent))
    (by rw [← Submodule.map_le_map_iff_of_injective (f := L₁.toIntSubmodule.subtype)
          Subtype.val_injective, Submodule.map_span, ← Set.range_comp, Submodule.map_top,
          Submodule.range_subtype, ← AddSubgroup.toIntSubmodule_closure]; exact h₁.le)
  let b₂' : Basis ι ℤ L₂ := .mk (v := fun i ↦ ⟨b₂ i, h₂.ge (AddSubgroup.subset_closure (by simp))⟩)
    (.of_comp L₂.subtype.toIntLinearMap
      (.restrict_scalars_algebras (S := ℚ) Int.cast_injective b₂.linearIndependent))
    (by rw [← Submodule.map_le_map_iff_of_injective (f := L₂.toIntSubmodule.subtype)
          Subtype.val_injective, Submodule.map_span, ← Set.range_comp, Submodule.map_top,
          Submodule.range_subtype, ← AddSubgroup.toIntSubmodule_closure]; exact h₂.le)
  have hb₂' : Finsupp.mapRange.linearMap (Algebra.linearMap ℤ ℚ) ∘ₗ b₂'.repr.toLinearMap =
      b₂.repr.toLinearMap.restrictScalars ℤ ∘ₗ L₂.subtype.toIntLinearMap := by
    refine b₂'.ext fun i ↦ ?_
    trans Finsupp.single i 1
    · simp
    · simp [b₂']
  have := AddSubfroup.index_eq_natAbs_det (L₁.addSubgroupOf L₂)
    (b₁'.map (AddSubgroup.addSubgroupOfEquivOfLe H).toIntLinearEquiv.symm) b₂'
  rw [AddSubgroup.relindex, this, Basis.det_apply, Nat.cast_natAbs, Int.cast_abs,
    ← eq_intCast (algebraMap ℤ ℚ), RingHom.map_det, Basis.det_apply]
  congr 2
  ext i j
  simpa [Basis.toMatrix_apply, b₁'] using congr($hb₂' ⟨b₁ j, _⟩ i)



lemma NumberField.absNorm_differentIdeal : (differentIdeal ℤ 𝒪).absNorm = (discr K).natAbs := by
  refine (differentIdeal ℤ 𝒪).toAddSubgroup.relindex_top_right.symm.trans ?_
  rw [← Submodule.comap_map_eq_of_injective (f := Algebra.linearMap 𝒪 K)
    (FaithfulSMul.algebraMap_injective 𝒪 K) (differentIdeal ℤ 𝒪)]
  refine (AddSubgroup.relindex_comap (IsLocalization.coeSubmodule K
    (differentIdeal ℤ 𝒪)).toAddSubgroup (algebraMap 𝒪 K).toAddMonoidHom ⊤).trans ?_
  have := FractionalIdeal.quotientEquiv (R := 𝒪) (K := K) 1 (differentIdeal ℤ 𝒪)
    (differentIdeal ℤ 𝒪)⁻¹ 1 (by simp [differentIdeal_ne_bot]) FractionalIdeal.coeIdeal_le_one
    (le_inv_of_le_inv₀ (by simp [pos_iff_ne_zero, differentIdeal_ne_bot])
      (by simpa using FractionalIdeal.coeIdeal_le_one)) one_ne_zero one_ne_zero
  have := Nat.card_congr this.toEquiv
  refine this.trans ?_
  rw [FractionalIdeal.coe_one, coeIdeal_differentIdeal (K := ℚ), inv_inv]
  let b := integralBasis K
  let b' := (Algebra.traceForm ℚ K).dualBasis (traceForm_nondegenerate ℚ K) b
  have hb : Submodule.span ℤ (Set.range b) = (1 : Submodule 𝒪 K).restrictScalars ℤ := by
    ext
    let e := IsIntegralClosure.equiv ℤ (RingOfIntegers K) K 𝒪
    simpa [e.symm.exists_congr_left, e] using mem_span_integralBasis K
  qify
  refine (AddSubgroup.relIndex_eq_det (1 : Submodule 𝒪 K).toAddSubgroup (FractionalIdeal.dual
    ℤ ℚ 1 : FractionalIdeal 𝒪⁰ K).coeToSubmodule.toAddSubgroup ?_ b b' ?_ ?_).trans ?_
  · rw [Submodule.toAddSubgroup_le, ← FractionalIdeal.coe_one]
    exact FractionalIdeal.one_le_dual_one ℤ ℚ (L := K) (B := 𝒪)
  · apply AddSubgroup.toIntSubmodule.injective
    rw [AddSubgroup.toIntSubmodule_closure, hb]
    rfl
  · apply AddSubgroup.toIntSubmodule.injective
    rw [AddSubgroup.toIntSubmodule_closure, ← LinearMap.BilinForm.dualSubmodule_span_of_basis, hb]
    simp
    rfl
  · simp only [Basis.det_apply, discr, Algebra.discr]
    rw [← eq_intCast (algebraMap ℤ ℚ), RingHom.map_det]
    congr! 2
    ext i j
    simp [b', Basis.toMatrix_apply, mul_comm (RingOfIntegers.basis K i),
      b, integralBasis_apply, ← map_mul, Algebra.trace_localization ℤ ℤ⁰]

lemma NumberField.discr_mem_differentIdeal : ↑(discr K) ∈ differentIdeal ℤ 𝒪 := by
  have := (differentIdeal ℤ 𝒪).absNorm_mem
  cases (discr K).natAbs_eq with
  | inl h =>
    rwa [absNorm_differentIdeal (K := K), ← Int.cast_natCast, ← h] at this
  | inr h =>
    rwa [absNorm_differentIdeal (K := K), ← Int.cast_natCast, Int.eq_neg_comm.mp h,
      Int.cast_neg, neg_mem_iff] at this

lemma Ideal.exists_isMaximal_dvd_of_dvd_absNorm
    {R : Type*} [CommRing R] [IsDedekindDomain R] [CharZero R] [Module.Finite ℤ R]
    {p : ℤ} (hp : Prime p) (I : Ideal R) (hI : p ∣ I.absNorm) :
    ∃ P : Ideal R, P.IsMaximal ∧ P.under ℤ = .span {p} ∧ P ∣ I := by
  have hpMax : (Ideal.span {p}).IsMaximal :=
    ((Ideal.span_singleton_prime hp.ne_zero).mpr hp).isMaximal (by simpa using hp.ne_zero)
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    obtain ⟨Q, hQ, e⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := R) (Ideal.span {p})
      (fun x ↦ by simp +contextual)
    exact ⟨Q, hQ, e, dvd_zero _⟩
  | h₂ I hI' =>
    obtain rfl : I = ⊤ := by simpa using hI'
    cases hp.not_dvd_one (by simpa using hI)
  | h₃ I P hI' hP IH =>
    simp only [_root_.map_mul, Nat.cast_mul, hp.dvd_mul] at hI
    cases hI with
    | inl hI =>
      have := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
      refine ⟨P, this, (hpMax.eq_of_le (by simpa using this.ne_top) ?_).symm, dvd_mul_right _ _⟩
      rw [← Int.span_natAbs]
      simp only [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, eq_intCast, Int.cast_natCast]
      letI := Ideal.fintypeQuotientOfFreeOfNeBot P hP.ne_zero
      letI := Ideal.Quotient.field P
      obtain ⟨q, hqR⟩ := CharP.exists (R ⧸ P)
      obtain ⟨n, hq, e⟩ := FiniteField.card (R ⧸ P) q
      have h₁ : P.absNorm = q ^ (n : ℕ) := (Nat.card_eq_fintype_card.trans e:)
      have h₂ := hp.associated_of_dvd (Nat.prime_iff_prime_int.mp hq)
        (by simpa [h₁, hp.dvd_pow_iff_dvd n.ne_zero] using hI)
      simp only [Int.associated_iff_natAbs, Int.natAbs_ofNat] at h₂
      rw [h₂, ← Ideal.IsPrime.pow_mem_iff_mem (I := P) inferInstance _ n.pos,
        ← Nat.cast_pow, ← h₁]
      exact P.absNorm_mem
    | inr h =>
      obtain ⟨Q, h₁, h₂, h₃⟩ := IH h
      refine ⟨Q, h₁, h₂, dvd_mul_of_dvd_right h₃ _⟩

lemma NumberField.not_dvd_discr_iff_forall_pow_mem (p : ℤ) (hp : Prime p) :
    ¬ p ∣ discr K ↔ ∀ (P : Ideal 𝒪), P.IsPrime → P.under ℤ = Ideal.span {p} → ↑p ∉ P ^ 2 := by
  constructor
  · intro H P hP hP' h
    have : (Ideal.span {(p : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal
      ((Ideal.span_singleton_prime hp.ne_zero).mpr hp) (by simpa using hp.ne_zero)
    have := pow_sub_one_dvd_differentIdeal ℤ (p := Ideal.span {(p : ℤ)}) P 2
      (by simpa using hp.ne_zero) (by simpa [Ideal.map_span] using h)
    simp only [Nat.add_one_sub_one, pow_one, Ideal.dvd_iff_le] at this
    replace this := (Ideal.comap_mono this).trans_eq hP'
      (NumberField.discr_mem_differentIdeal (K := K))
    exact H (Ideal.mem_span_singleton.mp this)
  · intro H h
    rw [← Int.dvd_natAbs, ← absNorm_differentIdeal (𝒪 := 𝒪)] at h
    obtain ⟨P, hP, h₁, h₂⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm hp _ h
    refine H P hP.isPrime h₁ ?_
    have hPbot : P ≠ ⊥ := fun e ↦ by simpa [e, hp.ne_zero] using h₁.symm
    have := Ideal.fintypeQuotientOfFreeOfNeBot (P.under ℤ) (by simpa [h₁] using hp.ne_zero)
    have := Nat.succ_le.mpr ((dvd_differentIdeal_iff ℤ P hPbot).mp h₂)
    simpa [h₁, Ideal.map_span, Ideal.span_singleton_le_iff_mem] using
      Ideal.le_pow_ramificationIdx.trans (Ideal.pow_le_pow_right this)

lemma NumberField.not_dvd_discr_iff (p : ℤ) (hp : Prime p) :
    ¬ p ∣ discr K ↔ ∀ (P : Ideal 𝒪) (_ : P.IsPrime), P.under ℤ = Ideal.span {p} →
      Algebra.IsUnramifiedAt ℤ P := by
  rw [not_dvd_discr_iff_forall_pow_mem p hp (𝒪 := 𝒪)]
  refine forall₃_congr fun P hP e ↦ ?_
  letI := Ideal.LiesOver.mk e.symm
  have : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain, ← not_ne_iff,
    Ideal.ramificationIdx_ne_one_iff, e, Ideal.map_span, Set.image_singleton,
    Ideal.span_singleton_le_iff_mem, eq_intCast]
  · rintro rfl
    simp [eq_comm (a := ⊥), hp.ne_zero] at e

lemma NumberField.dvd_discr_iff (p : ℤ) (hp : Prime p) :
    p ∣ discr K ↔ ∃ (P : Ideal 𝒪) (_ : P.IsPrime), P.under ℤ = Ideal.span {p} ∧
      ¬ Algebra.IsUnramifiedAt ℤ P := by
  rw [← not_iff_not, not_dvd_discr_iff p hp (𝒪 := 𝒪)]
  push_neg
  rfl

lemma NumberField.exists_ramified (H : 1 < Module.finrank ℚ K) :
    ∃ (P : Ideal 𝒪) (_ : P.IsMaximal), P ≠ ⊥ ∧ ¬ Algebra.IsUnramifiedAt ℤ P := by
  have := NumberField.abs_discr_gt_two H
  obtain ⟨q, hq, hqK⟩ := Int.exists_prime_and_dvd (n := discr K) (by zify; linarith)
  have := (dvd_discr_iff (𝒪 := 𝒪) q hq).mp hqK
  push_neg at this
  obtain ⟨P, hP, h, H⟩ := this
  have : P ≠ ⊥ := by
    rintro rfl
    simp [eq_comm (a := ⊥), hq.ne_zero] at h
  exact ⟨P, hP.isMaximal this, this, H⟩

lemma NumberField.exists_ramified_of_isGalois [IsGalois ℚ K]
    (H : 1 < Module.finrank ℚ K) :
    ∃ p : ℤ, Prime p ∧ ∀ (P : Ideal 𝒪) (_ : P.IsPrime),
      P.under ℤ = .span {p} → ¬ Algebra.IsUnramifiedAt ℤ P := by
  have := NumberField.abs_discr_gt_two H
  obtain ⟨q, hq, hqK⟩ := Int.exists_prime_and_dvd (n := discr K) (by zify; linarith)
  refine ⟨q, hq, fun P hP₀ e hP ↦ ?_⟩
  have hP' : P ≠ ⊥ := by rintro rfl; simp [eq_comm (a := ⊥), hq.ne_zero] at e
  have := (dvd_discr_iff (𝒪 := 𝒪) q hq).mp hqK
  push_neg at this
  obtain ⟨Q, hQ, h, H⟩ := this
  have hQ' : Q ≠ ⊥ := by rintro rfl; simp [eq_comm (a := ⊥), hq.ne_zero] at h
  letI := IsIntegralClosure.MulSemiringAction ℤ ℚ K 𝒪
  have := Algebra.isInvariant_of_isGalois ℤ ℚ K 𝒪
  obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq ℤ 𝒪 (K ≃ₐ[ℚ] K) P Q (e.trans h.symm)
  rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain ‹_›,
    ← Ideal.ramificationIdxIn_eq_ramificationIdx _ _ (K := ℚ) (L := K)] at hP H
  exact H (h ▸ e ▸ hP)
