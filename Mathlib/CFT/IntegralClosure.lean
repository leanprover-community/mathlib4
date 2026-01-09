module

public import Mathlib.CFT.IsStandardEtale
public import Mathlib.CFT.StandardSmooth
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Smooth.IntegralClosure

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]


open Polynomial

variable {B : Type*} [CommRing B] [Algebra R B]

attribute [local instance] Polynomial.algebra in
/-- Let `S` be an `R`-algebra and `f : S[X]` be a monic polynomial with `R`-integral coefficients.
Suppose `y` in `B = S[X]/f` is `R`-integral, then `f' * y` is the image of some `g : S[X]` with
`R`-integral coefficients. -/
-- We can also know that `deg g = deg f - 1`. Upgrade the lemma if we care.
lemma exists_derivative_mul_eq_and_isIntegral_coeff
    {φ : S[X] →ₐ[R] B} (hφ : Function.Surjective φ) {f : S[X]} (hf : f.Monic)
    (hf' : ∀ i, IsIntegral R (f.coeff i))
    (hfx : RingHom.ker φ.toRingHom = .span {f}) {y : B} (hy : IsIntegral R y) :
    ∃ (g : S[X]), φ f.derivative * y = φ g ∧ ∀ i, IsIntegral R (g.coeff i) := by
  cases subsingleton_or_nontrivial B
  · exact ⟨0, Subsingleton.elim _ _, by simp [isIntegral_zero]⟩
  have hfd : f.natDegree ≠ 0 := by
    rw [ne_eq, hf.natDegree_eq_zero]
    rintro rfl
    simpa using (RingHom.ker_ne_top φ.toRingHom).symm.trans_eq hfx
  classical
  let := (φ.toRingHom.comp C).toAlgebra
  have : IsScalarTower R S B := .of_algebraMap_eq' (φ.comp CAlgHom).comp_algebraMap.symm
  have := (algebraMap S B).domain_nontrivial
  obtain ⟨y, rfl⟩ := hφ y
  obtain ⟨S', _, _, _, _, _, hS'⟩ := hf.exists_splits_map
  obtain ⟨m, hm⟩ := Polynomial.splits_iff_exists_multiset.mp hS'
  simp only [hf.map _, Monic.leadingCoeff, map_one, one_mul] at hm
  algebraize [(algebraMap S S').comp (algebraMap R S)]
  have hm' : ∀ a ∈ m, IsIntegral R a := by
    refine fun a ham ↦ .of_aeval_monic_of_isIntegral_coeff (hf.map (algebraMap _ _)) ?_ ?_ ?_
    · rwa [hf.natDegree_map]
    · rw [hm, eval_multiset_prod, Multiset.prod_eq_zero]
      · exact isIntegral_zero
      · simpa using ⟨a, ham, by simp⟩
    · simp only [coeff_map]
      exact fun _ ↦ (hf' _).algebraMap
  have hmc : m.card = f.natDegree := by
    simpa [hf.natDegree_map, natDegree_multiset_prod_of_monic] using congr(($hm).natDegree).symm
  have H : (f.derivative * y %ₘ f).map (algebraMap S S') =
        (m.map fun x ↦ ((m.erase x).map (X - C ·)).prod * C (aeval x y)).sum := by
    have ⟨g, hg⟩ : f.map (algebraMap _ _) ∣ (f.derivative * y).map (algebraMap S S') -
        (m.map fun x ↦ ((m.erase x).map (X - C ·)).prod * C (aeval x y)).sum := by
      rw [Polynomial.map_mul, ← Polynomial.derivative_map, hm, derivative_prod,
        ← Multiset.sum_map_mul_right, ← Multiset.sum_map_sub]
      refine Multiset.dvd_sum ?_
      simp only [derivative_sub, derivative_X, derivative_C, sub_zero, mul_one, ← mul_sub,
        Multiset.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro a ham
      conv_lhs => rw [← Multiset.cons_erase ham]
      rw [Multiset.map_cons, Multiset.prod_cons, mul_comm]
      refine mul_dvd_mul_left _ ?_
      rw [Polynomial.dvd_iff_isRoot]
      simp
    rw [map_modByMonic _ hf]
    refine (div_modByMonic_unique g _ (hf.map _) ⟨(sub_eq_iff_eq_add'.mp hg).symm, ?_⟩).2
    refine degree_lt_degree ?_
    rw [hf.natDegree_map, ← Nat.le_sub_one_iff_lt (Ne.bot_lt hfd)]
    refine (natDegree_multiset_sum_le _).trans (Multiset.max_le_of_forall_le _ _ ?_)
    simp only [Multiset.map_map, Function.comp_apply, Multiset.mem_map, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂]
    refine fun a ha ↦ (natDegree_mul_C_le _ _).trans ((natDegree_multiset_prod_le _).trans ?_)
    simp [ha, hmc]
  have : IsScalarTower R[X] S[X] S'[X] := .of_algebraMap_eq' (mapRingHom_comp ..).symm
  have H' : IsIntegral R[X] (f.derivative * y %ₘ f) := by
    refine .tower_bot (B := S'[X]) (map_injective _ (FaithfulSMul.algebraMap_injective S S')) ?_
    simp only [algebraMap_def, coe_mapRingHom, H]
    refine .multiset_sum ?_
    simp only [Multiset.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    refine fun a ham ↦ .mul (.multiset_prod ?_) ?_
    · simp only [Multiset.mem_map, Polynomial.isIntegral_iff_isIntegral_coeff, forall_exists_index,
        and_imp, forall_apply_eq_imp_iff₂, coeff_sub]
      exact fun b hbm n ↦ .sub (by simp [coeff_X, apply_ite, isIntegral_one, isIntegral_zero])
        (by simp [coeff_C, apply_ite, isIntegral_zero, hm' b (Multiset.mem_of_mem_erase hbm)])
    · let ψ : B →ₐ[R] S' := AlgHom.liftOfSurjective _ hφ ((aeval a).restrictScalars R) <| by
        rw [hfx, Ideal.span_le]
        suffices (m.map (a - ·)).prod = 0 by simpa [← eval_map_algebraMap, hm, eval_multiset_prod]
        rw [Multiset.prod_eq_zero]
        simpa using ⟨a, ham, by simp⟩
      simpa [Polynomial.isIntegral_iff_isIntegral_coeff,
        coeff_C, apply_ite, isIntegral_zero, ψ] using hy.map ψ
  refine ⟨_, ?_, Polynomial.isIntegral_iff_isIntegral_coeff.mp H'⟩
  rw [modByMonic_eq_sub_mul_div _ hf, map_sub, map_mul, map_mul,
    show φ f = 0 from hfx.ge (Ideal.mem_span_singleton_self _), zero_mul, sub_zero]

lemma Polynomial.Monic.leadingCoeff_C_mul {R : Type*} [CommRing R] {p : R[X]}
    (hp : p.Monic) (r : R) : (C r * p).leadingCoeff = r := by
  by_cases hr : r = 0; · simp_all
  rw [← Polynomial.coeff_natDegree, natDegree_C_mul_of_mul_ne_zero (by simp_all), coeff_C_mul,
    hp.coeff_natDegree, mul_one]

/-- If `t` is `R`-integral in `S[M⁻¹]` where `M` is a submonoid of `R`,
then `m • t` is integral in `S` for some `m ∈ M`. -/
lemma IsLocalization.Away.exists_isIntegral_smul_of_isIntegral_map
    {R S Sₘ : Type*} [CommRing R] [CommRing S] [CommRing Sₘ] [Algebra R S] [Algebra S Sₘ]
    [Algebra R Sₘ] [IsScalarTower R S Sₘ] {r : S} (hr : IsIntegral R r)
    [IsLocalization.Away r Sₘ] {x : S}
    (hx : IsIntegral R (algebraMap S Sₘ x)) : ∃ n, IsIntegral R (r ^ n * x) := by
  nontriviality S
  obtain ⟨p, hpm, hp⟩ := hx
  simp only [IsScalarTower.algebraMap_eq R S Sₘ, ← hom_eval₂,
    IsLocalization.map_eq_zero_iff (.powers r), Subtype.exists, Submonoid.mem_powers_iff,
    exists_prop, exists_exists_eq_and] at hp
  obtain ⟨m, hm⟩ := hp
  have := isIntegral_trans (R := R) _ (isIntegral_leadingCoeff_smul (R := integralClosure R S)
    (C ⟨r, hr⟩ ^ m * p.map (algebraMap _ _)) x (by simpa [← aeval_def] using hm))
  rw [← map_pow, (hpm.map _).leadingCoeff_C_mul] at this
  exact ⟨m, this⟩

open TensorProduct

attribute [local instance] Polynomial.algebra in
theorem mem_adjoin_map_integralClosure_of_isStandardEtale
    {B : Type*} [CommRing B] [Algebra R B] [Algebra.IsStandardEtale R S]
    (x : S ⊗[R] B) (hx : IsIntegral S x) :
    x ∈ Algebra.adjoin S
      ((integralClosure R B).map Algebra.TensorProduct.includeRight : Subalgebra R (S ⊗[R] B)) := by
  have 𝓟 := Classical.ofNonempty (α := StandardEtalePresentation R S)
  obtain ⟨n, hx⟩ : ∃ n, ∀ m, IsIntegral R ((aeval 𝓟.x 𝓟.g) ^ (n + m) • x) := by
    let e := 𝓟.equivRing.trans 𝓟.equivAwayAdjoinRoot
    let := (e.symm.toAlgHom.comp (IsScalarTower.toAlgHom R (AdjoinRoot 𝓟.f) _)).toAlgebra
    have := IsScalarTower.of_algebraMap_eq'
      (e.symm.toAlgHom.comp (IsScalarTower.toAlgHom R (AdjoinRoot 𝓟.f) _)).comp_algebraMap.symm
    have := IsLocalization.isLocalization_of_algEquiv (R := AdjoinRoot 𝓟.f) (.powers (.mk _ 𝓟.g))
      { toRingEquiv := e.symm.toRingEquiv, commutes' := by simp [RingHom.algebraMap_toAlgebra] }
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (R := AdjoinRoot 𝓟.f) (.powers (.mk _ 𝓟.g)) _ hx
    replace hm := fun k : ℕ ↦ (isIntegral_algebraMap (x := AdjoinRoot.mk 𝓟.f 𝓟.g ^ k)).mul hm
    simp only [Submonoid.smul_def, ← @IsScalarTower.algebraMap_smul (AdjoinRoot 𝓟.f) S,
      ← map_pow, ← Algebra.smul_def, ← mul_smul, ← map_mul, ← pow_add, add_comm _ m] at hm
    simp_rw [map_pow] at hm
    have := 𝓟.monic_f.finite_adjoinRoot
    suffices algebraMap (AdjoinRoot 𝓟.f) S (.mk _ 𝓟.g) = aeval 𝓟.x 𝓟.g from
      ⟨m, fun k ↦ this ▸ isIntegral_trans (R := R) _ (hm k)⟩
    simp [RingHom.algebraMap_toAlgebra, e, StandardEtalePair.equivAwayAdjoinRoot,
      ← aeval_def, ← aeval_algHom_apply]
  let 𝓟' := 𝓟.baseChange (A := B)
  let e := 𝓟'.equivRing.trans 𝓟'.equivAwayAdjoinRoot
  obtain ⟨x, rfl⟩ := (Algebra.TensorProduct.comm _ _ _).surjective x
  obtain ⟨x, rfl⟩ := e.symm.surjective x
  obtain ⟨x, ⟨_, m, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq
    (R := AdjoinRoot 𝓟'.f) (.powers (.mk _ 𝓟'.g)) x
  have hfg : IsIntegral R (AdjoinRoot.mk 𝓟'.f 𝓟'.g) := by
    have := 𝓟.monic_f.finite_adjoinRoot
    let e : AdjoinRoot 𝓟.f →ₐ[R] AdjoinRoot 𝓟'.f :=
      AdjoinRoot.mapAlgHom (Algebra.ofId _ _) _ _ (dvd_refl _)
    convert (Algebra.IsIntegral.isIntegral (R := R) (AdjoinRoot.mk 𝓟.f 𝓟.g)).map e
    have : (AdjoinRoot.mk 𝓟'.f).comp (mapRingHom (algebraMap R B)) =
        e.toRingHom.comp (AdjoinRoot.mk _) := by ext <;> simp [e]
    exact congr($this 𝓟.g)
  have heg (g : R[X]) : e (1 ⊗ₜ aeval 𝓟.x g) =
      algebraMap _ _ (AdjoinRoot.mk 𝓟'.f (g.map (algebraMap _ _))) := by
    trans e (aeval (1 ⊗ₜ 𝓟.x) (g.map (algebraMap _ B)))
    · rw [← Algebra.TensorProduct.includeRight_apply, ← aeval_algHom_apply]
      simp [StandardEtalePresentation.baseChange, 𝓟']
    rw [← e.eq_symm_apply]
    simp [e, StandardEtalePair.equivAwayAdjoinRoot, ← aeval_def, ← aeval_algHom_apply]
    rfl
  obtain ⟨k, hk⟩ : ∃ k, IsIntegral R (AdjoinRoot.mk 𝓟'.f 𝓟'.g ^ k * x) := by
    have H : ∀ k, e (1 ⊗ₜ (aeval 𝓟.x 𝓟.g ^ k)) = algebraMap _ _ (AdjoinRoot.mk 𝓟'.f 𝓟'.g ^ k) := by
      intro k; convert congr($(heg 𝓟.g) ^ k) <;>
        simp [← map_pow, 𝓟', StandardEtalePresentation.baseChange]
    have := ((hx m).map (Algebra.TensorProduct.comm _ _ _).symm).map e
    simp only [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, map_mul, Algebra.TensorProduct.comm_symm_tmul, AlgEquiv.symm_apply_apply,
      AlgEquiv.apply_symm_apply] at this
    rw [H, pow_add, map_mul, mul_assoc, IsLocalization.mk'_spec'_mk, ← map_mul] at this
    obtain ⟨k, hk⟩ := IsLocalization.Away.exists_isIntegral_smul_of_isIntegral_map hfg this
    refine ⟨k + n, by convert hk using 1; ring_nf⟩
  obtain ⟨y, hy, hRy⟩ := exists_derivative_mul_eq_and_isIntegral_coeff
    (φ := (AdjoinRoot.mkₐ 𝓟'.f).restrictScalars R) AdjoinRoot.mk_surjective 𝓟'.monic_f
    (by simp [𝓟', StandardEtalePresentation.baseChange, isIntegral_algebraMap]) Ideal.mk_ker hk
  simp only [AlgHom.coe_restrictScalars', AdjoinRoot.coe_mkₐ] at hy
  rw [← Subalgebra.mem_toSubmodule, ← Submodule.smul_mem_iff_of_isUnit _
    (𝓟.hasMap.isUnit_derivative_f.mul <| (𝓟.hasMap.2.pow k).mul (𝓟.hasMap.2.pow m))]
  convert_to eval₂ Algebra.TensorProduct.includeRight.toRingHom (𝓟.x ⊗ₜ[R] 1) y ∈ _ using 1
  · convert congr(Algebra.TensorProduct.comm _ _ _ <| e.symm (algebraMap _ _ $hy))
    · apply (Algebra.TensorProduct.comm R B S).symm.injective
      apply e.injective
      simp only [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply, map_mul, Algebra.TensorProduct.comm_symm_tmul, AlgEquiv.symm_apply_apply,
        AlgEquiv.apply_symm_apply, map_pow, heg]
      simp_rw [mul_assoc, ← map_pow, show 𝓟.g.map (algebraMap R B) = 𝓟'.g from rfl,
        IsLocalization.mk'_spec'_mk, ← derivative_map]; rfl
    · simp only [← AlgEquiv.coe_algHom, ← AlgHom.coe_toRingHom, ← RingHom.comp_apply,
        ← coe_eval₂RingHom]
      congr 1
      ext <;> simp [e, StandardEtalePair.equivAwayAdjoinRoot]; rfl
  · rw [eval₂_eq_sum_range]
    exact sum_mem fun i hi ↦ Subalgebra.mul_mem _ (Algebra.subset_adjoin ⟨_, hRy _, rfl⟩)
      (pow_mem (Subalgebra.algebraMap_mem _ _) _)

theorem TensorProduct.toIntegralClosure_bijective_of_isStandardEtale
    {B : Type*} [CommRing B] [Algebra R B] [Algebra.IsStandardEtale R S] :
    Function.Bijective (toIntegralClosure R S B) := by
  have : Algebra.Smooth R S := {}
  refine ⟨toIntegralClosure_injective_of_flat, ?_⟩
  intro ⟨x, hx⟩
  simp only [toIntegralClosure, Subtype.ext_iff, AlgHom.coe_codRestrict, ← AlgHom.mem_range]
  refine Algebra.adjoin_le ?_ (mem_adjoin_map_integralClosure_of_isStandardEtale x hx)
  rintro _ ⟨y, hy : IsIntegral _ _, rfl⟩
  refine ⟨1 ⊗ₜ ⟨y, hy⟩, by simp⟩

open TensorProduct

lemma MvPolynomial.pderiv_sumToIter {σ ι} (p i) :
    (sumToIter R σ ι p).pderiv i = sumToIter R σ ι (p.pderiv (.inl i)) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q _ _ => simp_all
  | mul_X p n _ => cases n <;> simp_all [pderiv_X, Pi.single_apply, apply_ite]

@[simp]
lemma MvPolynomial.iterToSum_sumToIter {σ ι} (p) :
    iterToSum R σ ι (sumToIter R σ ι p) = p := (MvPolynomial.sumRingEquiv _ _ _).symm_apply_apply _

@[simp]
lemma MvPolynomial.sumToIter_iterToSum {σ ι} (p) :
    sumToIter R σ ι (iterToSum R σ ι p) = p := (MvPolynomial.sumRingEquiv _ _ _).apply_symm_apply _

theorem RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {n : ℕ} (hf : f.IsStandardSmoothOfRelativeDimension n) :
    ∃ g : MvPolynomial (Fin n) R →+* S, g.comp MvPolynomial.C = f ∧ g.Etale := by
  classical
  let := Fintype.ofFinite
  obtain ⟨ι, σ, _, _, P, e⟩ := hf
  let := f.toAlgebra
  let e₀ : σ ⊕ Fin n ≃ ι := ((Equiv.ofInjective _ P.map_inj).sumCongr
      (Finite.equivFinOfCardEq (by rw [Nat.card_coe_set_eq, Set.ncard_compl,
        Set.ncard_range_of_injective P.map_inj, ← e, Algebra.Presentation.dimension])).symm).trans
      (Equiv.Set.sumCompl _)
  let e : MvPolynomial σ (MvPolynomial (Fin n) R) ≃ₐ[R] P.Ring :=
    (MvPolynomial.sumAlgEquiv R _ _).symm.trans (MvPolynomial.renameEquiv _ e₀)
  let φ := e.toAlgHom.comp (IsScalarTower.toAlgHom _ (MvPolynomial (Fin n) R) _)
  algebraize [φ.toRingHom, (algebraMap P.Ring S).comp φ.toRingHom]
  have := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  have : IsScalarTower R (MvPolynomial (Fin n) R) S := .to₁₂₄ _ _ P.Ring _
  refine ⟨algebraMap _ _, (IsScalarTower.algebraMap_eq ..).symm, ?_⟩
  have H : (MvPolynomial.aeval fun x ↦ (algebraMap P.Ring S) (e (MvPolynomial.X x))).toRingHom =
      (algebraMap P.Ring S).comp e.toRingHom := by
    ext
    · simp [e, IsScalarTower.algebraMap_eq R (MvPolynomial (Fin n) R) S]
    · simp [e, @RingHom.algebraMap_toAlgebra (MvPolynomial (Fin n) R) S, φ]
    · simp [e]
  let P' : Algebra.PreSubmersivePresentation (MvPolynomial (Fin n) R) S σ σ :=
  { toGenerators := .ofSurjective (algebraMap _ _ <| e <| .X ·) <| by
      convert P.algebraMap_surjective.comp e.surjective
      exact congr($H)
    relation := e.symm ∘ P.relation
    span_range_relation_eq_ker := by
      rw [Set.range_comp, ← AlgEquiv.coe_ringEquiv e.symm, AlgEquiv.symm_toRingEquiv,
        ← Ideal.map_span, P.span_range_relation_eq_ker, Ideal.map_symm]
      exact congr(RingHom.ker $H).symm
    map := _
    map_inj := Function.injective_id }
  let P' : Algebra.SubmersivePresentation (MvPolynomial (Fin n) R) S σ σ :=
  { __ := P'
    jacobian_isUnit := by
      convert P.jacobian_isUnit using 1
      simp_rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, map_det]
      congr 1
      ext i j
      trans algebraMap P.Ring S (e ((e.symm (P.relation j)).pderiv i))
      · simpa [Algebra.PreSubmersivePresentation.jacobiMatrix_apply, P',
          Algebra.Generators.ofSurjective] using congr($H _)
      suffices e ((e.symm (P.relation j)).pderiv i) = (P.relation j).pderiv (P.map i) by
        simp [Algebra.PreSubmersivePresentation.jacobiMatrix_apply, this]
      simp [e, MvPolynomial.pderiv_sumToIter, ← MvPolynomial.pderiv_rename e₀.injective,
        show e₀ (Sum.inl i) = P.map i from rfl] }
  exact etale_algebraMap.mpr (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mpr
    ⟨_, _, _, inferInstance, P', by simp [Algebra.Presentation.dimension]⟩)

theorem RingHom.IsStandardSmooth.exists_etale_mvPolynomial
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsStandardSmooth) :
    ∃ n, ∃ g : MvPolynomial (Fin n) R →+* S, g.comp MvPolynomial.C = f ∧ g.Etale := by
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := hf
  let := f.toAlgebra
  exact ⟨_, RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial _
    ⟨_, _, _, ‹_›, P, rfl⟩⟩

instance {M : Submonoid S} [Algebra.FormallyEtale R S] : Algebra.FormallyEtale R (Localization M) :=
  have : Algebra.FormallyEtale S (Localization M) := .of_isLocalization M
  .comp _ S _

/-- Given `S` a finitely presented `R`-algebra, and `p` a prime of `S`. If `S` is smooth over `R`
at `p`, then there exists `f ∉ p` such that `R → S[1/f]` factors through some `R[X₁,...,Xₙ]`,
and that `S[1/f]` is standard etale over `R[X₁,...,Xₙ]`. -/
theorem Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial
    {p : Ideal S} [p.IsPrime] [Algebra.FinitePresentation R S]
    [Algebra.IsSmoothAt R p] :
    ∃ f ∉ p, ∃ (n : ℕ) (_ : Algebra (MvPolynomial (Fin n) R) (Localization.Away f)),
      IsScalarTower R (MvPolynomial (Fin n) R) (Localization.Away f) ∧
      Algebra.IsStandardEtale (MvPolynomial (Fin n) R) (Localization.Away f) := by
  classical
  obtain ⟨f, hfp, H⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth R p
  obtain ⟨n, φ, hgC, hg⟩ := RingHom.IsStandardSmooth.exists_etale_mvPolynomial
    (algebraMap R (Localization.Away f))
    (by delta RingHom.IsStandardSmooth; convert H; apply Algebra.algebra_ext; exact fun _ ↦ rfl)
  algebraize [φ]
  have := IsScalarTower.of_algebraMap_eq' hgC.symm
  have : (Ideal.map (algebraMap S (Localization.Away f)) p).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers f) _ _ ‹_›
      ((Ideal.disjoint_powers_iff_notMem _ (Ideal.IsPrime.isRadical ‹_›)).mpr hfp)
  obtain ⟨g₀, hg, H⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := (MvPolynomial (Fin n) R))
    (S := (Localization.Away f)) (p.map (algebraMap _ _))
  obtain ⟨g, ⟨_, m, rfl⟩, hg₀⟩ := IsLocalization.exists_mk'_eq (.powers f) g₀
  replace hg : g ∉ p := by simpa [Submonoid.mem_powers_iff, Ideal.IsPrime.mul_mem_iff_mem_or_mem,
    IsLocalization.mk'_mem_map_algebraMap_iff, mt (‹p.IsPrime›.mem_of_pow_mem _) hfp,
    ← hg₀] using hg
  have : IsLocalization.Away (f * g) (Localization.Away g₀) := by
    suffices IsLocalization.Away (algebraMap _ (Localization.Away f) g) (Localization.Away g₀) from
      .mul' (Localization.Away f) _ _ _
    refine IsLocalization.Away.of_associated (r := g₀)
      ⟨(IsLocalization.Away.algebraMap_pow_isUnit f m).unit, ?_⟩
    simp only [← hg₀, IsUnit.unit_spec, ← map_pow, mul_comm, IsLocalization.mk'_spec'_mk]
  let e : Localization.Away g₀ ≃ₐ[S] Localization.Away (f * g) :=
    IsLocalization.algEquiv (.powers (f * g)) _ _
  let : Algebra (MvPolynomial (Fin n) R) (Localization.Away (f * g)) :=
    (e.toRingHom.comp (algebraMap (MvPolynomial (Fin n) R) _)).toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin n) R) (Localization.Away (f * g)) := by
    refine .of_algebraMap_eq' ?_
    simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
    exact (e.toAlgHom.comp_algebraMap_of_tower (R := R)).symm
  let e' : Localization.Away g₀ ≃ₐ[MvPolynomial (Fin n) R] Localization.Away (f * g) :=
    { __ := e, commutes' r := rfl }
  refine ⟨f * g, ‹p.IsPrime›.mul_notMem ‹_› ‹_›, n, ‹_›, ‹_›, .of_equiv e'⟩

theorem TensorProduct.toIntegralClosure_bijective_of_smooth
    {B : Type*} [CommRing B] [Algebra R B] [Algebra.Smooth R S] :
    Function.Bijective (toIntegralClosure R S B) := by
  have (m : PrimeSpectrum S) : ∃ f ∉ m.asIdeal,
      Function.Bijective (toIntegralClosure R (Localization.Away f) B) := by
    obtain ⟨f, hfm, n, _, _, _⟩ :=
      Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := m.asIdeal)
    exact ⟨f, hfm, toIntegralClosure_bijective_of_tower (S := MvPolynomial (Fin n) R)
      toIntegralClosure_mvPolynomial_bijective toIntegralClosure_bijective_of_isStandardEtale⟩
  choose f hfm hf using this
  refine TensorProduct.toIntegralClosure_bijective_of_isLocalizationAway (R := R)
    (s := Set.range f) (B := B) ?_ (Localization.Away ·.1) (Set.forall_subtype_range_iff.mpr hf)
  by_contra H
  obtain ⟨m, hm, e⟩ := Ideal.exists_le_maximal _ H
  exact hfm ⟨m, inferInstance⟩ (e (Ideal.subset_span (Set.mem_range_self ⟨m, inferInstance⟩)):)
