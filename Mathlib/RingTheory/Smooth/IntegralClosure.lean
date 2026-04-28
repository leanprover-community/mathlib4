/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Smooth base change commutes with integral closure

In this file we aim to prove that smooth base change commutes with integral closure.
We define the map
`TensorProduct.toIntegralClosure : S ⊗[R] integralClosure R B →ₐ[S] integralClosure S (S ⊗[R] B)`
and show that it is bijective when `S` is `R`-smooth.

## Main results
- `TensorProduct.toIntegralClosure_injective_of_flat`:
  If `S` is `R`-flat, then `TensorProduct.toIntegralClosure` is injective.
- `TensorProduct.toIntegralClosure_mvPolynomial_bijective`:
  If `S = MvPolynomial σ R`, then `TensorProduct.toIntegralClosure` is bijective.
- `TensorProduct.toIntegralClosure_bijective_of_isLocalization`:
  If `S = Localization M`, then `TensorProduct.toIntegralClosure` is bijective.
- `TensorProduct.toIntegralClosure_bijective_of_smooth`:
  If `S` is `R`-smooth, then `TensorProduct.toIntegralClosure` is bijective.
-/

@[expose] public section

open Polynomial TensorProduct

variable {R S B : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing B] [Algebra R B]

variable (R S) in
/-- The comparison map from `S ⊗[R] integralClosure R B` to `integralClosure S (S ⊗[R] B)`.
This is injective when `S` is `R`-flat, and (TODO) bijective when `S` is `R`-smooth. -/
def TensorProduct.toIntegralClosure
    (B : Type*) [CommRing B] [Algebra R B] :
    S ⊗[R] integralClosure R B →ₐ[S] integralClosure S (S ⊗[R] B) :=
    (Algebra.TensorProduct.map (.id _ _) (integralClosure R B).val).codRestrict _ fun x ↦ by
  induction x with
  | zero => simp
  | add x y _ _ => rw [map_add]; exact add_mem ‹_› ‹_›
  | tmul x y =>
    convert ((y.2.map (Algebra.TensorProduct.includeRight
      (R := R) (A := S))).tower_top (A := S)).smul x
    simp [smul_tmul']

lemma TensorProduct.toIntegralClosure_injective_of_flat [Module.Flat R S] :
    Function.Injective (toIntegralClosure R S B) := by
  refine Function.Injective.of_comp (f := (integralClosure _ _).val) ?_
  rw [← AlgHom.coe_comp, toIntegralClosure, AlgHom.val_comp_codRestrict]
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := S)
    (integralClosure R B).val.toLinearMap Subtype.val_injective

/-- "Base change preserves integral closure" is stable under composition. -/
lemma TensorProduct.toIntegralClosure_bijective_of_tower
    {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (H : Function.Bijective (toIntegralClosure R S B))
    (H' : Function.Bijective (toIntegralClosure S T (S ⊗[R] B))) :
    Function.Bijective (toIntegralClosure R T B) := by
  let e := (Algebra.TensorProduct.cancelBaseChange ..).symm.trans <|
      (Algebra.TensorProduct.congr (.refl (R := T) (A := T)) (.ofBijective _ H)).trans <|
      (AlgEquiv.ofBijective _ H').trans <|
      (AlgEquiv.mapIntegralClosure (Algebra.TensorProduct.cancelBaseChange ..))
  convert e.bijective
  rw [← e.coe_algHom]
  congr 1
  ext; simp [e, toIntegralClosure, AlgEquiv.ofBijective_apply]

/-- "Base change preserves integral closure" can be checked Zariski-locally. -/
lemma TensorProduct.toIntegralClosure_bijective_of_isLocalizationAway
    {s : Set S} (hs : Ideal.span s = ⊤) (Sᵣ : s → Type*) [∀ r, CommRing (Sᵣ r)]
    [∀ r, Algebra S (Sᵣ r)] [∀ r, Algebra R (Sᵣ r)] [∀ r, IsScalarTower R S (Sᵣ r)]
    [∀ r, IsLocalization.Away r.1 (Sᵣ r)]
    (H : ∀ r, Function.Bijective (toIntegralClosure R (Sᵣ r) B)) :
    Function.Bijective (toIntegralClosure R S B) := by
  have (r : s) : IsLocalizedModule.Away r.1
      (Algebra.TensorProduct.map (Algebra.ofId S (Sᵣ r))
        (AlgHom.id R (integralClosure R B))).toLinearMap := by
    let := (Algebra.TensorProduct.map (Algebra.ofId S (Sᵣ r))
      (AlgHom.id R (integralClosure R B))).toAlgebra
    refine isLocalizedModule_iff_isLocalization.mpr ?_
    refine IsLocalization.tensorProduct_tensorProduct _ _ (.powers r.1) _ ?_
    ext; simp [RingHom.algebraMap_toAlgebra]
  let φ (r : s) : integralClosure S (S ⊗[R] B) →ₐ[S] integralClosure (Sᵣ r) (Sᵣ r ⊗[R] B) :=
    ((Algebra.TensorProduct.map (Algebra.ofId _ _) (.id _ _)).comp
      (integralClosure S (S ⊗[R] B)).val).codRestrict
        ((integralClosure (Sᵣ r) (Sᵣ r ⊗[R] B)).restrictScalars S) <| by
    simp only [AlgHom.coe_comp, Subalgebra.coe_val, Function.comp_apply,
      Subalgebra.mem_restrictScalars, Subtype.forall, mem_integralClosure_iff]
    exact fun a ha ↦ (ha.map _).tower_top
  have (r : s) : IsLocalizedModule.Away r.1 (φ r).toLinearMap := by
    let := (Algebra.TensorProduct.map (Algebra.ofId S (Sᵣ r))
          (AlgHom.id R B)).toAlgebra
    let := (φ r).toAlgebra
    have : IsScalarTower (integralClosure S (S ⊗[R] B)) (integralClosure (Sᵣ r) (Sᵣ r ⊗[R] B))
        (Sᵣ r ⊗[R] B) := .of_algebraMap_eq' rfl
    have : IsLocalization (Algebra.algebraMapSubmonoid (S ⊗[R] B) (Submonoid.powers r.1))
        (Sᵣ r ⊗[R] B) := by
      refine IsLocalization.tensorProduct_tensorProduct _ _ (.powers r.1) _ ?_
      ext; simp [RingHom.algebraMap_toAlgebra]
    refine isLocalizedModule_iff_isLocalization.mpr ?_
    exact IsLocalization.integralClosure ..
  refine bijective_of_isLocalized_span s hs (F := (toIntegralClosure R S B).toLinearMap)
    (fun r ↦ (Sᵣ r) ⊗[R] integralClosure R B)
    (fun r ↦ (Algebra.TensorProduct.map (Algebra.ofId _ _) (.id _ _)).toLinearMap)
    (fun r ↦ integralClosure (Sᵣ r) ((Sᵣ r) ⊗[R] B))
    (fun r ↦ (φ r).toLinearMap) fun r ↦ ?_
  convert show Function.Bijective ((toIntegralClosure R (Sᵣ r) B).toLinearMap.restrictScalars S)
    from H r using 1
  congr!
  refine IsLocalizedModule.ext (.powers r.1) (Algebra.TensorProduct.map (Algebra.ofId S (Sᵣ r))
    (AlgHom.id R (integralClosure R B))).toLinearMap
    (IsLocalizedModule.map_units (S := .powers r.1) (φ r).toLinearMap) ?_
  ext x
  exact congr($(IsLocalizedModule.map_apply (.powers r.1)
      ((Algebra.TensorProduct.map (Algebra.ofId S (Sᵣ r))
        (AlgHom.id R (integralClosure R B))).toLinearMap)
      (φ r).toLinearMap (toIntegralClosure R S B).toLinearMap (1 ⊗ₜ x)).1)

attribute [local instance] MvPolynomial.algebraMvPolynomial in
/-- Base changing to `MvPolynomial σ R` preserves integral closure. -/
lemma TensorProduct.toIntegralClosure_mvPolynomial_bijective {σ : Type*} :
    Function.Bijective (toIntegralClosure R (MvPolynomial σ R) B) := by
  classical
  refine ⟨toIntegralClosure_injective_of_flat, ?_⟩
  rintro ⟨x, hx⟩
  let e₀ : MvPolynomial σ R ⊗[R] B ≃ₐ[R] MvPolynomial σ B :=
    MvPolynomial.scalarRTensorAlgEquiv
  let e : MvPolynomial σ R ⊗[R] B ≃ₐ[MvPolynomial σ R] MvPolynomial σ B :=
    { toRingEquiv := e₀.toRingEquiv, commutes' r := by
        change e₀.toRingHom.comp (algebraMap _ _) r = _
        congr 1
        ext <;> simp [e₀, MvPolynomial.scalarRTensorAlgEquiv, MvPolynomial.coeff_map,
          ← Algebra.algebraMap_eq_smul_one, apply_ite (algebraMap _ _), MvPolynomial.coeff_X'] }
  have := MvPolynomial.isIntegral_iff_isIntegral_coeff.mp (hx.map e)
  obtain ⟨y, hy⟩ : e x ∈ RingHom.range (MvPolynomial.map (integralClosure R B).val.toRingHom) := by
    refine MvPolynomial.mem_range_map_iff_coeffs_subset.mpr ?_
    simp [Set.subset_def, mem_integralClosure_iff, MvPolynomial.mem_coeffs_iff,
      @forall_comm B, this]
  refine ⟨MvPolynomial.scalarRTensorAlgEquiv.symm y, Subtype.ext <| e.injective (.trans ?_ hy)⟩
  obtain ⟨y, rfl⟩ := (MvPolynomial.scalarRTensorAlgEquiv (R := R)).surjective y
  dsimp [TensorProduct.toIntegralClosure, e]
  simp only [AlgEquiv.symm_apply_apply]
  have : e₀.toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id R (MvPolynomial σ R)) (integralClosure R B).val) =
      (MvPolynomial.mapAlgHom (integralClosure R B).val).comp
      MvPolynomial.scalarRTensorAlgEquiv.toAlgHom := by
    ext <;> simp [e₀, MvPolynomial.coeff_map, MvPolynomial.scalarRTensorAlgEquiv]
  exact congr($this y)

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- Localization preserves integral closure. -/
lemma TensorProduct.toIntegralClosure_bijective_of_isLocalization
    (M : Submonoid R) [IsLocalization M S] :
    Function.Bijective (toIntegralClosure R S B) := by
  classical
  let φ : integralClosure R B →ₐ[R] integralClosure S (S ⊗[R] B) :=
    AlgHom.codRestrict (Algebra.TensorProduct.includeRight.comp (integralClosure R B).val)
      ((integralClosure S (S ⊗[R] B)).restrictScalars R) fun ⟨x, hx⟩ ↦ by
    refine .of_comp (f := algebraMap R S) ?_
    convert RingHom.IsIntegralElem.map hx
      (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B).toRingHom
    simp [← IsScalarTower.algebraMap_eq]
  let := φ.toAlgebra
  have := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  have : IsScalarTower (integralClosure R B) (integralClosure S (S ⊗[R] B)) (S ⊗[R] B) :=
    .of_algebraMap_eq' rfl
  have := IsLocalization.integralClosure (S := B) M (Rf := S) (Sf := S ⊗[R] B)
  convert (IsLocalization.algEquiv (Algebra.algebraMapSubmonoid (integralClosure R B) M)
    (S ⊗[R] integralClosure R B) (integralClosure S (S ⊗[R] B))).bijective
  rw [← AlgHom.coe_restrictScalars' R, ← AlgEquiv.coe_restrictScalars' R, ← AlgEquiv.coe_algHom]
  congr 1
  ext1
  · apply IsLocalization.algHom_ext M; ext
  · ext x
    dsimp [toIntegralClosure]
    simp [← Algebra.TensorProduct.right_algebraMap_apply]
    rfl

section IsStandardEtale

attribute [local instance] Polynomial.algebra in
/-- Let `S` be an `R`-algebra and `f : S[X]` be a monic polynomial with `R`-integral coefficients.
Suppose `y` in `B = S[X]/f` is `R`-integral, then `f' * y` is the image of some `g : S[X]` with
`R`-integral coefficients. -/
-- We can also know that `deg g = deg f - 1`. Upgrade the lemma if we care.
@[stacks 03GD]
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
  algebraize [φ.toRingHom.comp C]
  have := (algebraMap S B).domain_nontrivial
  obtain ⟨y, rfl⟩ := hφ y
  -- Consider the universal extension `S'` of `S` that splits `f`, so that `f = ∏ᵢ X - aᵢ`.
  obtain ⟨S', _, _, _, _, _, hS'⟩ := hf.exists_splits_map
  obtain ⟨m, hm⟩ := Polynomial.splits_iff_exists_multiset.mp hS'
  simp only [hf.map _, Monic.leadingCoeff, map_one, one_mul] at hm
  algebraize [(algebraMap S S').comp (algebraMap R S)]
  -- Each `aᵢ` is integral since `f` is still monic in `S'`.
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
  -- The key identity is `y * f' ≡ ∑ᵢ y(aᵢ) * ∏_{j ≠ i} X - aⱼ (mod f)`.
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
      simp [Polynomial.dvd_iff_isRoot]
    rw [map_modByMonic _ hf]
    refine (div_modByMonic_unique g _ (hf.map _) ⟨(sub_eq_iff_eq_add'.mp hg).symm, ?_⟩).2
    refine degree_lt_degree ?_
    rw [hf.natDegree_map, ← Nat.le_sub_one_iff_lt (Ne.bot_lt hfd)]
    refine (natDegree_multiset_sum_le _).trans (Multiset.max_le_of_forall_le _ _ ?_)
    simp only [Multiset.map_map, Function.comp_apply, Multiset.mem_map, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂]
    refine fun a ha ↦ (natDegree_mul_C_le _ _).trans ((natDegree_multiset_prod_le _).trans ?_)
    simp [ha, hmc]
  -- Every `y(aᵢ)` is `R`-integral as y is also `R`-integral by assumption.
  have H' (a : S') (ham : a ∈ m) : IsIntegral R (aeval a y) := by
    let ψ : B →ₐ[R] S' := AlgHom.liftOfSurjective _ hφ ((aeval a).restrictScalars R) <| by
      rw [hfx, Ideal.span_le]
      suffices (m.map (a - ·)).prod = 0 by simpa [← eval_map_algebraMap, hm, eval_multiset_prod]
      rw [Multiset.prod_eq_zero]
      simpa using ⟨a, ham, by simp⟩
    simpa [ψ] using hy.map ψ
  -- So `y * f' mod f` is integral over `R[X]` (i.e. its coefficients are `R`-integral)
  -- as a sum of products of integral elements.
  have H'' : IsIntegral R[X] (f.derivative * y %ₘ f) := by
    refine .tower_bot (B := S'[X]) (map_injective _ (FaithfulSMul.algebraMap_injective S S')) ?_
    simp only [algebraMap_def, coe_mapRingHom, H]
    refine .multiset_sum ?_
    simp only [Multiset.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    refine fun a ham ↦ .mul (.multiset_prod ?_) ?_
    · simp only [Multiset.mem_map, Polynomial.isIntegral_iff_isIntegral_coeff, forall_exists_index,
        and_imp, forall_apply_eq_imp_iff₂, coeff_sub]
      exact fun b hbm n ↦ .sub (by simp [coeff_X, apply_ite, isIntegral_one, isIntegral_zero])
        (by simp [coeff_C, apply_ite, isIntegral_zero, hm' b (Multiset.mem_of_mem_erase hbm)])
    · simpa [isIntegral_iff_isIntegral_coeff, coeff_C, apply_ite, isIntegral_zero] using H' a ham
  refine ⟨_, ?_, Polynomial.isIntegral_iff_isIntegral_coeff.mp H''⟩
  rw [modByMonic_eq_sub_mul_div, map_sub, map_mul, map_mul,
    show φ f = 0 from hfx.ge (Ideal.mem_span_singleton_self _), zero_mul, sub_zero]

open TensorProduct

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] Polynomial.algebra in
@[stacks 03GE "without the generalization to arbitrary etale algebra"]
theorem mem_adjoin_map_integralClosure_of_isStandardEtale [Algebra.IsStandardEtale R S]
    (a : S ⊗[R] B) (hx : IsIntegral S a) :
    a ∈ Algebra.adjoin S
      ((integralClosure R B).map Algebra.TensorProduct.includeRight : Subalgebra R (S ⊗[R] B)) := by
  -- By assumption, `S = (R[X]/f)[1/g]` for some `f g : R[X]`. Let `x : S` denote the image of `X`.
  have 𝓟 := Classical.ofNonempty (α := StandardEtalePresentation R S)
  -- Since `a` is integral over `S = (R[X]/f)[1/g]`, `gⁿ • a` is `R`-integral for `n` large enough.
  obtain ⟨n, hx⟩ : ∃ n, ∀ m, IsIntegral R ((aeval 𝓟.x 𝓟.g) ^ (n + m) • a) := by
    let e := 𝓟.equivRing.trans 𝓟.equivAwayAdjoinRoot
    algebraize [(e.symm.toAlgHom.comp (IsScalarTower.toAlgHom R (AdjoinRoot 𝓟.f) _)).toRingHom]
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
  -- Under `S ⊗[R] B ≃ (B[X]/f)[1/g]`, we may write `a` as `a/gᵐ` with `a` now living in `B[X]/f`.
  let 𝓟' := 𝓟.baseChange (T := B)
  let e := 𝓟'.equivRing.trans 𝓟'.equivAwayAdjoinRoot
  obtain ⟨a, rfl⟩ := (Algebra.TensorProduct.comm _ _ _).surjective a
  obtain ⟨a, rfl⟩ := e.symm.surjective a
  obtain ⟨a, ⟨_, m, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq
    (R := AdjoinRoot 𝓟'.f) (.powers (.mk _ 𝓟'.g)) a
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
  -- And `gᵏ • a` is still `R`-integral for `k` large enough.
  obtain ⟨k, hk⟩ : ∃ k, IsIntegral R (AdjoinRoot.mk 𝓟'.f 𝓟'.g ^ k * a) := by
    have H : ∀ k, e (1 ⊗ₜ (aeval 𝓟.x 𝓟.g ^ k)) = algebraMap _ _ (AdjoinRoot.mk 𝓟'.f 𝓟'.g ^ k) := by
      intro k; convert congr($(heg 𝓟.g) ^ k) <;>
        simp [← map_pow, 𝓟', StandardEtalePresentation.baseChange]
    have := ((hx m).map (Algebra.TensorProduct.comm _ _ _).symm).map e
    simp only [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, map_mul, Algebra.TensorProduct.comm_symm_tmul, AlgEquiv.symm_apply_apply,
      AlgEquiv.apply_symm_apply] at this
    rw [H, pow_add, map_mul, mul_assoc, IsLocalization.mk'_spec'_mk, ← map_mul] at this
    obtain ⟨k, hk⟩ := IsLocalization.Away.exists_isIntegral_mul_of_isIntegral_algebraMap hfg this
    refine ⟨k + n, by convert hk using 1; ring_nf⟩
  -- We now use the key lemma `exists_derivative_mul_eq_and_isIntegral_coeff` to get a `y : B[X]`
  -- with `R`-integral coefficients such that `f' * gᵏ * a = y` in `S ⊗[R] B`.
  obtain ⟨y, hy, hRy⟩ := exists_derivative_mul_eq_and_isIntegral_coeff
    (φ := (AdjoinRoot.mkₐ 𝓟'.f).restrictScalars R) AdjoinRoot.mk_surjective 𝓟'.monic_f
    (by simp [𝓟', StandardEtalePresentation.baseChange, isIntegral_algebraMap]) Ideal.mk_ker hk
  simp only [AlgHom.coe_restrictScalars', AdjoinRoot.coe_mkₐ] at hy
  -- Since `f' * gᵏ` is invertible in S, to show that `a ∈ S ⊗ B'` (where `B'` is the
  -- integral closure of `R` in `B`), it suffices to show that `y ∈ S ⊗ B'`,
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
  -- which follows from the fact that `y` has `R`-integral coefficients.
  rw [eval₂_eq_sum_range]
  exact sum_mem fun i hi ↦ Subalgebra.mul_mem _ (Algebra.subset_adjoin ⟨_, hRy _, rfl⟩)
    (pow_mem (Subalgebra.algebraMap_mem _ _) _)

-- Subsumed by `TensorProduct.toIntegralClosure_bijective_of_smooth`
private theorem TensorProduct.toIntegralClosure_bijective_of_isStandardEtale
    [Algebra.IsStandardEtale R S] : Function.Bijective (toIntegralClosure R S B) := by
  refine ⟨toIntegralClosure_injective_of_flat, ?_⟩
  intro ⟨x, hx⟩
  simp only [toIntegralClosure, Subtype.ext_iff, AlgHom.coe_codRestrict, ← AlgHom.mem_range]
  refine Algebra.adjoin_le ?_ (mem_adjoin_map_integralClosure_of_isStandardEtale x hx)
  rintro _ ⟨y, hy : IsIntegral _ _, rfl⟩
  refine ⟨1 ⊗ₜ ⟨y, hy⟩, by simp⟩

end IsStandardEtale

theorem TensorProduct.toIntegralClosure_bijective_of_smooth [Algebra.Smooth R S] :
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
  exact hfm ⟨m, inferInstance⟩ (e (Ideal.subset_span (Set.mem_range_self ⟨m, inferInstance⟩)) :)
