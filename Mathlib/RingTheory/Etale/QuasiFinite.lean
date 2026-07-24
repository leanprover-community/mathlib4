/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
public import Mathlib.RingTheory.ZariskisMainTheorem
public import Mathlib.RingTheory.Ideal.Quotient.Over

/-!
# Etale local structure of finite maps

We construct etale neighborhoods that split fibers of finite algebras.

## Main results
- `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`:
  Let `S` be a module-finite `R`-algebra, and `q` a prime lying over `p`.
  We may construct an etale `R`-algebra `R'` and a prime `P` lying over `p` with `κ(P) = κ(p)`,
  such that `R' ⊗[R] S = A × B` and there exists a unique prime in `A` lying over `P`.
  This prime will also lie over `q`.

-/

@[expose] public section

open TensorProduct

section BijectiveResidueField

variable {R R' S : Type*} [CommRing R] [CommRing R'] [CommRing S] [Algebra R R'] [Algebra R S]
    {p : Ideal R} {q : Ideal R'} [p.IsPrime] [q.IsPrime] [q.LiesOver p]

/-- If `q` is a prime of `R'` lying over `p`, a prime of `R`, such that `κ(q) = κ(p)`, then
the fiber of `R' → R' ⊗[R] S` over `q` is in bijection with the fiber of `R → S` over `p`. -/
noncomputable
def Ideal.fiberIsoOfBijectiveResidueField
    (H : Function.Bijective (Ideal.ResidueField.mapₐ p q (Algebra.ofId _ _) (q.over_def p))) :
    q.primesOver (R' ⊗[R] S) ≃o p.primesOver S :=
  let := Localization.AtPrime.algebraOfLiesOver p q
  let e : q.Fiber (R' ⊗[R] S) ≃ₐ[p.ResidueField] p.Fiber S :=
    ((Algebra.TensorProduct.cancelBaseChange _ _ q.ResidueField _ _).restrictScalars _).trans
      (Algebra.TensorProduct.congr (.symm <| .ofBijective (Algebra.ofId _ _) H) .refl)
  (PrimeSpectrum.primesOverOrderIsoFiber ..).trans <|
    (PrimeSpectrum.comapEquiv e.toRingEquiv).trans (PrimeSpectrum.primesOverOrderIsoFiber ..).symm

lemma Ideal.comap_fiberIsoOfBijectiveResidueField_symm
    (H : Function.Bijective (Ideal.ResidueField.mapₐ p q (Algebra.ofId _ _) (q.over_def p)))
    (Q : p.primesOver S) :
    ((Ideal.fiberIsoOfBijectiveResidueField H).symm Q).1.comap
      (RingHomClass.toRingHom Algebra.TensorProduct.includeRight) = Q.1 := by
  ext x
  simp [Ideal.fiberIsoOfBijectiveResidueField,
    PrimeSpectrum.primesOverOrderIsoFiber, PrimeSpectrum.preimageOrderIsoFiber,
    PrimeSpectrum.preimageEquivFiber]

@[simp]
lemma Ideal.comap_fiberIsoOfBijectiveResidueField_apply
    (H : Function.Bijective (Ideal.ResidueField.mapₐ p q (Algebra.ofId _ _) (q.over_def p)))
    (Q : q.primesOver (R' ⊗[R] S)) :
    (Ideal.fiberIsoOfBijectiveResidueField H Q).1 =
      Q.1.comap Algebra.TensorProduct.includeRight := by
  simpa using! (Ideal.comap_fiberIsoOfBijectiveResidueField_symm H
    (Ideal.fiberIsoOfBijectiveResidueField H Q)).symm

lemma Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap
    (H : Function.Bijective (Ideal.ResidueField.mapₐ p q (Algebra.ofId _ _) (q.over_def p)))
    (P₁ P₂ : Ideal (R' ⊗[R] S)) [P₁.IsPrime] [P₂.IsPrime] [P₁.LiesOver q] [P₂.LiesOver q]
    (H₂ : P₁.comap Algebra.TensorProduct.includeRight.toRingHom =
      P₂.comap Algebra.TensorProduct.includeRight.toRingHom) : P₁ = P₂ := by
  refine congr_arg Subtype.val ((Ideal.fiberIsoOfBijectiveResidueField
  (S := S) H).injective (a₁ := ⟨P₁, ‹_›, ‹_›⟩) (a₂ := ⟨P₂, ‹_›, ‹_›⟩) (by ext1; simpa))

end BijectiveResidueField

section

open Polynomial

universe u v

variable {R : Type u} {S : Type v} {T : Type*}
  [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

set_option backward.isDefEq.respectTransparency false in
/-- Suppose `f : S →ₐ[R] T` is an `R`-algebra homomorphism with `S` integral and `T` of finite type,
such that the induced map `S[1/g] → T[1/g]` is surjective for some `g : S`.
Then for any prime `p` of `R` such that `1 ⊗ₜ g` is invertible in `κ(p) ⊗ S`,
there exists `r ∉ p` such that `T[1/r]` is finite over `R[1/r]`. -/
@[stacks 00UI]
lemma Localization.exists_finite_awayMapₐ_of_surjective_awayMapₐ
    [Algebra.FiniteType R T] [Algebra.IsIntegral R S] (f : S →ₐ[R] T) (g : S)
    (hg : Function.Surjective (Localization.awayMapₐ f g)) (p : Ideal R) [p.IsPrime]
    (hgp : IsUnit (M := p.Fiber S) (1 ⊗ₜ g)) :
    ∃ r ∉ p, (Localization.awayMapₐ (Algebra.ofId R T) r).Finite := by
  have := PrimeSpectrum.isClosedMap_comap_of_isIntegral (algebraMap R S)
    (algebraMap_isIntegral_iff.mpr ‹_›) _ (PrimeSpectrum.isClosed_zeroLocus {g})
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hpr, hrg⟩ := PrimeSpectrum.isBasis_basic_opens
    |>.exists_subset_of_mem_open (a := ⟨p, ‹_›⟩) (ou := this.isOpen_compl) <| by
    rintro ⟨q, hq, e⟩
    have : q.asIdeal.LiesOver p := ⟨congr(($e).1).symm⟩
    have : 1 ⊗ₜ g ∉ (PrimeSpectrum.preimageEquivFiber R S ⟨p, ‹_›⟩ ⟨q, e⟩).asIdeal :=
      fun h ↦ Ideal.IsPrime.ne_top' (Ideal.eq_top_of_isUnit_mem _ h hgp)
    rw [PrimeSpectrum.preimageEquivFiber_apply_asIdeal] at this
    simp_all
  refine ⟨r, hpr, RingHom.finite_iff_isIntegral_and_finiteType.mpr ⟨?_, ?_⟩⟩
  · have : IsLocalization.Away (f.toRingHom (algebraMap R S r))
        (Localization.Away (algebraMap R T r)) := by
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]; infer_instance
    have h₁ : (Localization.awayMap (algebraMap R S) r).IsIntegral := isIntegral_localization
    have h₂ : Function.Surjective (IsLocalization.Away.map (Localization.Away (algebraMap R S r))
        (Localization.Away (algebraMap R T r)) f.toRingHom (algebraMap R S r)) := by
      intro x
      obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (.powers (algebraMap R T r)) x
      suffices ∃ a k l, algebraMap R T r ^ (l + n) * f a =
          algebraMap R T r ^ (l + k) * x by
        simpa [(IsLocalization.mk'_surjective (.powers (algebraMap R S r))).exists,
          IsLocalization.Away.map, IsLocalization.map_mk', IsLocalization.mk'_eq_iff_eq,
          ← map_pow, Submonoid.mem_powers_iff, IsLocalization.Away.map, IsLocalization.map_mk',
          IsLocalization.mk'_eq_iff_eq, ← map_mul, ← mul_assoc, ← pow_add,
          IsLocalization.eq_iff_exists (.powers (algebraMap R T r))]
      have : PrimeSpectrum.basicOpen (algebraMap R S r) ≤ PrimeSpectrum.basicOpen g := by
        simpa [← SetLike.coe_subset_coe] using hrg
      simp only [PrimeSpectrum.basicOpen_le_basicOpen_iff, Ideal.mem_radical_iff,
        Ideal.mem_span_singleton] at this
      obtain ⟨m', s, hs⟩ := this
      obtain ⟨b, m, e : f b = f g ^ m * x⟩ := Localization.awayMap_surjective_iff.mp hg x
      have : f (s ^ m * b) = f (g * s) ^ m * x := by simp [e, mul_pow, mul_assoc, mul_left_comm]
      simp_rw [← hs, map_pow, AlgHom.commutes, ← pow_mul] at this
      refine ⟨s ^ m * b, (n + m' * m), 0, this ▸ ?_⟩
      simp [pow_add, mul_assoc]
    convert! h₁.trans _ _ (RingHom.IsIntegral.of_finite (.of_surjective _ h₂)) using 1
    refine IsLocalization.ringHom_ext (.powers r) (RingHom.ext fun x ↦ ?_)
    simp [Localization.awayMap, IsLocalization.Away.map, ← IsScalarTower.algebraMap_apply R T]
  · algebraize [(Localization.awayMapₐ (Algebra.ofId R T) r).toRingHom]
    have := IsScalarTower.of_algebraMap_eq'
      (Localization.awayMapₐ (Algebra.ofId R T) r).comp_algebraMap.symm
    refine RingHom.finiteType_algebraMap.mpr ?_
    exact .of_restrictScalars_finiteType R _ _

set_option backward.isDefEq.respectTransparency false in
attribute [local instance high] Algebra.TensorProduct.leftAlgebra IsScalarTower.right
  DivisionRing.instIsArtinianRing in
/-- A variant of `Ideal.exists_not_mem_forall_mem_of_ne_of_liesOver` that also gives you
control on the primes in the integral closure. -/
lemma Algebra.exists_notMem_and_isIntegral_forall_mem_of_ne_of_liesOver
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Algebra.FiniteType R S]
    [Algebra.QuasiFiniteAt R q] :
    ∃ s ∉ q, ∃ hs : IsIntegral R s, (∀ q' : Ideal S, q'.IsPrime → q' ≠ q → q'.LiesOver p → s ∈ q') ∧
      ∀ (q' : Ideal (integralClosure R S)), q'.IsPrime →
        q' ≠ q.under _ → q'.LiesOver p → ⟨s, hs⟩ ∈ q' := by
  obtain ⟨s₁, hs₁q, hs₁⟩ := Ideal.exists_not_mem_forall_mem_of_ne_of_liesOver (R := R) p q
  obtain ⟨s₂, hs₂q, hs₂⟩ := Algebra.ZariskisMainProperty.of_finiteType (R := R) q
  obtain ⟨s₃, hs₃⟩ := hs₂.2 (algebraMap _ _ s₁)
  obtain ⟨s₃, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (.powers s₂) s₃
  obtain ⟨m, hm⟩ : ∃ m, ↑s₂ ^ m * ↑s₃ = ↑s₂ ^ m * (s₁ * ↑s₂ ^ n) := by
    simpa [IsLocalization.Away.map, IsLocalization.map_mk', IsLocalization.mk'_eq_iff_eq_mul,
      ← map_mul, ← map_pow, IsLocalization.eq_iff_exists (.powers s₂.1),
      Submonoid.mem_powers_iff] using! hs₃
  wlog hm0 : 0 < m generalizing m
  · refine this (m + 1) (by grind) (by simp)
  have hs₃q : s₃.1 ∉ q := fun h ↦ (show ↑s₂ ^ m * (s₁ * ↑s₂ ^ n) ∉ q from q.primeCompl.mul_mem
    (pow_mem hs₂q _) (mul_mem hs₁q (pow_mem hs₂q _))) (hm ▸ Ideal.mul_mem_left _ _ h)
  refine ⟨↑s₂ ^ m * ↑s₃, q.primeCompl.mul_mem (pow_mem hs₂q _) hs₃q, (s₂ ^ m * s₃).2,
    fun q' _ hq'q _ ↦ hm ▸ Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (hs₁ q' ‹_› hq'q ‹_›)),
    fun q' _ hq'q _ ↦ ?_⟩
  let : Algebra (integralClosure R S) (Localization.Away s₂.1) := OreLocalization.instAlgebra
  let e : Localization.Away s₂ ≃ₐ[integralClosure R S] Localization.Away s₂.1 :=
    .ofBijective (Localization.awayMapₐ (Algebra.ofId _ _) s₂) hs₂
  let q's : Ideal (Localization.Away s₂) := q'.map (algebraMap _ _)
  by_contra H
  have hq's : Disjoint (Submonoid.powers s₂ : Set (integralClosure R S)) ↑q' := by
    rw [Ideal.disjoint_powers_iff_notMem_of_isPrime]
    contrapose H; exact Ideal.mul_mem_right s₃ _ (Ideal.pow_mem_of_mem _ H m hm0)
  have : q's.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (.powers s₂) _ _ ‹_› hq's
  have : q's.LiesOver q' := ⟨(IsLocalization.under_map_of_isPrime_disjoint _ _ ‹_› hq's).symm⟩
  have : q's.LiesOver p := .trans _ q' _
  have := hs₁ (q's.comap (e.symm.toAlgHom.comp (IsScalarTower.toAlgHom _ _ _)).toRingHom)
    inferInstance (by
      contrapose hq'q
      rw [← hq'q, Ideal.under, Ideal.comap_comap, AlgHom.toRingHom_eq_coe,
        AlgHom.comp_algebraMap, q's.over_def q'])
    (inferInstanceAs ((q's.comap ((e.symm.toAlgHom.comp
      (IsScalarTower.toAlgHom _ _ _)).restrictScalars R)).LiesOver _))
  have : e.symm (algebraMap S (Localization.Away
      ((integralClosure R S).val.toRingHom s₂)) s₁) ∈ q's := by
    simpa using! this
  rw [← hs₃, ← Ideal.IsPrime.mul_mem_left_iff (x := algebraMap _ _ (s₂ ^ n))] at this
  · dsimp [Localization.awayMap, IsLocalization.Away.map] at this
    rw [IsLocalization.map_mk', ← e.symm.commutes, ← map_mul,
      IsScalarTower.algebraMap_eq _ S _] at this
    replace this : e.symm ((algebraMap _ (Localization.Away s₂.1)) s₃) ∈ q's := by
      simpa [-map_mul, -map_pow, -AlgEquiv.commutes] using! this
    replace this : s₃ ∈ q' := by simpa [← Ideal.mem_comap, ← q's.over_def q'] using! this
    exact H (Ideal.mul_mem_left _ (s₂ ^ m) this)
  · rw [map_pow]; exact Ideal.notMem_of_isUnit _ (.pow _ (IsLocalization.Away.algebraMap_isUnit _))

lemma Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq_aux
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] [Algebra.QuasiFiniteAt R q] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R') (P : Ideal R')
      (_ : P.IsPrime) (_ : P.LiesOver p) (e : R' ⊗[R] S) (_ : IsIdempotentElem e)
      (e₀ : R' ⊗[R] integralClosure R S) (_ : IsIdempotentElem e₀)
      (_ : Algebra.TensorProduct.map (.id R' R') (integralClosure R S).val e₀ = e)
      (P' : Ideal (R' ⊗[R] S)) (_ : P'.IsPrime) (_ : P'.LiesOver P), P'.comap
        Algebra.TensorProduct.includeRight.toRingHom = q ∧ e ∉ P' ∧
      Function.Bijective (Ideal.ResidueField.mapₐ p P (Algebra.ofId _ _) (P.over_def p)) ∧
      (∀ P'' : Ideal (R' ⊗[R] integralClosure R S),
          P''.IsPrime → P''.LiesOver P → e₀ ∉ P'' → P'' =
            P'.comap (Algebra.TensorProduct.map (.id R' R') (integralClosure R S).val).toRingHom) ∧
      ∀ P'' : Ideal (R' ⊗[R] S), P''.IsPrime → P''.LiesOver P → e ∉ P'' → P'' = P' := by
  classical
  obtain ⟨s, hsq, hRs, hs, hs₀⟩ := exists_notMem_and_isIntegral_forall_mem_of_ne_of_liesOver p q
  obtain ⟨m, f, b, hfm, hbm, hab, hfab, hf⟩ : ∃ (m : ℕ) (f : R[X])
      (b : p.ResidueField[X]), f.Monic ∧ b.Monic ∧ IsCoprime (X ^ (m + 1)) b ∧
        f.map (algebraMap _ _) = X ^ (m + 1) * b ∧ aeval s f = 0 := by
    let f := X * minpoly R s
    obtain ⟨q, hq, hq'⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd
      ((minpoly R s).map (algebraMap R p.ResidueField)) ((minpoly.monic hRs).map _).ne_zero 0
    have hqm : q.Monic := by
      simpa [((minpoly.monic hRs).map _).leadingCoeff] using! congr(leadingCoeff $hq).symm
    set m' := rootMultiplicity 0 ((minpoly R s).map (algebraMap R p.ResidueField))
    refine ⟨m', f, q, monic_X.mul (minpoly.monic hRs), hqm, ?_,
      by simp [f, hq, pow_succ', mul_assoc], by simp [f]⟩
    simpa [IsCoprime.pow_left_iff,
      (prime_X (R := p.ResidueField)).irreducible.coprime_iff_not_dvd] using! hq'
  obtain ⟨R', _, _, _, P, _, _, a', b', hP, ha'm, hb'm, hfab', ⟨c, d, hcd⟩, ha', hb'⟩ :=
    Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime p f
      (X ^ (m + 1)) b hfm (monic_X.pow _) hbm hfab hab
  let s₀ : integralClosure R S := ⟨s, hRs⟩
  have hfs₀ : aeval s₀ f = 0 := by
    ext1; change (integralClosure R S).val (aeval s₀ f) = 0; rwa [← aeval_algHom_apply]
  let s' : R' ⊗[R] S := 1 ⊗ₜ s
  have hs'f : aeval s' f = 0 :=
    show aeval (Algebra.TensorProduct.includeRight s) f = 0 by rw [aeval_algHom_apply, hf, map_zero]
  have hs₀'f : aeval (A := R' ⊗[R] integralClosure R S) (1 ⊗ₜ s₀) f = 0 :=
    show aeval (Algebra.TensorProduct.includeRight s₀) f = 0 by
    rw [aeval_algHom_apply, hfs₀, map_zero]
  let e₀ : R' ⊗[R] integralClosure R S := aeval (1 ⊗ₜ s₀) (c * a')
  have he₀ : IsIdempotentElem e₀ := by
    dsimp only [e₀, IsIdempotentElem]
    nth_rw 2 [eq_sub_iff_add_eq.mpr hcd]
    rw [← map_mul, mul_sub, mul_one, mul_mul_mul_comm, ← hfab']
    simp only [map_mul, map_sub, aeval_map_algebraMap, hs₀'f, mul_zero, sub_zero]
  let e : R' ⊗[R] S := aeval s' (c * a')
  let φ := Algebra.TensorProduct.map (.id R' R') (integralClosure R S).val
  have he₀e : φ e₀ = e := by
    simp only [e₀, ← aeval_algHom_apply]; rfl
  have he : IsIdempotentElem e := he₀e ▸ he₀.map _
  let P' := (Ideal.fiberIsoOfBijectiveResidueField hP).symm ⟨q, ‹_›, ‹_›⟩
  let := Localization.AtPrime.algebraOfLiesOver P P'.1
  have hP'q : P'.1.comap Algebra.TensorProduct.includeRight.toRingHom = q :=
    Ideal.comap_fiberIsoOfBijectiveResidueField_symm ..
  have hs'P' : s' ∉ P'.1 := mt (fun h ↦ hP'q.le h) hsq
  have ha'P' : aeval s' a' ∉ P'.1 := by
    simpa using! show IsScalarTower.toAlgHom R' _ P'.1.ResidueField (aeval s' a') ≠ 0 by
      rw [← aeval_algHom_apply, ← aeval_map_algebraMap P.ResidueField, ← ha']; simpa
  have hb'P' : aeval s' b' ∈ P'.1 := by
    rw [← Ideal.IsPrime.mul_mem_left_iff ha'P', ← map_mul, ← hfab']
    simp [hs'f]
  have heP' : e ∉ P'.1 := by
    intro H
    have := P'.1.mul_mem_left (aeval s' d) hb'P'
    rw [← map_mul, eq_sub_iff_add_eq'.mpr hcd, map_sub, Submodule.sub_mem_iff_left _ H,
      map_one] at this
    exact Ideal.one_notMem _ this
  refine ⟨_, inferInstance, inferInstance, inferInstance, P, ‹_›, ‹_›, e, he, e₀, he₀, he₀e, P',
    inferInstance, P'.2.2, hP'q, heP', hP, fun P'' _ _ H ↦ ?_, fun P'' _ _ H ↦ ?_⟩
  · have : (P'.1.comap φ.toRingHom).LiesOver P := inferInstanceAs ((P'.1.comap φ).LiesOver P)
    apply Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap hP
    simp only [Ideal.comap_comap, AlgHom.toRingHom_eq_coe,
      ← @AlgHom.coe_restrictScalars R R', ← AlgHom.comp_toRingHom,
      Algebra.TensorProduct.map_restrictScalars_comp_includeRight]
    simp_rw [AlgHom.comp_toRingHom, ← Ideal.comap_comap, ← AlgHom.toRingHom_eq_coe, hP'q]
    contrapose! H
    have : 1 ⊗ₜ s₀ ∈ P'' := hs₀ _ inferInstance H (by simp [Ideal.liesOver_iff, Ideal.under,
      Ideal.comap_comap, Ideal.over_def P p, Ideal.over_def P'' P, ← IsScalarTower.algebraMap_eq])
    rw [← Ideal.algebraMap_residueField_eq_zero, ← aeval_algebraMap_apply,
      Ideal.algebraMap_residueField_eq_zero.mpr this, ← eval_map_algebraMap, Polynomial.map_mul,
      mul_comm, ← (Ideal.ResidueField.mapₐ P P'' (Algebra.ofId _ _)
      (P''.over_def P)).comp_algebraMap, ← Polynomial.map_map, ← ha']
    simp
  · apply Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap hP
    rw [hP'q]
    contrapose! H
    have : s' ∈ P'' := hs _ inferInstance H (by simp [Ideal.liesOver_iff, Ideal.under,
      Ideal.comap_comap, Ideal.over_def P p, Ideal.over_def P'' P, ← IsScalarTower.algebraMap_eq])
    rw [← Ideal.algebraMap_residueField_eq_zero, ← aeval_algebraMap_apply,
      Ideal.algebraMap_residueField_eq_zero.mpr this, ← eval_map_algebraMap, Polynomial.map_mul,
      mul_comm, ← (Ideal.ResidueField.mapₐ P P'' (Algebra.ofId _ _)
      (P''.over_def P)).comp_algebraMap, ← Polynomial.map_map, ← ha']
    simp

set_option backward.isDefEq.respectTransparency false in
lemma Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq_aux₂
    {R S R' R'' : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    [CommRing R'] [Algebra R R'] [CommRing R''] [Algebra R R''] [Algebra R'' S]
    [Algebra.IsIntegral R R''] [IsScalarTower R R'' S] (q : Ideal S) (P : Ideal R') [P.IsPrime]
    (e : R' ⊗[R] S) (e₀ : R' ⊗[R] R'') (he₀ : IsIdempotentElem e₀)
    (he₀e : Algebra.TensorProduct.map (.id R' R') (IsScalarTower.toAlgHom R R'' S) e₀ = e)
    (P' : Ideal (R' ⊗[R] S))
    (hP'q : P'.comap Algebra.TensorProduct.includeRight.toRingHom = q)
    (H : ∀ P'' : Ideal (R' ⊗[R] R''), P''.IsPrime → P''.LiesOver P → e₀ ∉ P'' → P'' =
      P'.comap (Algebra.TensorProduct.map (.id R' R') (IsScalarTower.toAlgHom R R'' S)).toRingHom)
    (g : R'') (hgq : algebraMap R'' S g ∉ q)
    (hg : Function.Surjective (Localization.awayMap (algebraMap R'' S) g)) :
    ∃ f ∉ P, Module.Finite (Localization.Away f) (Localization.Away
      ((Algebra.TensorProduct.map (Algebra.ofId R' (Localization.Away f)) (AlgHom.id R S)) e)) := by
  have : Algebra.IsIntegral R' (Localization.Away e₀) :=
    .of_surjective (IsScalarTower.toAlgHom R' (R' ⊗[R] (R'')) _)
      (IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem e₀ he₀)
  obtain ⟨f, hfP, hf⟩ := Localization.exists_finite_awayMapₐ_of_surjective_awayMapₐ
    (Localization.awayMapₐ (Algebra.TensorProduct.map (.id R' R')
      (IsScalarTower.toAlgHom R R'' S)) e₀) (algebraMap (R' ⊗[R] R'') _ (1 ⊗ₜ g)) (by
    apply Localization.awayMap_awayMap_surjective
    refine Localization.awayMap_surjective_iff.mpr fun a ↦ ?_
    induction a with
    | zero => use 0; simp
    | tmul a b =>
      obtain ⟨b', m, e : _ = _⟩ := Localization.awayMap_surjective_iff.mp hg b
      refine ⟨e₀ ^ m * a ⊗ₜ b', m, ?_⟩
      simp [e, mul_pow, mul_assoc]
    | add a b ha hb =>
      obtain ⟨xa, ma, ea⟩ := ha
      obtain ⟨xb, mb, eb⟩ := hb
      refine ⟨(e₀ * 1 ⊗ₜ[R] g) ^ mb * xa + (e₀ * 1 ⊗ₜ[R] g) ^ ma * xb, ma + mb, ?_⟩
      dsimp at ea eb ⊢
      simp only [map_add, map_mul, map_pow, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
        ea, eb, pow_add]
      ring) P (by
    contrapose hgq
    obtain ⟨m, _, hm⟩ := Ideal.exists_le_maximal _ (Ideal.span_singleton_eq_top.not.mpr hgq)
    have := H (m.comap (Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap _ _)))
      inferInstance (m.comap_liesOver P (Algebra.TensorProduct.includeRight.comp
        (IsScalarTower.toAlgHom _ _ _)))
        (Ideal.notMem_of_isUnit (m.comap Algebra.TensorProduct.includeRight)
        (IsLocalization.Away.algebraMap_isUnit _))
    rw [← hP'q]
    exact this.le ((Ideal.span_singleton_le_iff_mem _).mp hm :))
  rw [he₀e] at hf
  refine ⟨f, hfP, ?_⟩
  let φ : R' ⊗[R] S →ₐ[R'] Localization.Away f ⊗[R] S :=
    Algebra.TensorProduct.map (Algebra.ofId _ _) (.id _ _)
  algebraize [φ.toRingHom]
  have : IsLocalization.Away (f ⊗ₜ 1 : R' ⊗[R] S) (Localization.Away f ⊗[R] S) := by
    have : .powers (f ⊗ₜ[R] 1) = Algebra.algebraMapSubmonoid (R' ⊗[R] S) (.powers f) := by simp
    rw [IsLocalization.Away, this]
    refine IsLocalization.tensorProduct_tensorProduct _ _ _ _ ?_
    ext; simp [RingHom.algebraMap_toAlgebra, φ]
  have : IsLocalization.Away (e * (f ⊗ₜ 1)) (Localization.Away (φ e)) :=
    .mul (Localization.Away f ⊗[R] S) (Localization.Away (algebraMap _ _ e)) _ _
  have : IsLocalization.Away (e * (f ⊗ₜ 1)) (Localization.Away (Algebra.ofId R'
      (Localization.Away e) f)) :=
    .mul' (Localization.Away e)
      (Localization.Away (algebraMap (R' ⊗[R] S) (Localization.Away e) (f ⊗ₜ[R] 1))) _ _
  let equiv := IsLocalization.algEquiv (.powers (e * (f ⊗ₜ 1)))
      (Localization.Away (φ e))
      (Localization.Away (Algebra.ofId R' (Localization.Away e) f))
  refine RingHom.finite_algebraMap.mp ?_
  convert! equiv.symm.toRingEquiv.finite.comp hf
  apply IsLocalization.ringHom_ext (.powers f)
  dsimp [-AlgEquiv.symm_toRingEquiv,
    ← AlgEquiv.toAlgHom_toRingHom, -AlgHomClass.toRingHom_toAlgHom]
  simp only [← IsScalarTower.algebraMap_eq, RingHom.comp_assoc, AlgHom.comp_algebraMap_of_tower]

/--
Let `S` be a finite type `R`-algebra, and `q` a prime lying over `p` such that `S` is quasi-finite
at `q`.
We may construct an etale `R`-algebra `R'` and a prime `P` lying over `p` with `κ(P) = κ(p)`,
such that `R' ⊗[R] S = A × B`, `A` is finite as an `R'`-module,
and there exists a unique prime in `A` lying over `P`. This prime will also lie over `q`.

The actual lemma is stated in terms of the idempotent element `e = (1, 0)`.
-/
@[stacks 00UJ]
lemma Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] [Algebra.QuasiFiniteAt R q] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R') (P : Ideal R')
      (_ : P.IsPrime) (_ : P.LiesOver p) (e : R' ⊗[R] S) (_ : IsIdempotentElem e)
      (P' : Ideal (R' ⊗[R] S)) (_ : P'.IsPrime) (_ : P'.LiesOver P), P'.comap
        Algebra.TensorProduct.includeRight.toRingHom = q ∧ e ∉ P' ∧
      Function.Bijective (Ideal.ResidueField.mapₐ p P (Algebra.ofId _ _) (P.over_def p)) ∧
      Module.Finite R' (Localization.Away e) ∧
      ∀ P'' : Ideal (R' ⊗[R] S), P''.IsPrime → P''.LiesOver P → e ∉ P'' → P'' = P' := by
  obtain ⟨R', _, _, _, P, _, _, e, he, e₀, he₀, he₀e, P', _, _, hP'q, heP', hpP, H', H⟩ :=
    exists_etale_isIdempotentElem_forall_liesOver_eq_aux p q
  obtain ⟨g, hgq, hg⟩ := Algebra.ZariskisMainProperty.of_finiteType (R := R) q
  obtain ⟨f, hfP, hf⟩ := exists_etale_isIdempotentElem_forall_liesOver_eq_aux₂ q P e e₀ he₀
    he₀e P' hP'q H' g hgq hg.2
  let Pf := P.map (algebraMap _ (Localization.Away f))
  have : Pf.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (.powers f) _ _ ‹_› (by
    rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime])
  have : Pf.LiesOver P := ⟨(IsLocalization.under_map_of_isPrime_disjoint (.powers f) _ ‹_› (by
    rwa [Ideal.disjoint_powers_iff_notMem _ (Ideal.IsPrime.isRadical ‹_›)])).symm⟩
  let φ : R' ⊗[R] S →ₐ[R'] Localization.Away f ⊗[R] S :=
    Algebra.TensorProduct.map (Algebra.ofId _ _) (.id _ _)
  let := φ.toAlgebra
  let := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  have : IsLocalization.Away (R := R' ⊗[R] S) (f ⊗ₜ 1) (Localization.Away f ⊗[R] S) := by
    have : .powers (f ⊗ₜ[R] 1) = Algebra.algebraMapSubmonoid (R' ⊗[R] S) (.powers f) := by simp
    rw [IsLocalization.Away, this]
    refine IsLocalization.tensorProduct_tensorProduct _ _ _ _ ?_
    ext; simp [RingHom.algebraMap_toAlgebra, φ]
  let P'f := P'.map (algebraMap _ (Localization.Away f ⊗[R] S))
  have hP'f : Disjoint (Submonoid.powers (f ⊗ₜ 1 : R' ⊗[R] S) : Set (R' ⊗[R] S)) ↑P' := by
    rw [Ideal.disjoint_powers_iff_notMem_of_isPrime]
    change f ∉ P'.under _
    rwa [← P'.over_def P]
  have : P'f.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ _ _ ‹_› hP'f
  have : P'f.LiesOver P' := ⟨(IsLocalization.under_map_of_isPrime_disjoint _ _ ‹_› hP'f).symm⟩
  have : P'f.LiesOver P := .trans _ P' _
  have : P'f.LiesOver Pf := ⟨congr($(PrimeSpectrum.localization_comap_injective
      (Localization.Away f) (.powers f) (a₁ := ⟨Pf, ‹_›⟩)
      (a₂ := ⟨P'f.under _, inferInstance⟩)
      (PrimeSpectrum.ext ((Pf.over_def P).symm.trans (P'f.over_def P)))).1)⟩
  refine ⟨Localization.Away f, inferInstance, inferInstance, inferInstance, Pf, inferInstance,
    .trans _ P _, Algebra.TensorProduct.map (Algebra.ofId _ _) (.id _ _) e,
    he.map _, P'f, ‹_›, ‹_›, ?_, ?_, ?_, hf, ?_⟩
  · rw [← hP'q, P'f.over_def P', Ideal.under, Ideal.comap_comap]
    congr
    ext; simp [RingHom.algebraMap_toAlgebra, φ]
  · change e ∉ P'f.under _
    rwa [← P'f.over_def P']
  · suffices Function.Bijective ⇑(Ideal.ResidueField.mapₐ P Pf
        (IsScalarTower.toAlgHom R R' (Localization.Away f)) (Pf.over_def P)) by
      convert! this.comp hpP; rw [← AlgHom.coe_comp]; congr; ext
    exact (RingHom.surjectiveOnStalks_of_isLocalization (.powers f)
      _).residueFieldMap_bijective _ _ _
  · intro P'' _ _ hP''
    have : P''.LiesOver P := .trans _ Pf _
    refine congr($(PrimeSpectrum.localization_comap_injective (R := R' ⊗[R] S)
      (Localization.Away f ⊗[R] S) (.powers (f ⊗ₜ 1)) (a₁ := ⟨P'', ‹_›⟩)
      (a₂ := ⟨P'f, ‹_›⟩) (PrimeSpectrum.ext ?_)).1)
    exact (H (P''.under _) inferInstance inferInstance hP'').trans (P'f.over_def P')

open TensorProduct

attribute [local instance] RingHom.ker_isPrime

open scoped nonZeroDivisors

attribute [local instance] Localization.AtPrime.algebraOfLiesOver

/-- A key induction step of `exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq`. -/
private theorem Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq_aux
    {R : Type u} {S : Type (max u v)} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    [q.LiesOver p] (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra.Etale R R'] (P : Ideal R')
    [P.IsPrime] [P.LiesOver p] (e : R' ⊗[R] S) (P' : Ideal (R' ⊗[R] S))
    [P'.IsPrime] [P'.LiesOver P]
    (hP'q : Ideal.comap Algebra.TensorProduct.includeRight.toRingHom P' = q)
    (heP' : e ∉ P') (hpP : Function.Bijective
      (Ideal.ResidueField.mapₐ p P (Algebra.ofId _ _) (P.over_def p)))
    (H : ∀ (P'' : Ideal (R' ⊗[R] S)), P''.IsPrime → P''.LiesOver P → e ∉ P'' → P'' = P')
    (R'' : Type u) [CommRing R''] [Algebra R' R''] [Algebra R R''] [IsScalarTower R R' R'']
    [Algebra.Etale R' R''] (Q : Ideal R'')
    [Q.IsPrime] [Q.LiesOver P] (n : ℕ)
    (e' : Fin ((n + 1) + 1) → R'' ⊗[R] S)
    (he' : CompleteOrthogonalIdempotents e')
    (he'0 : e' 0 = Algebra.TensorProduct.map (Algebra.ofId R' R'') (AlgHom.id R S) e)
    (Q' : Fin n → Ideal (R'' ⊗[R] S)) [∀ i, (Q' i).IsPrime] [∀ i, (Q' i).LiesOver Q]
    (hPQ : Function.Bijective (Ideal.ResidueField.mapₐ P Q (Algebra.ofId _ _) (Q.over_def P)))
    (hQ' : ∀ (i : Fin n), e' i.succ.castSucc ∉ Q' i)
    (H' : ∀ (P'' : Ideal (R'' ⊗[R] S)), e' 0 ∈ P'' → P''.IsPrime → P''.LiesOver Q →
      e' (.last _) ∈ P'' ∧ ∀ (i : Fin n), e' i.succ.castSucc ∉ P'' → P'' = Q' i) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R') (P : Ideal R')
      (_ : P.IsPrime) (_ : P.LiesOver p) (n : ℕ) (e : Fin (n + 1) → R' ⊗[R] S)
      (_ : CompleteOrthogonalIdempotents e) (P' : Fin n → Ideal (R' ⊗[R] S))
      (_ : ∀ i, (P' i).IsPrime) (_ : ∀ i, (P' i).LiesOver P),
      Function.Bijective (Ideal.ResidueField.mapₐ p P (Algebra.ofId _ _) (P.over_def p)) ∧
      (∀ i, e i.castSucc ∉ P' i) ∧
      ∀ (P'' : Ideal (R' ⊗[R] S)), P''.IsPrime → P''.LiesOver P →
        e (.last n) ∈ P'' ∧ ∀ i, e i.castSucc ∉ P'' → P'' = P' i := by
  let φ := Algebra.TensorProduct.map (Algebra.ofId R' R'') (AlgHom.id R S)
  have : Q.LiesOver p := .trans _ P _
  have hpQ :
    Function.Bijective (Ideal.ResidueField.mapₐ p Q (Algebra.ofId _ _) (Q.over_def p)) := by
    convert hPQ.comp hpP
    rw [← @AlgHom.coe_restrictScalars' R R', ← AlgHom.coe_comp]; congr 1; ext
  let P'φ := (Ideal.fiberIsoOfBijectiveResidueField hpQ).symm
    (Ideal.fiberIsoOfBijectiveResidueField hpP ⟨P', ‹_›, ‹_›⟩)
  have : P'φ.1.LiesOver P := .trans _ Q _
  have : (P'φ.1.comap φ.toRingHom).LiesOver P := inferInstanceAs ((P'φ.1.comap φ).LiesOver P)
  have hP'φ : P'φ.1.comap φ.toRingHom = P' := by
    apply Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap hpP
    rw [Ideal.comap_comap]
    convert Ideal.comap_fiberIsoOfBijectiveResidueField_symm hpQ _
    · ext; simp [φ]
    · simp; rfl
  refine ⟨R'', inferInstance, _, .comp R R' R'', Q, ‹_›, .trans _ P _, _, _, he', Fin.cons P'φ
    Q', Fin.cases P'φ.2.1 ?_, Fin.cases P'φ.2.2 ?_, hpQ, Fin.cases ?_ ?_, ?_⟩
  · intro P'' _ _
    by_cases heP'' : e ∈ P''.comap φ
    · obtain ⟨h₁, h₂⟩ := H' P'' (by simpa [he'0]) inferInstance inferInstance
      exact ⟨h₁, Fin.cases (fun h ↦ (h (by simpa [he'0])).elim) (by simpa)⟩
    · have : P''.LiesOver P := .trans _ Q _
      obtain rfl := H _ inferInstance inferInstance heP''
      have : ∀ i ≠ 0, e' i ∈ P'' := by
        intro j hj
        rw [← Ideal.IsPrime.mul_mem_left_iff (I := P'') heP'']
        simp [φ, ← he'0, he'.ortho hj.symm]
      refine ⟨by simp [this], Fin.cases (fun _ ↦ ?_) (by simp [this])⟩
      simp only [Fin.cons_zero]
      apply Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap hpQ
      have : (φ.restrictScalars _).comp Algebra.TensorProduct.includeRight =
          Algebra.TensorProduct.includeRight := by ext; simp [φ]
      rw [← this]
      exact congr(($hP'φ).comap Algebra.TensorProduct.includeRight).symm
  · simp only [Fin.cons_succ]; infer_instance
  · simp only [Fin.cons_succ]; infer_instance
  · rw [← hP'φ] at heP'; simpa [he'0]
  · simpa

set_option backward.isDefEq.respectTransparency false in
/-- A less universe polymorphic version of
`exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq`. Use that instead. -/
private lemma Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq'
    {R : Type u} {S : Type max u v} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : Ideal R) [p.IsPrime] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R') (P : Ideal R')
      (_ : P.IsPrime) (_ : P.LiesOver p) (n : ℕ) (e : Fin (n + 1) → R' ⊗[R] S)
      (_ : CompleteOrthogonalIdempotents e) (P' : Fin n → Ideal (R' ⊗[R] S))
      (_ : ∀ i, (P' i).IsPrime) (_ : ∀ i, (P' i).LiesOver P),
      Function.Bijective (Ideal.ResidueField.mapₐ p P (Algebra.ofId _ _) (P.over_def p)) ∧
      (∀ i, e i.castSucc ∉ P' i) ∧
      ∀ (P'' : Ideal (R' ⊗[R] S)), P''.IsPrime → P''.LiesOver P →
        e (.last n) ∈ P'' ∧ ∀ i, e i.castSucc ∉ P'' → P'' = P' i := by
  induction h : (p.primesOver S).ncard using Nat.strong_induction_on generalizing R S with
  | h n IH =>
    have : IsArtinianRing (p.ResidueField ⊗[R] S) := IsArtinianRing.of_finite p.ResidueField _
    have hpSfin : (p.primesOver S).Finite :=
      (PrimeSpectrum.primesOverOrderIsoFiber R S p).finite_iff.mpr inferInstance
    cases n with
    | zero =>
      have := (Set.ncard_eq_zero hpSfin).mp h
      refine ⟨R, inferInstance, inferInstance, inferInstance, p, inferInstance, ⟨rfl⟩, 0, 1,
        ⟨⟨by simp [IsIdempotentElem],
          by simp only [Nat.reduceAdd, Pi.one_apply, mul_one, Subsingleton.pairwise]⟩,
          by simp⟩, nofun, nofun, nofun, ?_, nofun, ?_⟩
      · rw! [ofId_self, Ideal.ResidueField.mapₐ_id]; exact Function.bijective_id
      · exact fun P h₁ h₂ ↦ (this.le
          ⟨show (P.comap Algebra.TensorProduct.includeRight.toRingHom).IsPrime from inferInstance,
          ⟨by simp [P.over_def p, Ideal.under, Ideal.comap_comap]⟩⟩).elim
    | succ n =>
    obtain ⟨q, hq, hq'⟩ := Set.nonempty_of_ncard_ne_zero (h.trans_ne (by simp))
    obtain ⟨R', _, _, _, P, _, _, e, he, P', _, _, hP'q, heP', hpP, _, H⟩ :=
      Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq p q
    have : (P.primesOver (R' ⊗[R] S ⧸ Ideal.span {e})).ncard < n + 1 := by
      let F := Ideal.fiberIsoOfBijectiveResidueField hpP (S := S)
      refine (Ideal.ncard_primesOver_quotient_singleton_lt_of_notMem _ _
        P' heP' (F.finite_iff.mpr hpSfin)).trans_le ?_
      rw [← h, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, Nat.card_congr F.toEquiv]
    obtain ⟨R'', _, _, _, Q, _, _, n, e' : _ → R'' ⊗[R'] (R' ⊗[R] S ⧸ Ideal.span {e}),
      he', Q' : _ → Ideal (R'' ⊗[R'] (R' ⊗[R] S ⧸ Ideal.span {e})), _, _, hPQ, hQ', H'⟩ :=
      IH _ this (R := R') (S := R' ⊗[R] S ⧸ Ideal.span {e}) P rfl
    let : Algebra R R'' := .compHom _ (algebraMap R R')
    have : IsScalarTower R R' R'' := .of_algebraMap_eq' rfl
    let φ := Algebra.TensorProduct.map (Algebra.ofId R' R'') (AlgHom.id R S)
    let e₁ : R'' ⊗[R'] (R' ⊗[R] S ⧸ Ideal.span {e}) ≃ₐ[R''] (R'' ⊗[R] S ⧸ Ideal.span {φ e}) :=
      tensorQuotientTensorEquiv (R'' := R'') e
    obtain ⟨e'', he'', he''e'⟩ := CompleteOrthogonalIdempotents.exists_eq_comp_of_ker_eq_span
      (Ideal.Quotient.mk (Ideal.span {φ e})) (I := Fin (n + 1)) (φ e) (he.map φ) (by simp)
      (e₁ ∘ e') (he'.map e₁.toRingHom) (fun _ ↦ Ideal.Quotient.mk_surjective _)
    have he''e'' (i : _) : e₁ (e' i) = e'' i := congr_fun he''e' i
    have hψe'' (i : _) : (e' i) = e₁.symm (e'' i) := e₁.eq_symm_apply.mpr (he''e'' i)
    refine exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq_aux p q R' P e P'
      hP'q heP' hpP (fun P'' h₁ h₂ heP'' ↦ H P'' h₁ h₂ heP'') R'' Q n _
      ((CompleteOrthogonalIdempotents.equiv (finSuccEquiv _)).mpr he'') rfl
      (Q' · |>.comap (e₁.symm.toAlgHom.comp (Ideal.Quotient.mkₐ _ _))) hPQ
      (fun i ↦ by rw [Function.comp_def]; simpa [← hψe''] using hQ' i) ?_
    simp only [Function.comp_apply, finSuccEquiv_zero, finSuccEquiv_last, Fin.castSucc_succ,
      finSuccEquiv_succ]
    intro P'' heP'' _ _
    have : (P''.map (Ideal.Quotient.mk (.span {φ e}))).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa [Ideal.span_le])
    have : (P''.map (Ideal.Quotient.mk (.span {φ e}))).LiesOver Q := ⟨by
      have : P'' ⊔ Ideal.span {φ e} = P'' := by simpa [Ideal.span_le]
      rw [← Ideal.under_under (B := R'' ⊗[R] S)]
      simpa [Ideal.under, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, this] using P''.over_def Q⟩
    have := H' ((P''.map (Ideal.Quotient.mk (.span {φ e}))).comap e₁) inferInstance
      (inferInstanceAs <| ((P''.map (Ideal.Quotient.mk (.span {φ e}))).comap
        e₁.toAlgHom).LiesOver Q)
    have hP'' : (1 - φ e) ∉ P'' :=
      fun h ↦ ‹P''.IsPrime›.one_notMem (by convert add_mem heP'' h; ring)
    simp only [Ideal.mem_comap, he''e'',
      Ideal.mem_map_span_singleton_iff_of_isIdempotentElem (he.map φ),
      Ideal.IsPrime.mul_mem_left_iff hP''] at this
    refine ⟨this.1, fun i hi ↦ (this.2 i hi).symm ▸ ?_⟩
    -- TODO: clean-up when `Ideal.comap` is refactored to take a `RingHom`
    change _ = Ideal.comap (Ideal.Quotient.mk _) (Ideal.comap (e₁.symm.trans e₁).toRingHom _)
    simp only [AlgEquiv.symm_trans_self, RingEquiv.toRingHom_eq_coe,
      AlgEquiv.toRingEquiv_toRingHom, AlgEquiv.refl_toRingHom, Ideal.comap_id]
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    simpa [left_eq_sup, ← RingHom.ker_eq_comap_bot, Ideal.span_le] using heP''

/--
If `S` is finite over `R`, and `p` is a prime of `R`, then there exists an étale neighborhood
`(R', P)` of `p` with `κ(p) = κ(P)` such that `R' ⊗[R] S ≃ₐ[R'] R₁ × ... × Rₙ × A`,
each `Rᵢ` has a unique prime `Pᵢ` lying over `P`, and no other prime in `R' ⊗[R] S` lies over `P`.

This is merely an iterated application of `exists_etale_isIdempotentElem_forall_liesOver_eq`.
This is weaker than the corresponding statement of stacks project (in particular we asked for
`Module.Finite` instead of quasi finite when localized at `p`, so that we don't need to keep
track of this when passing to quotients and tensor products), and the only reason is that
the corresponding stronger statement is even harder to state and even more annoying to prove.
-/
@[stacks 00UL]
lemma Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : Ideal R) [p.IsPrime] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R') (P : Ideal R')
      (_ : P.IsPrime) (_ : P.LiesOver p) (n : ℕ) (e : Fin (n + 1) → R' ⊗[R] S)
      (_ : CompleteOrthogonalIdempotents e) (P' : Fin n → Ideal (R' ⊗[R] S))
      (_ : ∀ i, (P' i).IsPrime) (_ : ∀ i, (P' i).LiesOver P),
      Function.Bijective (Ideal.ResidueField.mapₐ p P (Algebra.ofId _ _) (P.over_def p)) ∧
      (∀ i, e i.castSucc ∉ P' i) ∧
      ∀ (P'' : Ideal (R' ⊗[R] S)), P''.IsPrime → P''.LiesOver P →
        e (.last n) ∈ P'' ∧ ∀ i, e i.castSucc ∉ P'' → P'' = P' i := by
  have ⟨R', _, _, _, P, _, _, n, e, he, P', _, _, hP, hP', H⟩ :=
    exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq' (S := ULift.{u} S) p
  let e₁ : R' ⊗[R] S ≃ₐ[R'] R' ⊗[R] ULift.{u} S :=
    Algebra.TensorProduct.congr .refl ULift.algEquiv.symm
  refine ⟨R', _, _, ‹_›, P, ‹_›, ‹_›, n, e₁.symm ∘ e, he.map _,
    fun i ↦ (P' i).comap e₁.toAlgHom, inferInstance, inferInstance, hP, by simpa,
    fun P'' _ _ ↦ ?_⟩
  have := H (P''.comap e₁.symm.toAlgHom) inferInstance inferInstance
  refine ⟨by simpa using this.1, fun i hi ↦ ?_⟩
  simp [← this.2 i (by simpa), Ideal.comap_comapₐ]
