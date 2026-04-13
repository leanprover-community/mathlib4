/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.FieldTheory.SeparablyGenerated
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Transcendental separable extensions

In this file we introduce the concept of separably generated field extensions and
transcendental separable field extensions. We then formalizes the following result:

Let `K/k` be arbitrary field extension with characteristic `p > 0`, then TFAE
1. `K/k` is transcendental separable.
2. If `{ sᵢ } ⊆ K` is an arbitrary `k`-linearly independent set,
  `{ sᵢᵖ } ⊆ K` is also `k`-linearly independent.
3. `K ⊗ₖ k^{1/p}` is reduced.
4. `K` is geometrically reduced over `k`.

# Main definitions and results

* `Algebra.IsSeparablyGenerated` : A field extension is separably generated if there exists
  an transcendental basis such that the extension above it is separable.

* `Algebra.IsTranscendentalSeparable` : A field extension is transcendental separable if
  every finitely generated subextension is separably generated.

* `tensorProduct_isReduced_of_isTranscendentalSeparable_of_isReduced` : Tensor product of
  a transcendental separable field extension with a reduced algebra is reduced.

* `tensorProduct_isReduced_of_isSeparablyGenerated_of_isReduced` : Tensor product of
  a separably generated  field extension with a reduced algebra is reduced.

* `adjoinPthRoots`: Adjoining all `p`-th root to a field of characteristic `p`.
  It is defined as the field itself with algebra map being the frobenius map.

* `adjoinPthRootsPthRoot` : The map `k → adjoinPthRoots k p` for taking `p`-th root
  with underlying map `RingHom.id`.

* `Algebra.isTranscendentalSeparable_tfae` : The equivalent characterization of
  transcendental separable field extension mentioned above.

* `Algebra.isTranscendentalSeparable_of_isSeparablyGenerated` :
  Separably generated field extension is transcendental separable.

* `Algebra.isTranscendentalSeparable_of_perfectField` :
  All extension over perfect field is transcendental separable.

# TODO
Prove that "`k` and `Kᵖ` are linearly disjoint over `kᵖ` in `K`" is also equivalent to the
four equivalent characterization of being transcendental seprarable for
finitely generated field extension `K/k`.

-/

universe u v w

@[expose] public section

open TensorProduct

section

variable (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]

/-- A field extension is separably generated if there exists an transcendental basis such that
the extension above it is separable. -/
@[mk_iff, stacks 030O "Part 1"]
class Algebra.IsSeparablyGenerated : Prop where
  isSeparable' : ∃ (ι : Type v) (f : ι → K),
    IsTranscendenceBasis k f ∧
    Algebra.IsSeparable (IntermediateField.adjoin k (Set.range f)) K

variable {k K} in
lemma Algebra.isSeparablyGenerated_of_equiv {K' : Type w} [Field K'] [Algebra k K'] (e : K ≃ₐ[k] K')
    [Algebra.IsSeparablyGenerated k K] : Algebra.IsSeparablyGenerated k K' := by
  rcases ‹Algebra.IsSeparablyGenerated k K› with ⟨ι, f, isT, sep⟩
  have : Small.{w} ι := small_of_injective (e.injective.comp isT.1.injective)
  let g := (e ∘ f) ∘ (equivShrink ι).symm
  use Shrink.{w} ι, g, (e.isTranscendenceBasis isT).comp_equiv (equivShrink ι).symm
  have eq : (IntermediateField.adjoin k (Set.range f)).map e =
    (IntermediateField.adjoin k (Set.range g)) := by
    simp [IntermediateField.adjoin_map, g, Set.range_comp e f]
  let e' := ((IntermediateField.adjoin k (Set.range f)).equivMap e.toAlgHom).trans
    (IntermediateField.equivOfEq eq)
  exact Algebra.IsSeparable.of_equiv_equiv e'.toRingEquiv e.toRingEquiv rfl

/-- A field extension is transcendental separable if every finitely generated subextension is
separably generated. -/
@[mk_iff, stacks 030O "Part 2"]
class Algebra.IsTranscendentalSeparable : Prop where
  forall_isSeparablyGenerated : ∀ (A' : IntermediateField k K),
    Algebra.EssFiniteType k A' → Algebra.IsSeparablyGenerated k A'

end

lemma localization_minimal_isField {S : Type*} [CommRing S] [IsReduced S]
    (p : Ideal S) (min : p ∈ minimalPrimes S) :
    letI := Ideal.minimalPrimes_isPrime min
    IsField (Localization.AtPrime p) := by
  let := Ideal.minimalPrimes_isPrime min
  rw [IsLocalRing.isField_iff_maximalIdeal_eq, eq_bot_iff]
  intro x hx
  apply IsReduced.eq_zero x (nilpotent_iff_mem_prime.mpr (fun q hq ↦ ?_))
  convert hx
  have : Ideal.comap (algebraMap S (Localization.AtPrime p)) q ≤ p := by
    apply le_of_le_of_eq _ (IsLocalization.AtPrime.comap_maximalIdeal (Localization.AtPrime p) p)
    exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal_of_isPrime q)
  rw [← Localization.AtPrime.eq_maximalIdeal_iff_comap_eq]
  exact le_antisymm this (min.2 ⟨q.comap_isPrime _, bot_le⟩ this)

/-- The map of a ring to product of its localizations at minimal primes. -/
def toLocalizationMinimal (S : Type*) [CommRing S] :=
  (Pi.ringHom (fun (p : minimalPrimes S) ↦
    letI := Ideal.minimalPrimes_isPrime p.2
    algebraMap S (Localization.AtPrime p.1)))

/-- The map of a reduced ring to product of its localizations at minimal primes is injective. -/
lemma isReduced_injective_to_prod_localizations (S : Type*) [CommRing S] [IsReduced S] :
    Function.Injective (toLocalizationMinimal S) := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro x hx
  apply IsReduced.eq_zero x (nilpotent_iff_mem_prime.mpr (fun q hq ↦ ?_))
  rcases Ideal.exists_minimalPrimes_le (bot_le (a := q)) with ⟨p, min, hp⟩
  let := Ideal.minimalPrimes_isPrime min
  apply hp
  rw [← IsLocalization.AtPrime.comap_maximalIdeal (Localization.AtPrime p) p, Ideal.mem_comap]
  have : (toLocalizationMinimal S) x ⟨p, min⟩ = 0 := by simp [hx]
  simp only [toLocalizationMinimal, Pi.ringHom_apply] at this
  simp [this]

lemma IsReduced.tensorProduct_of_forall_fg_intermediateField {k : Type*} [Field k]
    {S : Type*} [CommRing S] [Algebra k S] {K : Type*} [Field K] [Algebra k K]
    (h : ∀ (L : IntermediateField k K), L.FG → IsReduced (TensorProduct k S L)) :
    IsReduced (TensorProduct k S K) := by
  refine IsReduced.tensorProduct_of_flat_of_forall_fg (fun B ⟨T, hT⟩ ↦ ?_)
  have := h _ (IntermediateField.fg_adjoin_finset T)
  have le : B ≤ (IntermediateField.adjoin k (T : Set K)).toSubalgebra := by
    simp [← hT, Algebra.adjoin_le_iff]
  have : Function.Injective (Algebra.TensorProduct.lTensor S (Subalgebra.inclusion le)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (Subalgebra.inclusion_injective le)
  exact isReduced_of_injective _ this

variable (k : Type u) [Field k] (K : Type v) [Field K] [Algebra k K]

open scoped Polynomial

lemma isReduced_of_quotient_separable_of_field (S : Type*) [Field S] (f : S[X])
    (sep : f.Separable) : IsReduced (S[X] ⧸ Ideal.span {f}) := by
  generalize deg : f.natDegree = n
  induction n using Nat.case_strong_induction_on generalizing f with
  | hz =>
    rcases Polynomial.natDegree_eq_zero.mp deg with ⟨s, rfl⟩
    by_cases eq0 : s = 0
    · have : (Ideal.span {Polynomial.C s}).IsPrime := by simpa [eq0] using Ideal.isPrime_bot
      infer_instance
    · have : Subsingleton (S[X] ⧸ Ideal.span {Polynomial.C s}) := by simp [eq0]
      infer_instance
  | hi n ih =>
    have nu : ¬IsUnit f := Polynomial.not_isUnit_of_natDegree_pos f (by simp [deg])
    have ne0 : f ≠ 0 := Polynomial.Separable.ne_zero sep
    rcases WfDvdMonoid.exists_irreducible_factor nu ne0 with ⟨p, irr, ⟨g, rfl⟩⟩
    rw [← Ideal.span_singleton_mul_span_singleton]
    have cop : IsCoprime (Ideal.span {p}) (Ideal.span {g}) := by
      rw [Ideal.isCoprime_span_singleton_iff, Irreducible.coprime_iff_not_dvd irr]
      by_contra ⟨h, rfl⟩
      absurd sep.squarefree
      simp only [Squarefree, not_forall]
      use p
      simp [← mul_assoc, irr.not_isUnit]
    have red1 : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime irr.ne_zero).mpr irr.prime
    have red2 : IsReduced (S[X] ⧸ Ideal.span {g}) := by
      have : p.natDegree > 0 := Irreducible.natDegree_pos irr
      have := deg.symm.trans (Polynomial.natDegree_mul irr.ne_zero (right_ne_zero_of_mul ne0))
      exact ih g.natDegree (by linarith) g sep.of_mul_right rfl
    exact isReduced_of_injective _ (Ideal.quotientMulEquivQuotientProd _ _ cop).injective

variable (S : Type*) [CommRing S] [Algebra k S]

lemma isReduced_of_quotient_separable [IsDomain S] (f : S[X]) (mon : f.Monic)
    (sep : f.Separable) : IsReduced (S[X] ⧸ Ideal.span {f}) := by
  let iS := (algebraMap S (FractionRing S))
  have eq : (Ideal.span {f.map iS}).comap (Polynomial.mapRingHom iS) = Ideal.span {f} := by
    ext g
    simpa [Ideal.map_span, Ideal.mem_span_singleton] using
      Polynomial.map_dvd_map iS (FaithfulSMul.algebraMap_injective _ _) mon
  let iQ : (S[X] ⧸ Ideal.span {f}) →+* ((FractionRing S)[X] ⧸ Ideal.span {f.map iS}) :=
    Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (Polynomial.mapRingHom iS)) (fun x hx ↦ by
      simpa [Ideal.Quotient.eq_zero_iff_mem] using le_of_eq eq.symm hx)
  have := isReduced_of_quotient_separable_of_field _ (f.map iS) sep.map
  apply isReduced_of_injective iQ ((Ideal.injective_lift_iff _).mpr _)
  simp [← RingHom.comap_ker, eq]

/-- The canonical isomorphism `K[X] ⊗[k] S ≃ₐ[K] (K ⊗[k] S)[X]` for `k`-algebra `S, K`. -/
noncomputable def polynomialTensorProductEquiv : K[X] ⊗[k] S ≃ₐ[K] (K ⊗[k] S)[X] :=
  ((((Algebra.TensorProduct.congr (polyEquivTensor' k K) AlgEquiv.refl).trans
    (Algebra.TensorProduct.assoc k k K K k[X] S)).trans
      (Algebra.TensorProduct.congr AlgEquiv.refl (Algebra.TensorProduct.comm k k[X] S))).trans
        (Algebra.TensorProduct.assoc k k K K S k[X]).symm).trans
          ((polyEquivTensor' k (K ⊗[k] S)).symm.restrictScalars K)

lemma polynomialTensorProductEquiv_map_algebraMap (f : K[X]) :
    f.map (algebraMap K (K ⊗[k] S)) =
    (polynomialTensorProductEquiv k K S) ((algebraMap K[X] (K[X] ⊗[k] S)) f) := by
  obtain ⟨g, rfl⟩ := (polyEquivTensor' k K).symm.surjective f
  induction g with
  | zero => simp
  | add g1 g2 hg1 hg2 => simp only [map_add, Polynomial.map_add, hg1, hg2]
  | tmul x y =>
    have : Polynomial.map (algebraMap K (K ⊗[k] S)) ((polyEquivTensor k K).symm (x ⊗ₜ[k] y)) =
      (polyEquivTensor k (K ⊗[k] S)).symm (x ⊗ₜ[k] 1 ⊗ₜ[k] y) := by
      simp [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    simpa [- polyEquivTensor_symm_apply_tmul_eq_smul, polynomialTensorProductEquiv]

/-- The equivalence of adjoining on root inside tensor product and outside tensor product. -/
noncomputable def quotientPolynomialTensorProductEquiv (f : K[X]) :
    (K[X] ⧸ Ideal.span {f}) ⊗[k] S ≃ₐ[K]
    (K ⊗[k] S)[X] ⧸ Ideal.span {f.map (algebraMap K (K ⊗[k] S))} :=
  let : IsScalarTower K (K[X] ⧸ Ideal.span {f})
    (K[X] ⊗[k] S ⧸ Ideal.map (algebraMap K[X] (K[X] ⊗[k] S)) (Ideal.span {f})) :=
    IsScalarTower.of_algebraMap_eq' rfl
  (((Algebra.TensorProduct.cancelBaseChange k K[X] K[X] (K[X] ⧸ Ideal.span {f})
    S).symm.restrictScalars K).trans
      ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor _ _).symm.restrictScalars K)).trans
        (Ideal.quotientEquivAlg _ _ (polynomialTensorProductEquiv k K S) (by
          simp only [Ideal.map_span, Set.image_singleton, RingHom.coe_coe,
            polynomialTensorProductEquiv_map_algebraMap]))

open IntermediateField.algebraAdjoinAdjoin in
lemma tensorProduct_isReduced_of_isTranscendentalBasis_of_isDomain [IsDomain S]
    {ι : Type v} (f : ι → K) (isT : IsTranscendenceBasis k f)
    [sep : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range f)) K]
    [Algebra.EssFiniteType (IntermediateField.adjoin k (Set.range f)) K] :
    IsReduced (TensorProduct k K S) := by
  classical
  set K' := IntermediateField.adjoin k (Set.range f)
  have : Algebra.IsAlgebraic K' K := isT.isAlgebraic_field
  have : FiniteDimensional K' K := Algebra.finite_of_essFiniteType_of_isAlgebraic
  obtain ⟨y, hy⟩ := Field.exists_primitive_element K' K
  let kx := Algebra.adjoin k (Set.range f)
  let e : TensorProduct k kx S ≃ₐ[k] MvPolynomial ι S :=
    (Algebra.TensorProduct.congr (AlgebraicIndependent.aevalEquiv isT.1).symm AlgEquiv.refl).trans
      MvPolynomial.scalarRTensorAlgEquiv
  have isd1 : IsDomain (TensorProduct k kx S) := e.injective.isDomain
  let nz := nonZeroDivisors kx
  have : IsLocalization nz K' := inferInstanceAs (IsFractionRing _ K')
  have isl := IsLocalization.tensorRight K' nz (S := TensorProduct k kx S)
  let : Algebra (kx ⊗[k] S) (K' ⊗[kx] (kx ⊗[k] S)) := Algebra.TensorProduct.rightAlgebra
  have le_nz : nz.map (algebraMap kx (kx ⊗[k] S)) ≤ nonZeroDivisors (↥kx ⊗[k] S) := by
    rw [Submonoid.map_le_iff_le_comap]
    intro x
    simp only [mem_nonZeroDivisors_iff_ne_zero, ne_eq, Submonoid.mem_comap, nz]
    exact fun hx ↦ (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective kx (kx ⊗[k] S))).mpr hx
  have isd2 := @IsLocalization.isDomain_of_le_nonZeroDivisors _ _ _ _ _ _ isl isd1 le_nz
  have isd3 : IsDomain (K' ⊗[k] S) :=
    (Algebra.TensorProduct.cancelBaseChange k kx kx K' S).symm.injective.isDomain
  let f := minpoly K' y
  have fsep : f.Separable := sep.1 y
  have fmon : f.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral y)
  let eK : K ≃ₐ[K'] K'[X] ⧸ Ideal.span {f} :=
    (IntermediateField.topEquiv.symm.trans (IntermediateField.equivOfEq hy).symm).trans
    (IntermediateField.adjoinRootEquivAdjoin K' (Algebra.IsIntegral.isIntegral y)).symm
  let eTen : K ⊗[k] S ≃ₐ[K'] (K' ⊗[k] S)[X] ⧸ Ideal.span {f.map (algebraMap K' (K' ⊗[k] S))} :=
    (Algebra.TensorProduct.congr eK AlgEquiv.refl).trans
    (quotientPolynomialTensorProductEquiv k K' S f)
  have red : IsReduced ((K' ⊗[k] S)[X] ⧸ Ideal.span {f.map (algebraMap K' (K' ⊗[k] S))}) :=
    isReduced_of_quotient_separable _ _ (fmon.map _) fsep.map
  exact isReduced_of_injective _ eTen.injective

open IntermediateField.algebraAdjoinAdjoin in
lemma tensorProduct_isReduced_of_isSeparablyGenerated_isDomain [IsDomain S]
    [Algebra.IsSeparablyGenerated k K] [Algebra.EssFiniteType k K] :
    IsReduced (TensorProduct k K S) := by
  obtain ⟨ι, f, isT, sep⟩ : Algebra.IsSeparablyGenerated k K := ‹_›
  have := Algebra.EssFiniteType.of_comp k (IntermediateField.adjoin k (Set.range f)) K
  exact tensorProduct_isReduced_of_isTranscendentalBasis_of_isDomain k K S f isT

lemma tensorProduct_isReduced_of_isTranscendentalBasis_of_isReduced [IsReduced S]
    [Algebra.FiniteType k S] {ι : Type v} (f : ι → K) (isT : IsTranscendenceBasis k f)
    [sep : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range f)) K]
    [Algebra.EssFiniteType (IntermediateField.adjoin k (Set.range f)) K] :
    IsReduced (TensorProduct k K S) := by
  classical
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have h (x : k) (y : S) : (toLocalizationMinimal S) (x • y) = x • (toLocalizationMinimal S) y := by
    ext p
    simp [toLocalizationMinimal, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
  let g := AlgHom.mk' (toLocalizationMinimal S) h
  have inj : Function.Injective (Algebra.TensorProduct.lTensor K g) :=
    Module.Flat.lTensor_preserves_injective_linearMap _
      (isReduced_injective_to_prod_localizations S)
  let : Fintype (minimalPrimes S) := (minimalPrimes.finite_of_isNoetherianRing S).fintype
  have (p : minimalPrimes S) :
    letI := Ideal.minimalPrimes_isPrime p.2
    IsReduced (K ⊗[k] Localization.AtPrime p.1) := by
    let := (localization_minimal_isField p.1 p.2).toField
    exact tensorProduct_isReduced_of_isTranscendentalBasis_of_isDomain k K _ f isT
  have : IsReduced (K ⊗[k] ((p : (minimalPrimes S)) →
    letI := Ideal.minimalPrimes_isPrime p.2
    Localization.AtPrime p.1)) := by
    apply isReduced_of_injective _ (Algebra.TensorProduct.piRight k k K
      (fun (p : (minimalPrimes S)) ↦
        letI := Ideal.minimalPrimes_isPrime p.2
        Localization.AtPrime p.1)).injective
  exact isReduced_of_injective _ inj

lemma tensorProduct_isReduced_of_isTranscendentalSeparable_of_isReduced_of_essFiniteType
    [Algebra.FiniteType k S] [IsReduced S] [Algebra.IsSeparablyGenerated k K]
    [Algebra.EssFiniteType k K] : IsReduced (TensorProduct k K S) := by
  classical
  obtain ⟨ι, f, isT, sep⟩ : Algebra.IsSeparablyGenerated k K := ‹_›
  have := Algebra.EssFiniteType.of_comp k (IntermediateField.adjoin k (Set.range f)) K
  exact tensorProduct_isReduced_of_isTranscendentalBasis_of_isReduced k K S f isT

@[stacks 030U "Part 1"]
lemma tensorProduct_isReduced_of_isTranscendentalSeparable_of_isReduced [IsReduced S]
    [Algebra.IsTranscendentalSeparable k K] : IsReduced (TensorProduct k K S) := by
  refine IsReduced.tensorProduct_of_flat_of_forall_fg (fun B hB ↦ ?_)
  have : Algebra.FiniteType k B := (Subalgebra.fg_iff_finiteType B).mp hB
  have : IsReduced B := isReduced_of_injective B.val Subtype.val_injective
  have : IsReduced (TensorProduct k B K) := by
    refine IsReduced.tensorProduct_of_forall_fg_intermediateField (fun L hL ↦ ?_)
    rw [← IntermediateField.essFiniteType_iff] at hL
    have := Algebra.IsTranscendentalSeparable.forall_isSeparablyGenerated L hL
    have := tensorProduct_isReduced_of_isTranscendentalSeparable_of_isReduced_of_essFiniteType k L B
    exact isReduced_of_injective _ (Algebra.TensorProduct.comm k B L).injective
  exact isReduced_of_injective _ (Algebra.TensorProduct.comm k K B).injective

@[stacks 030U "Part 2"]
lemma tensorProduct_isReduced_of_isSeparablyGenerated_of_isReduced [IsReduced S]
    [Algebra.IsSeparablyGenerated k K] : IsReduced (TensorProduct k K S) := by
  refine IsReduced.tensorProduct_of_flat_of_forall_fg (fun B hB ↦ ?_)
  have : Algebra.FiniteType k B := (Subalgebra.fg_iff_finiteType B).mp hB
  have : IsReduced B := isReduced_of_injective B.val Subtype.val_injective
  have : IsReduced (TensorProduct k B K) := by
    refine IsReduced.tensorProduct_of_forall_fg_intermediateField (fun L ⟨G, hG⟩ ↦ ?_)
    rcases ‹Algebra.IsSeparablyGenerated k K› with ⟨ι, f, isT, sep⟩
    set M := IntermediateField.adjoin k (Set.range f)
    let M' := IntermediateField.adjoin k ((Set.range f) ∪ (G : Set K))
    have : IsReduced (TensorProduct k B M') := by
      have mem (x : ι) : f x ∈ M' := IntermediateField.subset_adjoin _ _ (by simp)
      let f' : ι → M' := fun x ↦ ⟨f x, mem x⟩
      have imagef' : Subtype.val '' Set.range f' = Set.range f := (Set.range_comp _ _).symm
      have isT' : IsTranscendenceBasis k f' := isT.of_comp M'.val Subtype.val_injective
      have : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range f')) M' := by
        have Mle : M ≤ M' := IntermediateField.adjoin.mono _ _ _ (by simp)
        let := (IntermediateField.inclusion Mle).toRingHom.toAlgebra
        let : IsScalarTower M M' K := IsScalarTower.of_algebraMap_eq' rfl
        have : Algebra.IsSeparable M M' := Algebra.isSeparable_tower_bot_of_isSeparable M M' K
        have eq : (IntermediateField.adjoin k (Set.range f')).map M'.val = M := by
          simp [IntermediateField.adjoin_map, f', M, imagef']
        let e := ((IntermediateField.adjoin k (Set.range f')).equivMap M'.val).trans
          (IntermediateField.equivOfEq eq)
        apply Algebra.IsSeparable.of_equiv_equiv e.toRingEquiv.symm (RingEquiv.refl M')
        ext m
        have : (e.symm m).1.1 = (e (e.symm m)).1 := by simp [- AlgEquiv.apply_symm_apply, e]
        simpa only [e.apply_symm_apply] using this
      have : Algebra.EssFiniteType (IntermediateField.adjoin k (Set.range f')) ↥M' := by
        rw [← IntermediateField.fg_top_iff]
        use G.preimage M'.val Subtype.val_injective.injOn
        refine le_antisymm le_top (fun x hx ↦ ?_)
        rw [← IntermediateField.mem_restrictScalars k, IntermediateField.adjoin_adjoin_left]
        simp only [IntermediateField.coe_val, Finset.coe_preimage, ← IntermediateField.mem_lift,
          IntermediateField.lift_adjoin, Set.image_union, imagef']
        convert x.2
        ext z
        have : z ∈ G → z ∈ M' := fun hz ↦ IntermediateField.subset_adjoin _ _ (by simp [hz])
        simpa
      have := tensorProduct_isReduced_of_isTranscendentalBasis_of_isReduced k _ B f' isT'
      exact isReduced_of_injective _ (Algebra.TensorProduct.comm k B _).injective
    have le : L ≤ M' := le_of_eq_of_le hG.symm (IntermediateField.adjoin.mono _ _ _ (by simp))
    have : Function.Injective (Algebra.TensorProduct.lTensor B (IntermediateField.inclusion le)) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ (IntermediateField.inclusion_injective le)
    exact isReduced_of_injective _ this
  exact isReduced_of_injective _ (Algebra.TensorProduct.comm k K B).injective

section charp

/-- Adjoining all `p`-th root to a field of characteristic `p`.
It is defined as the field itself with algebra map being the frobenius map. -/
@[nolint unusedArguments]
def adjoinPthRoots (p : ℕ) [ExpChar k p] := k

variable (p : ℕ) [ExpChar k p]

instance : Field (adjoinPthRoots k p) := inferInstanceAs (Field k)

instance : Algebra k (adjoinPthRoots k p) := (frobenius k p).toAlgebra

/-- The map `adjoinPthRoots k p → k` with underlying map `RingHom.id`. -/
def adjoinPthRootsSelf : (adjoinPthRoots k p) →+* k := RingHom.id k

lemma adjoinPthRootsSelf_algebraMap (x : adjoinPthRoots k p) :
    algebraMap k (adjoinPthRoots k p) (adjoinPthRootsSelf k p x) = x ^ p := rfl

lemma adjoinPthRoots_pth_power_mem_bot (x : adjoinPthRoots k p) :
    x ^ p ∈ (⊥ : IntermediateField k (adjoinPthRoots k p)) := by
  use adjoinPthRootsSelf k p x
  rfl

instance [Fact (Nat.Prime p)] : Algebra.IsAlgebraic k (adjoinPthRoots k p) where
  isAlgebraic x := by
    use Polynomial.X ^ p - Polynomial.C (adjoinPthRootsSelf k p x)
    refine ⟨(Polynomial.monic_X_pow_sub_C _ (NeZero.ne' p).symm).ne_zero, ?_⟩
    simp [adjoinPthRootsSelf_algebraMap]

/-- The map `k → adjoinPthRoots k p` for taking `p`-th root with underlying map `RingHom.id`. -/
def adjoinPthRootsPthRoot : k →+* (adjoinPthRoots k p) := RingHom.id k

lemma adjoinPthRootsPthRoot_bijective : Function.Bijective (adjoinPthRootsPthRoot k p) :=
  (RingEquiv.refl k).bijective

lemma adjoinPthRootsPthRoot_pow (x : k) : algebraMap k (adjoinPthRoots k p) x =
    (adjoinPthRootsPthRoot k p x) ^ p := rfl

lemma linearIndepOn_pow_of_isReduced_tensorProduct (hp : Nat.Prime p)
    (red : IsReduced (TensorProduct k (adjoinPthRoots k p) K)) (s : Finset K)
    (li : LinearIndepOn k _root_.id (s : Set K)) : LinearIndepOn k (· ^ p) (s : Set K) := by
  simp only [LinearIndepOn, LinearIndependent, SetLike.coe_sort_coe, ← LinearMap.ker_eq_bot,
    LinearMap.ker_eq_bot']
  intro y hy
  have li' := Module.Flat.linearIndependent_one_tmul (S := (adjoinPthRoots k p)) li
  let rooty := Finsupp.mapRange.addMonoidHom (adjoinPthRootsPthRoot k p).toAddMonoidHom y
  have : Fact (Nat.Prime p) := ⟨hp⟩
  let : Nontrivial (adjoinPthRoots k p ⊗[k] K) := by
    apply Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left
    exact RingHom.injective _
  have : CharP (adjoinPthRoots k p ⊗[k] K) p := by
    apply (Algebra.charP_iff k _ p).mp
    induction ‹ExpChar k p› with
    | zero => exact (Nat.not_prime_one hp).elim
    | prime hq => assumption
  have rooty_supp : rooty.support = y.support :=
    Finsupp.support_mapRange_of_injective (map_zero _) y (adjoinPthRootsPthRoot_bijective k p).1
  have rooty_app (x : s) : (rooty x) ^ p = algebraMap k _ (y x) := adjoinPthRootsPthRoot_pow k p _
  have h0 : frobenius _ p (rooty.sum fun (i : s) (c : adjoinPthRoots k p) ↦ c ⊗ₜ[k] i.1) = 0 := by
    simp only [Finsupp.sum, map_sum, frobenius_def, Algebra.TensorProduct.tmul_pow, rooty_app]
    simp only [Finsupp.linearCombination, Finsupp.coe_lsum, Finsupp.sum, LinearMap.coe_smulRight,
      LinearMap.id_coe, id_eq, ← rooty_supp] at hy
    apply Eq.trans _ ((Algebra.TensorProduct.includeRight.congr_arg hy).trans (map_zero _))
    simp only [map_sum, map_smul, Algebra.TensorProduct.includeRight_apply]
    congr
    ext x
    simp [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul']
  have : (Finsupp.linearCombination (adjoinPthRoots k p)
    fun (x : s) ↦ (1 : adjoinPthRoots k p) ⊗ₜ[k] x.1) rooty = 0 := by
    simpa [Finsupp.linearCombination, rooty, Algebra.smul_def] using eq_zero_of_pow_eq_zero h0
  exact (map_eq_zero_iff (Finsupp.mapRange.addMonoidHom (adjoinPthRootsPthRoot k p).toAddMonoidHom)
    (Finsupp.mapRange_injective _ (map_zero _) (adjoinPthRootsPthRoot_bijective k p).1)).mp
    ((map_eq_zero_iff _ li').mp this)

instance : ExpChar (AlgebraicClosure k) p := ExpChar.of_injective_algebraMap' k _

@[stacks 030W]
lemma Algebra.isTranscendentalSeparable_tfae (hp : Nat.Prime p) :
    [ Algebra.IsTranscendentalSeparable k K,
      ∀ s : Finset K,
        LinearIndepOn k _root_.id (s : Set K) → LinearIndepOn k (· ^ p) (s : Set K),
      IsReduced (TensorProduct k (adjoinPthRoots k p) K),
      Algebra.IsGeometricallyReduced k K].TFAE := by
  tfae_have 1 → 4 := by
    intro sep
    have := tensorProduct_isReduced_of_isTranscendentalSeparable_of_isReduced
      k K (AlgebraicClosure k)
    apply (Algebra.isGeometricallyReduced_iff k K).mpr
    exact isReduced_of_injective _ (Algebra.TensorProduct.comm k _ K).injective
  tfae_have 4 → 3 := by
    have : Fact (Nat.Prime p) := ⟨hp⟩
    simp only [isGeometricallyReduced_iff]
    intro red
    let f : (adjoinPthRoots k p) →ₐ[k] (AlgebraicClosure k) :=
      (IsAlgClosure.equiv k (AlgebraicClosure (adjoinPthRoots k p))
        (AlgebraicClosure k)).toAlgHom.comp (IsScalarTower.toAlgHom k (adjoinPthRoots k p) _)
    have : Function.Injective (Algebra.TensorProduct.rTensor K f) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (RingHom.injective _)
    exact isReduced_of_injective _ this
  tfae_have 3 → 2 := fun red s li ↦ linearIndepOn_pow_of_isReduced_tensorProduct k K p hp red s li
  tfae_have 2 → 1 := by
    simp only [Algebra.isTranscendentalSeparable_iff, Algebra.isSeparablyGenerated_iff]
    intro h L hL
    classical
    have h' (s : Finset L) : LinearIndepOn k _root_.id (s : Set L) →
      LinearIndepOn k (fun x ↦ x ^ p) (s : Set L) := by
      intro li
      have li' := h (s.image L.val) (by
        simpa using (li.map_injOn L.val.toLinearMap Subtype.val_injective.injOn).id_image)
      simp only [IntermediateField.coe_val, Finset.coe_image] at li'
      have li'' := li'.comp_of_image Subtype.val_injective.injOn
      have : (fun x ↦ x ^ p) ∘ Subtype.val = L.val.toLinearMap ∘ (fun x ↦ x ^ p) := rfl
      rw [this] at li''
      exact li''.of_comp
    rcases exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType p hp h'
      with ⟨T, isT, sep⟩
    use T, Subtype.val, isT
    convert sep
    <;> simp
  tfae_finish

end charp

lemma Algebra.isSeparablyGenerated_of_charZero [CharZero k] : Algebra.IsSeparablyGenerated k K := by
  rcases exists_isTranscendenceBasis' k K with ⟨ι, f, isT⟩
  use ι, f, isT
  have : Algebra.IsAlgebraic (IntermediateField.adjoin k (Set.range f)) K := isT.isAlgebraic_field
  exact Algebra.IsSeparable.of_integral _ K

lemma Algebra.isTranscendentalSeparable_of_charZero [CharZero k] :
    Algebra.IsTranscendentalSeparable k K :=
  ⟨fun L _ ↦ isSeparablyGenerated_of_charZero k L⟩

/-- Separably generated field extension is transcendental separable. -/
@[stacks 030X]
lemma Algebra.isTranscendentalSeparable_of_isSeparablyGenerated [Algebra.IsSeparablyGenerated k K] :
    Algebra.IsTranscendentalSeparable k K := by
  rcases CharP.exists' k with char0|⟨p, prime, charp⟩
  · exact Algebra.isTranscendentalSeparable_of_charZero k K
  · apply ((Algebra.isTranscendentalSeparable_tfae k K p prime.out).out 0 2).mpr
    have := tensorProduct_isReduced_of_isSeparablyGenerated_of_isReduced k K (adjoinPthRoots k p)
    exact isReduced_of_injective _ (Algebra.TensorProduct.comm k _ _).injective

lemma Algebra.isTranscendentalSeparable_iff_isSeparablyGenerated_of_essFiniteType
    [Algebra.EssFiniteType k K] :
    Algebra.IsTranscendentalSeparable k K ↔ Algebra.IsSeparablyGenerated k K := by
  refine ⟨fun h ↦ ?_, fun _ ↦ Algebra.isTranscendentalSeparable_of_isSeparablyGenerated k K⟩
  have := h.1 ⊤ (IntermediateField.essFiniteType_iff.mpr (IntermediateField.fg_top_iff.mpr ‹_›))
  exact Algebra.isSeparablyGenerated_of_equiv IntermediateField.topEquiv

@[stacks 030Y "Equivalence to the alternative definition."]
lemma Algebra.isTranscendentalSeparable_of_perfectField [PerfectField k] :
    Algebra.IsTranscendentalSeparable k K := by
  rcases CharP.exists' k with char0|⟨p, prime, charp⟩
  · exact Algebra.isTranscendentalSeparable_of_charZero k K
  · apply ((Algebra.isTranscendentalSeparable_tfae k K p prime.out).out 0 2).mpr
    have perf : PerfectRing k p := inferInstance
    have bij : Function.Bijective (Algebra.ofId k (adjoinPthRoots k p)) := perf.bijective_frobenius
    let e := (Algebra.TensorProduct.congr (AlgEquiv.ofBijective _ bij).symm AlgEquiv.refl).trans
      (Algebra.TensorProduct.lid k K)
    exact isReduced_of_injective _ e.injective
