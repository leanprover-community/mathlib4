-- `Mathlib/AlgebraicGeometry/Morphisms/UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.ValuativeCriterion.Fiber

open CategoryTheory CategoryTheory.Limits TopologicalSpace

section TOBEMOVED

lemma _root_.SpecializingMap.comp {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {f : X → Y} {g : Y → Z} (hf : SpecializingMap f)
    (hg : SpecializingMap g) :
    SpecializingMap (g ∘ f) := by
  rw [specializingMap_iff_closure_singleton_subset] at hf hg ⊢
  intro x z hz
  obtain ⟨y, hy, rfl⟩ := hg (f x) hz
  obtain ⟨x', hx', rfl⟩ := hf x hy
  use x', hx'
  simp

namespace AlgebraicGeometry

instance specializingMap_respectsIso : (topologically @SpecializingMap).RespectsIso := by
  apply topologically_respectsIso
  · introv
    exact f.isClosedMap.specializingMap
  · introv hf hg
    exact hf.comp hg

instance specializingMap_isLocalAtTarget : IsLocalAtTarget (topologically @SpecializingMap) := by
  apply topologically_isLocalAtTarget
  · introv _ _ hf
    rw [specializingMap_iff_closure_singleton_subset] at hf ⊢
    intro ⟨x, hx⟩ ⟨y, hy⟩ hcl
    simp only [closure_subtype, Set.restrictPreimage_mk, Set.image_singleton] at hcl
    obtain ⟨a, ha, hay⟩ := hf x hcl
    rw [← specializes_iff_mem_closure] at hcl
    exact ⟨⟨a, by simp [hay, hy]⟩, by simpa [closure_subtype], by simpa⟩
  · introv hU _ hsp
    simp_rw [specializingMap_iff_closure_singleton_subset] at hsp ⊢
    intro x y hy
    have : ∃ i, y ∈ U i := Opens.mem_iSup.mp (hU ▸ trivial)
    obtain ⟨i, hi⟩ := this
    rw [← specializes_iff_mem_closure] at hy
    have hfx : f x ∈ U i := (U i).2.stableUnderGeneralization hy hi
    have hy : (⟨y, hi⟩ : U i) ∈ closure {⟨f x, hfx⟩} := by
      simp only [closure_subtype, Set.image_singleton]
      rwa [← specializes_iff_mem_closure]
    obtain ⟨a, ha, hay⟩ := hsp i ⟨x, hfx⟩ hy
    rw [closure_subtype] at ha
    simp only [Opens.carrier_eq_coe, Set.image_singleton] at ha
    apply_fun Subtype.val at hay
    simp only [Opens.carrier_eq_coe, Set.restrictPreimage_coe] at hay
    use a.val, ha, hay

end AlgebraicGeometry

end TOBEMOVED

/--
move to `PrimeSpectrum/Basic`

Uses `Ideal.exists_minimalPrimes_comap_eq` and `Ideal.exists_minimalPrimes_le`

-/
lemma PrimeSpectrum.isClosed_range_of_stableUnderSpecialization
    {R S} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : StableUnderSpecialization (Set.range (comap f))) :
    IsClosed (Set.range (comap f)) := by
  rw [isClosed_iff_zeroLocus]
  use (RingHom.ker f)
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact Ideal.comap_mono bot_le
  · intro (hp : RingHom.ker f ≤ p.asIdeal)
    obtain ⟨q, hq, hqle⟩ := Ideal.exists_minimalPrimes_le hp
    replace hq : Minimal (fun a ↦ a.IsPrime ∧ RingHom.ker f ≤ a) q := hq
    obtain ⟨q', hq', hq'c⟩ := Ideal.exists_minimalPrimes_comap_eq f q hq
    replace hq' : Minimal (fun a ↦ a.IsPrime ∧ ⊥ ≤ a) q' := hq'
    apply hf ((le_iff_specializes ⟨q, (Minimal.prop hq).left⟩ p).mp hqle)
    use ⟨q', (Minimal.prop hq').left⟩
    ext : 1
    exact hq'c

lemma PrimeSpectrum.isClosed_image_of_stableUnderSpecialization'
    {R S} [CommRing R] [CommRing S] (f : R →+* S)
    (A : Set (PrimeSpectrum S)) (hA : IsClosed A)
    (hf : StableUnderSpecialization (comap f '' A)) :
    IsClosed (comap f '' A) := by
  rw [isClosed_iff_zeroLocus_ideal] at hA ⊢
  obtain ⟨I, rfl⟩ := hA
  use I.comap f
  ext p
  constructor
  · rintro ⟨q, hqle, rfl⟩
    exact Ideal.comap_mono hqle
  · intro (hp : I.comap f ≤ p.asIdeal)
    obtain ⟨q, hq, hqle⟩ := Ideal.exists_minimalPrimes_le hp
    replace hq : Minimal (fun a ↦ a.IsPrime ∧ I.comap f ≤ a) q := hq
    obtain ⟨q', hq', hq'c⟩ := Ideal.exists_minimalPrimes_comap_eq f q hq
    replace hq' : Minimal (fun a ↦ a.IsPrime ∧ I ≤ a) q' := hq'
    apply hf ((le_iff_specializes ⟨q, (Minimal.prop hq).left⟩ p).mp hqle)
    refine ⟨⟨q', (Minimal.prop hq').left⟩, (Minimal.prop hq').right, ?_⟩
    ext : 1
    exact hq'c

namespace AlgebraicGeometry

open AlgebraicGeometry (topologically)

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

lemma isClosed_image_of_stableUnderSpecialization_of_isAffine [IsAffine X] [IsAffine Y]
    (A : Set X) (hA : IsClosed A) (hf : StableUnderSpecialization (f.base '' A)) :
    IsClosed (f.base '' A) := by
  let φ := f.app ⊤
  let iX := X.isoSpec
  let iY := Y.isoSpec
  let f' : Spec Γ(X, f ⁻¹ᵁ ⊤) ⟶ Spec Γ(Y, ⊤) := Spec.map φ
  let A' : Set (Spec Γ(X, f ⁻¹ᵁ ⊤)) := iX.hom.base '' A
  have hA' : IsClosed A' := iX.hom.homeomorph.isClosedMap A hA
  have hf' : StableUnderSpecialization (f'.base '' A') := by
    dsimp only [A']
    rw [← Set.image_comp]
    erw [← TopCat.coe_comp]
    rw [← Scheme.comp_base]
    dsimp only [iX, f', φ]
    rw [Scheme.isoSpec_hom_naturality, Scheme.comp_base, TopCat.coe_comp, Set.image_comp]
    exact iY.hom.homeomorph.isClosedMap.specializingMap.stableUnderSpecialization_image hf
  have res' : IsClosed (f'.base '' A') :=
    PrimeSpectrum.isClosed_image_of_stableUnderSpecialization' φ A' hA' hf'
  have nat : iX.hom ≫ f' ≫ iY.inv = f := by
    dsimp only [f', φ, iX, iY]
    simp [Scheme.isoSpec_hom_naturality_assoc]
  have : f.base '' A = iY.inv.base '' (f'.base '' A') := by
    simp only [A']
    rw [← Set.image_comp, ← Set.image_comp, ← TopCat.coe_comp, ← Scheme.comp_base]
    erw [← TopCat.coe_comp]
    rw [← Scheme.comp_base, nat]
  rw [this]
  have : IsClosedMap iY.inv.base := iY.inv.homeomorph.isClosedMap
  apply this
  exact res'

lemma compactSpace_iff_exists :
    CompactSpace X ↔
      ∃ (R : CommRingCat.{u}) (f : Spec R ⟶ X), Function.Surjective f.base := by
  constructor
  · intro h
    let 𝒰 : X.OpenCover := X.affineCover.finiteSubcover
    have (x : 𝒰.J) : IsAffine (𝒰.obj x) := X.isAffine_affineCover _
    let R : CommRingCat := .of (Π (x : 𝒰.J), Γ(𝒰.obj x, ⊤))
    let i : Spec R ≅ ∐ (fun x : 𝒰.J ↦ Spec Γ(𝒰.obj x, ⊤)) := (asIso (sigmaSpec _)).symm
    let p : ∐ (fun x : 𝒰.J ↦ Spec Γ(𝒰.obj x, ⊤)) ⟶ X :=
      Sigma.desc (fun x : 𝒰.J ↦ (𝒰.obj x).isoSpec.inv ≫ 𝒰.map x)
    use R, i.hom ≫ p
    simp only [Scheme.comp_coeBase, TopCat.coe_comp]
    apply Function.Surjective.comp ?_ i.hom.surjective
    intro x
    let j : 𝒰.J := 𝒰.f x
    obtain ⟨y, hy⟩ := 𝒰.covers x
    use (Sigma.ι (fun x : 𝒰.J ↦ Spec Γ(𝒰.obj x, ⊤)) j).base ((𝒰.obj j).isoSpec.hom.base y)
    rw [← Scheme.comp_base_apply]
    rw [← Scheme.comp_base_apply]
    simpa [p]
  · intro ⟨R, f, hf⟩
    constructor
    rw [← hf.range_eq]
    apply isCompact_range
    exact Scheme.Hom.continuous f

/-- Best proved using #14428 -/
lemma isCompact_iff_exists {U : X.Opens} :
    IsCompact (U : Set X) ↔
      ∃ (R : CommRingCat.{u}) (f : Spec R ⟶ X), Set.range f.1.base = U := by
  constructor
  · intro hU
    have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
    obtain ⟨R, f, hf⟩ := compactSpace_iff_exists.mp this
    use R, f ≫ U.ι
    simp [hf.range_comp]
  · intro ⟨R, f, hf⟩
    have : CompactSpace U.toScheme := by
      rw [compactSpace_iff_exists]
      use R, IsOpenImmersion.lift U.ι f (by simp [hf])
      rw [← Set.range_iff_surjective]
      have : Function.Injective (U.ι.base '' ·) := Set.image_val_injective
      apply this
      simp only [Set.image_univ, Scheme.Opens.range_ι]
      rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.comp_base]
      simpa
    exact isCompact_iff_compactSpace.mpr this

lemma isClosedMap_of_comp {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : X → Y) (g : Y → Z) (hf : Continuous f)
    (hfs : Function.Surjective f) (hgf : IsClosedMap (g ∘ f)) :
    IsClosedMap g := by
  intro A hA
  have : g '' A = (g ∘ f) '' (f ⁻¹' A) := by
    rw [Set.image_comp, Set.image_preimage_eq _ hfs]
  rw [this]
  exact hgf _ (hA.preimage hf)

/--
use `isCompact_iff_exists` to reduce to range and use
`PrimeSpectrum.isClosed_range_of_stableUnderSpecialization`.

https://stacks.math.columbia.edu/tag/01K9
-/
private lemma isClosedMap_iff_isSpecializingMap_aux [IsAffine Y] (f : X ⟶ Y) [QuasiCompact f] :
    IsClosedMap f.base ↔ SpecializingMap f.base := by
  refine ⟨fun h ↦ h.specializingMap, fun h ↦ ?_⟩
  have : CompactSpace X := (quasiCompact_over_affine_iff f).mp inferInstance
  let U : Opens X := ⊤
  have hU : IsCompact (U : Set X) := CompactSpace.isCompact_univ
  obtain ⟨S, g, hg⟩ := isCompact_iff_exists.mp hU
  intro A hA
  let A' : Set (Spec S) := g.base ⁻¹' A
  have hgs : Function.Surjective g.base := by
    rwa [← Set.range_iff_surjective]
  have : IsClosed A' := hA.preimage (Scheme.Hom.continuous g)
  have : f.base '' A = (g ≫ f).base '' A' := by
    rw [Scheme.comp_base, TopCat.coe_comp, Set.image_comp]
    simp only [A', Set.image_preimage_eq _ hgs]
  rw [this]
  apply isClosed_image_of_stableUnderSpecialization_of_isAffine
  · exact hA.preimage (Scheme.Hom.continuous g)
  rw [← this]
  exact h.stableUnderSpecialization_image hA.stableUnderSpecialization

/--
use `isClosedMap_iff_isSpecializingMap_aux` and the fact that both sides are local at target.
(maybe postpone this until refactor lands)

https://stacks.math.columbia.edu/tag/01K9
-/
lemma isClosedMap_iff_specializingMap [QuasiCompact f] :
    IsClosedMap f.1.base ↔ SpecializingMap f.1.base := by
  constructor
  · intro hf
    exact hf.specializingMap
  intro hf
  wlog h : IsAffine Y generalizing X Y
  · show topologically @IsClosedMap f
    rw [IsLocalAtTarget.iff_of_iSup_eq_top (P := topologically @IsClosedMap) _
      (iSup_affineOpens_eq_top _)]
    intro U
    haveI hqc : QuasiCompact (f ∣_ U) := IsLocalAtTarget.restrict ‹QuasiCompact f› U
    apply this (f ∣_ U)
    · exact IsLocalAtTarget.restrict (P := topologically @SpecializingMap) hf U
    exact U.2
  rwa [isClosedMap_iff_isSpecializingMap_aux]

/-
use `isClosedMap_iff_specializingMap`
-/
lemma universallyClosed_iff_specializingMap [QuasiCompact f] :
    UniversallyClosed f ↔ (topologically @SpecializingMap).universally f := by
  rw [universallyClosed_eq]
  constructor
  · intro h Z W g i₂ f' hp
    have : QuasiCompact f' := MorphismProperty.of_isPullback hp.flip inferInstance
    have hcl : IsClosedMap f'.base := h g i₂ f' hp
    rwa [isClosedMap_iff_specializingMap] at hcl
  · intro h Z W g i₂ f' hp
    have : QuasiCompact f' := MorphismProperty.of_isPullback hp.flip inferInstance
    have hcl : SpecializingMap f'.base := h g i₂ f' hp
    rwa [← isClosedMap_iff_specializingMap] at hcl

lemma _root_.AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality_apply
    {R S : CommRingCat} (f : R ⟶ S) (r : R) :
    (Scheme.ΓSpecIso S).inv (f r) = ((Spec.map f).app ⊤) ((Scheme.ΓSpecIso R).inv r) := by
  show (f ≫ (Scheme.ΓSpecIso S).inv) r = _
  simp

@[simp]
lemma _root_.CommRingCat.of_apply {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (r : R) :
    CommRingCat.ofHom f r = f r :=
  rfl

instance {K} [Field K] : Unique (Spec (.of K)) :=
  inferInstanceAs <| Unique (PrimeSpectrum K)

@[simp]
lemma default_asIdeal {K} [Field K] : (default : Spec (.of K)).asIdeal = ⊥ := rfl

lemma Spec_mem_basicOpen {R : CommRingCat} (f : Γ(Spec R, ⊤)) (x : Spec R) :
    x ∈ (Spec R).basicOpen f ↔ (Scheme.ΓSpecIso R).hom f ∉ x.asIdeal := by
  simp
  rfl

lemma Spec_map_base {R S : CommRingCat} (f : R ⟶ S) (x : Spec S) :
    (Spec.map f).base x = PrimeSpectrum.comap f x :=
  rfl

lemma aeval_ite_mem_vars {σ R : Type*} [CommRing R] [DecidableEq σ] (q : MvPolynomial σ R) :
    MvPolynomial.aeval (fun i ↦ if i ∈ q.vars then .X i else 0) q = q := by
  rw [MvPolynomial.as_sum q, MvPolynomial.aeval_sum]
  refine Finset.sum_congr rfl (fun u hu ↦ ?_)
  rw [MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq]
  congr 1
  refine Finsupp.prod_congr (fun i hi ↦ ?_)
  have : i ∈ q.vars := by
    rw [MvPolynomial.mem_vars]
    use u
  simp [this]

@[simp]
lemma CommRingCat.hom_inv_apply {R S : CommRingCat} (e : R ≅ S) (r : R) :
    e.inv (e.hom r) = r := by
  show (e.hom ≫ e.inv) r = r
  simp

@[simp]
lemma CommRingCat.inv_hom_apply {R S : CommRingCat} (e : R ≅ S) (s : S) :
    e.hom (e.inv s) = s := by
  show (e.inv ≫ e.hom) s = s
  simp

/--
For a (formalizable) proof, see https://imgur.com/a/nTDzDFj.

inspired by
https://mathoverflow.net/questions/23337/is-a-universally-closed-morphism-of-schemes-quasi-compact/23528#23528
-/
lemma compactSpace_of_universallyClosed
    {K} [Field K] (f : X ⟶ Spec (.of K)) [UniversallyClosed f] : CompactSpace X := by
  classical
  let 𝒰 : X.OpenCover := X.affineCover
  let U (i : 𝒰.J) : X.Opens := 𝒰.map i ''ᵁ ⊤
  let T : Scheme := Spec (.of <| MvPolynomial 𝒰.J K)
  let q : T ⟶ Spec (.of K) := Spec.map MvPolynomial.C
  let R : CommRingCat := .of <| MvPolynomial 𝒰.J K
  let Ti (i : 𝒰.J) : T.Opens := T.basicOpen ((Scheme.ΓSpecIso R).inv <| MvPolynomial.X (R := K) i)
  let fT : pullback f q ⟶ T := pullback.snd f q
  let p : pullback f q ⟶ X := pullback.fst f q
  let V (i : 𝒰.J) : (pullback f q).Opens := fT ⁻¹ᵁ (Ti i) ⊓ p ⁻¹ᵁ (U i)
  let Z : Set (pullback f q).carrier := (iSup V).carrierᶜ
  have hZ : IsClosed Z := by
    rw [isClosed_compl_iff]
    simp only [Opens.carrier_eq_coe, Opens.coe_iSup, Opens.coe_inf, Opens.map_coe]
    apply isOpen_iUnion
    intro i
    apply IsOpen.inter
    exact (Ti i).2.preimage (Scheme.Hom.continuous fT)
    exact (U i).2.preimage (Scheme.Hom.continuous p)
  have hfT : IsClosedMap fT.base :=
    UniversallyClosed.out p q fT (IsPullback.of_hasPullback f q).flip
  have hfZ : IsClosed (fT.base '' Z) := hfT _ hZ
  let Zc : Opens T := ⟨(fT.base '' Z)ᶜ, hfZ.isOpen_compl⟩
  let ψ : MvPolynomial 𝒰.J K →ₐ[K] K := MvPolynomial.aeval (fun _ ↦ 1)
  let h : Spec (.of K) ⟶ T := Spec.map ψ.toRingHom
  let t : T := h.base default
  have ht (i : 𝒰.J) : t ∈ Ti i := by
    simp only [Ti, t]
    rw [Spec_mem_basicOpen]
    simp only [R]
    erw [CommRingCat.inv_hom_apply]
    rw [Spec_map_base]
    simp [ψ]
  have : t ∉ fT.base '' Z := by
    intro ⟨z, hz, hzt⟩
    apply hz
    simp only [Opens.carrier_eq_coe, Opens.coe_iSup, Opens.coe_inf, Opens.map_coe, Set.mem_iUnion,
      Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]
    refine ⟨𝒰.f (p.base z), ?_, ?_⟩
    · rw [hzt]
      apply ht
    · simpa [U] using 𝒰.covers (p.base z)
  have htZc : t ∈ Zc := this
  obtain ⟨U', ⟨g, rfl⟩, htU', hU'le⟩ :=
    Opens.isBasis_iff_nbhd.mp (AlgebraicGeometry.isBasis_basicOpen T) htZc
  let σ : Finset 𝒰.J := MvPolynomial.vars ((Scheme.ΓSpecIso R).hom g)
  let φ : MvPolynomial 𝒰.J K →+* MvPolynomial 𝒰.J K :=
    (MvPolynomial.aeval (fun i : 𝒰.J ↦ if i ∈ σ then MvPolynomial.X i else 0)).toRingHom
  let t' : T := (Spec.map φ).base t
  have ht'g : t' ∈ T.basicOpen g := by
    simp only [t']
    rw [Spec_mem_basicOpen, Spec_map_base]
    have : φ ((Scheme.ΓSpecIso R).hom g) = (Scheme.ΓSpecIso R).hom g :=
      aeval_ite_mem_vars ((Scheme.ΓSpecIso R).hom g)
    simp only [CommRingCat.coe_of, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, this]
    erw [← Spec_mem_basicOpen g t]
    exact htU'
  have ht'Zc : t' ∉ fT.base '' Z := hU'le ht'g
  have hσ : ⋃ i ∈ σ, (U i).1 = Set.univ := by
    by_contra h
    apply ht'Zc
    rw [Set.iUnion_eq_univ_iff] at h
    simp only [Opens.carrier_eq_coe, Set.mem_iUnion, SetLike.mem_coe, exists_prop, not_forall,
      not_exists, not_and] at h
    obtain ⟨x, hx⟩ := h
    have tri : f.base x = q.base t' := Subsingleton.elim _ _
    obtain ⟨z, hzl, hzr⟩ := Scheme.Pullback.exists_preimage_pullback x t' tri
    refine ⟨z, ?_, hzr⟩
    simp only [Opens.carrier_eq_coe, Opens.coe_iSup, Opens.coe_inf, Opens.map_coe, Set.compl_iUnion,
      Set.mem_iInter, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe, Z,
      not_and_or]
    intro i
    rw [hzl, hzr]
    by_cases h : i ∈ σ
    · exact Or.inr (hx i h)
    · apply Or.inl
      simp only [t']
      convert_to t ∉ (Spec.map φ) ⁻¹ᵁ (Ti i)
      simp only [Ti]
      have hφi : (CommRingCat.ofHom φ) (MvPolynomial.X i) = 0 := by
        simpa [φ]
      have : ((Spec.map <| CommRingCat.ofHom φ).app ⊤)
          ((Scheme.ΓSpecIso R).inv (MvPolynomial.X i)) = 0 := by
        erw [← Scheme.ΓSpecIso_inv_naturality_apply]
        erw [hφi]
        simp
      simp only [Scheme.preimage_basicOpen]
      erw [this]
      simp only [Opens.map_top, Scheme.basicOpen_zero]
      intro a
      exact a
  constructor
  rw [← hσ]
  apply Finset.isCompact_biUnion
  rintro i -
  simp only [Scheme.Hom.image_top_eq_opensRange, Opens.carrier_eq_coe, Scheme.Hom.opensRange_coe, U]
  exact isCompact_range (Scheme.Hom.continuous _)

/--
Use `compactSpace_of_universallyClosed` and `universallyClosed_stableUnderBaseChange` and
`Scheme.Hom.range_fiberι` and `isProperMap_iff_isClosedMap_and_compact_fibers`
-/
lemma isProperMap_of_universallyClosed [UniversallyClosed f] : IsProperMap f.base := by
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  refine ⟨Scheme.Hom.continuous f, ?_, ?_⟩
  · exact MorphismProperty.universally_le (P := topologically @IsClosedMap) _ UniversallyClosed.out
  · intro y
    have : UniversallyClosed (f.fiberToResidueField y) :=
      MorphismProperty.of_isPullback (f.fiber_isPullback y) inferInstance
    have : CompactSpace (f.fiber y) := compactSpace_of_universallyClosed (f.fiberToResidueField y)
    rw [← Scheme.Hom.range_fiberι]
    exact isCompact_range (Scheme.Hom.continuous _)

/--
Use `IsProperMap.isCompact_preimage`.
This holds for any map between topological spaces. Maybe generalize.
-/
instance (priority := 900) [UniversallyClosed f] : QuasiCompact f where
  isCompact_preimage _ _ hUc :=
    IsProperMap.isCompact_preimage (isProperMap_of_universallyClosed f) hUc

/-- needs the instance above and `universallyClosed_iff_specializingMap`. -/
lemma universallyClosed_eq_universallySpecializing :
    @UniversallyClosed = (topologically @SpecializingMap).universally ⊓ @QuasiCompact := by
  ext X Y f
  constructor
  · intro hf
    exact ⟨(universallyClosed_iff_specializingMap f).mp hf, inferInstance⟩
  · intro ⟨hf, _⟩
    exact (universallyClosed_iff_specializingMap f).mpr hf

end AlgebraicGeometry
