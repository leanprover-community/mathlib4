-- `Mathlib/AlgebraicGeometry/Morphisms/UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.ValuativeCriterion.Fiber

open CategoryTheory CategoryTheory.Limits TopologicalSpace

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
    (A : Set X) (hA : IsClosed A) (hf : StableUnderSpecialization (f.val.base '' A)) :
    IsClosed (f.val.base '' A) := by
  let φ := f.app ⊤
  let iX := X.isoSpec
  let iY := Y.isoSpec
  let f' : Spec Γ(X, f ⁻¹ᵁ ⊤) ⟶ Spec Γ(Y, ⊤) := Spec.map φ
  let A' : Set (Spec Γ(X, f ⁻¹ᵁ ⊤)) := iX.hom.val.base '' A
  have hA' : IsClosed A' := iX.hom.homeomorph.isClosedMap A hA
  have hf' : StableUnderSpecialization (f'.val.base '' A') := by
    dsimp only [A']
    rw [← Set.image_comp]
    erw [← TopCat.coe_comp]
    rw [← Scheme.comp_val_base]
    dsimp only [iX, f', φ]
    rw [Scheme.isoSpec_hom_naturality, Scheme.comp_val_base, TopCat.coe_comp, Set.image_comp]
    exact iY.hom.homeomorph.isClosedMap.specializingMap.stableUnderSpecialization_image hf
  have res' : IsClosed (f'.val.base '' A') :=
    PrimeSpectrum.isClosed_image_of_stableUnderSpecialization' φ A' hA' hf'
  have nat : iX.hom ≫ f' ≫ iY.inv = f := by
    dsimp only [f', φ, iX, iY]
    simp [Scheme.isoSpec_hom_naturality_assoc]
  have : f.val.base '' A = iY.inv.val.base '' (f'.val.base '' A') := by
    simp only [A']
    rw [← Set.image_comp, ← Set.image_comp, ← TopCat.coe_comp, ← Scheme.comp_val_base]
    erw [← TopCat.coe_comp]
    rw [← Scheme.comp_val_base, nat]
  rw [this]
  have : IsClosedMap iY.inv.val.base := iY.inv.homeomorph.isClosedMap
  apply this
  exact res'

lemma compactSpace_iff_exists :
    CompactSpace X ↔
      ∃ (R : CommRingCat.{u}) (f : Spec R ⟶ X), Function.Surjective f.val.base := by
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
    use (Sigma.ι (fun x : 𝒰.J ↦ Spec Γ(𝒰.obj x, ⊤)) j).val.base ((𝒰.obj j).isoSpec.hom.val.base y)
    rw [← Scheme.comp_val_base_apply]
    rw [← Scheme.comp_val_base_apply]
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
      have : Function.Injective (U.ι.val.base '' ·) := Set.image_val_injective
      apply this
      simp only [Set.image_univ, Scheme.Opens.range_ι]
      rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.comp_val_base]
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
private lemma isClosedMap_iff_isSpecializingMap_aux {R} (f : X ⟶ Spec R) [QuasiCompact f] :
    IsClosedMap f.1.base ↔ SpecializingMap f.1.base := by
  refine ⟨fun h ↦ h.specializingMap, fun h ↦ ?_⟩
  have : CompactSpace X := (quasiCompact_over_affine_iff f).mp inferInstance
  let U : Opens X := ⊤
  have hU : IsCompact (U : Set X) := CompactSpace.isCompact_univ
  obtain ⟨S, g, hg⟩ := isCompact_iff_exists.mp hU
  intro A hA
  let A' : Set (Spec S) := g.val.base ⁻¹' A
  have hgs : Function.Surjective g.val.base := by
    rwa [← Set.range_iff_surjective]
  have : IsClosed A' := hA.preimage (Scheme.Hom.continuous g)
  have : f.val.base '' A = (g ≫ f).val.base '' A' := by
    rw [Scheme.comp_val_base, TopCat.coe_comp, Set.image_comp]
    simp only [A', Set.image_preimage_eq _ hgs]
  rw [this]
  apply isClosed_image_of_stableUnderSpecialization_of_isAffine
  exact hA.preimage (Scheme.Hom.continuous g)
  rw [← this]
  exact h.stableUnderSpecialization_image hA.stableUnderSpecialization

/--
use `isClosedMap_iff_isSpecializingMap_aux` and the fact that both sides are local at target.
(maybe postpone this until refactor lands)

https://stacks.math.columbia.edu/tag/01K9
-/
lemma isClosedMap_iff_specializingMap [QuasiCompact f] :
    IsClosedMap f.1.base ↔ SpecializingMap f.1.base := by
  show topologically @IsClosedMap f ↔ topologically @SpecializingMap f
  sorry

/--
use `isClosedMap_iff_specializingMap`
-/
lemma universallyClosed_iff_specializingMap [QuasiCompact f] :
    UniversallyClosed f ↔ (topologically @SpecializingMap).universally f := by
  rw [universallyClosed_eq]
  constructor
  · intro h Z W g i₂ f' hp
    have : QuasiCompact f' := quasiCompact_stableUnderBaseChange hp.flip inferInstance
    have hcl : IsClosedMap f'.val.base := h g i₂ f' hp
    rwa [isClosedMap_iff_specializingMap] at hcl
  · intro h Z W g i₂ f' hp
    have : QuasiCompact f' := quasiCompact_stableUnderBaseChange hp.flip inferInstance
    have hcl : SpecializingMap f'.val.base := h g i₂ f' hp
    rwa [← isClosedMap_iff_specializingMap] at hcl

/--
For a (formalizable) proof, see https://imgur.com/a/nTDzDFj.

inspired by
https://mathoverflow.net/questions/23337/is-a-universally-closed-morphism-of-schemes-quasi-compact/23528#23528
-/
lemma compactSpace_of_universallyClosed
    {K} [Field K] (f : X ⟶ Spec (.of K)) [UniversallyClosed f] : CompactSpace X := sorry

/--
Use `compactSpace_of_universallyClosed` and `universallyClosed_stableUnderBaseChange` and
`Scheme.Hom.range_fiberι` and `isProperMap_iff_isClosedMap_and_compact_fibers`
-/
lemma isProperMap_of_universallyClosed [UniversallyClosed f] : IsProperMap f.1.base := by
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  refine ⟨Scheme.Hom.continuous f, ?_, ?_⟩
  · exact MorphismProperty.universally_le (P := topologically @IsClosedMap) _ UniversallyClosed.out
  · intro y
    have : UniversallyClosed (f.fiberToResidueField y) :=
      universallyClosed_stableUnderBaseChange (f.fiber_isPullback y) inferInstance
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
