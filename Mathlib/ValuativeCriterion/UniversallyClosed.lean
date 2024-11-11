-- `Mathlib/AlgebraicGeometry/Morphisms/UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.ValuativeCriterion.Fiber

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

open AlgebraicGeometry (topologically)

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

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

instance {K} [Field K] : Unique (Spec (.of K)) :=
  inferInstanceAs <| Unique (PrimeSpectrum K)

@[simp]
lemma default_asIdeal {K} [Field K] : (default : Spec (.of K)).asIdeal = ⊥ := rfl

lemma Spec.map_base_apply {R S : CommRingCat} (f : R ⟶ S) (x : Spec S) :
    (Spec.map f).base x = PrimeSpectrum.comap f x :=
  rfl

lemma aeval_ite_mem_eq_self {σ R : Type*} [CommRing R] (q : MvPolynomial σ R)
    {s : Set σ} (hs : q.vars.toSet ⊆ s) [∀ i, Decidable (i ∈ s)] :
    MvPolynomial.aeval (fun i ↦ if i ∈ s then .X i else 0) q = q := by
  rw [MvPolynomial.as_sum q, MvPolynomial.aeval_sum]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  rw [MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq]
  congr 1
  exact Finsupp.prod_congr (fun i hi ↦ by simp [hs ((MvPolynomial.mem_vars _).mpr ⟨u, hu, hi⟩)])

lemma Scheme.Hom.isClosedMap {X Y : Scheme} (f : X.Hom Y) [UniversallyClosed f] :
    IsClosedMap f.base := UniversallyClosed.out _ _ _ IsPullback.of_id_snd

open Scheme.Pullback _root_.PrimeSpectrum in
/--
For a (formalizable) proof, see https://imgur.com/a/nTDzDFj.

inspired by
https://mathoverflow.net/questions/23337/is-a-universally-closed-morphism-of-schemes-quasi-compact/23528#23528
-/
lemma compactSpace_of_universallyClosed
    {K} [Field K] (f : X ⟶ Spec (.of K)) [UniversallyClosed f] : CompactSpace X := by
  classical
  let 𝒰 : X.OpenCover := X.affineCover
  let U (i : 𝒰.J) : X.Opens := (𝒰.map i).opensRange
  let T : Scheme := Spec (.of <| MvPolynomial 𝒰.J K)
  let q : T ⟶ Spec (.of K) := Spec.map MvPolynomial.C
  let Ti (i : 𝒰.J) : T.Opens := basicOpen (MvPolynomial.X i)
  let fT : pullback f q ⟶ T := pullback.snd f q
  let p : pullback f q ⟶ X := pullback.fst f q
  let Z : Set (pullback f q : _) := (⨆ i, fT ⁻¹ᵁ (Ti i) ⊓ p ⁻¹ᵁ (U i) : (pullback f q).Opens)ᶜ
  have hZ : IsClosed Z := by
    simp only [Z, isClosed_compl_iff, Opens.coe_iSup, Opens.coe_inf, Opens.map_coe]
    exact isOpen_iUnion fun i ↦ (fT.continuous.1 _ (Ti i).2).inter (p.continuous.1 _ (U i).2)
  let Zc : T.Opens := ⟨(fT.base '' Z)ᶜ, (fT.isClosedMap _ hZ).isOpen_compl⟩
  let ψ : MvPolynomial 𝒰.J K →ₐ[K] K := MvPolynomial.aeval (fun _ ↦ 1)
  let t : T := (Spec.map <| CommRingCat.ofHom ψ.toRingHom).base default
  have ht (i : 𝒰.J) : t ∈ Ti i := show ψ (.X i) ≠ 0 by simp [ψ]
  have htZc : t ∈ Zc := by
    intro ⟨z, hz, hzt⟩
    suffices ∃ i, fT.base z ∈ Ti i ∧ p.base z ∈ U i from hz (by simpa)
    exact ⟨𝒰.f (p.base z), hzt ▸ ht _, by simpa [U] using 𝒰.covers (p.base z)⟩
  obtain ⟨U', ⟨g, rfl⟩, htU', hU'le⟩ := Opens.isBasis_iff_nbhd.mp isBasis_basic_opens htZc
  let σ : Finset 𝒰.J := MvPolynomial.vars g
  let φ : MvPolynomial 𝒰.J K →+* MvPolynomial 𝒰.J K :=
    (MvPolynomial.aeval fun i : 𝒰.J ↦ if i ∈ σ then MvPolynomial.X i else 0).toRingHom
  let t' : T := (Spec.map φ).base t
  have ht'g : t' ∈ PrimeSpectrum.basicOpen g :=
    show φ g ∉ t.asIdeal from (show φ g = g from aeval_ite_mem_eq_self g subset_rfl).symm ▸ htU'
  have h : t' ∉ fT.base '' Z := hU'le ht'g
  suffices ⋃ i ∈ σ, (U i).1 = Set.univ from
    ⟨this ▸ Finset.isCompact_biUnion _ fun i _ ↦ isCompact_range (𝒰.map i).continuous⟩
  rw [Set.iUnion₂_eq_univ_iff]
  contrapose! h
  obtain ⟨x, hx⟩ := h
  obtain ⟨z, rfl, hzr⟩ := exists_preimage_pullback x t' (Subsingleton.elim (f.base x) (q.base t'))
  suffices ∀ i, t ∈ (Ti i).comap (comap φ) → p.base z ∉ U i from ⟨z, by simpa [Z, p, hzr], hzr⟩
  intro i hi₁ hi₂
  rw [comap_basicOpen, show φ (.X i) = 0 by simpa [φ] using (hx i · hi₂), basicOpen_zero] at hi₁
  cases hi₁

/--
Use `compactSpace_of_universallyClosed` and `universallyClosed_stableUnderBaseChange` and
`Scheme.Hom.range_fiberι` and `isProperMap_iff_isClosedMap_and_compact_fibers`
-/
lemma isProperMap_of_universallyClosed [UniversallyClosed f] : IsProperMap f.base := by
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  refine ⟨Scheme.Hom.continuous f, ?_, ?_⟩
  · exact MorphismProperty.universally_le (P := topologically @IsClosedMap) _ UniversallyClosed.out
  · intro y
    have := compactSpace_of_universallyClosed (pullback.snd f (Y.fromSpecResidueField y))
    rw [← Scheme.range_fromSpecResidueField, ← Scheme.Pullback.range_fst]
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
