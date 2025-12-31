import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.CFT.Etale
import Mathlib.CFT.NewNo

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

variable {X Y S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]

noncomputable
def IsOpenImmersion.opensRangeIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    X ≅ f.opensRange :=
  X.topIso.symm ≪≫ f.isoImage _ ≪≫ Scheme.isoOfEq _ f.image_top_eq_opensRange

-- open Topology in
-- @[stacks 02LN]
-- theorem stacks02LK {x : X} {s : S} (h : f x = s) (hx : x ∈ f.quasiFiniteLocus) :
--     ∃ (U : Scheme) (g : U ⟶ S) (u : U), Etale g ∧ IsIso (g.residueFieldMap u) ∧ g u = s ∧
--     ∃ (V : (pullback f g).Opens) (v : V), IsFinite (V.ι ≫ pullback.snd f g) ∧
--       (V.ι ≫ pullback.snd f g) ⁻¹' {u} = {v} ∧ pullback.fst f g v.1 = x ∧
--       IsIso ((pullback.fst f g).residueFieldMap v.1) ∧
--       ∀ w ∈ W, pullback.snd f g w = u → pullback.fst f g w ≠ x := by sorry

open TensorProduct in
@[stacks 02LN]
theorem stacks02LN_easy [IsSeparated f]
    {x : X} {s : S} (h : f x = s) (hx : x ∈ f.quasiFiniteLocus) :
    ∃ (U : Scheme) (g : U ⟶ S) (u : U), Etale g ∧ g u = s ∧
    ∃ (V W : (pullback f g).Opens) (v : V), IsCompl V W ∧ IsFinite (V.ι ≫ pullback.snd f g) ∧
      pullback.fst f g v.1 = x := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hUV : V ≤ f ⁻¹ᵁ U⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).2
  have : (f.appLE U V hUV).hom.FiniteType :=
    LocallyOfFiniteType.finiteType_of_affine_subset ⟨U, hU⟩ ⟨V, hV⟩ hUV
  algebraize [(f.appLE U V hUV).hom]
  have : (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.LiesOver (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal := by
    suffices hU.primeIdealOf ⟨f x, hxU⟩ = Spec.map (f.appLE U V hUV) (hV.primeIdealOf ⟨x, hxV⟩) from
      ⟨congr(($this).1)⟩
    apply hU.isoSpec.inv.homeomorph.injective
    apply Subtype.ext
    simp only [IsAffineOpen.primeIdealOf, Scheme.Hom.homeomorph_apply, Scheme.hom_inv_apply]
    simp only [← Scheme.Hom.comp_apply, ← Scheme.Opens.ι_apply,
      Category.assoc, IsAffineOpen.isoSpec_inv_ι, IsAffineOpen.SpecMap_appLE_fromSpec _ hU hV,
      IsAffineOpen.isoSpec_hom, IsAffineOpen.toSpecΓ_fromSpec_assoc]
    rfl
  have : Algebra.QuasiFiniteAt Γ(S, U) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    f.quasiFiniteAt_of_memQuasiFiniteLocus x hx ⟨V, hV⟩ ⟨U, hU⟩ hUV hxV
  obtain ⟨R, _, _, _, P, _, _, e, _, P', _, _, hP', heP', -, _, -⟩ :=
    exists_etale_isIdempotentElem_forall_liesOver_eq
    (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have : (algebraMap R (Localization.Away e)).Finite := RingHom.finite_algebraMap.mpr ‹_›
  let φ : Γ(S, U) ⟶ .of R := CommRingCat.ofHom <| algebraMap Γ(S, U) R
  have hφ : φ.hom.Etale := RingHom.etale_algebraMap.mpr ‹_›
  have : Etale (Spec.map φ) := HasRingHomProperty.Spec_iff.mpr hφ
  let e₁ : Spec (.of (R ⊗ Γ(X, V))) ≅ pullback (Spec.map (f.appLE U V hUV)) (Spec.map φ) :=
    (pullbackSpecIso _ _ _).symm ≪≫ pullbackSymmetry _ _
  have he₁ : e₁.hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) := by
    dsimp [e₁, RingHom.algebraMap_toAlgebra]
    rw [Category.assoc, pullbackSymmetry_hom_comp_fst]
    exact pullbackSpecIso_inv_snd ..
  let g : Spec (.of (R ⊗[Γ(S, U)] Γ(X, V))) ⟶ pullback f (Spec.map φ ≫ hU.fromSpec) :=
    e₁.hom ≫ pullback.map _ _ _ _ hV.fromSpec (𝟙 _) hU.fromSpec
      (IsAffineOpen.SpecMap_appLE_fromSpec ..) (by simp)
  let W₁ := g ''ᵁ (PrimeSpectrum.basicOpen e)
  have : IsFinite (W₁.ι ≫ pullback.snd f _) := by
    let ι : Spec (.of (Localization.Away e)) ⟶ pullback f (Spec.map φ ≫ hU.fromSpec) :=
      Spec.map (CommRingCat.ofHom <| algebraMap _ _) ≫ g
    have : ι.opensRange = W₁ := by
      simp only [Scheme.Hom.opensRange_comp, ι, W₁]
      congr 1
      exact TopologicalSpace.Opens.ext <| PrimeSpectrum.localization_away_comap_range _ _
    rw [← this, ← MorphismProperty.cancel_left_of_respectsIso @IsFinite
      (IsOpenImmersion.opensRangeIso _).hom]
    have H : (pullbackSpecIso _ R _).inv ≫ pullback.fst _ (Spec.map (f.appLE U V hUV)) = _ :=
      pullbackSpecIso_inv_fst ..
    simpa [IsOpenImmersion.opensRangeIso, ι, g, e₁, RingHom.algebraMap_toAlgebra, φ, H,
      ← Spec.map_comp, IsFinite.SpecMap_iff]
  have : IsFinite W₁.ι := .of_comp _ (pullback.snd f _)
  let W₂ : (pullback f (Spec.map φ ≫ hU.fromSpec)).Opens :=
    ⟨W₁ᶜ, by simpa using W₁.ι.isClosedMap.isClosed_range⟩
  refine ⟨Spec (.of R), Spec.map φ ≫ hU.fromSpec,
    ⟨P, ‹_›⟩, inferInstance, ?_, W₁, W₂, ⟨g ⟨P', ‹_›⟩, ?_⟩, ?_, ‹_›, ?_⟩
  · change hU.fromSpec ⟨P.comap φ.hom, inferInstance⟩ = _
    convert hU.fromSpec_primeIdealOf ⟨f x, hxU⟩
    · exact (Ideal.over_def _ _).symm
    · simp [h]
  · exact ⟨⟨P', ‹_›⟩, heP', rfl⟩
  · simp [isCompl_iff, disjoint_iff, codisjoint_iff, W₂, SetLike.ext'_iff]
  · trans hV.fromSpec ⟨P'.comap Algebra.TensorProduct.includeRight.toRingHom, inferInstance⟩
    · simp [← Scheme.Hom.comp_apply, - Scheme.Hom.comp_base, g, reassoc_of% he₁]; rfl
    convert hV.fromSpec_primeIdealOf ⟨x, hxV⟩


-- open TensorProduct in
-- @[stacks 02LN]
-- theorem stacks02LN [IsSeparated f] {x : X} {s : S} (h : f x = s) (hx : x ∈ f.quasiFiniteLocus) :
--     ∃ (U : Scheme) (g : U ⟶ S) (u : U), Etale g ∧ IsIso (g.residueFieldMap u) ∧ g u = s ∧
--     ∃ (V W : (pullback f g).Opens) (v : V), IsCompl V W ∧ IsFinite (V.ι ≫ pullback.snd f g) ∧
--       (V.ι ≫ pullback.snd f g) ⁻¹' {u} = {v} ∧ pullback.fst f g v.1 = x ∧
--       IsIso ((pullback.fst f g).residueFieldMap v.1) ∧
--       ∀ w ∈ W, pullback.snd f g w = u → pullback.fst f g w ≠ x := by
--   obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
--     (Set.mem_univ (f x)) isOpen_univ
--   obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hUV : V ≤ f ⁻¹ᵁ U⟩ :=
--     X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).2
--   have : (f.appLE U V hUV).hom.FiniteType :=
--     LocallyOfFiniteType.finiteType_of_affine_subset ⟨U, hU⟩ ⟨V, hV⟩ hUV
--   algebraize [(f.appLE U V hUV).hom]
--   have : (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.LiesOver (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal := by
--     sorry
--   have : Algebra.QuasiFiniteAt Γ(S, U) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := sorry
--   obtain ⟨R, _, _, _, P, _, _, e, _, P', _, _, hP', heP', H₁, H₂⟩ :=
--     exists_etale_isIdempotentElem_forall_liesOver_eq
--     (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
--   let φ : Γ(S, U) ⟶ .of R := CommRingCat.ofHom <| algebraMap Γ(S, U) R
--   have hφ : φ.hom.Etale := RingHom.etale_algebraMap.mpr ‹_›
--   have : Etale (Spec.map φ) := HasRingHomProperty.Spec_iff.mpr hφ
--   let e₁ : Spec (.of (R ⊗ Γ(X, V))) ≅ pullback (Spec.map (f.appLE U V hUV)) (Spec.map φ) :=
--     (pullbackSpecIso _ _ _).symm ≪≫ pullbackSymmetry _ _
--   let g : Spec (.of (R ⊗[Γ(S, U)] Γ(X, V))) ⟶ pullback f (Spec.map φ ≫ hU.fromSpec) :=
--     e₁.hom ≫ pullback.map _ _ _ _ hV.fromSpec (𝟙 _) hU.fromSpec
--       (IsAffineOpen.SpecMap_appLE_fromSpec ..) (by simp)
--   let W₁ := g ''ᵁ (PrimeSpectrum.basicOpen e)
--   have : IsFinite (W₁.ι ≫ pullback.snd f _) := by
--     sorry
--   have : IsFinite W₁.ι := .of_comp _ (pullback.snd f _)
--   let W₂ : (pullback f (Spec.map φ ≫ hU.fromSpec)).Opens :=
--     ⟨W₁ᶜ, by simpa using W₁.ι.isClosedMap.isClosed_range⟩
--   -- have :
--   -- have : IsOpenImmersion g := by infer_instance
--   refine ⟨Spec (.of R), Spec.map φ ≫ hU.fromSpec,
--     ⟨P, ‹_›⟩, inferInstance, ?_, ?_, W₁, W₂, ⟨g ⟨P', ‹_›⟩, ?_⟩, ?_, ‹_›, ?_⟩
--   · sorry -- use H₁
--   · sorry
--   · sorry
--   · simp [isCompl_iff, disjoint_iff, codisjoint_iff, W₂, SetLike.ext'_iff]

end AlgebraicGeometry
-- exists_etale_isIdempotentElem_forall_liesOver_eq
