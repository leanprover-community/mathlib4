import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp_

@[expose] public section

open CategoryTheory Limits

section

theorem JacobsonSpace.closure_inter_closedPoints_eq_closure
    {X : Type*} [TopologicalSpace X] [JacobsonSpace X]
    (S : Set X) (hS : IsLocallyClosed S) :
    closure (S ∩ closedPoints X) = closure S := by
  refine (closure_mono (Set.inter_subset_left)).antisymm ?_
  rw [IsClosed.closure_subset_iff isClosed_closure]
  intro x hx
  by_contra H
  obtain ⟨y, ⟨hy₁, hy₂⟩, hy₃⟩ := nonempty_inter_closedPoints (Z := S \ closure (S ∩ closedPoints X))
    ⟨x, hx, H⟩ (.inter hS isClosed_closure.isOpen_compl.isLocallyClosed)
  exact hy₂ (subset_closure ⟨hy₁, hy₃⟩)

lemma Set.Finite.isDiscrete_of_subset_closedPoints {X : Type*} [TopologicalSpace X]
    {s : Set X} (hs : s.Finite) (hs' : s ⊆ closedPoints X) : IsDiscrete s := by
  have : T1Space s := ⟨fun x ↦ by convert (hs' x.2).preimage continuous_subtype_val; aesop⟩
  have : Finite s := hs
  exact ⟨inferInstance⟩

theorem subsingleton_image_closure_of_finite_of_isIrreducible
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [JacobsonSpace X]
    (S : Set X) (hS : IsLocallyClosed S) (hS' : IsIrreducible S)
    (f : X → Y) (hf₁ : Continuous f) (hf₂ : IsClosedMap f) (hfS : (f '' S).Finite) :
    (f '' closure S).Subsingleton := by
  have H₁ : IsIrreducible (S ∩ closedPoints X) := by
    rwa [← isIrreducible_iff_closure, ← JacobsonSpace.closure_inter_closedPoints_eq_closure _ hS,
      isIrreducible_iff_closure] at hS'
  have H₂ : f '' (S ∩ closedPoints X) ⊆ closedPoints Y := by
    rintro _ ⟨x, hx, rfl⟩; simpa using hf₂ _ hx.2
  have H₃ := ((hfS.subset (Set.image_mono Set.inter_subset_left)).isDiscrete_of_subset_closedPoints
    H₂).subsingleton_of_isPreirreducible (H₁.image _ hf₁.continuousOn).isPreirreducible
  have H₄ : IsClosed (f '' (S ∩ closedPoints X)) := by
    obtain (h | ⟨x, hx⟩) := Set.eq_empty_or_nonempty (f '' (S ∩ closedPoints X))
    · simp [h]
    · rw [H₃.eq_singleton_of_mem hx]; exact H₂ hx
  have := image_closure_subset_closure_image (s := S ∩ closedPoints X) hf₁
  rw [JacobsonSpace.closure_inter_closedPoints_eq_closure _ hS, H₄.closure_eq] at this
  exact H₃.anti this

end

namespace AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X : Scheme}

open MonoidalCategory CartesianMonoidalCategory MonObj

instance (G : Over (Spec (.of K))) [GrpObj G] : IsClosedImmersion η[G].left :=
  isClosedImmersion_of_comp_eq_id (Y := Spec (.of K)) G.hom η[G].left (by simp)

section IsAlgClosed

variable [IsAlgClosed K]

lemma ext_of_apply_closedPoint_eq
    (f g : Spec (.of K) ⟶ X) (h : X ⟶ Spec (.of K))
    [LocallyOfFiniteType h]
    (hf : f ≫ h = 𝟙 _) (hg : g ≫ h = 𝟙 _)
    (H : f (IsLocalRing.closedPoint K) = g (IsLocalRing.closedPoint K)) : f = g :=
  congr($((pointEquivClosedPoint h).injective (a₁ := ⟨f, hf⟩) (a₂ := ⟨g, hg⟩) (Subtype.ext H)).1)

lemma ext_of_fromSpecResidueField_eq {X Y Z : Scheme} (f g : X ⟶ Y) (i : Y ⟶ Z) [IsSeparated i]
    [IsReduced X]
    (S : Set X) (hS' : Dense S)
    (H : ∀ x ∈ S, X.fromSpecResidueField x ≫ f = X.fromSpecResidueField x ≫ g)
    (H' : f ≫ i = g ≫ i) : f = g := by
  suffices IsDominant (equalizer.ι f g) from
    ext_of_isDominant_of_isSeparated i H' (equalizer.ι f g) (equalizer.condition _ _)
  refine ⟨.mono (fun x hx ↦ ⟨equalizer.lift _ (H _ hx) default, ?_⟩) hS'⟩
  rw [← Scheme.Hom.comp_apply, equalizer.lift_ι, Scheme.fromSpecResidueField_apply]

lemma ext_of_apply_eq {X Y : Scheme} (f g : X ⟶ Y) (i : Y ⟶ Spec (.of K)) [IsSeparated i]
    [LocallyOfFiniteType i]
    [IsReduced X] [LocallyOfFiniteType (f ≫ i)]
    (S : Set X) (hS : IsLocallyClosed S) (hS' : Dense S)
    (H : ∀ x ∈ S, IsClosed {x} → f x = g x)
    (H' : f ≫ i = g ≫ i) : f = g := by
  have : JacobsonSpace ↥X := LocallyOfFiniteType.jacobsonSpace (f ≫ i)
  refine ext_of_fromSpecResidueField_eq f g i (S ∩ closedPoints X) ?_ ?_ H'
  · rwa [dense_iff_closure_eq, JacobsonSpace.closure_inter_closedPoints_eq_closure _ hS,
      ← dense_iff_closure_eq]
  · rintro x ⟨hxS, hx⟩
    rw [← cancel_epi (Spec.map (residueFieldIsoBase (f ≫ i) x hx).hom)]
    refine ext_of_apply_closedPoint_eq _ _ i ?_ ?_ ?_
    · simp only [Category.assoc, ← SpecMap_residueFieldIsoBase_inv (f ≫ i) x hx, ← Spec.map_comp,
        Iso.inv_hom_id, Spec.map_id]
    · simp only [Category.assoc, ← SpecMap_residueFieldIsoBase_inv (f ≫ i) x hx, ← Spec.map_comp,
        Iso.inv_hom_id, Spec.map_id, ← H']
    · simpa using H x hxS hx

theorem isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed
    (G : Over (Spec (.of K))) [IsProper G.hom] [IsIntegral (G ⊗ G).left] [GrpObj G] :
    IsCommMonObj G := by
  let S := Spec (.of K)
  have : IsProper (G ⊗ G).hom := by dsimp; infer_instance
  have : JacobsonSpace (G ⊗ G).left :=
    LocallyOfFiniteType.jacobsonSpace (Y := Spec _) (G ⊗ G).hom
  let γ : G ⊗ G ⟶ G ⊗ G := lift (fst _ _) (GrpObj.commutator _)
  have : IsProper (fst G G).left := by dsimp; infer_instance
  have : IsProper (γ.left ≫ (fst G G).left) := by simpa [γ]
  have : IsProper γ.left := .of_comp _ (fst G G).left
  have : IsClosedImmersion (lift η[G] η[G]).left := by
    suffices IsClosedImmersion ((lift η[G] η[G]).left ≫ (fst G G).left)
      from .of_comp _ (g := (fst G G).left)
    suffices IsClosedImmersion η[G].left by simpa
    infer_instance
  have : JacobsonSpace ↥(pullback G.hom G.hom) :=
      LocallyOfFiniteType.jacobsonSpace (Y := S) (pullback.fst G.hom G.hom ≫ G.hom)
  rw [isCommMonObj_iff_commutator_eq_toUnit_η]
  ext1
  have : Surjective G.hom := by
    apply +allowSynthFailures Surjective.of_comp η[G].left
    simp only [Over.tensorUnit_left, Over.w, Over.tensorUnit_hom]
    infer_instance
  have : Surjective (fst G G).left := by dsimp; infer_instance
  have : IsProper ((GrpObj.commutator G).left ≫ G.hom) := by rw [Over.w]; infer_instance
  let point : S := IsLocalRing.closedPoint K
  have hpoint : IsClosed {point} := isClosed_discrete _
  have H : γ.left '' ((fst G G).left ⁻¹' {η[G].left point}) ⊆
      {(lift η[G] η[G]).left point} := by
    rw [Set.image_subset_iff, ← Set.diff_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro H
    obtain ⟨c₀, ⟨hc₁, hc₂⟩, hc₃⟩ := nonempty_inter_closedPoints H (by
      rw [Set.diff_eq_compl_inter, ← Set.image_singleton, ← Set.image_singleton];
      refine .inter (IsClosed.isOpen_compl (self := ?_)).isLocallyClosed
        (IsClosed.isLocallyClosed ?_)
      · exact ((lift η[G] η[G]).left.isClosedMap _ hpoint).preimage γ.left.continuous
      · exact (η[G].left.isClosedMap _ hpoint).preimage (fst G G).left.continuous)
    obtain ⟨⟨c, hc⟩, e⟩ := (pointEquivClosedPoint (G ⊗ G).hom).surjective ⟨c₀, hc₃⟩
    obtain rfl : c point = c₀ := congr(($e).1)
    let fc : 𝟙_ (Over S) ⟶ 𝟙_ (Over S) ⊗ G := lift (𝟙 _) (Over.homMk (c ≫ pullback.snd _ _)
      (by simpa [← pullback.condition]))
    have : c ≫ pullback.fst G.hom G.hom = η[G].left :=
      ext_of_apply_closedPoint_eq (h := G.hom) _ _ (by simpa) (by simp) (by simpa)
    have : c = fc.left ≫ (η[G] ▷ G).left := by dsimp; ext <;> simp [fc, S, this]
    have H : fc ≫ η ▷ G ≫ γ = lift η η := by ext1 <;> simp [fc, γ, S]
    apply hc₂
    simp [this, ← Scheme.Hom.comp_apply, Category.assoc, ← Over.comp_left, H]
  obtain ⟨U, hηU, H⟩ := exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage
    γ.left (fst G G).left (η[G].left point) (by
      dsimp [-Scheme.Hom.comp_base, γ]
      simp only [pullback.lift_fst]
      exact (Set.finite_singleton _).subset H)
  have := ((γ.left.imageι ≫ (fst G G).left) ∣_ U).finite_preimage_singleton ⟨_, hηU⟩
  have H (x : U) : ((pullback.fst G.hom G.hom) ⁻¹' {x.1} ∩ Set.range ⇑γ.left).Finite := by
    have : ((Scheme.Opens.ι _ ≫ γ.left.imageι) ''
        (((γ.left.imageι ≫ (fst G G).left) ∣_ U) ⁻¹' {x})).Finite :=
      (((γ.left.imageι ≫ (fst G G).left) ∣_ U).finite_preimage_singleton x).image _
    refine this.subset ?_
    have : U.ι ⁻¹' {x.1} = {x} := by ext; simp
    rw [← this, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
      morphismRestrict_ι, ← Category.assoc, Scheme.Hom.comp_base (_ ≫ _) (fst G G).left,
      TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq_inter_range]
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    dsimp
    rw [Set.image_preimage_eq_inter_range, Scheme.IdealSheafData.range_subschemeι,
      Scheme.Hom.support_ker, ← Set.inter_assoc, ← Set.preimage_inter,
      Set.singleton_inter_of_mem x.2, IsClosed.closure_eq
      (by exact γ.left.isClosedMap.isClosed_range)]
  refine ext_of_apply_eq _ _ G.hom _
    ((fst G G).left ⁻¹ᵁ U).isOpen.isLocallyClosed
    (((fst G G).left ⁻¹ᵁ U).isOpen.dense ?_) ?_ ?_
  · exact .preimage ⟨_, hηU⟩ (fst G G).left.surjective
  · rintro y hyU hy
    have hx : IsClosed {(fst G G).left y} := by simpa using (fst G G).left.isClosedMap _ hy
    let x : 𝟙_ _ ⟶ G := Over.homMk (pointOfClosedPoint G.hom _ hx) (by simp)
    have := subsingleton_image_closure_of_finite_of_isIrreducible
      ((pullback.fst G.hom G.hom) ⁻¹' {(fst G G).left y})
      (hx.preimage (pullback.fst G.hom _).continuous).isLocallyClosed (by
        let α : G ⊗ G ⟶ G ⊗ G := toUnit _ ≫ x ⊗ₘ 𝟙 _
        convert (IrreducibleSpace.isIrreducible_univ _).image α.left α.left.continuous.continuousOn
        rw [Over.tensorHom_left]
        simp [Set.range_comp, Scheme.Pullback.range_map, x]) γ.left
      γ.left.continuous
      γ.left.isClosedMap ((H ⟨_, hyU⟩).subset (Set.image_subset_iff.mpr fun _ ↦ by
        simp [← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base, γ]))
    let xe : (G ⊗ G).left := (fst G G ≫ (ρ_ _).inv ≫ G ◁ η[G]).left y
    have := this (x := γ.left y) ⟨_, subset_closure (by simp), rfl⟩
      (y := xe) ⟨xe, subset_closure (by
        simp [xe, ← Scheme.Hom.comp_apply, - Scheme.Hom.comp_base]), (by
        simp only [xe, γ, ← Scheme.Hom.comp_apply, ← Over.comp_left]
        congr 6; ext <;> simp)⟩
    convert congr((snd G G).left $this) using 1
    · simp [γ, ← Scheme.Hom.comp_apply]
    · simp [xe, ← Scheme.Hom.comp_apply, - Scheme.Hom.comp_base]
  · simp

end IsAlgClosed

instance (priority := low) {X Y : Scheme} (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] :
    LocallyOfFinitePresentation f := by
  refine ⟨fun {U hU V hV} hUV ↦ ?_⟩
  let := (f.appLE U V hUV).hom.toAlgebra
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  exact Algebra.FinitePresentation.of_finiteType.mp (f.finiteType_appLE hU hV hUV)

instance (priority := low) {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] :
    IsLocallyNoetherian (pullback f g) :=
  LocallyOfFiniteType.isLocallyNoetherian (pullback.snd _ _)

instance (priority := low) {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S)
    [IsLocallyNoetherian X] [LocallyOfFiniteType g] :
    IsLocallyNoetherian (pullback f g) :=
  LocallyOfFiniteType.isLocallyNoetherian (pullback.fst _ _)

instance (priority := low) {X Y : Scheme} [Nonempty X] [Subsingleton Y] (f : X ⟶ Y) :
    Surjective f := ⟨Function.surjective_to_subsingleton _⟩

instance {X Y : Scheme} (f : X ⟶ Y) [Surjective f] [Flat f] [QuasiCompact f] :
    (Over.pullback f).Faithful :=
  MorphismProperty.faithful_overPullback_of_isomorphisms_descendAlong
    (P := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

section
variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]
  {D : Type*} [Category* D] [CartesianMonoidalCategory D] (F : C ⥤ D)
  [F.Monoidal]

open scoped CategoryTheory.Obj

@[simp]
lemma Functor.map_inv' {X G : C} (f : X ⟶ G) [GrpObj G] : F.map (f⁻¹) = (F.map f)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← Functor.map_mul, inv_mul_cancel, Functor.map_one]

end

theorem isCommMonObj_of_isProper_of_geometricallyIntegral_of_isAlgClosed
    (G : Over (Spec (.of K))) [IsProper G.hom] [GeometricallyIntegral G.hom] [GrpObj G] :
    IsCommMonObj G := by
  let K' := AlgebraicClosure K
  let f := Spec.map (CommRingCat.ofHom <| algebraMap K K')
  let G' := (Over.pullback f).obj G
  have : IsProper G'.hom := by dsimp [G']; infer_instance
  have : IsIntegral (G' ⊗ G').left := by dsimp [G']; infer_instance
  let : GrpObj G' := CategoryTheory.Functor.grpObjObj
  have := isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed G'
  rw [isCommMonObj_iff_commutator_eq_toUnit_η] at this ⊢
  apply (Over.pullback f).map_injective
  rw [← cancel_epi (Functor.Monoidal.μIso (Over.pullback f) G G).hom]
  dsimp [GrpObj.commutator] at this ⊢
  simpa only [Functor.map_mul, one_eq_one, comp_one, Functor.map_one, Functor.map_inv',
    comp_mul, GrpObj.comp_inv, Functor.Monoidal.μ_fst, K', Functor.Monoidal.μ_snd] using this

end AlgebraicGeometry
