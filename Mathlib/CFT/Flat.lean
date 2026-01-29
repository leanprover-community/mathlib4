module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Algebra.Category.Ring.Under.Limits

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

variable {R S : CommRingCat.{u}} (φ : R ⟶ S) (hφ : φ.hom.Flat)

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y)

/-- Let `X` be a scheme over `R`, `S` an `R`, algebra, and `Y = X ×_R S`.
This is the canonical map `Γ(X, U) ⊗[R] S ⟶ Γ(Y, f ⁻¹ U)`. -/
noncomputable
def pushoutSectionToSection {R S : CommRingCat} (φ : R ⟶ S) {X Y : Scheme} (iX : X ⟶ Spec R)
    (iY : Y ⟶ Spec S) (f : Y ⟶ X) (H : IsPullback f iY iX (Spec.map φ))
    (U : X.Opens) :
      pushout ((Scheme.ΓSpecIso R).inv ≫ iX.appLE _ U le_top) φ ⟶ Γ(Y, f ⁻¹ᵁ U) :=
  pushout.desc (f.app U) ((Scheme.ΓSpecIso S).inv ≫ iY.appLE _ (f ⁻¹ᵁ U) le_top) <| by
    simp [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, - Scheme.Hom.comp_appLE, H.w]

@[reassoc (attr := simp)]
lemma inl_pushoutSectionToSection {R S : CommRingCat} (φ : R ⟶ S) {X Y : Scheme} (iX : X ⟶ Spec R)
    (iY : Y ⟶ Spec S) (f : Y ⟶ X) (H : IsPullback f iY iX (Spec.map φ))
    (U : X.Opens) :
      pushout.inl _ _ ≫ pushoutSectionToSection _ _ _ _ H U = f.app U :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma inr_pushoutSectionToSection {R S : CommRingCat} (φ : R ⟶ S) {X Y : Scheme} (iX : X ⟶ Spec R)
    (iY : Y ⟶ Spec S) (f : Y ⟶ X) (H : IsPullback f iY iX (Spec.map φ))
    (U : X.Opens) :
      pushout.inr _ _ ≫ pushoutSectionToSection _ _ _ _ H U =
        (Scheme.ΓSpecIso S).inv ≫ iY.appLE _ (f ⁻¹ᵁ U) le_top :=
  pushout.inr_desc _ _ _

-- -- #check Presheaf.isSheaf_iff_multifork
open TensorProduct
lemma isIso_pushoutSectionToSection_of_isAffineOpen
    {R S : CommRingCat} (φ : R ⟶ S) {X Y : Scheme} (iX : X ⟶ Spec R)
    (iY : Y ⟶ Spec S) (f : Y ⟶ X) (H : IsPullback f iY iX (Spec.map φ))
    (U : X.Opens) (hU : IsAffineOpen U) :
    IsIso (pushoutSectionToSection _ _ _ _ H U) := by
  refine (IsPushout.isoPushout ?_).isIso_inv
  suffices IsPullback (f.app U).op ((Scheme.ΓSpecIso S).inv ≫ iY.appLE ⊤ (f ⁻¹ᵁ U) le_top).op
    ((Scheme.ΓSpecIso R).inv ≫ iX.appLE ⊤ U le_top).op φ.op from this.flip.unop
  apply IsPullback.of_map Scheme.Spec (by simp [← op_comp, Scheme.Hom.app_eq_appLE,
    Scheme.Hom.appLE_comp_appLE, - Scheme.Hom.comp_appLE, H.w])
  have : IsAffineHom f := MorphismProperty.of_isPullback H.flip inferInstance
  have : IsPullback (Spec.map (f.app U)) (hU.preimage f).isoSpec.inv hU.isoSpec.inv (f ∣_ U) :=
    .of_vert_isIso ⟨by simp [← cancel_mono U.ι, Scheme.Hom.app_eq_appLE, hU.preimage f,
      IsAffineOpen.SpecMap_appLE_fromSpec]⟩
  convert this.paste_vert ((isPullback_morphismRestrict f U).paste_vert H)
  · have : iY.appLE ⊤ (f ⁻¹ᵁ U) le_top = iY.appTop ≫ Y.presheaf.map (homOfLE le_top).op := rfl
    simpa [← IsIso.eq_comp_inv, ← Spec.map_inv, Scheme.toSpecΓ_naturality] using
      congr(Spec.map $this)
  · have : iX.appLE ⊤ U le_top = iX.appTop ≫ X.presheaf.map (homOfLE le_top).op := rfl
    simpa [← IsIso.eq_comp_inv, ← Spec.map_inv, Scheme.toSpecΓ_naturality] using
      congr(Spec.map $this)

open TensorProduct

lemma pushoutSectionToSection_injective_of_isCompact
    {R S : CommRingCat} (φ : R ⟶ S) (hφ : φ.hom.Flat) {X Y : Scheme} (iX : X ⟶ Spec R)
    (iY : Y ⟶ Spec S) (f : Y ⟶ X) (H : IsPullback f iY iX (Spec.map φ))
    (U : X.Opens) (hU : IsCompact (X := X) U) :
    Function.Injective (pushoutSectionToSection _ _ _ _ H U) := by
  classical
  obtain ⟨I, hI, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hU
  have hIE (i : I) : i.1 ≤ U := by rw [e]; intro i; aesop
  let (U : X.Opens) : Algebra R Γ(X, U) :=
    ((Scheme.ΓSpecIso R).inv ≫ iX.appLE _ U le_top).hom.toAlgebra
  algebraize [φ.hom]
  let ψ : Γ(X, U) →ₐ[R] Π i : I, Γ(X, i) := Pi.algHom _ _ fun i ↦
    ⟨(X.presheaf.map (homOfLE (by rw [e]; intro i; aesop)).op).hom, fun r ↦ by
      dsimp [RingHom.algebraMap_toAlgebra]
      simp only [← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.appLE_map]⟩
  have hψ : Function.Injective ψ := by
    intro s t est
    apply X.IsSheaf.section_ext fun x hx ↦ ?_
    simp only [e, Opens.mem_iSup] at hx
    obtain ⟨i, hiI, hxi⟩ := hx
    exact ⟨_, _, hxi, congr($est ⟨i, hiI⟩)⟩
  have hψ' : Function.Injective (Algebra.TensorProduct.map (AlgHom.id R S) ψ) :=
    Module.Flat.lTensor_preserves_injective_linearMap ψ.toLinearMap hψ
  let e₁ : pushout ((Scheme.ΓSpecIso R).inv ≫ Scheme.Hom.appLE iX ⊤ U le_top) φ ≅
      .of (S ⊗[R] Γ(X, U)) :=
    (CommRingCat.isPushout_tensorProduct R S Γ(X, U)).flip.isoPushout.symm
  let := hI.fintype
  let e₂ : (S ⊗[R] Π i : I, Γ(X, i)) ≃+* Π i : I, Γ(Y, f ⁻¹ᵁ i) :=
    (Algebra.TensorProduct.piRight _ R _ _).toRingEquiv.trans (RingEquiv.piCongrRight fun i ↦
      letI := isIso_pushoutSectionToSection_of_isAffineOpen _ _ _ _ H i i.1.2
      (CommRingCat.isPushout_tensorProduct R S _).flip.isoPushout.commRingCatIsoToRingEquiv.trans
      (asIso (pushoutSectionToSection φ iX iY f H i)).commRingCatIsoToRingEquiv)
  let ψY : Γ(Y, f ⁻¹ᵁ U) →+* Π i : I, Γ(Y, f ⁻¹ᵁ i) := Pi.ringHom fun i ↦
      (Y.presheaf.map (homOfLE (by rw [e]; intro i; aesop)).op).hom
  refine .of_comp (f := ψY) ?_
  suffices pushoutSectionToSection φ iX iY f H U ≫ CommRingCat.ofHom ψY = e₁.hom ≫
      CommRingCat.ofHom (Algebra.TensorProduct.map (.id R S) ψ).toRingHom ≫
      CommRingCat.ofHom e₂.toRingHom by
    convert (e₂.injective.comp hψ').comp e₁.commRingCatIsoToRingEquiv.injective
    exact congr($this)
  ext1
  · suffices Scheme.Hom.app f U ≫ CommRingCat.ofHom ψY = CommRingCat.ofHom
        (e₂.toRingHom.comp (Algebra.TensorProduct.includeRight.comp ψ).toRingHom) by
      simpa [e₁, ← CommRingCat.ofHom_comp, RingHom.comp_assoc, ← AlgHom.comp_toRingHom]
    ext x i
    trans (X.presheaf.map (homOfLE (hIE _)).op ≫
        CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫
        (CommRingCat.isPushout_tensorProduct ↑R ↑S ↑Γ(X, i.1)).flip.isoPushout.hom ≫
        pushoutSectionToSection φ iX iY f H i.1) x
    · change (Scheme.Hom.app f U ≫
        Y.presheaf.map (homOfLE (f.preimage_mono (hIE _))).op) x = _
      congr 2
      simp [RingHom.algebraMap_toAlgebra]
    · simp [e₂, Iso.commRingCatIsoToRingEquiv, -IsPushout.inl_isoPushout_hom_assoc]; rfl
  · suffices (Scheme.ΓSpecIso S).inv ≫ iY.appLE ⊤ (f ⁻¹ᵁ U) le_top ≫ CommRingCat.ofHom ψY =
        CommRingCat.ofHom (e₂.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom) by
      simpa [e₁, ← CommRingCat.ofHom_comp, RingHom.comp_assoc,
        ← AlgHom.comp_toRingHom, show Algebra.TensorProduct.includeLeftRingHom =
          (Algebra.TensorProduct.includeLeft (S := R)).toRingHom from rfl]
    ext x i
    trans (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫
        (CommRingCat.isPushout_tensorProduct ↑R ↑S ↑Γ(X, i.1)).flip.isoPushout.hom ≫
        pushoutSectionToSection φ iX iY f H i.1) x
    · change ((Scheme.ΓSpecIso S).inv ≫ iY.appLE ⊤ (f ⁻¹ᵁ U) le_top ≫
        Y.presheaf.map (homOfLE (f.preimage_mono (hIE _))).op) x = _
      congr 2
      simpa [-inr_pushoutSectionToSection] using (inr_pushoutSectionToSection ..).symm
    · simp [e₂, -IsPushout.inr_isoPushout_hom_assoc]; rfl

lemma isIso_pushoutSectionToSection_of_isQuasiSeparated
    {R S : CommRingCat} (φ : R ⟶ S) (hφ : φ.hom.Flat) {X Y : Scheme} (iX : X ⟶ Spec R)
    (iY : Y ⟶ Spec S) (f : Y ⟶ X) (H : IsPullback f iY iX (Spec.map φ))
    (U : X.Opens) (hU : IsCompact (X := X) U) (hU' : IsQuasiSeparated (α := X) U) :
    IsIso (pushoutSectionToSection _ _ _ _ H U) := by
  classical
  obtain ⟨s, hs, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hU
  have hsU (i : s) : i.1 ≤ U := by rw [e]; intro i; aesop
  let D := Pairwise.diagram fun i : s ↦ i.1.1
  let iXU : R ⟶ Γ(X, U) :=
    (Scheme.ΓSpecIso R).inv ≫ iX.appTop ≫ X.presheaf.map (homOfLE le_top).op
  have h : iSup D.obj = U := by
    refine le_antisymm (iSup_le_iff.mpr ?_)
      (e.trans_le (iSup₂_le_iff.mpr fun i hi ↦ le_iSup D.obj (.single ⟨i, hi⟩)))
    rintro (i | ⟨i, j⟩)
    exacts [hsU _, inf_le_left.trans (hsU i)]
  let c₀ : Cocone (Pairwise.diagram fun i : s ↦ (i : X.Opens)) := (colimit.cocone _).extend
    (eqToIso (Y := U) (by simpa [CompleteLattice.colimit_eq_iSup])).hom
  let F := Under.lift _ ((Functor.const _).map iXU ≫ ((X.presheaf.mapCone c₀.op).π)) ⋙
      Under.pushout φ ⋙ Under.forget S
  let αF : F ⟶ D.op ⋙ (Opens.map f.base).op ⋙ Y.presheaf :=
  { app _ := (pushout.congrHom (by simp [iXU, Scheme.Hom.app_eq_appLE]) rfl).hom ≫
      pushoutSectionToSection _ _ _ _ H _  }
  let c : Cone F := (Under.pushout φ ⋙ Under.forget S).mapCone
    (Under.liftCone (X.presheaf.mapCone c₀.op) iXU)
  have := CommRingCat.Under.preservesFiniteLimits_of_flat _ hφ
  let : Fintype s := hs.fintype
  let hc : IsLimit c :=
    haveI HX := ((TopCat.Presheaf.isSheaf_iff_isSheafPreservesLimitPairwiseIntersections
      _).mp X.IsSheaf (fun i : s ↦ i)).preserves (c := c₀.op)
    haveI HX := (HX (IsColimit.extendIso _ (colimit.isColimit _)).op).some
    isLimitOfPreserves (Under.pushout φ ⋙ Under.forget _) (Under.isLimitLiftCone _ iXU HX)
  let c'₀ : Cocone (D ⋙ Opens.map f.base) := (colimit.cocone _).extend
    (eqToIso (Y := f ⁻¹ᵁ U) (by
      simp only [colimit.cocone_x, CompleteLattice.colimit_eq_iSup, ← h, Scheme.Hom.preimage_iSup]
      rfl)).hom
  let c' : Cone (D.op ⋙ (Opens.map f.base).op ⋙ Y.presheaf) := Y.presheaf.mapCone c'₀.op
  let hc' : IsLimit c' :=
    letI e : D ⋙ Opens.map f.base ≅ Pairwise.diagram fun i : s ↦ f ⁻¹ᵁ i :=
      NatIso.ofComponents (fun | .single i => .refl _ | .pair i j => .refl _)
    haveI HX := ((TopCat.Presheaf.isSheaf_iff_isSheafPreservesLimitPairwiseIntersections _).mp
      Y.IsSheaf (fun i : s ↦ f ⁻¹ᵁ i)).preserves (c := ((Cocones.precompose e.inv).obj c'₀).op)
    (IsLimit.postcomposeHomEquiv (Functor.isoWhiskerRight (NatIso.op e.symm) Y.presheaf) _)
      ((HX ((IsColimit.precomposeInvEquiv e _).symm
        (IsColimit.extendIso _ (colimit.isColimit _))).op).some.ofIsoLimit (Cones.ext (.refl _)))
  have HαF₁ (i : _) : IsIso (αF.app (.op <| .single i)) := by
    dsimp [αF]
    have := isIso_pushoutSectionToSection_of_isAffineOpen _ _ _ _ H i i.1.2
    infer_instance
  have HαF₂ (i j : _) : Mono (αF.app (.op <| .pair i j)) := by
    dsimp [αF]
    have := pushoutSectionToSection_injective_of_isCompact _ hφ _ _ _ H (i ⊓ j)
      (hU' _ _ (hsU _) i.1.1.2 i.1.2.isCompact (hsU _) j.1.1.2 j.1.2.isCompact)
    rw [← ConcreteCategory.mono_iff_injective_of_preservesPullback] at this
    infer_instance
  let f₁ : c.pt ⟶ c'.pt := hc'.lift ((Cones.postcompose αF).obj c)
  let f₂ : c'.pt ⟶ c.pt := hc.lift ⟨c'.pt, ⟨fun
    | .op (.single i) => c'.π.app _ ≫ inv (αF.app (.op <| .single i))
    | .op (.pair i j) => c'.π.app (.op (.single i)) ≫ inv (αF.app (.op <| .single i)) ≫
        F.map (Quiver.Hom.op <| Pairwise.Hom.left i j), by
    rintro ⟨i⟩ ⟨j⟩ f
    obtain ⟨i | ⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j⟩, rfl⟩ :=
      (show Function.Surjective Quiver.Hom.op from Quiver.Hom.opEquiv.surjective) f
    · simp [show Pairwise.Hom.id_single i = 𝟙 (Pairwise.single i) from rfl]
    · simp [show Pairwise.Hom.id_pair i j = 𝟙 (Pairwise.pair i j) from rfl]
    · simp
    · rw [← cancel_mono (αF.app _)]
      simpa using (c'.w (Quiver.Hom.op <| Pairwise.Hom.left i j)).trans
        (c'.w (Quiver.Hom.op <| Pairwise.Hom.right i j)).symm⟩⟩
  let e : c.pt ≅ c'.pt := by
    refine ⟨f₁, f₂, hc.hom_ext ?_, hc'.hom_ext ?_⟩
    · rintro ⟨i | ⟨i, j⟩⟩ <;> simp [f₁, f₂]
    · rintro ⟨i | ⟨i, j⟩⟩
      · simp [f₁, f₂]
      · simpa [f₁, f₂] using c'.w (Quiver.Hom.op <| Pairwise.Hom.left i j)
  convert e.isIso_hom using 1
  · refine hc'.hom_ext fun i ↦ ?_
    rw [hc'.fac]
    ext1
    · simp [αF, c, @pushout.inl_desc_assoc, Under.liftCone]; rfl
    · simp [αF, c, @pushout.inr_desc_assoc, c']; rfl

attribute [gcongr] Scheme.Hom.preimage_mono

/-- Given `Y = X ×ₛ T` with `Uₜ` an affine open subset of `T` and `Uₓ` a qcqs subset of `X`.
Suppose that `T` is flat over `S`, and `Uₜ` and `Uₓ` are contained in a common affine open `Uₛ ⊆ S`,
then `Γ(Y, prₜ ⁻¹ Uₜ ∩ prₓ ⁻¹ Uₓ) = Γ(T, Uₜ) ⊗[Γ(S, Uₛ)] Γ(X, Uₓ)`. -/
lemma isIso_pushoutDesc_appLE_appLE_of_isCompact_of_isQuasiSeparated_of_flat
    {X Y S T : Scheme} {f : T ⟶ S} {g : Y ⟶ X} {iX : X ⟶ S} {iY : Y ⟶ T}
    (H : IsPullback g iY iX f) [Flat f]
    {US : S.Opens} (hUS : IsAffineOpen US) {UT : T.Opens} (hUT : IsAffineOpen UT)
    {UX : X.Opens} (hUST : UT ≤ f ⁻¹ᵁ US) (hUSX : UX ≤ iX ⁻¹ᵁ US)
    {UY : Y.Opens} (hUY : g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT = UY)
    (hUX : IsCompact (X := X) UX) (hUX' : IsQuasiSeparated (α := X) UX) :
    IsIso (pushout.desc (g.appLE UX UY (by simp [← hUY])) (iY.appLE UT UY (by simp [← hUY]))
      (by simp only [Scheme.Hom.appLE_comp_appLE, H.w]) :
      pushout (iX.appLE US UX hUSX) (f.appLE US UT hUST) ⟶ Γ(Y, UY)) := by
  have h₁ : IsPullback (g ∣_ UX) (iY.resLE (f ⁻¹ᵁ US) (g ⁻¹ᵁ UX)
      (by rw [← Scheme.Hom.comp_preimage, ← H.w]; exact g.preimage_mono hUSX))
      (iX.resLE _ _ hUSX) (f ∣_ US) := by
    refine .of_bot ?_ ?_ (isPullback_morphismRestrict f US)
    · simpa using (isPullback_morphismRestrict g UX).paste_vert H
    · simp [← cancel_mono US.ι, H.w]
  have h₂ : IsPullback (Scheme.homOfLE _ (by simp [← hUY])) (iY.resLE UT UY (by simp [← hUY]))
      ((iY.resLE (f ⁻¹ᵁ US) (g ⁻¹ᵁ UX)
      (by rw [← Scheme.Hom.comp_preimage, ← H.w]; exact g.preimage_mono hUSX)))
      (Scheme.homOfLE _ hUST) := by
    refine (IsOpenImmersion.isPullback _ _ _ _ (by simp) ?_).flip
    simp only [Scheme.opensRange_homOfLE,
      ← Scheme.Hom.comp_preimage, Scheme.Hom.resLE_comp_ι]
    rw [Scheme.Hom.comp_preimage, ← (g ⁻¹ᵁ UX).ι.image_injective.eq_iff]
    simp only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    simp [← hUY]
  have h₃ : IsPullback (f.resLE US UT hUST) hUT.isoSpec.hom hUS.isoSpec.hom
    (Spec.map (f.appLE _ _ hUST)) := .of_vert_isIso ⟨by simp [IsAffineOpen.isoSpec_hom]⟩
  have H := (h₂.paste_horiz h₁).paste_vert h₃
  simp only [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.map_resLE] at H
  have inst : CompactSpace UX := isCompact_iff_compactSpace.mp hUX
  have inst : QuasiSeparatedSpace UX := (isQuasiSeparated_iff_quasiSeparatedSpace _ UX.2).mp hUX'
  have := isIso_pushoutSectionToSection_of_isQuasiSeparated _
    (f.flat_appLE hUS hUT hUST) _ _ _ H ⊤ isCompact_univ
    isQuasiSeparated_univ
  have : IsIso (pushout.map (iX.appLE US UX hUSX) (f.appLE US UT hUST) _ _
    (X.presheaf.map (eqToHom (show UX.ι ''ᵁ ⊤ = UX by simp)).op) (𝟙 _) (𝟙 _)
      (by simp [IsAffineOpen.isoSpec_hom_appTop, Scheme.Hom.resLE_appLE]) (by simp) ≫
      pushoutSectionToSection (f.appLE US UT hUST)
      (iX.resLE US UX hUSX ≫ hUS.isoSpec.hom)
      (iY.resLE UT UY (by simp [← hUY]) ≫ hUT.isoSpec.hom)
      (g.resLE UX UY (by simp [← hUY])) H ⊤ ≫
      Y.presheaf.map (eqToHom (show UY = UY.ι ''ᵁ ⊤ by simp)).op) :=
    inferInstance
  convert this
  ext1
  · simp [Scheme.Hom.app_eq_appLE, Scheme.Hom.resLE_appLE]
  · simp [IsAffineOpen.isoSpec_hom_appTop, Scheme.Hom.resLE_appLE]

end AlgebraicGeometry
