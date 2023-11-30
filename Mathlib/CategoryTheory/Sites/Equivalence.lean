import Mathlib.CategoryTheory.Sites.InducedTopology

universe v u v' u' w

open CategoryTheory LocallyCoverDense Functor Limits GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (F : C ⥤ C) (i : F ≅ 𝟭 C)

theorem coverDense_of_iso_id : F.IsCoverDense J where
  is_cover U := by
    convert J.top_mem U
    ext Y f
    simp only [Sieve.coverByImage, Presieve.coverByImage, Sieve.top_apply, iff_true]
    refine ⟨⟨U, f ≫ i.inv.app U, i.hom.app U, (by simp)⟩⟩

theorem inducedTopology_of_iso_id_eq_self : haveI := Full.ofIso i.symm
    haveI := Faithful.of_iso i.symm
    haveI : IsCoverDense F J := coverDense_of_iso_id J F i
    (locallyCoverDense_of_isCoverDense F J).inducedTopology = J := by
  ext Y S
  simp only [inducedTopology]
  refine ⟨fun (h : S.functorPushforward F ∈ J.sieves (F.obj Y)) ↦ ?_, fun h ↦ ?_⟩
  · convert J.pullback_stable (i.inv.app Y) h
    simp only [Functor.id_obj]
    ext Z f
    simp only [Sieve.pullback_apply, Sieve.functorPushforward_apply, Presieve.functorPushforward,
      exists_and_left]
    refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
    · refine ⟨F.obj Z, i.hom.app Z ≫ f, S.downward_closed hf (i.hom.app Z),
        i.inv.app Z ≫ F.map (i.inv.app Z), ?_⟩
      simp only [Category.assoc, ← Functor.map_comp]
      simpa using i.inv.naturality f
    · obtain ⟨W, g, hg, x, hx⟩ := hf
      have : f = (f ≫ i.inv.app Y) ≫ i.hom.app Y := by simp
      rw [this, hx, Category.assoc]
      apply S.downward_closed
      rw [i.hom.naturality g]
      apply S.downward_closed
      exact hg
  · change S.functorPushforward F ∈ J.sieves (F.obj Y)
    convert J.pullback_stable (i.hom.app Y) h
    ext T Z f
    simp only [Sieve.functorPushforward_apply, Presieve.functorPushforward, exists_and_left,
      Functor.id_obj, Sieve.pullback_apply]
    refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
    · obtain ⟨W, g, hg, x, hx⟩ := hf
      rw [hx, Category.assoc, i.hom.naturality g, ← Category.assoc]
      exact T.downward_closed hg (x ≫ i.hom.app W)
    · refine ⟨Z, f ≫ i.hom.app Y, hf, ?_⟩
      refine ⟨i.inv.app Z, ?_⟩
      simp only [Functor.map_comp, ← Category.assoc]
      rw [← i.inv.naturality f]
      have : F.map (i.hom.app Y) = i.hom.app (F.obj Y) := by
        have := i.hom.naturality (i.hom.app Y)
        apply_fun fun g ↦ g ≫ i.inv.app Y at this
        simp only [Functor.id_obj, Functor.id_map, Category.assoc,
          Iso.hom_inv_id_app, Category.comp_id] at this
        exact this
      simp [this]

variable {D : Type u'} [Category.{v'} D] (e : C ≌ D)

theorem locallyCoverDense_equiv : LocallyCoverDense J e.inverse := by
  intro X T
  convert T.prop
  ext Z f
  constructor
  · rintro ⟨_, _, g', hg, rfl⟩
    exact T.val.downward_closed hg g'
  · intro hf
    refine ⟨e.functor.obj Z, (Adjunction.homEquiv e.toAdjunction _ _).symm f, e.unit.app Z, ?_, ?_⟩
    · simp only [Adjunction.homEquiv_counit, Functor.id_obj, Equivalence.toAdjunction_counit,
        Sieve.functorPullback_apply, Presieve.functorPullback_mem, Functor.map_comp,
        Equivalence.inv_fun_map, Functor.comp_obj, Category.assoc, Equivalence.unit_inverse_comp,
        Category.comp_id]
      exact T.val.downward_closed hf _
    · simp

theorem coverPreserving_equiv :
    CoverPreserving J (locallyCoverDense_equiv J e).inducedTopology e.functor where
  cover_preserve {U S} h := by
    simp only [inducedTopology]
    rw [← inducedTopology_of_iso_id_eq_self J (i := e.unitIso.symm)] at h
    simp only [inducedTopology, comp_obj] at h
    have hS : S.functorPushforward (e.functor ⋙ e.inverse) ∈
      J.sieves (e.inverse.obj (e.functor.obj U)) := h
    rw [Sieve.functorPushforward_comp] at hS
    change _ ∈ J.sieves (e.inverse.obj (e.functor.obj U))
    exact hS

instance : IsCoverDense e.functor (locallyCoverDense_equiv J e).inducedTopology where
  is_cover U := by
    change _ ∈ J.sieves _
    convert J.top_mem (e.inverse.obj U)
    ext Y f
    simp only [Sieve.functorPushforward_apply, Presieve.functorPushforward, exists_and_left,
      Sieve.top_apply, iff_true]
    exact ⟨e.functor.obj Y, (Adjunction.homEquiv e.toAdjunction _ _).symm f,
      Presieve.in_coverByImage _ _, e.unit.app _, (by simp)⟩

instance : IsContinuous e.functor J (locallyCoverDense_equiv J e).inducedTopology :=
  IsCoverDense.isContinuous _ _ _ (coverPreserving_equiv J e)

instance : IsCoverDense e.inverse J where
  is_cover U := by
    convert J.top_mem U
    ext Y f
    simp only [Sieve.functorPushforward_apply, Presieve.functorPushforward, exists_and_left,
      Sieve.top_apply, iff_true]
    let g : e.inverse.obj _ ⟶ U := (e.unitInv.app Y) ≫ f
    have : (Sieve.coverByImage e.inverse U).arrows g := Presieve.in_coverByImage _ g
    replace := Sieve.downward_closed _ this (e.unit.app Y)
    simpa using this

instance : IsContinuous e.inverse (locallyCoverDense_equiv J e).inducedTopology J :=
  IsCoverDense.isContinuous _ _ _ (inducedTopology_coverPreserving (locallyCoverDense_equiv J e))

variable {A : Type w} [Category.{max u' v'} A]

namespace CategoryTheory.Equivalence

@[simps!]
def sheafCongr_functor : Sheaf J A ⥤ Sheaf (locallyCoverDense_equiv J e).inducedTopology A where
  obj F := ⟨e.inverse.op ⋙ F.val, e.inverse.op_comp_isSheaf _ _ _⟩
  map f := ⟨whiskerLeft e.inverse.op f.val⟩

@[simps!]
def sheafCongr_inverse : Sheaf (locallyCoverDense_equiv J e).inducedTopology A ⥤ Sheaf J A where
  obj F := ⟨e.functor.op ⋙ F.val, e.functor.op_comp_isSheaf _ _ _⟩
  map f := ⟨whiskerLeft e.functor.op f.val⟩

@[simps!]
def sheafCongr_unitIso : 𝟭 (Sheaf J A) ≅ e.sheafCongr_functor J ⋙ e.sheafCongr_inverse J :=
  NatIso.ofComponents (fun F ↦ ⟨⟨(isoWhiskerRight e.op.unitIso F.val).hom⟩,
    ⟨(isoWhiskerRight e.op.unitIso F.val).inv⟩,
    Sheaf.hom_ext _ _ (isoWhiskerRight e.op.unitIso F.val).hom_inv_id,
    Sheaf.hom_ext _ _ (isoWhiskerRight e.op.unitIso F.val).inv_hom_id⟩ ) (by aesop)

@[simps!]
def sheafCongr_counitIso : e.sheafCongr_inverse J ⋙ e.sheafCongr_functor J ≅ 𝟭 (Sheaf _ A) :=
  NatIso.ofComponents (fun F ↦ ⟨⟨(isoWhiskerRight e.op.counitIso F.val).hom⟩,
    ⟨(isoWhiskerRight e.op.counitIso F.val).inv⟩,
    Sheaf.hom_ext _ _ (isoWhiskerRight e.op.counitIso F.val).hom_inv_id,
    Sheaf.hom_ext _ _ (isoWhiskerRight e.op.counitIso F.val).inv_hom_id⟩ ) (by aesop)

def sheafCongr : Sheaf J A ≌ Sheaf (locallyCoverDense_equiv J e).inducedTopology A where
  functor := e.sheafCongr_functor J
  inverse := e.sheafCongr_inverse J
  unitIso := e.sheafCongr_unitIso J
  counitIso := e.sheafCongr_counitIso J
  functor_unitIso_comp X := by
    ext
    simp only [id_obj, sheafCongr_functor_obj_val_obj, comp_obj, Sheaf.instCategorySheaf_comp_val,
      NatTrans.comp_app, sheafCongr_inverse_obj_val_obj, Opposite.unop_op,
      sheafCongr_functor_map_val_app, sheafCongr_unitIso_hom_app_val_app,
      sheafCongr_counitIso_hom_app_val_app, sheafCongr_functor_obj_val_map, Quiver.Hom.unop_op,
      Sheaf.instCategorySheaf_id_val, NatTrans.id_app]
    simp [← Functor.map_comp, ← op_comp]

end CategoryTheory.Equivalence

/-- This would allow to weaken the assumption `HasLimits A`. -/
proof_wanted hasMultiEqualizer_index_of_equiv
    [∀ (P : Cᵒᵖ ⥤ A) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
    (P : Dᵒᵖ ⥤ A) (X : D) (S : (locallyCoverDense_equiv J e).inducedTopology.Cover X) :
    HasMultiequalizer (S.index P)

/-- This would allow to weaken the assumption `HasColimits A`. -/
proof_wanted hasColimitsOfShape_cover_of_equiv
    [∀ (X : C), HasColimitsOfShape (J.Cover X)ᵒᵖ A] (X : D) :
    HasColimitsOfShape ((locallyCoverDense_equiv J e).inducedTopology.Cover X)ᵒᵖ A

variable [HasLimits A] [HasColimits A]

namespace CategoryTheory.GrothendieckTopology

noncomputable
def smallSheafify (F : Cᵒᵖ ⥤ A) : Cᵒᵖ ⥤ A :=
  e.functor.op ⋙ (locallyCoverDense_equiv J e).inducedTopology.sheafify (e.inverse.op ⋙ F)

variable [ConcreteCategory A] [PreservesLimits (forget A)] [ReflectsIsomorphisms (forget A)]
  [PreservesFilteredColimits (forget A)]

/-- This would allow to weaken the assumption `PreservesFilteredColimits (forget A)`. -/
proof_wanted preservesColimitsOfShape_cover
    [∀ (X : C), PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget A)] (X : D) :
    Nonempty (PreservesColimitsOfShape
      ((locallyCoverDense_equiv J e).inducedTopology.Cover X)ᵒᵖ (forget A))

theorem smallSheafify_isSheaf (F : Cᵒᵖ ⥤ A) : Presheaf.IsSheaf J (J.smallSheafify e F) := by
  let G : Sheaf (locallyCoverDense_equiv J e).inducedTopology A :=
    ⟨(locallyCoverDense_equiv J e).inducedTopology.sheafify (e.inverse.op ⋙ F),
      (locallyCoverDense_equiv J e).inducedTopology.sheafify_isSheaf _⟩
  change Presheaf.IsSheaf J (e.functor.op ⋙ G.val)
  exact e.functor.op_comp_isSheaf _ _ _

noncomputable
def toSmallSheafify (F : Cᵒᵖ ⥤ A) : F ⟶ J.smallSheafify e F :=
  whiskerRight e.op.unit F ≫ (Functor.associator _ _ _).hom ≫
    whiskerLeft e.functor.op (toSheafify _ _)

noncomputable
def smallSheafifyLift {F G : Cᵒᵖ ⥤ A} (η : F ⟶ G) (hG : Presheaf.IsSheaf J G) :
    J.smallSheafify e F ⟶ G := by
  have hG' : Presheaf.IsSheaf (locallyCoverDense_equiv J e).inducedTopology (e.inverse.op ⋙ G) := by
    let G' : Sheaf _ _ := ⟨G, hG⟩
    change Presheaf.IsSheaf _ (_ ⋙ G'.val)
    exact e.inverse.op_comp_isSheaf (locallyCoverDense_equiv J e).inducedTopology J _
  refine whiskerLeft e.functor.op (sheafifyLift _ (whiskerLeft e.inverse.op η) hG') ≫ whiskerRight e.op.unitInv G

end CategoryTheory.GrothendieckTopology

variable [ConcreteCategory A] [PreservesLimits (forget A)] [ReflectsIsomorphisms (forget A)]
  [PreservesFilteredColimits (forget A)]

noncomputable
def smallPresheafToSheaf : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A :=
  e.op.congrLeft.functor ⋙ presheafToSheaf _ _ ⋙ (e.sheafCongr J).inverse

noncomputable
def smallSheafificationAdjunction_aux :=
  (e.op.congrLeft.toAdjunction.comp (sheafificationAdjunction _ _)).comp
    (e.sheafCongr (A := A) J).symm.toAdjunction

noncomputable
def sheafToPresheafIso : (e.sheafCongr J).functor ⋙ sheafToPresheaf (locallyCoverDense_equiv J e).inducedTopology A ⋙
    e.op.congrLeft.inverse ≅ sheafToPresheaf J A := by
  refine NatIso.ofComponents (fun F ↦ isoWhiskerRight e.op.unitIso.symm F.val) ?_
  intros; ext; simp [Equivalence.sheafCongr]

noncomputable
def smallSheafificationAdjunction : smallPresheafToSheaf J e ⊣ sheafToPresheaf J A :=
  (smallSheafificationAdjunction_aux J e (A := A)).ofNatIsoRight (sheafToPresheafIso _ _)
