import Mathlib.CategoryTheory.Sites.InducedTopology

universe u

open CategoryTheory LocallyCoverDense Functor Limits GrothendieckTopology

variable {C : Type (u+1)} [LargeCategory C] (J : GrothendieckTopology C) (F : C ⥤ C) (i : F ≅ 𝟭 C)

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

variable {D : Type u} [SmallCategory D] (e : C ≌ D)

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

variable {A : Type (u + 1)} [LargeCategory A] [HasLimits A] [HasColimits A]

/-- This would allow to weaken the assumption `HasLimits A`. -/
proof_wanted hasMultiEqualizer_index_of_equiv
    [∀ (P : Cᵒᵖ ⥤ A) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
    (P : Dᵒᵖ ⥤ A) (X : D) (S : (locallyCoverDense_equiv J e).inducedTopology.Cover X) :
    HasMultiequalizer (S.index P)

/-- This would allow to weaken the assumption `HasColimits A`. -/
proof_wanted hasColimitsOfShape_cover_of_equiv
    [∀ (X : C), HasColimitsOfShape (J.Cover X)ᵒᵖ A] (X : D) :
    HasColimitsOfShape ((locallyCoverDense_equiv J e).inducedTopology.Cover X)ᵒᵖ A

noncomputable
def CategoryTheory.GrothendieckTopology.smallSheafify (F : Cᵒᵖ ⥤ A) : Cᵒᵖ ⥤ A :=
  e.functor.op ⋙ (locallyCoverDense_equiv J e).inducedTopology.sheafify (e.inverse.op ⋙ F)

variable [ConcreteCategory A] [PreservesLimits (forget A)] [ReflectsIsomorphisms (forget A)]
  [PreservesFilteredColimits (forget A)]

/-- This would allow to weaken the assumption `PreservesFilteredColimits (forget A)`. -/
proof_wanted preservesColimitsOfShape_cover
    [∀ (X : C), PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget A)] (X : D) :
    Nonempty (PreservesColimitsOfShape
      ((locallyCoverDense_equiv J e).inducedTopology.Cover X)ᵒᵖ (forget A))

theorem smallSheafify_isSheaf (F : Cᵒᵖ ⥤ A) : Presheaf.IsSheaf J (J.smallSheafify e F) := by
  have : IsContinuous e.functor J (locallyCoverDense_equiv J e).inducedTopology :=
    IsCoverDense.isContinuous _ _ _ (coverPreserving_equiv J e)
  let G : Sheaf (locallyCoverDense_equiv J e).inducedTopology A :=
    ⟨(locallyCoverDense_equiv J e).inducedTopology.sheafify (e.inverse.op ⋙ F),
      (locallyCoverDense_equiv J e).inducedTopology.sheafify_isSheaf _⟩
  change Presheaf.IsSheaf J (e.functor.op ⋙ G.val)
  exact e.functor.op_comp_isSheaf _ _ _
