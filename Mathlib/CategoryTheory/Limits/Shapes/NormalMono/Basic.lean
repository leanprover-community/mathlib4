/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Basic

#align_import category_theory.limits.shapes.normal_mono.basic from "leanprover-community/mathlib"@"bbe25d4d92565a5fd773e52e041a90387eee3c93"

/-!
# Definitions and basic properties of normal monomorphisms and epimorphisms.

A normal monomorphism is a morphism that is the kernel of some other morphism.

We give the construction `NormalMono → RegularMono` (`CategoryTheory.NormalMono.regularMono`)
as well as the dual construction for normal epimorphisms. We show equivalences reflect normal
monomorphisms (`CategoryTheory.equivalenceReflectsNormalMono`), and that the pullback of a
normal monomorphism is normal (`CategoryTheory.normalOfIsPullbackSndOfNormal`).

We also define classes `NormalMonoCategory` and `NormalEpiCategory` for classes in which
every monomorphism or epimorphism is normal, and deduce that these categories are
`RegularMonoCategory`s resp. `RegularEpiCategory`s.

-/


noncomputable section

namespace CategoryTheory

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]

variable {X Y : C}

section

variable [HasZeroMorphisms C]

/-- A normal monomorphism is a morphism which is the kernel of some morphism. -/
class NormalMono (f : X ⟶ Y) where
  Z : C -- Porting note: violates naming convention but can't think of a better one
  g : Y ⟶ Z
  w : f ≫ g = 0
  isLimit : IsLimit (KernelFork.ofι f w)
#align category_theory.normal_mono CategoryTheory.NormalMono
#align category_theory.normal_mono.is_limit CategoryTheory.NormalMono.isLimit

attribute [inherit_doc NormalMono] NormalMono.Z NormalMono.g NormalMono.w NormalMono.isLimit

section

attribute [local instance] fullyFaithfulReflectsLimits

attribute [local instance] Equivalence.essSurj_of_equivalence

/-- If `F` is an equivalence and `F.map f` is a normal mono, then `f` is a normal mono. -/
def equivalenceReflectsNormalMono {D : Type u₂} [Category.{v₁} D] [HasZeroMorphisms D] (F : C ⥤ D)
    [IsEquivalence F] {X Y : C} {f : X ⟶ Y} (hf : NormalMono (F.map f)) : NormalMono f where
  Z := F.objPreimage hf.Z
  g := Full.preimage (hf.g ≫ (F.objObjPreimageIso hf.Z).inv)
  w := F.map_injective <| by
    have reassoc' {W : D} (h : hf.Z ⟶ W) : F.map f ≫ hf.g ≫ h = 0 ≫ h := by
      rw [← Category.assoc, eq_whisker hf.w]
    simp [reassoc']
    -- 🎉 no goals
  isLimit :=
    @ReflectsLimit.reflects C _ D _ _ _ _ F _ _ <|
      IsLimit.ofConeEquiv (Cones.postcomposeEquivalence (@compNatIso C _ _ _ _ _ D _ _ F _)) <|
        IsLimit.ofIsoLimit
          (IsLimit.ofIsoLimit
            (IsKernel.ofCompIso _ _ (F.objObjPreimageIso hf.Z) (by
              simp only [Full.witness, Category.assoc, Iso.inv_hom_id, Category.comp_id])
              -- 🎉 no goals
            hf.isLimit)
            (ofιCongr (Category.comp_id _).symm))
        <| by apply Iso.symm; apply isoOfι  -- Porting note: very fiddly unification here
              -- ⊢ (Cones.postcomposeEquivalence (compNatIso F)).functor.obj (F.mapCone (Kernel …
                              -- 🎉 no goals
#align category_theory.equivalence_reflects_normal_mono CategoryTheory.equivalenceReflectsNormalMono

end

/-- Every normal monomorphism is a regular monomorphism. -/
instance (priority := 100) NormalMono.regularMono (f : X ⟶ Y) [I : NormalMono f] : RegularMono f :=
  { I with
    left := I.g
    right := 0
    w := by simpa using I.w }
            -- 🎉 no goals
#align category_theory.normal_mono.regular_mono CategoryTheory.NormalMono.regularMono

/-- If `f` is a normal mono, then any map `k : W ⟶ Y` such that `k ≫ normal_mono.g = 0` induces
    a morphism `l : W ⟶ X` such that `l ≫ f = k`. -/
def NormalMono.lift' {W : C} (f : X ⟶ Y) [hf :NormalMono f] (k : W ⟶ Y) (h : k ≫ hf.g = 0) :
    { l : W ⟶ X // l ≫ f = k } :=
  KernelFork.IsLimit.lift' NormalMono.isLimit _ h
#align category_theory.normal_mono.lift' CategoryTheory.NormalMono.lift'

/-- The second leg of a pullback cone is a normal monomorphism if the right component is too.

See also `pullback.sndOfMono` for the basic monomorphism version, and
`normalOfIsPullbackFstOfNormal` for the flipped version.
-/
def normalOfIsPullbackSndOfNormal {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    [hn : NormalMono h] (comm : f ≫ h = g ≫ k) (t : IsLimit (PullbackCone.mk _ _ comm)) :
    NormalMono g where
  Z := hn.Z
  g := k ≫ hn.g
  w := by
    have reassoc' {W : C} (h' : S ⟶ W) : f ≫ h ≫ h' = g ≫ k ≫ h' := by
      simp only [← Category.assoc, eq_whisker comm]
    rw [← reassoc', hn.w, HasZeroMorphisms.comp_zero]
    -- 🎉 no goals
  isLimit := by
    letI gr := regularOfIsPullbackSndOfRegular comm t
    -- ⊢ IsLimit (KernelFork.ofι g (_ : g ≫ k ≫ NormalMono.g = 0))
    have q := (HasZeroMorphisms.comp_zero k hn.Z).symm
    -- ⊢ IsLimit (KernelFork.ofι g (_ : g ≫ k ≫ NormalMono.g = 0))
    convert gr.isLimit
    -- 🎉 no goals
#align category_theory.normal_of_is_pullback_snd_of_normal CategoryTheory.normalOfIsPullbackSndOfNormal

/-- The first leg of a pullback cone is a normal monomorphism if the left component is too.

See also `pullback.fstOfMono` for the basic monomorphism version, and
`normalOfIsPullbackSndOfNormal` for the flipped version.
-/
def normalOfIsPullbackFstOfNormal {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    [NormalMono k] (comm : f ≫ h = g ≫ k) (t : IsLimit (PullbackCone.mk _ _ comm)) :
    NormalMono f :=
  normalOfIsPullbackSndOfNormal comm.symm (PullbackCone.flipIsLimit t)
#align category_theory.normal_of_is_pullback_fst_of_normal CategoryTheory.normalOfIsPullbackFstOfNormal

section

variable (C)

/-- A normal mono category is a category in which every monomorphism is normal. -/
class NormalMonoCategory where
  normalMonoOfMono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], NormalMono f
#align category_theory.normal_mono_category CategoryTheory.NormalMonoCategory
#align category_theory.normal_mono_category.normal_mono_of_mono CategoryTheory.NormalMonoCategory.normalMonoOfMono

attribute [inherit_doc NormalMonoCategory] NormalMonoCategory.normalMonoOfMono

end

/-- In a category in which every monomorphism is normal, we can express every monomorphism as
    a kernel. This is not an instance because it would create an instance loop. -/
def normalMonoOfMono [NormalMonoCategory C] (f : X ⟶ Y) [Mono f] : NormalMono f :=
  NormalMonoCategory.normalMonoOfMono _
#align category_theory.normal_mono_of_mono CategoryTheory.normalMonoOfMono

instance (priority := 100) regularMonoCategoryOfNormalMonoCategory [NormalMonoCategory C] :
    RegularMonoCategory C where
  regularMonoOfMono f _ := by
    haveI := normalMonoOfMono f
    -- ⊢ RegularMono f
    infer_instance
    -- 🎉 no goals
#align category_theory.regular_mono_category_of_normal_mono_category CategoryTheory.regularMonoCategoryOfNormalMonoCategory

end

section

variable [HasZeroMorphisms C]

/-- A normal epimorphism is a morphism which is the cokernel of some morphism. -/
class NormalEpi (f : X ⟶ Y) where
  W : C
  g : W ⟶ X
  w : g ≫ f = 0
  isColimit : IsColimit (CokernelCofork.ofπ f w)
#align category_theory.normal_epi CategoryTheory.NormalEpi
#align category_theory.normal_epi.is_colimit CategoryTheory.NormalEpi.isColimit

attribute [inherit_doc NormalEpi] NormalEpi.W NormalEpi.g NormalEpi.w NormalEpi.isColimit

section

attribute [local instance] fullyFaithfulReflectsColimits

attribute [local instance] Equivalence.essSurj_of_equivalence

/-- If `F` is an equivalence and `F.map f` is a normal epi, then `f` is a normal epi. -/
def equivalenceReflectsNormalEpi {D : Type u₂} [Category.{v₁} D] [HasZeroMorphisms D] (F : C ⥤ D)
    [IsEquivalence F] {X Y : C} {f : X ⟶ Y} (hf : NormalEpi (F.map f)) : NormalEpi f where
  W := F.objPreimage hf.W
  g := Full.preimage ((F.objObjPreimageIso hf.W).hom ≫ hf.g)
  w := F.map_injective <| by simp [hf.w]
                             -- 🎉 no goals
  isColimit :=
    ReflectsColimit.reflects <|
      IsColimit.ofCoconeEquiv (Cocones.precomposeEquivalence (compNatIso F).symm) <|
        IsColimit.ofIsoColimit
          (IsColimit.ofIsoColimit
            (IsCokernel.ofIsoComp _ _ (F.objObjPreimageIso hf.W).symm (by simp) hf.isColimit)
                                                                          -- 🎉 no goals
            (ofπCongr (Category.id_comp _).symm))
          <| by apply Iso.symm; apply isoOfπ
                -- ⊢ (Cocones.precomposeEquivalence (compNatIso F).symm).functor.obj (F.mapCocone …
                                -- 🎉 no goals
#align category_theory.equivalence_reflects_normal_epi CategoryTheory.equivalenceReflectsNormalEpi

end

/-- Every normal epimorphism is a regular epimorphism. -/
instance (priority := 100) NormalEpi.regularEpi (f : X ⟶ Y) [I : NormalEpi f] : RegularEpi f :=
  { I with
    left := I.g
    right := 0
    w := by simpa using I.w }
            -- 🎉 no goals
#align category_theory.normal_epi.regular_epi CategoryTheory.NormalEpi.regularEpi

/-- If `f` is a normal epi, then every morphism `k : X ⟶ W` satisfying `normal_epi.g ≫ k = 0`
    induces `l : Y ⟶ W` such that `f ≫ l = k`. -/
def NormalEpi.desc' {W : C} (f : X ⟶ Y) [nef : NormalEpi f] (k : X ⟶ W) (h : nef.g ≫ k = 0) :
    { l : Y ⟶ W // f ≫ l = k } :=
  CokernelCofork.IsColimit.desc' NormalEpi.isColimit _ h
#align category_theory.normal_epi.desc' CategoryTheory.NormalEpi.desc'

/-- The second leg of a pushout cocone is a normal epimorphism if the right component is too.

See also `pushout.sndOfEpi` for the basic epimorphism version, and
`normalOfIsPushoutFstOfNormal` for the flipped version.
-/
def normalOfIsPushoutSndOfNormal {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    [gn : NormalEpi g] (comm : f ≫ h = g ≫ k) (t : IsColimit (PushoutCocone.mk _ _ comm)) :
    NormalEpi h where
  W := gn.W
  g := gn.g ≫ f
  w := by
    have reassoc' {W : C} (h' : R ⟶ W) :  gn.g ≫ g ≫ h' = 0 ≫ h' := by
      rw [← Category.assoc, eq_whisker gn.w]
    rw [Category.assoc, comm, reassoc', zero_comp]
    -- 🎉 no goals
  isColimit := by
    letI hn := regularOfIsPushoutSndOfRegular comm t
    -- ⊢ IsColimit (CokernelCofork.ofπ h (_ : (NormalEpi.g ≫ f) ≫ h = 0))
    have q := (@zero_comp _ _ _ gn.W _ _ f).symm
    -- ⊢ IsColimit (CokernelCofork.ofπ h (_ : (NormalEpi.g ≫ f) ≫ h = 0))
    convert hn.isColimit
    -- 🎉 no goals
#align category_theory.normal_of_is_pushout_snd_of_normal CategoryTheory.normalOfIsPushoutSndOfNormal

/-- The first leg of a pushout cocone is a normal epimorphism if the left component is too.

See also `pushout.fstOfEpi` for the basic epimorphism version, and
`normalOfIsPushoutSndOfNormal` for the flipped version.
-/
def normalOfIsPushoutFstOfNormal {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    [NormalEpi f] (comm : f ≫ h = g ≫ k) (t : IsColimit (PushoutCocone.mk _ _ comm)) :
    NormalEpi k :=
  normalOfIsPushoutSndOfNormal comm.symm (PushoutCocone.flipIsColimit t)
#align category_theory.normal_of_is_pushout_fst_of_normal CategoryTheory.normalOfIsPushoutFstOfNormal

end

open Opposite

variable [HasZeroMorphisms C]

/-- A normal mono becomes a normal epi in the opposite category. -/
def normalEpiOfNormalMonoUnop {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : NormalMono f.unop) : NormalEpi f
    where
  W := op m.Z
  g := m.g.op
  w := congrArg Quiver.Hom.op m.w
  isColimit :=
    CokernelCofork.IsColimit.ofπ _ _
      (fun g' w' =>
        (KernelFork.IsLimit.lift' m.isLimit g'.unop (congrArg Quiver.Hom.unop w')).1.op)
      (fun g' w' =>
        congrArg Quiver.Hom.op
          (KernelFork.IsLimit.lift' m.isLimit g'.unop (congrArg Quiver.Hom.unop w')).2)
      (by
        rintro Z' g' w' m' rfl
        -- ⊢ m' = (fun {Z'} g' w' => (↑(KernelFork.IsLimit.lift' NormalMono.isLimit g'.un …
        apply Quiver.Hom.unop_inj
        -- ⊢ m'.unop = ((fun {Z'} g' w' => (↑(KernelFork.IsLimit.lift' NormalMono.isLimit …
        apply m.isLimit.uniq (KernelFork.ofι (m'.unop ≫ f.unop) _) m'.unop
        -- ⊢ ∀ (j : WalkingParallelPair), m'.unop ≫ NatTrans.app (KernelFork.ofι f.unop ( …
        rintro (⟨⟩ | ⟨⟩) <;> simp)
        -- ⊢ m'.unop ≫ NatTrans.app (KernelFork.ofι f.unop (_ : f.unop ≫ NormalMono.g = 0 …
                             -- 🎉 no goals
                             -- 🎉 no goals
#align category_theory.normal_epi_of_normal_mono_unop CategoryTheory.normalEpiOfNormalMonoUnop

/-- A normal epi becomes a normal mono in the opposite category. -/
def normalMonoOfNormalEpiUnop {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : NormalEpi f.unop) : NormalMono f
    where
  Z := op m.W
  g := m.g.op
  w := congrArg Quiver.Hom.op m.w
  isLimit :=
    KernelFork.IsLimit.ofι _ _
      (fun g' w' =>
        (CokernelCofork.IsColimit.desc' m.isColimit g'.unop (congrArg Quiver.Hom.unop w')).1.op)
      (fun g' w' =>
        congrArg Quiver.Hom.op
          (CokernelCofork.IsColimit.desc' m.isColimit g'.unop (congrArg Quiver.Hom.unop w')).2)
      (by
        rintro Z' g' w' m' rfl
        -- ⊢ m' = (fun {W'} g' w' => (↑(CokernelCofork.IsColimit.desc' NormalEpi.isColimi …
        apply Quiver.Hom.unop_inj
        -- ⊢ m'.unop = ((fun {W'} g' w' => (↑(CokernelCofork.IsColimit.desc' NormalEpi.is …
        apply m.isColimit.uniq (CokernelCofork.ofπ (f.unop ≫ m'.unop) _) m'.unop
        -- ⊢ ∀ (j : WalkingParallelPair), NatTrans.app (CokernelCofork.ofπ f.unop (_ : No …
        rintro (⟨⟩ | ⟨⟩) <;> simp)
        -- ⊢ NatTrans.app (CokernelCofork.ofπ f.unop (_ : NormalEpi.g ≫ f.unop = 0)).ι Wa …
                             -- 🎉 no goals
                             -- 🎉 no goals
#align category_theory.normal_mono_of_normal_epi_unop CategoryTheory.normalMonoOfNormalEpiUnop

section

variable (C)

/-- A normal epi category is a category in which every epimorphism is normal. -/
class NormalEpiCategory where
  normalEpiOfEpi : ∀ {X Y : C} (f : X ⟶ Y) [Epi f], NormalEpi f
#align category_theory.normal_epi_category CategoryTheory.NormalEpiCategory
#align category_theory.normal_epi_category.normal_epi_of_epi CategoryTheory.NormalEpiCategory.normalEpiOfEpi

attribute [inherit_doc NormalEpiCategory] NormalEpiCategory.normalEpiOfEpi

end

/-- In a category in which every epimorphism is normal, we can express every epimorphism as
    a kernel. This is not an instance because it would create an instance loop. -/
def normalEpiOfEpi [NormalEpiCategory C] (f : X ⟶ Y) [Epi f] : NormalEpi f :=
  NormalEpiCategory.normalEpiOfEpi _
#align category_theory.normal_epi_of_epi CategoryTheory.normalEpiOfEpi

instance (priority := 100) regularEpiCategoryOfNormalEpiCategory [NormalEpiCategory C] :
    RegularEpiCategory C where
  regularEpiOfEpi f _ := by
    haveI := normalEpiOfEpi f
    -- ⊢ RegularEpi f
    infer_instance
    -- 🎉 no goals
#align category_theory.regular_epi_category_of_normal_epi_category CategoryTheory.regularEpiCategoryOfNormalEpiCategory

end CategoryTheory
