/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Definitions and basic properties of normal monomorphisms and epimorphisms.

A normal monomorphism is a morphism that is the kernel of some other morphism.

We give the construction `NormalMono → RegularMono` (`CategoryTheory.NormalMono.regularMono`)
as well as the dual construction for normal epimorphisms. We show equivalences reflect normal
monomorphisms (`CategoryTheory.equivalenceReflectsNormalMono`), and that the pullback of a
normal monomorphism is normal (`CategoryTheory.normalOfIsPullbackSndOfNormal`).

We also define classes `IsNormalMonoCategory` and `IsNormalEpiCategory` for categories in which
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
  Z : C
  g : Y ⟶ Z
  w : f ≫ g = 0
  isLimit : IsLimit (KernelFork.ofι f w)

attribute [inherit_doc NormalMono] NormalMono.Z NormalMono.g NormalMono.w NormalMono.isLimit

section

/-- If `F` is an equivalence and `F.map f` is a normal mono, then `f` is a normal mono. -/
def equivalenceReflectsNormalMono {D : Type u₂} [Category.{v₁} D] [HasZeroMorphisms D] (F : C ⥤ D)
    [F.IsEquivalence] {X Y : C} {f : X ⟶ Y} (hf : NormalMono (F.map f)) : NormalMono f where
  Z := F.objPreimage hf.Z
  g := F.preimage (hf.g ≫ (F.objObjPreimageIso hf.Z).inv)
  w := F.map_injective <| by
    have reassoc' {W : D} (h : hf.Z ⟶ W) : F.map f ≫ hf.g ≫ h = 0 ≫ h := by
      rw [← Category.assoc, eq_whisker hf.w]
    simp [reassoc']
  isLimit := isLimitOfReflects F <|
    IsLimit.ofConeEquiv (Cones.postcomposeEquivalence (compNatIso F)) <|
      (IsLimit.ofIsoLimit (IsKernel.ofCompIso _ _ (F.objObjPreimageIso hf.Z) (by
        simp only [Functor.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id])
        hf.isLimit)) (Fork.ext (Iso.refl _) (by simp [compNatIso, Fork.ι]))

end

/-- Every normal monomorphism is a regular monomorphism. -/
instance (priority := 100) NormalMono.regularMono (f : X ⟶ Y) [I : NormalMono f] : RegularMono f :=
  { I with
    left := I.g
    right := 0
    w := by simpa using I.w }

/-- If `f` is a normal mono, then any map `k : W ⟶ Y` such that `k ≫ normal_mono.g = 0` induces
a morphism `l : W ⟶ X` such that `l ≫ f = k`. -/
def NormalMono.lift' {W : C} (f : X ⟶ Y) [hf : NormalMono f] (k : W ⟶ Y) (h : k ≫ hf.g = 0) :
    { l : W ⟶ X // l ≫ f = k } :=
  KernelFork.IsLimit.lift' NormalMono.isLimit _ h

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
  isLimit := by
    letI gr := regularOfIsPullbackSndOfRegular comm t
    have q := (HasZeroMorphisms.comp_zero k hn.Z).symm
    convert gr.isLimit

/-- The first leg of a pullback cone is a normal monomorphism if the left component is too.

See also `pullback.fstOfMono` for the basic monomorphism version, and
`normalOfIsPullbackSndOfNormal` for the flipped version.
-/
def normalOfIsPullbackFstOfNormal {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    [NormalMono k] (comm : f ≫ h = g ≫ k) (t : IsLimit (PullbackCone.mk _ _ comm)) :
    NormalMono f :=
  normalOfIsPullbackSndOfNormal comm.symm (PullbackCone.flipIsLimit t)

section

variable (C)

/-- A normal mono category is a category in which every monomorphism is normal. -/
class IsNormalMonoCategory : Prop where
  normalMonoOfMono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], Nonempty (NormalMono f)

attribute [inherit_doc IsNormalMonoCategory] IsNormalMonoCategory.normalMonoOfMono

end

/-- In a category in which every monomorphism is normal, we can express every monomorphism as
a kernel. This is not an instance because it would create an instance loop. -/
def normalMonoOfMono [IsNormalMonoCategory C] (f : X ⟶ Y) [Mono f] : NormalMono f :=
  (IsNormalMonoCategory.normalMonoOfMono _).some

instance (priority := 100) regularMonoCategoryOfNormalMonoCategory [IsNormalMonoCategory C] :
    IsRegularMonoCategory C where
  regularMonoOfMono f _ := ⟨by
    haveI := normalMonoOfMono f
    infer_instance⟩

end

section

variable [HasZeroMorphisms C]

/-- A normal epimorphism is a morphism which is the cokernel of some morphism. -/
class NormalEpi (f : X ⟶ Y) where
  W : C
  g : W ⟶ X
  w : g ≫ f = 0
  isColimit : IsColimit (CokernelCofork.ofπ f w)

attribute [inherit_doc NormalEpi] NormalEpi.W NormalEpi.g NormalEpi.w NormalEpi.isColimit

section

/-- If `F` is an equivalence and `F.map f` is a normal epi, then `f` is a normal epi. -/
def equivalenceReflectsNormalEpi {D : Type u₂} [Category.{v₁} D] [HasZeroMorphisms D] (F : C ⥤ D)
    [F.IsEquivalence] {X Y : C} {f : X ⟶ Y} (hf : NormalEpi (F.map f)) : NormalEpi f where
  W := F.objPreimage hf.W
  g := F.preimage ((F.objObjPreimageIso hf.W).hom ≫ hf.g)
  w := F.map_injective <| by simp [hf.w]
  isColimit := isColimitOfReflects F <|
    IsColimit.ofCoconeEquiv (Cocones.precomposeEquivalence (compNatIso F).symm) <|
      (IsColimit.ofIsoColimit
        (IsCokernel.ofIsoComp _ _ (F.objObjPreimageIso hf.W).symm (by simp) hf.isColimit)
          (Cofork.ext (Iso.refl _) (by simp [compNatIso, Cofork.π])))

end

/-- Every normal epimorphism is a regular epimorphism. -/
instance (priority := 100) NormalEpi.regularEpi (f : X ⟶ Y) [I : NormalEpi f] : RegularEpi f :=
  { I with
    left := I.g
    right := 0
    w := by simpa using I.w }

/-- If `f` is a normal epi, then every morphism `k : X ⟶ W` satisfying `NormalEpi.g ≫ k = 0`
induces `l : Y ⟶ W` such that `f ≫ l = k`. -/
def NormalEpi.desc' {W : C} (f : X ⟶ Y) [nef : NormalEpi f] (k : X ⟶ W) (h : nef.g ≫ k = 0) :
    { l : Y ⟶ W // f ≫ l = k } :=
  CokernelCofork.IsColimit.desc' NormalEpi.isColimit _ h

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
  isColimit := by
    letI hn := regularOfIsPushoutSndOfRegular comm t
    have q := (@zero_comp _ _ _ gn.W _ _ f).symm
    convert hn.isColimit

/-- The first leg of a pushout cocone is a normal epimorphism if the left component is too.

See also `pushout.fstOfEpi` for the basic epimorphism version, and
`normalOfIsPushoutSndOfNormal` for the flipped version.
-/
def normalOfIsPushoutFstOfNormal {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    [NormalEpi f] (comm : f ≫ h = g ≫ k) (t : IsColimit (PushoutCocone.mk _ _ comm)) :
    NormalEpi k :=
  normalOfIsPushoutSndOfNormal comm.symm (PushoutCocone.flipIsColimit t)

end

open Opposite

variable [HasZeroMorphisms C]

/-- A normal mono becomes a normal epi in the opposite category. -/
def normalEpiOfNormalMonoUnop {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : NormalMono f.unop) : NormalEpi f where
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
        apply Quiver.Hom.unop_inj
        apply m.isLimit.uniq (KernelFork.ofι (m'.unop ≫ f.unop) _) m'.unop
        rintro (⟨⟩ | ⟨⟩) <;> simp)

/-- A normal epi becomes a normal mono in the opposite category. -/
def normalMonoOfNormalEpiUnop {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : NormalEpi f.unop) : NormalMono f where
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
        apply Quiver.Hom.unop_inj
        apply m.isColimit.uniq (CokernelCofork.ofπ (f.unop ≫ m'.unop) _) m'.unop
        rintro (⟨⟩ | ⟨⟩) <;> simp)

section

variable (C)

/-- A normal epi category is a category in which every epimorphism is normal. -/
class IsNormalEpiCategory : Prop where
  normalEpiOfEpi : ∀ {X Y : C} (f : X ⟶ Y) [Epi f], Nonempty (NormalEpi f)

attribute [inherit_doc IsNormalEpiCategory] IsNormalEpiCategory.normalEpiOfEpi

end

/-- In a category in which every epimorphism is normal, we can express every epimorphism as
a kernel. This is not an instance because it would create an instance loop. -/
def normalEpiOfEpi [IsNormalEpiCategory C] (f : X ⟶ Y) [Epi f] : NormalEpi f :=
  (IsNormalEpiCategory.normalEpiOfEpi _).some

instance (priority := 100) regularEpiCategoryOfNormalEpiCategory [IsNormalEpiCategory C] :
    IsRegularEpiCategory C where
  regularEpiOfEpi f _ := ⟨by
    haveI := normalEpiOfEpi f
    infer_instance⟩

end CategoryTheory
