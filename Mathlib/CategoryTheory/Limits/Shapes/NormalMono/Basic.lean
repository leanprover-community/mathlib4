/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.limits.shapes.normal_mono.basic
! leanprover-community/mathlib commit bbe25d4d92565a5fd773e52e041a90387eee3c93
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Shapes.RegularMono
import Mathbin.CategoryTheory.Limits.Shapes.Kernels
import Mathbin.CategoryTheory.Limits.Preserves.Basic

/-!
# Definitions and basic properties of normal monomorphisms and epimorphisms.

A normal monomorphism is a morphism that is the kernel of some other morphism.

We give the construction `normal_mono → regular_mono` (`category_theory.normal_mono.regular_mono`)
as well as the dual construction for normal epimorphisms. We show equivalences reflect normal
monomorphisms (`category_theory.equivalence_reflects_normal_mono`), and that the pullback of a
normal monomorphism is normal (`category_theory.normal_of_is_pullback_snd_of_normal`).

We also define classes `normal_mono_category` and `normal_epi_category` for classes in which
every monomorphism or epimorphism is normal, and deduce that these categories are
`regular_mono_category`s resp. `regular_epi_category`s.

-/


noncomputable section

namespace CategoryTheory

open CategoryTheory.Limits

universe v₁ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]

variable {X Y : C}

section

variable [HasZeroMorphisms C]

/-- A normal monomorphism is a morphism which is the kernel of some morphism. -/
class NormalMono (f : X ⟶ Y) where
  z : C
  g : Y ⟶ Z
  w : f ≫ g = 0
  IsLimit : IsLimit (KernelFork.ofι f w)
#align category_theory.normal_mono CategoryTheory.NormalMono

section

attribute [local instance] fully_faithful_reflects_limits

attribute [local instance] equivalence.ess_surj_of_equivalence

/-- If `F` is an equivalence and `F.map f` is a normal mono, then `f` is a normal mono. -/
def equivalenceReflectsNormalMono {D : Type u₂} [Category.{v₁} D] [HasZeroMorphisms D] (F : C ⥤ D)
    [IsEquivalence F] {X Y : C} {f : X ⟶ Y} (hf : NormalMono (F.map f)) : NormalMono f
    where
  z := F.objPreimage hf.z
  g := Full.preimage (hf.g ≫ (F.objObjPreimageIso hf.z).inv)
  w := Faithful.map_injective F <| by simp [reassoc_of hf.w]
  IsLimit :=
    ReflectsLimit.reflects <|
      IsLimit.ofConeEquiv (Cones.postcomposeEquivalence (compNatIso F : _)) <|
        IsLimit.ofIsoLimit
          (is_limit.of_iso_limit
            (is_kernel.of_comp_iso _ _ (F.obj_obj_preimage_iso hf.Z) (by simp) hf.is_limit)
            (of_ι_congr (category.comp_id _).symm))
          (isoOfι _).symm
#align category_theory.equivalence_reflects_normal_mono CategoryTheory.equivalenceReflectsNormalMono

end

/-- Every normal monomorphism is a regular monomorphism. -/
instance (priority := 100) NormalMono.regularMono (f : X ⟶ Y) [I : NormalMono f] : RegularMono f :=
  { I with
    left := I.g
    right := 0
    w := by simpa using I.w }
#align category_theory.normal_mono.regular_mono CategoryTheory.NormalMono.regularMono

/-- If `f` is a normal mono, then any map `k : W ⟶ Y` such that `k ≫ normal_mono.g = 0` induces
    a morphism `l : W ⟶ X` such that `l ≫ f = k`. -/
def NormalMono.lift' {W : C} (f : X ⟶ Y) [NormalMono f] (k : W ⟶ Y) (h : k ≫ NormalMono.g = 0) :
    { l : W ⟶ X // l ≫ f = k } :=
  KernelFork.IsLimit.lift' NormalMono.isLimit _ h
#align category_theory.normal_mono.lift' CategoryTheory.NormalMono.lift'

/-- The second leg of a pullback cone is a normal monomorphism if the right component is too.

See also `pullback.snd_of_mono` for the basic monomorphism version, and
`normal_of_is_pullback_fst_of_normal` for the flipped version.
-/
def normalOfIsPullbackSndOfNormal {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    [hn : NormalMono h] (comm : f ≫ h = g ≫ k) (t : IsLimit (PullbackCone.mk _ _ comm)) :
    NormalMono g where
  z := hn.z
  g := k ≫ hn.g
  w := by rw [← reassoc_of comm, hn.w, has_zero_morphisms.comp_zero]
  IsLimit := by
    letI gr := regular_of_is_pullback_snd_of_regular comm t
    have q := (has_zero_morphisms.comp_zero k hn.Z).symm
    convert gr.is_limit
    dsimp only [kernel_fork.of_ι, fork.of_ι]
    congr ; exact q; exact q; exact q; apply proof_irrel_heq
#align category_theory.normal_of_is_pullback_snd_of_normal CategoryTheory.normalOfIsPullbackSndOfNormal

/-- The first leg of a pullback cone is a normal monomorphism if the left component is too.

See also `pullback.fst_of_mono` for the basic monomorphism version, and
`normal_of_is_pullback_snd_of_normal` for the flipped version.
-/
def normalOfIsPullbackFstOfNormal {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    [hn : NormalMono k] (comm : f ≫ h = g ≫ k) (t : IsLimit (PullbackCone.mk _ _ comm)) :
    NormalMono f :=
  normalOfIsPullbackSndOfNormal comm.symm (PullbackCone.flipIsLimit t)
#align category_theory.normal_of_is_pullback_fst_of_normal CategoryTheory.normalOfIsPullbackFstOfNormal

section

variable (C)

/-- A normal mono category is a category in which every monomorphism is normal. -/
class NormalMonoCategory where
  normalMonoOfMono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], NormalMono f
#align category_theory.normal_mono_category CategoryTheory.NormalMonoCategory

end

/-- In a category in which every monomorphism is normal, we can express every monomorphism as
    a kernel. This is not an instance because it would create an instance loop. -/
def normalMonoOfMono [NormalMonoCategory C] (f : X ⟶ Y) [Mono f] : NormalMono f :=
  NormalMonoCategory.normalMonoOfMono _
#align category_theory.normal_mono_of_mono CategoryTheory.normalMonoOfMono

instance (priority := 100) regularMonoCategoryOfNormalMonoCategory [NormalMonoCategory C] :
    RegularMonoCategory C
    where regularMonoOfMono _ _ f _ :=
    by
    haveI := normal_mono_of_mono f
    infer_instance
#align category_theory.regular_mono_category_of_normal_mono_category CategoryTheory.regularMonoCategoryOfNormalMonoCategory

end

section

variable [HasZeroMorphisms C]

/-- A normal epimorphism is a morphism which is the cokernel of some morphism. -/
class NormalEpi (f : X ⟶ Y) where
  w : C
  g : W ⟶ X
  w : g ≫ f = 0
  IsColimit : IsColimit (CokernelCofork.ofπ f w)
#align category_theory.normal_epi CategoryTheory.NormalEpi

section

attribute [local instance] fully_faithful_reflects_colimits

attribute [local instance] equivalence.ess_surj_of_equivalence

/-- If `F` is an equivalence and `F.map f` is a normal epi, then `f` is a normal epi. -/
def equivalenceReflectsNormalEpi {D : Type u₂} [Category.{v₁} D] [HasZeroMorphisms D] (F : C ⥤ D)
    [IsEquivalence F] {X Y : C} {f : X ⟶ Y} (hf : NormalEpi (F.map f)) : NormalEpi f
    where
  w := F.objPreimage hf.w
  g := Full.preimage ((F.objObjPreimageIso hf.w).Hom ≫ hf.g)
  w := Faithful.map_injective F <| by simp [hf.w]
  IsColimit :=
    ReflectsColimit.reflects <|
      IsColimit.ofCoconeEquiv (Cocones.precomposeEquivalence (compNatIso F).symm) <|
        IsColimit.ofIsoColimit
          (is_colimit.of_iso_colimit
            (is_cokernel.of_iso_comp _ _ (F.obj_obj_preimage_iso hf.W).symm (by simp) hf.is_colimit)
            (of_π_congr (category.id_comp _).symm))
          (isoOfπ _).symm
#align category_theory.equivalence_reflects_normal_epi CategoryTheory.equivalenceReflectsNormalEpi

end

/-- Every normal epimorphism is a regular epimorphism. -/
instance (priority := 100) NormalEpi.regularEpi (f : X ⟶ Y) [I : NormalEpi f] : RegularEpi f :=
  { I with
    left := I.g
    right := 0
    w := by simpa using I.w }
#align category_theory.normal_epi.regular_epi CategoryTheory.NormalEpi.regularEpi

/-- If `f` is a normal epi, then every morphism `k : X ⟶ W` satisfying `normal_epi.g ≫ k = 0`
    induces `l : Y ⟶ W` such that `f ≫ l = k`. -/
def NormalEpi.desc' {W : C} (f : X ⟶ Y) [NormalEpi f] (k : X ⟶ W) (h : NormalEpi.g ≫ k = 0) :
    { l : Y ⟶ W // f ≫ l = k } :=
  CokernelCofork.IsColimit.desc' NormalEpi.isColimit _ h
#align category_theory.normal_epi.desc' CategoryTheory.NormalEpi.desc'

/-- The second leg of a pushout cocone is a normal epimorphism if the right component is too.

See also `pushout.snd_of_epi` for the basic epimorphism version, and
`normal_of_is_pushout_fst_of_normal` for the flipped version.
-/
def normalOfIsPushoutSndOfNormal {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    [gn : NormalEpi g] (comm : f ≫ h = g ≫ k) (t : IsColimit (PushoutCocone.mk _ _ comm)) :
    NormalEpi h where
  w := gn.w
  g := gn.g ≫ f
  w := by rw [category.assoc, comm, reassoc_of gn.w, zero_comp]
  IsColimit := by
    letI hn := regular_of_is_pushout_snd_of_regular comm t
    have q := (@zero_comp _ _ _ gn.W _ _ f).symm
    convert hn.is_colimit
    dsimp only [cokernel_cofork.of_π, cofork.of_π]
    congr ; exact q; exact q; exact q; apply proof_irrel_heq
#align category_theory.normal_of_is_pushout_snd_of_normal CategoryTheory.normalOfIsPushoutSndOfNormal

/-- The first leg of a pushout cocone is a normal epimorphism if the left component is too.

See also `pushout.fst_of_epi` for the basic epimorphism version, and
`normal_of_is_pushout_snd_of_normal` for the flipped version.
-/
def normalOfIsPushoutFstOfNormal {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    [hn : NormalEpi f] (comm : f ≫ h = g ≫ k) (t : IsColimit (PushoutCocone.mk _ _ comm)) :
    NormalEpi k :=
  normalOfIsPushoutSndOfNormal comm.symm (PushoutCocone.flipIsColimit t)
#align category_theory.normal_of_is_pushout_fst_of_normal CategoryTheory.normalOfIsPushoutFstOfNormal

end

open Opposite

variable [HasZeroMorphisms C]

/-- A normal mono becomes a normal epi in the opposite category. -/
def normalEpiOfNormalMonoUnop {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : NormalMono f.unop) : NormalEpi f
    where
  w := op m.z
  g := m.g.op
  w := congr_arg Quiver.Hom.op m.w
  IsColimit :=
    CokernelCofork.IsColimit.ofπ _ _
      (fun Z' g' w' =>
        (KernelFork.IsLimit.lift' m.IsLimit g'.unop (congr_arg Quiver.Hom.unop w')).1.op)
      (fun Z' g' w' =>
        congr_arg Quiver.Hom.op
          (KernelFork.IsLimit.lift' m.IsLimit g'.unop (congr_arg Quiver.Hom.unop w')).2)
      (by
        rintro Z' g' w' m' rfl
        apply Quiver.Hom.unop_inj
        apply m.is_limit.uniq (kernel_fork.of_ι (m'.unop ≫ f.unop) _) m'.unop
        rintro (⟨⟩ | ⟨⟩) <;> simp)
#align category_theory.normal_epi_of_normal_mono_unop CategoryTheory.normalEpiOfNormalMonoUnop

/-- A normal epi becomes a normal mono in the opposite category. -/
def normalMonoOfNormalEpiUnop {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : NormalEpi f.unop) : NormalMono f
    where
  z := op m.w
  g := m.g.op
  w := congr_arg Quiver.Hom.op m.w
  IsLimit :=
    KernelFork.IsLimit.ofι _ _
      (fun Z' g' w' =>
        (CokernelCofork.IsColimit.desc' m.IsColimit g'.unop (congr_arg Quiver.Hom.unop w')).1.op)
      (fun Z' g' w' =>
        congr_arg Quiver.Hom.op
          (CokernelCofork.IsColimit.desc' m.IsColimit g'.unop (congr_arg Quiver.Hom.unop w')).2)
      (by
        rintro Z' g' w' m' rfl
        apply Quiver.Hom.unop_inj
        apply m.is_colimit.uniq (cokernel_cofork.of_π (f.unop ≫ m'.unop) _) m'.unop
        rintro (⟨⟩ | ⟨⟩) <;> simp)
#align category_theory.normal_mono_of_normal_epi_unop CategoryTheory.normalMonoOfNormalEpiUnop

section

variable (C)

/-- A normal epi category is a category in which every epimorphism is normal. -/
class NormalEpiCategory where
  normalEpiOfEpi : ∀ {X Y : C} (f : X ⟶ Y) [Epi f], NormalEpi f
#align category_theory.normal_epi_category CategoryTheory.NormalEpiCategory

end

/-- In a category in which every epimorphism is normal, we can express every epimorphism as
    a kernel. This is not an instance because it would create an instance loop. -/
def normalEpiOfEpi [NormalEpiCategory C] (f : X ⟶ Y) [Epi f] : NormalEpi f :=
  NormalEpiCategory.normalEpiOfEpi _
#align category_theory.normal_epi_of_epi CategoryTheory.normalEpiOfEpi

instance (priority := 100) regularEpiCategoryOfNormalEpiCategory [NormalEpiCategory C] :
    RegularEpiCategory C
    where regularEpiOfEpi _ _ f _ :=
    by
    haveI := normal_epi_of_epi f
    infer_instance
#align category_theory.regular_epi_category_of_normal_epi_category CategoryTheory.regularEpiCategoryOfNormalEpiCategory

end CategoryTheory

