/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.SmallShiftedHom

/-!
# Ext groups in abelian categories

Let `C` be an abelian category (with `C : Type u` and `Category.{v} C`).
In this file, we introduce the assumption `HasExt.{w} C` which asserts
that morphisms between single complexes in arbitrary degrees in
the derived category of `C` are `w`-small. Under this assumption,
we define `Ext.{w} X Y n : Type w` as shrunk versions of suitable
types of morphisms in the derived category. In particular, when `C` has
enough projectives or enough injectives, the property `HasExt.{v} C`
shall hold (TODO).

Note: in certain situations, `w := v` shall be the preferred
choice of universe (e.g. if `C := ModuleCat.{v} R` with `R : Type v`).
However, in the development of the API for Ext-groups, it is important
to keep a larger degree of generality for universes, as `w < v`
may happen in certain situations. Indeed, if `X : Scheme.{u}`,
then the underlying category of the étale site of `X` shall be a large
category. However, the category `Sheaf X.Etale AddCommGroupCat.{u}`
shall have good properties (because there is a small category of affine
schemes with the same category of sheaves), and even though the type of
morphisms in `Sheaf X.Etale AddCommGroupCat.{u}` shall be
in `Type (u + 1)`, these types are going to be `u`-small.
Then, for `C := Sheaf X.etale AddCommGroupCat.{u}`, we will have
`Category.{u + 1} C`, but `HasExt.{u} C` will hold
(as `C` has enough injectives). Then, the `Ext` groups between étale
sheaves over `X` shall be in `Type u`.

## TODO
* construct the additive structure on `Ext`
* compute `Ext X Y 0`
* define the class in `Ext S.X₃ S.X₁ 1` of a short exact short complex `S`
* construct the long exact sequences of `Ext`.

-/

universe w' t' w t v v' u u'

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]

open Localization Limits

/-- The property that morphisms between single complexes in arbitrary degrees are `w`-small
in the derived category. -/
abbrev HasExt : Prop :=
  ∀ (X Y : C), HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) ℤ
    ((CochainComplex.singleFunctor C 0).obj X) ((CochainComplex.singleFunctor C 0).obj Y)

-- TODO: when the canonical t-structure is formalized, replace `n : ℤ` by `n : ℕ`
lemma hasExt_iff [HasDerivedCategory.{w'} C] :
    HasExt.{w} C ↔ ∀ (X Y : C) (n : ℤ), Small.{w}
      ((DerivedCategory.singleFunctor C 0).obj X ⟶
        (((DerivedCategory.singleFunctor C 0).obj Y)⟦n⟧)) := by
  dsimp [HasExt]
  simp only [hasSmallLocalizedShiftedHom_iff _ _ DerivedCategory.Q]
  constructor
  · intro h X Y n
    exact (small_congr ((shiftFunctorZero _ ℤ).app
      ((DerivedCategory.singleFunctor C 0).obj X)).homFromEquiv).1 (h X Y 0 n)
  · intro h X Y a b
    refine (small_congr ?_).1 (h X Y (b - a))
    exact (Functor.FullyFaithful.ofFullyFaithful
      (shiftFunctor _ a)).homEquiv.trans
      ((shiftFunctorAdd' _ _ _ _ (Int.sub_add_cancel b a)).symm.app _).homToEquiv

lemma hasExt_of_hasDerivedCategory [HasDerivedCategory.{w} C] : HasExt.{w} C := by
  rw [hasExt_iff.{w}]
  infer_instance

variable {C}

variable [HasExt.{w} C]

section

variable {ι : Type*} {c : ComplexShape ι} [DecidableEq ι]

class _root_.HomologicalComplex.IsSingle (K : HomologicalComplex C c) : Prop where
  nonempty : ∃ (X : C) (i : ι), Nonempty (K ≅ (HomologicalComplex.single C c i).obj X)

instance (X : C) (i : ι) : ((HomologicalComplex.single C c i).obj X).IsSingle where
  nonempty := ⟨X, i, ⟨Iso.refl _⟩⟩

instance (X : C) (n : ℤ) : ((CochainComplex.singleFunctor C n).obj X).IsSingle where
  nonempty := ⟨X, n, ⟨Iso.refl _⟩⟩

instance (a b i j : ℤ)  (X Y : C) :
    HasSmallLocalizedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      ((shiftFunctor (HomologicalComplex C (ComplexShape.up ℤ)) a).obj
        ((HomologicalComplex.single C (ComplexShape.up ℤ) i).obj X))
      ((shiftFunctor (HomologicalComplex C (ComplexShape.up ℤ)) b).obj
        ((HomologicalComplex.single C (ComplexShape.up ℤ) j).obj Y)) := by
  have : HasExt.{w} C := inferInstance
  sorry

instance (K L : CochainComplex C ℤ) [hK : K.IsSingle] [hL : L.IsSingle] :
    HasSmallLocalizedShiftedHom.{w}
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) ℤ K L := by
  obtain ⟨X, i, ⟨e₁⟩⟩ := hK
  obtain ⟨Y, j, ⟨e₂⟩⟩ := hL
  exact hasSmallLocalizedShiftedHom_of_isos _ ℤ e₁ e₂

end

namespace Abelian

/-- A Ext-group in an abelian category `C`, defined as a `Type w` when `[HasExt.{w} C]`. -/
def Ext (X Y : C) (n : ℕ) : Type w :=
  SmallShiftedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    ((CochainComplex.singleFunctor C 0).obj X)
    ((CochainComplex.singleFunctor C 0).obj Y) (n : ℤ)

namespace Ext

variable {X Y Z T : C}

/-- The composition of `Ext`. -/
noncomputable def comp {a b : ℕ} (α : Ext X Y a) (β : Ext Y Z b) {c : ℕ} (h : a + b = c) :
    Ext X Z c :=
  SmallShiftedHom.comp α β (by omega)

lemma comp_assoc {a₁ a₂ a₃ a₁₂ a₂₃ a : ℕ} (α : Ext X Y a₁) (β : Ext Y Z a₂) (γ : Ext Z T a₃)
    (h₁₂ : a₁ + a₂ = a₁₂) (h₂₃ : a₂ + a₃ = a₂₃) (h : a₁ + a₂ + a₃ = a) :
    (α.comp β h₁₂).comp γ (show a₁₂ + a₃ = a by omega) =
      α.comp (β.comp γ h₂₃) (by omega) :=
  SmallShiftedHom.comp_assoc _ _ _ _ _ _ (by omega)

section

variable [HasDerivedCategory.{w'} C]

/-- When an instance of `[HasDerivedCategory.{w'} C]` is available, this is the bijection
between `Ext.{w} X Y n` and a type of morphisms in the derived category. -/
noncomputable def homEquiv {n : ℕ} :
    Ext.{w} X Y n ≃ ShiftedHom ((DerivedCategory.singleFunctor C 0).obj X)
      ((DerivedCategory.singleFunctor C 0).obj Y) (n : ℤ) :=
  SmallShiftedHom.equiv (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) DerivedCategory.Q

/-- The morphism in the derived category which corresponds to an element in `Ext X Y a`. -/
noncomputable abbrev hom {a : ℕ} (α : Ext X Y a) :
    ShiftedHom ((DerivedCategory.singleFunctor C 0).obj X)
      ((DerivedCategory.singleFunctor C 0).obj Y) (a : ℤ) :=
  homEquiv α

@[simp]
lemma comp_hom {a b : ℕ} (α : Ext X Y a) (β : Ext Y Z b) {c : ℕ} (h : a + b = c) :
    (α.comp β h).hom = α.hom.comp β.hom (by omega) := by
  apply SmallShiftedHom.equiv_comp

@[ext]
lemma ext {n : ℕ} {α β : Ext X Y n} (h : α.hom = β.hom) : α = β :=
  homEquiv.injective h

end

-- TODO: promote `homEquiv` above as `homAddEquiv` with the same
-- degree of generality, i.e. for any `[HasDerivedCategory.{w'} C]`
noncomputable instance {n : ℕ} : AddCommGroup (Ext X Y n) :=
  letI := HasDerivedCategory.standard C
  homEquiv.addCommGroup

section

variable {n}
variable
  (α β : Ext.{w} X Y n)
  [HasExt.{t} D] (F : C ⥤ D) [F.Additive] [F.PreservesHomology]

instance (K : CochainComplex C ℤ) [K.IsSingle] :
    ((F.mapHomologicalComplex _).obj K).IsSingle := sorry

instance (X : C) :
    ((F ⋙ HomologicalComplex.single D (ComplexShape.up ℤ) 0).obj X).IsSingle := by
  dsimp
  infer_instance

instance (X : C) (n : ℤ) : ((HomologicalComplex.single C
    (ComplexShape.up ℤ) n ⋙ F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X).IsSingle :=
  ⟨F.obj X, n, ⟨(HomologicalComplex.singleMapHomologicalComplex F _ n).app X⟩⟩

noncomputable def map : Ext.{t} (F.obj X) (F.obj Y) n :=
  (SmallShiftedHom.mk (HomologicalComplex.quasiIso D (ComplexShape.up ℤ))
    (ShiftedHom.mk₀ ((0 : ℕ) : ℤ) (by simp)
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app X).inv)).comp
    (((F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).mapSmallShiftedHom α).comp
      (SmallShiftedHom.mk (HomologicalComplex.quasiIso D (ComplexShape.up ℤ))
        (ShiftedHom.mk₀ ((0 : ℕ) : ℤ) (by simp)
    ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app Y).hom)) (zero_add _))
      (add_zero _)

section

variable [HasDerivedCategory.{w'} C] [HasDerivedCategory.{t'} D]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

lemma map_eq : homEquiv (α.map F) =
    (ShiftedHom.mk₀ 0 (by simp) ((F.singleFunctorCompMapDerivedCategoryIso 0).inv.app X)).comp
      (((homEquiv α).map F.mapDerivedCategory).comp (ShiftedHom.mk₀ 0 (by simp)
        ((F.singleFunctorCompMapDerivedCategoryIso 0).hom.app Y)) (zero_add _)) (add_zero _) := by
  sorry

lemma map_id : α.map (𝟭 C) = α := by
  sorry

set_option pp.universes true

lemma homEquiv_add : homEquiv (α + β) = homEquiv α + homEquiv β := by
  letI := HasDerivedCategory.standard C
  rw [← (α + β).map_id]
  conv_rhs => rw [← α.map_id, ← β.map_id]
  apply (map_eq.{max u v, w', w, w} (α + β) (𝟭 C)).trans
  sorry

end

end

end Ext

end Abelian

end CategoryTheory
