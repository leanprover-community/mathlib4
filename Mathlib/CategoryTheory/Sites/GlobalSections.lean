/-
Copyright (c) 2025 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Global sections of sheaves

In this file we define a global sections functor `Sheaf.Γ : Sheaf J A ⥤ A` and show that it
is isomorphic to several other constructions when they exist, most notably evaluation of sheaves
on a terminal object and `Functor.sectionsFunctor`.

## Main definitions / results

* `HasGlobalSectionsFunctor J A`: typeclass stating that the constant sheaf functor `A ⥤ Sheaf J A`
  has a right-adjoint.
* `Sheaf.Γ J A`: the global sections functor `Sheaf J A ⥤ A`, defined as the right-adjoint of the
  constant sheaf functor, whenever that exists.
* `constantSheafΓAdj J A`: the adjunction between the constant sheaf functor and `Sheaf.Γ J A`.
* `Sheaf.ΓNatIsoSheafSections J A hT`: on sites with a terminal object `T`, `Sheaf.Γ J A` exists and
  is isomorphic to the functor evaluating sheaves at `T`.
* `Sheaf.ΓNatIsoLim J A`: when `A` has limits of shape `Cᵒᵖ`, `Sheaf.Γ J A` exists and is isomorphic
  to the functor taking each sheaf to the limit of its underlying presheaf.
* `Sheaf.isLimitConeΓ F`: global sections are limits even when not all limits of shape `Cᵒᵖ` exist.
* `Sheaf.ΓRes F U`: the restriction morphism from global sections of `F` to sections of `F` on `U`.
* `Sheaf.natTransΓRes J A U`: the natural transformation from the global sections functor to
  the sections functor on `U`.
* `Sheaf.ΓNatIsoSectionsFunctor J`: for sheaves of types, `Sheaf.Γ J A` is isomorphic to the
  functor taking each sheaf to the type of sections of its underlying presheaf in the sense of
  `Functor.sections`.
* `Sheaf.ΓNatIsoCoyoneda J`: for sheaves of types, `Sheaf.Γ J A` is isomorphic to the
  coyoneda embedding of the terminal sheaf, i.e. the functor sending each sheaf `F` to the type
  of morphisms from the terminal sheaf to `F`.

## TODO

* Generalise `Sheaf.ΓNatIsoSectionsFunctor` and `Sheaf.ΓNatIsoCoyoneda` from `Type max u v` to
  `Type max u v w`. This should hopefully be doable by relaxing the universe constraints of
  `instHasSheafifyOfHasFiniteLimits`.

-/

universe u v w u₂ v₂

open CategoryTheory Limits Sheaf Opposite GrothendieckTopology

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type u₂) [Category.{v₂} A] [HasWeakSheafify J A]

/-- Typeclass stating that the constant sheaf functor has a right adjoint. This right adjoint will
then be called the global sections functor and written `Sheaf.Γ`. -/
abbrev HasGlobalSectionsFunctor := (constantSheaf J A).IsLeftAdjoint

/-- We define the global sections functor as the right-adjoint of the constant sheaf functor
whenever it exists. -/
noncomputable def Sheaf.Γ [HasGlobalSectionsFunctor J A] : Sheaf J A ⥤ A :=
  (constantSheaf J A).rightAdjoint

/-- The constant sheaf functor is by definition left-adjoint to the global sections functor. -/
noncomputable def constantSheafΓAdj [HasGlobalSectionsFunctor J A] :
    constantSheaf J A ⊣ Γ J A :=
  Adjunction.ofIsLeftAdjoint (constantSheaf J A)

instance [HasGlobalSectionsFunctor J A] : (Γ J A).IsRightAdjoint := by
  unfold Γ; infer_instance

/-- Sites with a terminal object admit a global sections functor. -/
instance hasGlobalSectionsFunctor_of_hasTerminal [HasTerminal C] :
    HasGlobalSectionsFunctor J A :=
  ⟨_, ⟨constantSheafAdj J A terminalIsTerminal⟩⟩

/-- On sites with a terminal object, the global sections functor is isomorphic to the functor
of sections on that object. -/
noncomputable def Sheaf.ΓNatIsoSheafSections [HasTerminal C] {T : C} (hT : IsTerminal T) :
    Γ J A ≅ (sheafSections J A).obj (op T) :=
  (constantSheafΓAdj J A).rightAdjointUniq (constantSheafAdj J A hT)

/-- Every site `C` admits a global sections functor for `A`-valued sheaves when `A` has limits of
shape `Cᵒᵖ`. -/
instance hasGlobalSectionsFunctor_of_hasLimitsOfShape [HasLimitsOfShape Cᵒᵖ A] :
    HasGlobalSectionsFunctor J A :=
  ⟨sheafToPresheaf J A ⋙ lim, ⟨constLimAdj.comp (sheafificationAdjunction J A)⟩⟩

/-- Global sections of sheaves are naturally isomorphic to the limits of the underlying presheaves.
Note that while `HasLimitsOfShape Cᵒᵖ A` is needed here to talk about `lim` as a functor, global
sections are still limits without it - see `Sheaf.isLimitConeΓ`. -/
noncomputable def Sheaf.ΓNatIsoLim [HasLimitsOfShape Cᵒᵖ A] :
    Γ J A ≅ sheafToPresheaf J A ⋙ lim :=
  (constantSheafΓAdj J A).rightAdjointUniq (constLimAdj.comp (sheafificationAdjunction J A))

variable {J A}

/-- Natural transformations from a constant presheaf into a sheaf correspond to morphisms to its
global sections. -/
noncomputable def Sheaf.ΓHomEquiv [HasGlobalSectionsFunctor J A] {X : A} {F : Sheaf J A} :
    ((Functor.const _).obj X ⟶ F.val) ≃ (X ⟶ (Γ J A).obj F) :=
  ((sheafificationAdjunction J A).homEquiv _ _).symm.trans
    ((constantSheafΓAdj J A).homEquiv _ _)

/-- Naturality lemma for `ΓHomEquiv` analogous to `Adjunction.homEquiv_naturality_left`. -/
lemma Sheaf.ΓHomEquiv_naturality_left [HasGlobalSectionsFunctor J A] {X' X : A} {F : Sheaf J A}
    (f : X' ⟶ X) (g : (Functor.const _).obj X ⟶ F.val) :
    ΓHomEquiv ((Functor.const _).map f ≫ g) = f ≫ ΓHomEquiv g :=
  (congrArg _ ((sheafificationAdjunction J A).homEquiv_naturality_left_symm _ _)).trans
    ((constantSheafΓAdj J A).homEquiv_naturality_left _ _)

/-- Naturality lemma for `ΓHomEquiv` analogous to `Adjunction.homEquiv_naturality_left_symm`. -/
lemma Sheaf.ΓHomEquiv_naturality_left_symm [HasGlobalSectionsFunctor J A] {X' X : A} {F : Sheaf J A}
    (f : X' ⟶ X) (g : X ⟶ (Γ J A).obj F) :
    ΓHomEquiv.symm (f ≫ g) = (Functor.const _).map f ≫ ΓHomEquiv.symm g :=
  (congrArg _ ((constantSheafΓAdj J A).homEquiv_naturality_left_symm _ _)).trans
    ((sheafificationAdjunction J A).homEquiv_naturality_left _ _)

/-- Naturality lemma for `ΓHomEquiv` analogous to `Adjunction.homEquiv_naturality_right`. -/
lemma Sheaf.ΓHomEquiv_naturality_right [HasGlobalSectionsFunctor J A] {X : A} {F F' : Sheaf J A}
    (f : (Functor.const _).obj X ⟶ F.val) (g : F ⟶ F') :
    ΓHomEquiv (f ≫ g.val) = ΓHomEquiv f ≫ (Γ J A).map g :=
  (congrArg _ ((sheafificationAdjunction J A).homEquiv_naturality_right_symm _ _)).trans
    ((constantSheafΓAdj J A).homEquiv_naturality_right _ _)

/-- Naturality lemma for `ΓHomEquiv` analogous to `Adjunction.homEquiv_naturality_right_symm`. -/
lemma Sheaf.ΓHomEquiv_naturality_right_symm [HasGlobalSectionsFunctor J A] {X : A}
    {F F' : Sheaf J A} (f : X ⟶ (Γ J A).obj F) (g : F ⟶ F') :
    ΓHomEquiv.symm (f ≫ (Γ J A).map g) = ΓHomEquiv.symm f ≫ g.val :=
  (congrArg _ ((constantSheafΓAdj J A).homEquiv_naturality_right_symm _ _)).trans
    ((sheafificationAdjunction J A).homEquiv_naturality_right _ _)

/-- The cone over a given sheaf whose cone point are the global sections and whose components are
the restriction maps. -/
@[simps pt]
noncomputable def Sheaf.coneΓ [HasGlobalSectionsFunctor J A] (F : Sheaf J A) : Cone F.val where
  pt := (Γ J A).obj F
  π := ΓHomEquiv.symm (𝟙 _)

/-- The global sections cone `Sheaf.coneΓ` is limiting - that is, global sections are limits even
when not all limits of shape `Cᵒᵖ` exist in `A`. -/
noncomputable def Sheaf.isLimitConeΓ [HasGlobalSectionsFunctor J A] (F : Sheaf J A) :
    IsLimit F.coneΓ where
  lift c := F.ΓHomEquiv c.π
  fac c j := by
    suffices h : ((Functor.const Cᵒᵖ).map (ΓHomEquiv c.π)) ≫ F.coneΓ.π = c.π from congr_app h j
    simp [coneΓ, ← ΓHomEquiv_naturality_left_symm]
  uniq c f hf := by
    replace hf : ((Functor.const Cᵒᵖ).map f) ≫ F.coneΓ.π = c.π := by ext j; exact hf j
    simpa [coneΓ, ← ΓHomEquiv_naturality_left_symm, Equiv.symm_apply_eq] using hf

/-- The restriction map from global sections of `F` to sections on `U`. -/
noncomputable def Sheaf.ΓRes [HasGlobalSectionsFunctor J A] (F : Sheaf J A) (U : Cᵒᵖ) :
    (Γ J A).obj F ⟶ F.val.obj U :=
  F.coneΓ.π.app U

@[reassoc (attr := simp)]
lemma Sheaf.ΓRes_map [HasGlobalSectionsFunctor J A] (F : Sheaf J A) {V U : Cᵒᵖ} (f : U ⟶ V) :
    F.ΓRes U ≫ F.val.map f = F.ΓRes V :=
  F.coneΓ.w f

@[simp]
lemma Sheaf.coneΓ_π_app [HasGlobalSectionsFunctor J A] (F : Sheaf J A) (U : Cᵒᵖ) :
    F.coneΓ.π.app U = F.ΓRes U := rfl

lemma Sheaf.ΓRes_naturality [HasGlobalSectionsFunctor J A] {F G : Sheaf J A} (f : F ⟶ G) (U : Cᵒᵖ) :
    (Γ J A).map f ≫ ΓRes G U = ΓRes F U ≫ f.val.app U := by
  refine .trans ?_ <| congr_app (ΓHomEquiv_naturality_right_symm _ _) U
  exact (congr_app (ΓHomEquiv_naturality_left_symm ((Γ J A).map f) (𝟙 _)) U).symm.trans (by simp)

variable (J A)

/-- The natural transformation from the global sections functor to the sections functor on any
object `U`. -/
@[simps!]
noncomputable def Sheaf.natTransΓRes [HasGlobalSectionsFunctor J A] (U : Cᵒᵖ) :
    Γ J A ⟶ (sheafSections J A).obj U where
  app F := ΓRes F U
  naturality _ _ f := ΓRes_naturality f U

-- this is currently needed to obtain the instance `HasSheafify J (Type max u v)`.
attribute [local instance] CategoryTheory.Types.instConcreteCategory
attribute [local instance] CategoryTheory.Types.instFunLike

/-- Global sections of a sheaf of types correspond to sections of the underlying presheaf. -/
noncomputable def Sheaf.ΓObjEquivSections [HasWeakSheafify J (Type w)]
    [HasGlobalSectionsFunctor J (Type w)] (F : Sheaf J (Type w)) :
      (Γ J (Type w)).obj F ≃ F.val.sections :=
  (Equiv.trans (by exact (Equiv.funUnique PUnit _).symm) ΓHomEquiv.symm).trans
    (F.val.sectionsEquivHom PUnit).symm

lemma Sheaf.ΓObjEquivSections_naturality [HasWeakSheafify J (Type w)]
    [HasGlobalSectionsFunctor J (Type w)] {F G : Sheaf J (Type w)} (f : F ⟶ G) (x : (Γ J _).obj F) :
    (ΓObjEquivSections J G) ((Γ J _).map f x) =
      (Functor.sectionsFunctor _).map f.val ((ΓObjEquivSections J F) x) := by
  dsimp [ΓObjEquivSections]
  exact (congr_arg _ (ΓHomEquiv_naturality_right_symm _ _)).trans
    (Functor.sectionsEquivHom_naturality_symm _ _ _)

lemma Sheaf.ΓObjEquivSections_naturality_symm [HasWeakSheafify J (Type w)]
    [HasGlobalSectionsFunctor J (Type w)] {F G : Sheaf J (Type w)} (f : F ⟶ G)
    (x : F.val.sections) : (ΓObjEquivSections J G).symm ((Functor.sectionsFunctor _).map f.val x) =
      (Γ J _).map f ((ΓObjEquivSections J F).symm x) :=
  congr_fun (ΓHomEquiv_naturality_right (F.val.sectionsEquivHom _ x) f) _

/-- For sheaves of types, the global sections functor is isomorphic to the sections functor
on presheaves. -/
noncomputable def Sheaf.ΓNatIsoSectionsFunctor :
    Γ J (Type max u v) ≅ sheafToPresheaf J _ ⋙ Functor.sectionsFunctor _ :=
  NatIso.ofComponents (fun F ↦ (ΓObjEquivSections J F).toIso) fun f ↦ by
    ext x
    exact ΓObjEquivSections_naturality J f x

/-- Global sections of a sheaf of types `F` correspond to morphisms from a terminal sheaf to `F`.
We use the constant sheaf on a singleton type as a specific choice of terminal sheaf here. -/
noncomputable def Sheaf.ΓObjEquivHom [HasWeakSheafify J (Type w)]
    [HasGlobalSectionsFunctor J (Type w)] (F : Sheaf J (Type w)) (X : Type w) [Unique X]:
      (Γ J (Type w)).obj F ≃ ((constantSheaf J (Type w)).obj X ⟶ F) :=
  (Equiv.funUnique X _).symm.trans ((constantSheafΓAdj J (Type w)).homEquiv _ _).symm

lemma Sheaf.ΓObjEquivHom_naturality [HasWeakSheafify J (Type w)]
    [HasGlobalSectionsFunctor J (Type w)] (X : Type w) [Unique X] {F G : Sheaf J (Type w)}
    (f : F ⟶ G) (x : (Γ J _).obj F) :
    (ΓObjEquivHom J G X) ((Γ J _).map f x) = (ΓObjEquivHom J F X) x ≫ f :=
  (constantSheafΓAdj J _).homEquiv_naturality_right_symm _ _

lemma Sheaf.ΓObjEquivHom_naturality_symm [HasWeakSheafify J (Type w)]
    [HasGlobalSectionsFunctor J (Type w)] {X : Type w} [Unique X] {F G : Sheaf J (Type w)}
    (f : F ⟶ G) (x : (constantSheaf J _).obj X ⟶ F) :
    (ΓObjEquivHom J G X).symm (x ≫ f) = (Γ J _).map f ((ΓObjEquivHom J F X).symm x) :=
  congr_fun ((constantSheafΓAdj J _).homEquiv_naturality_right x f) default

/-- For sheaves of types, the global sections functor is isomorphic to the covariant hom
functor of the terminal sheaf. -/
noncomputable def Sheaf.ΓNatIsoCoyoneda (X : Type max u v) [Unique X] :
    Γ J (Type max u v) ≅ coyoneda.obj (op ((constantSheaf J _).obj X)) :=
  NatIso.ofComponents (fun F ↦ (F.ΓObjEquivHom J X).toIso) fun f ↦ by
    ext x
    exact ΓObjEquivHom_naturality J X f x

end CategoryTheory
