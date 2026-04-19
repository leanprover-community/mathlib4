/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Sheaves of modules over a sheaf of rings

In this file, we define the category `SheafOfModules R` when `R : Sheaf J RingCat`
is a sheaf of rings on a category `C` equipped with a Grothendieck topology `J`.

-/

@[expose] public section

universe v v₁ u₁ u w

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

/-- A sheaf of modules is a presheaf of modules such that the underlying presheaf
of abelian groups is a sheaf. -/
structure SheafOfModules where
  /-- the underlying presheaf of modules of a sheaf of modules -/
  val : PresheafOfModules.{v} R.obj
  isSheaf : Presheaf.IsSheaf J val.presheaf

namespace SheafOfModules

variable {R}

/-- A morphism between sheaves of modules is a morphism between the underlying
presheaves of modules. -/
@[ext]
structure Hom (X Y : SheafOfModules.{v} R) where
  /-- a morphism between the underlying presheaves of modules -/
  val : X.val ⟶ Y.val

instance : Category (SheafOfModules.{v} R) where
  Hom := Hom
  id _ := ⟨𝟙 _⟩
  comp f g := ⟨f.val ≫ g.val⟩

@[ext]
lemma hom_ext {X Y : SheafOfModules.{v} R} {f g : X ⟶ Y} (h : f.val = g.val) : f = g :=
  Hom.ext h

@[simp]
lemma id_val (X : SheafOfModules.{v} R) : Hom.val (𝟙 X) = 𝟙 X.val := rfl

@[simp, reassoc]
lemma comp_val {X Y Z : SheafOfModules.{v} R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).val = f.val ≫ g.val := rfl

variable (R)
/-- The forgetful functor `SheafOfModules.{v} R ⥤ PresheafOfModules R.val`. -/
@[simps]
def forget : SheafOfModules.{v} R ⥤ PresheafOfModules R.obj where
  obj F := F.val
  map φ := φ.val

/-- The forget functor `SheafOfModules R ⥤ PresheafOfModules R.val` is fully faithful. -/
@[simps]
def fullyFaithfulForget : (forget.{v} R).FullyFaithful where
  preimage φ := ⟨φ⟩

instance : (forget.{v} R).Faithful := (fullyFaithfulForget R).faithful

instance : (forget.{v} R).Full := (fullyFaithfulForget R).full

instance : (forget.{v} R).ReflectsIsomorphisms := (fullyFaithfulForget R).reflectsIsomorphisms

/-- Evaluation on an object `X` gives a functor
`SheafOfModules R ⥤ ModuleCat (R.val.obj X)`. -/
def evaluation (X : Cᵒᵖ) : SheafOfModules.{v} R ⥤ ModuleCat.{v} (R.obj.obj X) :=
  forget _ ⋙ PresheafOfModules.evaluation _ X

/-- The forget functor `SheafOfModules R ⥤ Sheaf J AddCommGrpCat`. -/
@[simps]
noncomputable def toSheaf : SheafOfModules.{v} R ⥤ Sheaf J AddCommGrpCat.{v} where
  obj M := ⟨_, M.isSheaf⟩
  map f := { hom := (forget R ⋙ PresheafOfModules.toPresheaf R.obj).map f }

/--
The forgetful functor from sheaves of modules over sheaf of ring `R` to sheaves of `R(X)`-module
when `X` is initial.
-/
@[simps]
noncomputable def forgetToSheafModuleCat
      (X : Cᵒᵖ) (hX : Limits.IsInitial X) :
    SheafOfModules.{w} R ⥤ Sheaf J (ModuleCat.{w} (R.1.obj X)) where
  obj M := ⟨(PresheafOfModules.forgetToPresheafModuleCat X hX).obj M.1,
    Presheaf.isSheaf_of_isSheaf_comp _ _
      (forget₂ (ModuleCat.{w} (R.1.obj X)) AddCommGrpCat.{w}) M.isSheaf⟩
  map f := { hom := (PresheafOfModules.forgetToPresheafModuleCat X hX).map f.1 }

/-- The canonical isomorphism between
`SheafOfModules.toSheaf R ⋙ sheafToPresheaf J AddCommGrpCat.{v}`
and `SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.val`. -/
noncomputable def toSheafCompSheafToPresheafIso :
    toSheaf R ⋙ sheafToPresheaf J AddCommGrpCat.{v} ≅
      forget R ⋙ PresheafOfModules.toPresheaf R.obj := Iso.refl _

instance : (toSheaf.{v} R).Faithful :=
  Functor.Faithful.of_comp_iso (toSheafCompSheafToPresheafIso.{v} R)

instance (M N : SheafOfModules.{v} R) : AddCommGroup (M ⟶ N) :=
  (fullyFaithfulForget R).homEquiv.addCommGroup

@[simp]
lemma add_val {M N : SheafOfModules.{v} R} (f g : M ⟶ N) :
    (f + g).val = f.val + g.val := rfl

instance : Preadditive (SheafOfModules.{v} R) where
  add_comp := by intros; ext1; dsimp; simp only [Preadditive.add_comp]
  comp_add := by tauto

instance : (forget R).Additive where

instance : (toSheaf R).Additive where

open ZeroObject Limits in
instance : HasZeroObject (SheafOfModules.{v} R) where
  zero := ⟨⟨0, fun M _ _ _ ↦ by
    letI (X : Cᵒᵖ) : Unique ((PresheafOfModules.presheaf (R := R.obj) 0 ⋙
      coyoneda.obj (Opposite.op M)).obj X) :=
      isTerminalEquivUnique _ _ (Limits.IsZero.isTerminal
        ((Functor.map_isZero (PresheafOfModules.toPresheaf R.obj)
          (isZero_zero _)).obj _)) _
    exact Presieve.IsSheafFor.ofUnique⟩, by
    rw [IsZero.iff_id_eq_zero]
    cat_disch⟩

variable {R}

/-- The type of sections of a sheaf of modules. -/
abbrev sections (M : SheafOfModules.{v} R) : Type _ := M.val.sections

/-- The map `M.sections → N.sections` induced by a morphism `M ⟶ N` of sheaves of modules. -/
abbrev sectionsMap {M N : SheafOfModules.{v} R} (f : M ⟶ N) (s : M.sections) : N.sections :=
  PresheafOfModules.sectionsMap f.val s

@[simp]
lemma sectionsMap_comp {M N P : SheafOfModules.{v} R} (f : M ⟶ N) (g : N ⟶ P) (s : M.sections) :
    sectionsMap (f ≫ g) s = sectionsMap g (sectionsMap f s) := rfl

@[simp]
lemma sectionsMap_id {M : SheafOfModules.{v} R} (s : M.sections) :
    sectionsMap (𝟙 M) s = s := rfl

variable (R) in
/-- The functor which sends a sheaf of modules to its type of sections. -/
@[simps]
def sectionsFunctor : SheafOfModules.{v} R ⥤ Type _ where
  obj M := M.sections
  map f := TypeCat.ofHom (sectionsMap f)

variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

variable (R) in
/-- The obvious free sheaf of modules of rank `1`. -/
@[simps]
noncomputable def unit : SheafOfModules R where
  val := PresheafOfModules.unit R.obj
  isSheaf := ((sheafCompose J (forget₂ RingCat.{u} AddCommGrpCat.{u})).obj R).property

/-- The bijection `(unit R ⟶ M) ≃ M.sections` for `M : SheafOfModules R`. -/
noncomputable def unitHomEquiv (M : SheafOfModules R) :
    (unit R ⟶ M) ≃ M.sections :=
  (fullyFaithfulForget R).homEquiv.trans M.val.unitHomEquiv

@[simp]
lemma unitHomEquiv_apply_coe (M : SheafOfModules R) (f : unit R ⟶ M) (X : Cᵒᵖ) :
    (M.unitHomEquiv f).val X = f.val.app X (1 : R.obj.obj X) := rfl

lemma unitHomEquiv_comp_apply {M N : SheafOfModules.{u} R}
    (f : unit R ⟶ M) (p : M ⟶ N) :
    N.unitHomEquiv (f ≫ p) = sectionsMap p (M.unitHomEquiv f) := rfl

lemma unitHomEquiv_symm_comp {M N : SheafOfModules.{u} R} (s : M.sections) (p : M ⟶ N) :
    M.unitHomEquiv.symm s ≫ p = N.unitHomEquiv.symm (sectionsMap p s) :=
  N.unitHomEquiv.injective (by simp [unitHomEquiv_comp_apply])

end SheafOfModules

namespace PresheafOfModules

variable (J)
variable {R : Cᵒᵖ ⥤ RingCat.{u}} {M₁ M₂ : PresheafOfModules.{v} R} (f : M₁ ⟶ M₂)

/-- A morphism of presheaves of modules is locally surjective
if the underlying morphism of presheaves of abelian groups is. -/
abbrev IsLocallySurjective : Prop :=
  Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R).map f)

/-- A morphism of presheaves of modules is locally injective
if the underlying morphism of presheaves of abelian groups is. -/
abbrev IsLocallyInjective : Prop :=
  Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf R).map f)

variable {N : PresheafOfModules.{v} R} (hN : Presheaf.IsSheaf J N.presheaf)
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [IsLocallySurjective J f] [IsLocallyInjective J f]

variable {J}

set_option backward.isDefEq.respectTransparency false in
/-- The bijection `(M₂ ⟶ N) ≃ (M₁ ⟶ N)` induced by a locally bijective morphism
`f : M₁ ⟶ M₂` of presheaves of modules, when `N` is a sheaf. -/
@[simps]
noncomputable def homEquivOfIsLocallyBijective : (M₂ ⟶ N) ≃ (M₁ ⟶ N) where
  toFun φ := f ≫ φ
  invFun ψ := homMk (((J.W_of_isLocallyBijective
      ((PresheafOfModules.toPresheaf R).map f)).homEquiv _ hN).symm
      ((PresheafOfModules.toPresheaf R).map ψ)) (by
        obtain ⟨φ, hφ⟩ := ((J.W_of_isLocallyBijective
          ((PresheafOfModules.toPresheaf R).map f)).homEquiv _ hN).surjective
          ((PresheafOfModules.toPresheaf R).map ψ)
        simp only [← hφ, Equiv.symm_apply_apply]
        replace hφ : ∀ (Z : Cᵒᵖ) (x : M₁.obj Z), φ.app Z (f.app Z x) = ψ.app Z x :=
          fun Z x ↦ CategoryTheory.congr_fun (congr_app hφ Z) x
        intro X r y
        apply hN.isSeparated _ _
          (Presheaf.imageSieve_mem J ((toPresheaf R).map f) y)
        rintro Y p ⟨x : M₁.obj _, hx : f.app _ x = M₂.map p.op y⟩
        have hφ' : ∀ (z : M₂.obj X), φ.app _ (M₂.map p.op z) =
            N.map p.op (φ.app _ z) := CategoryTheory.congr_fun (φ.naturality p.op)
        change N.map p.op (φ.app X (r • y)) = N.map p.op (r • φ.app X y)
        rw [← hφ', M₂.map_smul, ← hx, ← (f.app _).hom.map_smul, hφ, (ψ.app _).hom.map_smul,
          ← hφ, hx, N.map_smul, hφ'])
  left_inv φ := (toPresheaf _).map_injective
    (((J.W_of_isLocallyBijective
      ((PresheafOfModules.toPresheaf R).map f)).homEquiv _ hN).left_inv
      ((PresheafOfModules.toPresheaf R).map φ))
  right_inv ψ := (toPresheaf _).map_injective
    (((J.W_of_isLocallyBijective
      ((PresheafOfModules.toPresheaf R).map f)).homEquiv _ hN).right_inv
      ((PresheafOfModules.toPresheaf R).map ψ))

end PresheafOfModules
