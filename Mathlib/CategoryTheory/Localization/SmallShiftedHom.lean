/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.SmallHom
import Mathlib.CategoryTheory.Shift.ShiftedHom
import Mathlib.CategoryTheory.Shift.Localization

/-!
# Shrinking morphisms in localized categories equipped with shifts

If `C` is a category equipped with a shift by an additive monoid `M`,
and `W : MorphismProperty C` is compatible with the shift,
we define a type-class `HasSmallLocalizedShiftedHom.{w} W X Y` which
says that all the types of morphisms from `X⟦a⟧` to `Y⟦b⟧` in the
localized category are `w`-small for a certain universe. Then,
we define types `SmallShiftedHom.{w} W X Y m : Type w` for all `m : M`,
and endow these with a composition which transports the composition
on the types `ShiftedHom (L.obj X) (L.obj Y) m` when `L : C ⥤ D` is
any localization functor for `W`.

-/

universe w'' w w' v₁ v₂ v₁' v₂' u₁ u₂ u₁' u₂'

namespace CategoryTheory

open Category

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (W : MorphismProperty C) {M : Type w'} [AddMonoid M] [HasShift C M] [HasShift D M]

namespace Localization

section

variable (X Y : C)
variable (M)

/-- Given objects `X` and `Y` in a category `C`, this is the property that
all the types of morphisms from `X⟦a⟧` to `Y⟦b⟧` are `w`-small
in the localized category with respect to a class of morphisms `W`. -/
abbrev HasSmallLocalizedShiftedHom : Prop :=
  ∀ (a b : M), HasSmallLocalizedHom.{w} W (X⟦a⟧) (Y⟦b⟧)

lemma hasSmallLocalizedShiftedHom_iff
    (L : C ⥤ D) [L.IsLocalization W] [L.CommShift M] (X Y : C) :
    HasSmallLocalizedShiftedHom.{w} W M X Y ↔
      ∀ (a b : M), Small.{w} ((L.obj X)⟦a⟧ ⟶ (L.obj Y)⟦b⟧) := by
  dsimp [HasSmallLocalizedShiftedHom]
  have eq := fun (a b : M) ↦ small_congr.{w}
    (Iso.homCongr ((L.commShiftIso a).app X) ((L.commShiftIso b).app Y))
  dsimp at eq
  simp only [hasSmallLocalizedHom_iff _ L, eq]

variable {Y} in
lemma hasSmallLocalizedShiftedHom_iff_target [W.IsCompatibleWithShift M]
    {Y' : C} (f : Y ⟶ Y') (hf : W f) :
    HasSmallLocalizedShiftedHom.{w} W M X Y ↔ HasSmallLocalizedShiftedHom.{w} W M X Y' :=
  forall_congr' (fun a ↦ forall_congr' (fun b ↦
    hasSmallLocalizedHom_iff_target W (X⟦a⟧) (f⟦b⟧') (W.shift hf b)))

variable {X} in
lemma hasSmallLocalizedShiftedHom_iff_source [W.IsCompatibleWithShift M]
    {X' : C} (f : X ⟶ X') (hf : W f) (Y : C) :
    HasSmallLocalizedShiftedHom.{w} W M X Y ↔ HasSmallLocalizedShiftedHom.{w} W M X' Y :=
  forall_congr' (fun a ↦ forall_congr' (fun b ↦
    hasSmallLocalizedHom_iff_source W (f⟦a⟧') (W.shift hf a) (Y⟦b⟧)))

variable [HasSmallLocalizedShiftedHom.{w} W M X Y]

include M in
lemma hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₀ :
    HasSmallLocalizedHom.{w} W X Y :=
  (hasSmallLocalizedHom_iff_of_isos W
    ((shiftFunctorZero C M).app X) ((shiftFunctorZero C M).app Y)).1 inferInstance

variable {M}

instance (m : M) : HasSmallLocalizedHom.{w} W X (Y⟦m⟧) :=
  (hasSmallLocalizedHom_iff_of_isos W
    ((shiftFunctorZero C M).app X) (Iso.refl (Y⟦m⟧))).1 inferInstance

instance (m : M) : HasSmallLocalizedHom.{w} W (X⟦m⟧) Y :=
  (hasSmallLocalizedHom_iff_of_isos W
    (Iso.refl (X⟦m⟧)) ((shiftFunctorZero C M).app Y)).1 inferInstance

instance (m m' n : M) : HasSmallLocalizedHom.{w} W (X⟦m⟧⟦m'⟧) (Y⟦n⟧) :=
  (hasSmallLocalizedHom_iff_of_isos W
    ((shiftFunctorAdd C m m').app X) (Iso.refl (Y⟦n⟧))).1 inferInstance

instance (m n n' : M) : HasSmallLocalizedHom.{w} W (X⟦m⟧) (Y⟦n⟧⟦n'⟧) :=
  (hasSmallLocalizedHom_iff_of_isos W
    (Iso.refl (X⟦m⟧)) ((shiftFunctorAdd C n n').app Y)).1 inferInstance

end

namespace SmallHom

variable {W}
variable [W.IsCompatibleWithShift M] (L : C ⥤ D) [L.IsLocalization W] [L.CommShift M]
  {X Y : C} [HasSmallLocalizedHom.{w} W X Y]
  (f : SmallHom.{w} W X Y) (a : M) [HasSmallLocalizedHom.{w} W (X⟦a⟧) (Y⟦a⟧)]

/-- Given `f : SmallHom W X Y` and `a : M`, this is the element
in `SmallHom W (X⟦a⟧) (Y⟦a⟧)` obtained by shifting by `a`. -/
noncomputable def shift : SmallHom.{w} W (X⟦a⟧) (Y⟦a⟧) :=
  (W.shiftLocalizerMorphism a).smallHomMap f

lemma equiv_shift : equiv W L (f.shift a) =
    (L.commShiftIso a).hom.app X ≫ (equiv W L f)⟦a⟧' ≫ (L.commShiftIso a).inv.app Y :=
  (W.shiftLocalizerMorphism a).equiv_smallHomMap _ _ _ (L.commShiftIso a) f

end SmallHom

/-- The type of morphisms from `X` to `Y⟦m⟧` in the localized category
with respect to `W : MorphismProperty C` that is shrunk to `Type w`
when `HasSmallLocalizedShiftedHom.{w} W X Y` holds. -/
def SmallShiftedHom (X Y : C) [HasSmallLocalizedShiftedHom.{w} W M X Y] (m : M) : Type w :=
  SmallHom W X (Y⟦m⟧)

namespace SmallShiftedHom

section

variable {W}
variable [W.IsCompatibleWithShift M]
variable {X Y Z : C}

/-- Given `f : SmallShiftedHom.{w} W X Y a`, this is the element in
`SmallHom.{w} W (X⟦n⟧) (Y⟦a'⟧)` that is obtained by shifting by `n`
when `a + n = a'`. -/
noncomputable def shift {a : M} [HasSmallLocalizedShiftedHom.{w} W M X Y]
    [HasSmallLocalizedShiftedHom.{w} W M Y Y]
    (f : SmallShiftedHom.{w} W X Y a) (n a' : M) (h : a + n = a') :
    SmallHom.{w} W (X⟦n⟧) (Y⟦a'⟧) :=
  (SmallHom.shift f n).comp (SmallHom.mk W ((shiftFunctorAdd' C a n a' h).inv.app Y))

/-- The composition on `SmallShiftedHom W`. -/
noncomputable def comp {a b c : M} [HasSmallLocalizedShiftedHom.{w} W M X Y]
    [HasSmallLocalizedShiftedHom.{w} W M Y Z] [HasSmallLocalizedShiftedHom.{w} W M X Z]
    [HasSmallLocalizedShiftedHom.{w} W M Z Z]
    (f : SmallShiftedHom.{w} W X Y a) (g : SmallShiftedHom.{w} W Y Z b) (h : b + a = c) :
    SmallShiftedHom.{w} W X Z c :=
  SmallHom.comp f (g.shift a c h)

variable (W) in
/-- The canonical map `(X ⟶ Y) → SmallShiftedHom.{w} W X Y m₀` when `m₀ = 0` and
`[HasSmallLocalizedShiftedHom.{w} W M X Y]` holds. -/
noncomputable def mk₀ [HasSmallLocalizedShiftedHom.{w} W M X Y]
    (m₀ : M) (hm₀ : m₀ = 0) (f : X ⟶ Y) :
    SmallShiftedHom.{w} W X Y m₀ :=
  SmallHom.mk W (f ≫ (shiftFunctorZero' C m₀ hm₀).inv.app Y)

end

section

variable (L : C ⥤ D) [L.IsLocalization W] [L.CommShift M]
  {X Y Z T : C}

/-- The bijection `SmallShiftedHom.{w} W X Y m ≃ ShiftedHom (L.obj X) (L.obj Y) m`
for all `m : M`, and `X` and `Y` in `C` when `L : C ⥤ D` is a localization functor for
`W : MorphismProperty C` such that the category `D` is equipped with a shift by `M`
and `L` commutes with the shifts. -/
noncomputable def equiv [HasSmallLocalizedShiftedHom.{w} W M X Y] {m : M} :
    SmallShiftedHom.{w} W X Y m ≃ ShiftedHom (L.obj X) (L.obj Y) m :=
  (SmallHom.equiv W L).trans ((L.commShiftIso m).app Y).homToEquiv

section
variable [W.IsCompatibleWithShift M]

lemma equiv_shift' {a : M} [HasSmallLocalizedShiftedHom.{w} W M X Y]
    [HasSmallLocalizedShiftedHom.{w} W M Y Y]
    (f : SmallShiftedHom.{w} W X Y a) (n a' : M) (h : a + n = a') :
    SmallHom.equiv W L (f.shift n a' h) = (L.commShiftIso n).hom.app X ≫
      (SmallHom.equiv W L f)⟦n⟧' ≫ ((L.commShiftIso a).hom.app Y)⟦n⟧' ≫
        (shiftFunctorAdd' D a n a' h).inv.app (L.obj Y) ≫ (L.commShiftIso a').inv.app Y := by
  simp only [shift, SmallHom.equiv_comp, SmallHom.equiv_shift, SmallHom.equiv_mk, assoc,
    L.commShiftIso_add' h, Functor.CommShift.isoAdd'_inv_app, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.comp_obj, comp_id]

lemma equiv_shift {a : M} [HasSmallLocalizedShiftedHom.{w} W M X Y]
    [HasSmallLocalizedShiftedHom.{w} W M Y Y]
    (f : SmallShiftedHom.{w} W X Y a) (n a' : M) (h : a + n = a') :
    equiv W L (f.shift n a' h) = (L.commShiftIso n).hom.app X ≫ (equiv W L f)⟦n⟧' ≫
      (shiftFunctorAdd' D a n a' h).inv.app (L.obj Y) := by
  dsimp [equiv]
  erw [Iso.homToEquiv_apply, Iso.homToEquiv_apply, equiv_shift']
  simp only [Functor.comp_obj, Iso.app_hom, assoc, Iso.inv_hom_id_app, comp_id, Functor.map_comp]
  rfl

lemma equiv_comp [HasSmallLocalizedShiftedHom.{w} W M X Y]
    [HasSmallLocalizedShiftedHom.{w} W M Y Z] [HasSmallLocalizedShiftedHom.{w} W M X Z]
    [HasSmallLocalizedShiftedHom.{w} W M Z Z] {a b c : M}
    (f : SmallShiftedHom.{w} W X Y a) (g : SmallShiftedHom.{w} W Y Z b) (h : b + a = c) :
    equiv W L (f.comp g h) = (equiv W L f).comp (equiv W L g) h := by
  dsimp [comp, equiv, ShiftedHom.comp]
  erw [Iso.homToEquiv_apply, Iso.homToEquiv_apply, Iso.homToEquiv_apply, SmallHom.equiv_comp]
  simp only [equiv_shift', Functor.comp_obj, Iso.app_hom, assoc, Iso.inv_hom_id_app,
    comp_id, Functor.map_comp]
  rfl

end

@[simp]
lemma equiv_mk₀ [HasSmallLocalizedShiftedHom.{w} W M X Y]
    (m₀ : M) (hm₀ : m₀ = 0) (f : X ⟶ Y) :
    equiv W L (SmallShiftedHom.mk₀ W m₀ hm₀ f) =
      ShiftedHom.mk₀ m₀ hm₀ (L.map f) := by
  subst hm₀
  dsimp [equiv, mk₀]
  erw [SmallHom.equiv_mk, Iso.homToEquiv_apply, Functor.map_comp]
  dsimp [equiv, mk₀, ShiftedHom.mk₀, shiftFunctorZero']
  simp only [comp_id, L.commShiftIso_zero, Functor.CommShift.isoZero_hom_app, assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.id_obj, Functor.map_id, id_comp]

end

section

variable [W.IsCompatibleWithShift M]

lemma comp_assoc {X Y Z T : C} {a₁ a₂ a₃ a₁₂ a₂₃ a : M}
    [HasSmallLocalizedShiftedHom.{w} W M X Y] [HasSmallLocalizedShiftedHom.{w} W M X Z]
    [HasSmallLocalizedShiftedHom.{w} W M X T] [HasSmallLocalizedShiftedHom.{w} W M Y Z]
    [HasSmallLocalizedShiftedHom.{w} W M Y T] [HasSmallLocalizedShiftedHom.{w} W M Z T]
    [HasSmallLocalizedShiftedHom.{w} W M Z Z] [HasSmallLocalizedShiftedHom.{w} W M T T]
    (α : SmallShiftedHom.{w} W X Y a₁) (β : SmallShiftedHom.{w} W Y Z a₂)
    (γ : SmallShiftedHom.{w} W Z T a₃)
    (h₁₂ : a₂ + a₁ = a₁₂) (h₂₃ : a₃ + a₂ = a₂₃) (h : a₃ + a₂ + a₁ = a) :
    (α.comp β h₁₂).comp γ (show a₃ + a₁₂ = a by rw [← h₁₂, ← add_assoc, h]) =
      α.comp (β.comp γ h₂₃) (by rw [← h₂₃, h]) := by
  apply (equiv W W.Q).injective
  simp only [equiv_comp, ShiftedHom.comp_assoc _ _ _ h₁₂ h₂₃ h]

end

section ChangeOfUniverse

variable {W}

/-- Up to an equivalence, the type `SmallShiftedHom.{w} W X Y m` does
not depend on the universe `w`. -/
noncomputable def chgUniv {X Y : C} {m : M}
    [HasSmallLocalizedShiftedHom.{w} W M X Y]
    [HasSmallLocalizedShiftedHom.{w''} W M X Y] :
    SmallShiftedHom.{w} W X Y m ≃ SmallShiftedHom.{w''} W X Y m :=
  SmallHom.chgUniv

lemma equiv_chgUniv (L : C ⥤ D) [L.IsLocalization W] [L.CommShift M] {X Y : C} {m : M}
    [HasSmallLocalizedShiftedHom.{w} W M X Y]
    [HasSmallLocalizedShiftedHom.{w''} W M X Y]
    (e : SmallShiftedHom.{w} W X Y m) :
    equiv W L (chgUniv.{w''} e) = equiv W L e := by
  dsimp [equiv]
  congr
  apply SmallHom.equiv_chgUniv

end ChangeOfUniverse

section Map

end Map

end SmallShiftedHom

end Localization

namespace LocalizerMorphism

open Localization

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {D₁ : Type u₁'} [Category.{v₁'} D₁] {D₂ : Type u₂'} [Category.{v₂'} D₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  (Φ : LocalizerMorphism W₁ W₂)
  (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  {M : Type w'} [AddMonoid M] [HasShift C₁ M] [HasShift C₂ M]
  [HasShift D₁ M] [HasShift D₂ M] [L₁.CommShift M] [L₂.CommShift M]
  [Φ.functor.CommShift M]
  {X₁ Y₁ Z₁ : C₁} {X₂ Y₂ Z₂ : C₂}
  [HasSmallLocalizedShiftedHom.{w} W₁ M X₁ Y₁] [HasSmallLocalizedShiftedHom.{w''} W₂ M X₂ X₂]
  [HasSmallLocalizedShiftedHom.{w''} W₂ M X₂ Y₂] [HasSmallLocalizedShiftedHom.{w''} W₂ M Y₂ Y₂]
  (eX : Φ.functor.obj X₁ ≅ X₂) (eY : Φ.functor.obj Y₁ ≅ Y₂)
  (eZ : Φ.functor.obj Z₁ ≅ Z₂)

/-- The action of a localizer morphism `Φ` on `SmallShiftedHom`. -/
noncomputable def smallShiftedHomMap {m : M} (f : SmallShiftedHom.{w} W₁ X₁ Y₁ m) :
      SmallShiftedHom.{w''} W₂ X₂ Y₂ m :=
  have := hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₀.{w''} W₂ M X₂ X₂
  Φ.smallHomMap' eX ((Φ.functor.commShiftIso m).app Y₁ ≪≫ (shiftFunctor _ _).mapIso eY) f

lemma equiv_smallShiftedHomMap (G : D₁ ⥤ D₂) [G.CommShift M]
    (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G) [NatTrans.CommShift e.hom M]
    {m : M} (f : SmallShiftedHom.{w} W₁ X₁ Y₁ m) :
    SmallShiftedHom.equiv W₂ L₂ (Φ.smallShiftedHomMap eX eY f) =
      (ShiftedHom.mk₀ 0 rfl (L₂.map eX.inv ≫ e.hom.app _)).comp
        (((SmallShiftedHom.equiv W₁ L₁ f).map G).comp
          ((ShiftedHom.mk₀ 0 rfl (e.inv.app _ ≫ L₂.map eY.hom)))
          (zero_add m)) (add_zero m) := by
  have := hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₀.{w''} W₂ M X₂ X₂
  dsimp [smallShiftedHomMap, SmallShiftedHom.equiv]
  erw [Iso.homToEquiv_apply, Iso.homToEquiv_apply,
    Φ.equiv_smallHomMap' L₁ L₂ _ _ G e f]
  simp only [Functor.comp_obj, NatTrans.app_shift, Functor.commShiftIso_comp_hom_app,
    Functor.commShiftIso_comp_inv_app, assoc, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Functor.commShiftIso_hom_naturality, ShiftedHom.map, ShiftedHom.comp_mk₀,
    ShiftedHom.mk₀_comp]
  congr 3
  simp [← Functor.map_comp_assoc, -Functor.map_comp]

end LocalizerMorphism

end CategoryTheory
