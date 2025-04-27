/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
<<<<<<< HEAD
import Mathlib.CategoryTheory.Shift.CommShift
=======
import Mathlib.CategoryTheory.Shift.Adjunction
>>>>>>> origin/jriou_localization_bump_deps
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The pullback of a shift by a monoid morphism

Given a shift by a monoid `B` on a category `C` and a monoid morphism  `φ : A →+ B`,
we define a shift by `A` on a category `PullbackShift C φ` which is a type synonym for `C`.

If `F : C ⥤ D` is a functor between categories equipped with shifts by `B`, we define
a type synonym `PullbackShift.functor F φ` for `F`. When `F` has a `CommShift` structure
by `B`, we define a pulled back `CommShift` structure by `A` on `PullbackShift.functor F φ`.

Similarly, if `τ` is a natural transformation between functors `F,G : C ⥤ D`, we define
a type synonym
`PullbackShift.natTrans τ φ : PullbackShift.functor F φ ⟶ PullbackShift.functor G φ`.
When `τ` has a `CommShift` structure by `B` (i.e. is compatible with `CommShift` structures
on `F` and `G`), we define a pulled back `CommShift` structure by `A` on
`PullbackShift.natTrans τ φ`.

Finally, if we have an adjunction `F ⊣ G` (with `G : D ⥤ C`), we define a type synonym
`PullbackShift.adjunction adj φ : PullbackShift.functor F φ ⊣ PullbackShift.functor G φ`
and we show that, if `adj` compatible with `CommShift` structures
on `F` and `G`, then `PullbackShift.adjunction adj φ` iis also compatible with the pulled back
`CommShift` structures.
-/

namespace CategoryTheory

open Limits Category

variable (C D : Type*) [Category C] [Category D]
  (F : C ⥤ D) {A B : Type*} [AddMonoid A] [AddMonoid B]
  (φ : A →+ B) [HasShift C B] [HasShift D B]

/-- The category `PullbackShift C φ` is equipped with a shift such that for all `a`,
the shift functor by `a` is `shiftFunctor C (φ a)`. -/
@[nolint unusedArguments]
def PullbackShift (_ : A →+ B) [HasShift C B] := C

instance : Category (PullbackShift C φ) := by
  dsimp only [PullbackShift]
  infer_instance

attribute [local instance] endofunctorMonoidalCategory

/-- The shift on `PullbackShift C φ` is obtained by precomposing the shift on `C` with
the monoidal functor `Discrete.addMonoidalFunctor φ : Discrete A ⥤ Discrete B`. -/
noncomputable instance : HasShift (PullbackShift C φ) A where
  shift := Discrete.addMonoidalFunctor φ ⋙ shiftMonoidalFunctor C B

instance [HasZeroObject C] : HasZeroObject (PullbackShift C φ) := by
  dsimp [PullbackShift]
  infer_instance

instance [Preadditive C] : Preadditive (PullbackShift C φ) := by
  dsimp [PullbackShift]
  infer_instance

instance [Preadditive C] (a : A) [(shiftFunctor C (φ a)).Additive] :
    (shiftFunctor (PullbackShift C φ) a).Additive := by
  change (shiftFunctor C (φ a)).Additive
  infer_instance

/-- When `b = φ a`, this is the canonical
isomorphism `shiftFunctor (PullbackShift C φ) a ≅ shiftFunctor C b`. -/
noncomputable def pullbackShiftIso (a : A) (b : B) (h : b = φ a) :
    shiftFunctor (PullbackShift C φ) a ≅ shiftFunctor C b := eqToIso (by subst h; rfl)

variable {C}
variable (X : PullbackShift C φ) (a₁ a₂ a₃ : A) (h : a₁ + a₂ = a₃) (b₁ b₂ b₃ : B)
  (h₁ : b₁ = φ a₁) (h₂ : b₂ = φ a₂) (h₃ : b₃ = φ a₃)

lemma pullbackShiftFunctorZero_inv_app :
    (shiftFunctorZero _ A).inv.app X =
      (shiftFunctorZero C B).inv.app X ≫ (pullbackShiftIso C φ 0 0 (by simp)).inv.app X := by
  change (shiftFunctorZero C B).inv.app X ≫ _ = _
  dsimp [Discrete.eqToHom, Discrete.addMonoidalFunctor_ε]
  congr 2
  apply eqToHom_map

lemma pullbackShiftFunctorZero_hom_app :
    (shiftFunctorZero _ A).hom.app X =
      (pullbackShiftIso C φ 0 0 (by simp)).hom.app X ≫ (shiftFunctorZero C B).hom.app X := by
  rw [← cancel_epi ((shiftFunctorZero _ A).inv.app X), Iso.inv_hom_id_app,
    pullbackShiftFunctorZero_inv_app, assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  rfl

lemma pullbackShiftFunctorZero'_inv_app :
    (shiftFunctorZero _ A).inv.app X = (shiftFunctorZero' C (φ 0) (by rw [map_zero])).inv.app X ≫
      (pullbackShiftIso C φ 0 (φ 0) rfl).inv.app X := by
  rw [pullbackShiftFunctorZero_inv_app]
  simp only [Functor.id_obj, pullbackShiftIso, eqToIso.inv, eqToHom_app, shiftFunctorZero',
    Iso.trans_inv, NatTrans.comp_app, eqToIso_refl, Iso.refl_inv, NatTrans.id_app, assoc]
  erw [comp_id]

lemma pullbackShiftFunctorZero'_hom_app :
    (shiftFunctorZero _ A).hom.app X = (pullbackShiftIso C φ 0 (φ 0) rfl).hom.app X ≫
      (shiftFunctorZero' C (φ 0) (by rw [map_zero])).hom.app X := by
  rw [← cancel_epi ((shiftFunctorZero _ A).inv.app X), Iso.inv_hom_id_app,
    pullbackShiftFunctorZero'_inv_app, assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  rfl

lemma pullbackShiftFunctorAdd'_inv_app :
    (shiftFunctorAdd' _ a₁ a₂ a₃ h).inv.app X =
      (shiftFunctor (PullbackShift C φ) a₂).map ((pullbackShiftIso C φ a₁ b₁ h₁).hom.app X) ≫
        (pullbackShiftIso C φ a₂ b₂ h₂).hom.app _ ≫
        (shiftFunctorAdd' C b₁ b₂ b₃ (by rw [h₁, h₂, h₃, ← h, φ.map_add])).inv.app X ≫
        (pullbackShiftIso C φ a₃ b₃ h₃).inv.app X := by
  subst h₁ h₂ h
  obtain rfl : b₃ = φ a₁ + φ a₂ := by rw [h₃, φ.map_add]
  simp only [Functor.comp_obj, NatTrans.naturality_assoc]
  erw [Functor.map_id, id_comp, id_comp, shiftFunctorAdd'_eq_shiftFunctorAdd,
    shiftFunctorAdd'_eq_shiftFunctorAdd]
  change _ ≫ _ = _
  congr 1
  rw [Discrete.addMonoidalFunctor_μ]
  dsimp [Discrete.eqToHom]
  congr 2
  apply eqToHom_map

lemma pullbackShiftFunctorAdd'_hom_app :
    (shiftFunctorAdd' _ a₁ a₂ a₃ h).hom.app X =
      (pullbackShiftIso C φ a₃ b₃ h₃).hom.app X ≫
      (shiftFunctorAdd' C b₁ b₂ b₃ (by rw [h₁, h₂, h₃, ← h, φ.map_add])).hom.app X ≫
      (pullbackShiftIso C φ a₂ b₂ h₂).inv.app _ ≫
      (shiftFunctor (PullbackShift C φ) a₂).map ((pullbackShiftIso C φ a₁ b₁ h₁).inv.app X) := by
  rw [← cancel_epi ((shiftFunctorAdd' _ a₁ a₂ a₃ h).inv.app X), Iso.inv_hom_id_app,
    pullbackShiftFunctorAdd'_inv_app φ X a₁ a₂ a₃ h b₁ b₂ b₃ h₁ h₂ h₃, assoc, assoc, assoc,
    Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
  rfl

<<<<<<< HEAD
namespace Functor

variable {D}
variable [F.CommShift B]

def pullbackShift : PullbackShift C φ ⥤ PullbackShift D φ := F

namespace pullbackShiftCommShift

def iso (a : A) :
    shiftFunctor (PullbackShift C φ) a ⋙ pullbackShift F φ ≅
      pullbackShift F φ ⋙ shiftFunctor (PullbackShift D φ) a :=
  F.commShiftIso (φ a)

lemma iso_eq (a : A) (b : B) (h : b = φ a) :
    iso F φ a =
      isoWhiskerRight (pullbackShiftIso C φ a b h) _ ≪≫ F.commShiftIso b ≪≫
        isoWhiskerLeft _ (pullbackShiftIso D φ a b h).symm := by
  ext X
  subst h
  dsimp [pullbackShiftIso]
  rw [map_id]
  erw [id_comp, comp_id]
  rfl

end pullbackShiftCommShift

open pullbackShiftCommShift in
instance : (F.pullbackShift φ).CommShift A where
  iso a := iso F φ a
  zero := by
    ext X
    dsimp
    rw [iso_eq F φ 0 0 (by simp), F.commShiftIso_zero, CommShift.isoZero_hom_app]
    dsimp
    rw [CommShift.isoZero_hom_app, assoc,
      pullbackShiftFunctorZero_hom_app, pullbackShiftFunctorZero_inv_app,
      map_comp, assoc]
    rfl
  add a b := by
    ext X
    dsimp
    rw [iso_eq F φ (a + b) (φ a + φ b) (by simp), CommShift.isoAdd_hom_app,
      F.commShiftIso_add]
    dsimp
    simp only [CommShift.isoAdd_hom_app, comp_obj, assoc,
      iso_eq F φ a (φ a) rfl, iso_eq F φ b (φ b) rfl]
    dsimp
    conv_rhs => rw [← shiftFunctorAdd'_eq_shiftFunctorAdd]
    rw [pullbackShiftFunctorAdd'_hom_app φ X a b (a + b) rfl (φ a) (φ b) (φ a + φ b)
      rfl rfl (by simp)]
    conv_rhs => rw [shiftFunctorAdd'_eq_shiftFunctorAdd]
    dsimp
    simp only [map_comp, assoc]
    congr 2
    dsimp [pullbackShiftIso]
    simp only [eqToHom_app, map_id]
    erw [Functor.map_id, Functor.map_id, Functor.map_id, Functor.map_id, Functor.map_id,
      id_comp, id_comp, id_comp, id_comp, id_comp, id_comp]
    congr 2
    conv_rhs => rw [← shiftFunctorAdd'_eq_shiftFunctorAdd]
    erw [pullbackShiftFunctorAdd'_inv_app φ (F.obj X) a b (a + b) rfl (φ a) (φ b) (φ a + φ b)
      rfl rfl (by simp)]
    rw [shiftFunctorAdd'_eq_shiftFunctorAdd]
    dsimp [pullbackShiftIso]
    simp only [map_id, eqToHom_app, id_comp]
    rfl

end Functor

=======
variable {D : Type*} [Category D] [HasShift D B] (F : C ⥤ D) [F.CommShift B]

/--
The functor `F`, seen as a functor from `PullbackShift C φ` to `PullbackShift D φ`.
Then a `CommShift B` instance on `F` will define a `CommShift A` instance on
`PullbackShift.functor F φ`, and we won't have to juggle with two `CommShift` instances
on `F`.
-/
def PullbackShift.functor : PullbackShift C φ ⥤ PullbackShift D φ := F

variable {F} in
/--
The natural transformation `τ`, seen as a natural transformation from `PullbackShift.functor F φ`
to `PullbackShift.functor G φ`. Then a `CommShift B` instance on `τ` will define a `CommShift A`
instance on `PullbackShift.natTrans τ φ`, and we won't have to juggle with two `CommShift`
instances on `τ`.
-/
def PullbackShift.natTrans {G : C ⥤ D} (τ : F ⟶ G) :
    PullbackShift.functor φ F ⟶ PullbackShift.functor φ G := τ

namespace Functor

/-- If `F : C ⥤ D` commutes with the shifts on `C` and `D`, then `PullbackShift.functor F φ`
commutes with their pullbacks by an additive map `φ`.
-/
noncomputable instance commShiftPullback : (PullbackShift.functor φ F).CommShift A where
  iso a := isoWhiskerRight (pullbackShiftIso C φ a (φ a) rfl) F ≪≫
    F.commShiftIso (φ a) ≪≫ isoWhiskerLeft _  (pullbackShiftIso D φ a (φ a) rfl).symm
  zero := by
    ext
    dsimp
    simp only [F.commShiftIso_zero' (A := B) (φ 0) (by rw [map_zero]), CommShift.isoZero'_hom_app,
      assoc, CommShift.isoZero_hom_app, pullbackShiftFunctorZero'_hom_app, map_comp,
      pullbackShiftFunctorZero'_inv_app]
    rfl
  add _ _ := by
    ext
    simp only [PullbackShift.functor, comp_obj, Iso.trans_hom, isoWhiskerRight_hom,
      isoWhiskerLeft_hom, Iso.symm_hom, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      CommShift.isoAdd_hom_app, map_comp, assoc]
    rw [F.commShiftIso_add' (φ.map_add _ _).symm,
      ← shiftFunctorAdd'_eq_shiftFunctorAdd, ← shiftFunctorAdd'_eq_shiftFunctorAdd,
      pullbackShiftFunctorAdd'_hom_app φ _ _ _ _ rfl _ _ _ rfl rfl rfl,
      pullbackShiftFunctorAdd'_inv_app φ _ _ _ _ rfl _ _ _ rfl rfl rfl]
    simp only [CommShift.isoAdd'_hom_app, assoc, map_comp, NatTrans.naturality_assoc,
      Iso.inv_hom_id_app_assoc]
    slice_rhs 9 10 => rw [← map_comp, Iso.inv_hom_id_app, map_id]
    simp only [comp_obj, id_comp]
    rw [← Functor.comp_map F (shiftFunctor D _), ← (F.commShiftIso _).hom.naturality_assoc]
    slice_rhs 4 5 => rw [← map_comp, (pullbackShiftIso C φ _ _ rfl).hom.naturality, map_comp]
    slice_rhs 3 4 => rw [← map_comp, Iso.inv_hom_id_app, map_id]
    simp only [comp_obj, id_comp, comp_map, assoc]
    slice_rhs 3 4 => rw [← map_comp, ← map_comp, Iso.inv_hom_id_app, map_id, map_id]
    rw [id_comp, assoc, assoc]
    rfl

lemma commShiftPullback_iso_eq (a : A) (b : B) (h : b = φ a) :
    (PullbackShift.functor φ F).commShiftIso a (C := PullbackShift C φ) (D := PullbackShift D φ) =
      isoWhiskerRight (pullbackShiftIso C φ a b h) F ≪≫ (F.commShiftIso b) ≪≫
        isoWhiskerLeft F (pullbackShiftIso D φ a b h).symm := by
  obtain rfl : b = φ a := h
  rfl

end Functor

namespace NatTrans

variable {F} {G : C ⥤ D} [G.CommShift B]

open Functor in
instance commShiftPullback (τ : F ⟶ G) [NatTrans.CommShift τ B] :
    NatTrans.CommShift (PullbackShift.natTrans φ τ) A where
  shift_comm _ := by
    ext
    dsimp [PullbackShift.natTrans]
    simp only [commShiftPullback_iso_eq φ _ _ _ rfl, Iso.trans_hom, isoWhiskerRight_hom,
      isoWhiskerLeft_hom, Iso.symm_hom, comp_app, comp_obj, whiskerRight_app, whiskerLeft_app,
      assoc]
    rw [← τ.naturality_assoc]
    simp  [← NatTrans.shift_app_comm_assoc]

variable (C) in
/-- The natural isomorphism between the identity of `PullbackShift C φ` and the
pullback of the identity of `C`.
-/
def PullbackShift.natIsoId : 𝟭 (PullbackShift C φ) ≅ PullbackShift.functor φ (𝟭 C) := Iso.refl _

/--
This expresses the compatibility between two `CommShift` structures by `A` on (synonyms of)
`𝟭 C`: the canonical `CommShift` structure on `𝟭 (PullbackShift C φ)`, and the `CommShift`
structure on `PullbackShift.functor (𝟭 C) φ` (i.e the pullback of the canonical `CommShift`
structure on `𝟭 C`).
-/
instance : NatTrans.CommShift (PullbackShift.natIsoId C φ).hom A where
  shift_comm _ := by
    ext
    simp [PullbackShift.natIsoId, Functor.commShiftPullback_iso_eq]

variable (F) {E : Type*} [Category E] [HasShift E B] (G : D ⥤ E) [G.CommShift B]

/-- The natural isomorphism between the pullback of `F ⋙ G` and the
composition of the pullbacks of `F` and `G`.
-/
def PullbackShift.natIsoComp : PullbackShift.functor φ (F ⋙ G) ≅
    PullbackShift.functor φ F ⋙ PullbackShift.functor φ G := Iso.refl _

/-
Suppose that `F` and `G` have `CommShift` structure by `B`. This expresses the
compatibility between two `CommShift` structures by `A` on (synonyms of) `F ⋙ G`:
the `CommShift` structure on `PullbackShift.functor (F ⋙ G) φ` (i.e the pullback of the
composition of `CommShift` structures by `B` on `F` and `G`), and that on
`PullbackShift.functor F φ ⋙ PullbackShift.functor G φ` (i.e. the one coming from
the composition of the pulled back `CommShift` structures on `F` and `G`).
-/
open Functor in
instance : NatTrans.CommShift (PullbackShift.natIsoComp φ F G).hom A where
  shift_comm _ := by
    ext
    dsimp [PullbackShift.natIsoComp]
    simp only [commShiftPullback_iso_eq φ _ _ _ rfl, Iso.trans_hom, isoWhiskerRight_hom,
      isoWhiskerLeft_hom, Iso.symm_hom, comp_app, comp_obj, whiskerRight_app, Functor.comp_map,
      commShiftIso_comp_hom_app, whiskerLeft_app, assoc, map_id, comp_id, map_comp, id_comp]
    dsimp [PullbackShift.functor]
    slice_rhs 3 4 => rw [← G.map_comp, Iso.inv_hom_id_app]
    simp

end NatTrans

/--
The adjunction `adj`, seen as an adjunction between `PullbackShift.functor F φ`
and `PullbackShift.functor G φ`.
-/
@[simps -isSimp]
def PullbackShift.adjunction {F} {G : D ⥤ C} (adj : F ⊣ G) :
    PullbackShift.functor φ F ⊣ PullbackShift.functor φ G where
  unit := (NatTrans.PullbackShift.natIsoId C φ).hom ≫
    PullbackShift.natTrans φ adj.unit ≫ (NatTrans.PullbackShift.natIsoComp φ F G).hom
  counit := (NatTrans.PullbackShift.natIsoComp φ G F).inv ≫
    PullbackShift.natTrans φ adj.counit ≫ (NatTrans.PullbackShift.natIsoId D φ).inv
  left_triangle_components _ := by
    simp [PullbackShift.natTrans, NatTrans.PullbackShift.natIsoComp,
      NatTrans.PullbackShift.natIsoId, PullbackShift.functor]
  right_triangle_components _ := by
    simp [PullbackShift.natTrans, NatTrans.PullbackShift.natIsoComp,
      NatTrans.PullbackShift.natIsoId, PullbackShift.functor]

namespace Adjunction

variable {F} {G : D ⥤ C} (adj : F ⊣ G) [G.CommShift B]

/--
If an adjunction `F ⊣ G` is compatible with `CommShift` structures on `F` and `G`, then
it is also compatible with the pulled back `CommShift` structures by an additive map
`φ : B →+ A`.
-/
instance commShiftPullback [adj.CommShift B] : (PullbackShift.adjunction φ adj).CommShift A where
  commShift_unit := by
    dsimp [PullbackShift.adjunction]
    infer_instance
  commShift_counit := by
    dsimp [PullbackShift.adjunction]
    infer_instance

end Adjunction

>>>>>>> origin/jriou_localization_bump_deps
end CategoryTheory
