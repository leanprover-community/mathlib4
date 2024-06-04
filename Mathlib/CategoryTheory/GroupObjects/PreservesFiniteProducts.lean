import Mathlib.CategoryTheory.GroupObjects.Basic
import Mathlib.CategoryTheory.GroupObjects.StupidLemmas
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
open CategoryTheory Limits

namespace CategoryTheory.Functor
universe v u v₁ u₁
variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]

variable [HasFiniteProducts C] [HasFiniteProducts D]
variable (F : C ⥤ D) [PreservesFiniteProducts F]

/-- Lifting a functor `C ⥤ D` that commutes with finite products to a functor between the
categories of group objects: the action on objects.-/
@[simps]
noncomputable def mapGroupObjectObj (G : GroupObject C) : GroupObject D where
  X := F.obj G.X
  one := (PreservesTerminal.iso F).inv ≫ F.map G.one
  mul := (PreservesLimitPair.iso F _ _).inv ≫ F.map G.mul
  inv := F.map G.inv
  one_mul := by
    rw [prod.map_comp_id]
    slice_lhs 2 3 =>
      rw [PreservesLimitPair.iso_inv, ← F.map_id, ← prodComparison_inv_natural]
    simp [← F.map_comp, inv_prodComparison_map_snd]
  mul_one := by
    rw [prod.map_id_comp]
    slice_lhs 2 3 =>
      rw [PreservesLimitPair.iso_inv, ← F.map_id, ← prodComparison_inv_natural]
    simp [← F.map_comp, inv_prodComparison_map_fst]
  mul_assoc := by
    rw [prod.map_comp_id, prod.map_id_comp]
    simp only [PreservesLimitPair.iso_inv]
    slice_lhs 2 3 =>
      rw [← F.map_id, ← prodComparison_inv_natural]
    slice_lhs 3 4 =>
      rw [← F.map_comp, G.mul_assoc]
    have := PreservesLimitsPair.iso.inv_comp_prod.associator G.X G.X G.X F
    simp only [PreservesLimitPair.iso_inv] at this
    simp only [F.map_comp]
    slice_lhs 1 3 =>
      rw [this]
    slice_rhs 3 4 =>
      rw [← F.map_id, ← prodComparison_inv_natural]
    simp only [Category.assoc]
    rfl
  mul_left_inv := by
    slice_lhs 1 2 =>
      rw [← F.map_id, PreservesLimitPair.iso.inv_comp_lift]
    rw [← F.map_comp, G.mul_left_inv]
    simp only [Functor.map_comp, PreservesTerminal.iso_inv]
    rw [← Category.assoc, default_comp_inv_terminalComparison]

/-- Lifting a functor `C ⥤ D` that commutes with finite products to a functor between the
categories of group objects: the action on maps.-/
@[simps]
def mapGroupObjectMap {X Y : GroupObject C}
    (f : X ⟶ Y) : F.mapGroupObjectObj X ⟶ F.mapGroupObjectObj Y  where
  hom := F.map f.hom
  one_hom := by simp [← F.map_comp]
  mul_hom := by
    simp only [mapGroupObjectObj_X, mapGroupObjectObj_mul, PreservesLimitPair.iso_inv,
      Category.assoc, IsIso.inv_comp_eq]
    rw [← F.map_comp]
    slice_rhs 2 3 =>
      rw [← prodComparison_inv_natural]
    simp
  inv_hom := by
    simp only [mapGroupObjectObj_X, mapGroupObjectObj_inv]
    rw [← F.map_comp, f.inv_hom, F.map_comp]

/-- Lifting a functor `C ⥤ D` that commutes with finite products to a functor between the
categories of group objects.-/
@[simps]
noncomputable def mapGroupObject : GroupObject C ⥤ GroupObject D where
  obj X := mapGroupObjectObj F X
  map f := mapGroupObjectMap F f
  map_id X := by ext; simp
  map_comp f g := by ext; simp

/-- Lifting a functor `C ⥤ D` that commutes with finite products to a functor between the
categories of group objects is compatible with the forgetful functors from the categories of
groups objects to the original categories.-/
noncomputable def mapGroupObject_comp_forget :
    F.mapGroupObject ⋙ GroupObject.forget D ≅ GroupObject.forget C ⋙ F :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)
  (fun _ ↦ by simp only [comp_obj, mapGroupObject_obj, GroupObject.forget_obj, mapGroupObjectObj_X,
    comp_map, mapGroupObject_map, GroupObject.forget_map, mapGroupObjectMap_hom, Iso.refl_hom,
    Category.comp_id, Category.id_comp])

/-- If `F : C ⥤ D` is faithful, then so is the induced functor `F.mapGroupObject` on
group objects.-/
lemma mapGroupObject_faitful [Faithful F] : Faithful F.mapGroupObject where
  map_injective := by
    intro X Y f g
    dsimp; intro eq; ext
    apply_fun (fun h ↦ h.hom) at eq
    dsimp at eq
    exact F.map_injective eq

/-- If `F : C ⥤ D` is fully faithful, then the induced functor `F.mapGroupObject` on
group objects is full (it is also faithful by `mapGroupObject_faithful`).-/
lemma mapGroupObject_full [Faithful F] [Full F] : Full  F.mapGroupObject where
  map_surjective := by
    intro X Y h
    obtain ⟨f, hf⟩ := F.map_surjective h.hom
    existsi {hom := f, one_hom := ?_, mul_hom := ?_, inv_hom := ?_}
    · refine F.map_injective (Epi.left_cancellation (f := (PreservesTerminal.iso F).inv) _ _ ?_)
      simp only [map_comp, hf, mapGroupObject_obj]
      rw [← Category.assoc]; conv_rhs => rw [← mapGroupObjectObj_one]
      change _ = (F.mapGroupObject.obj Y).one
      rw [← h.one_hom]; simp only [mapGroupObject_obj, mapGroupObjectObj_X,
        PreservesTerminal.iso_inv, Category.assoc, mapGroupObjectObj_one]
    · refine F.map_injective (Epi.left_cancellation (f := (PreservesLimitPair.iso F _ _).inv)
        _ _ ?_)
      simp only [map_comp]
      conv_lhs => rw [← Category.assoc, ← F.mapGroupObjectObj_mul, hf]
                  change (F.mapGroupObject.obj X).mul ≫ h.hom
                  rw [h.mul_hom, ← hf]
      simp only [mapGroupObject_obj, mapGroupObjectObj_X, mapGroupObjectObj_mul,
        PreservesLimitPair.iso_inv, IsIso.eq_inv_comp]
      slice_lhs 1 2 => rw [← prodComparison_natural]
      simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    · refine F.map_injective ?_
      simp only [map_comp, ← F.mapGroupObjectObj_inv, hf]
      change (F.mapGroupObject.obj X).inv ≫ _ = _
      rw [h.inv_hom]; simp only [mapGroupObject_obj, mapGroupObjectObj_X, mapGroupObjectObj_inv]
    · ext; simp only [mapGroupObject_obj, mapGroupObjectObj_X, mapGroupObject_map,
      mapGroupObjectMap_hom, hf]

/-- The construction `mapGroupObject`, as a functor from the category of functors `C ⥤ D`
that respect finite limits to the category of functors `GroupObject C ⥤ GroupObject D`.-/
noncomputable def mapGroupObjectAsFunctor :
    FullSubcategory (fun (F : C ⥤ D) ↦ Nonempty (PreservesFiniteProducts F)) ⥤
    GroupObject C ⥤ GroupObject D where
  obj F := by
    set hF := Classical.choice F.2
    exact @mapGroupObject _ _ _ _ _ _ F.1 hF
  map := by
    intro F G α
    simp only
    refine { app := ?_, naturality := ?_}
    · intro X; dsimp
      refine {hom := α.app X.X, one_hom := ?_, mul_hom := ?_, inv_hom := ?_}
      · dsimp
        rw [Category.assoc, α.naturality, ← Category.assoc]
        congr 1
        simp only [PreservesTerminal.iso_inv, IsIso.inv_comp_eq, IsIso.eq_comp_inv]
        exact Subsingleton.elim _ _
      · simp only [mapGroupObjectObj_X, mapGroupObjectObj_mul, PreservesLimitPair.iso_inv, id_eq,
        Category.assoc, NatTrans.naturality, IsIso.inv_comp_eq]
        slice_rhs 1 2 => rw [prodComparison_natTrans]
        simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      · simp only [mapGroupObjectObj_X, mapGroupObjectObj_inv, id_eq, NatTrans.naturality]
    · aesop_cat
