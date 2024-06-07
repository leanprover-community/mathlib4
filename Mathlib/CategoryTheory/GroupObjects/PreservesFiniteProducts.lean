import Mathlib.CategoryTheory.GroupObjects.Basic
import Mathlib.CategoryTheory.GroupObjects.StupidLemmas
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Yoneda
open CategoryTheory Limits

noncomputable section

universe v u v₁ u₁ u₂ v₂

variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D] {E : Type u₂}
  [Category.{v₂, u₂} E]

namespace CategoryTheory.GroupObjectFunctor

variable [HasFiniteProducts C] [HasFiniteProducts D] [HasFiniteProducts E]
variable (F F' F'' : C ⥤ D) [PreservesFiniteProducts F] [PreservesFiniteProducts F']
  [PreservesFiniteProducts F'']
variable {G G' : D ⥤ E} [PreservesFiniteProducts G] [PreservesFiniteProducts G']
variable {H H' : E ⥤ C} [PreservesFiniteProducts H] [PreservesFiniteProducts H']

/-- Lifting a functor `C ⥤ D` that commutes with finite products to a functor between the
categories of group objects: the action on objects.-/
@[simps]
noncomputable def map_obj (G : GroupObject C) : GroupObject D where
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
def map_map {X Y : GroupObject C}
    (f : X ⟶ Y) : map_obj F X ⟶ map_obj F Y  where
  hom := F.map f.hom
  one_hom := by simp [← F.map_comp]
  mul_hom := by
    simp only [map_obj_X, map_obj_mul, PreservesLimitPair.iso_inv, Category.assoc,
      IsIso.inv_comp_eq]
    rw [← F.map_comp]
    slice_rhs 2 3 =>
      rw [← prodComparison_inv_natural]
    simp
  inv_hom := by
    simp only [map_obj_X, map_obj_inv]
    rw [← F.map_comp, f.inv_hom, F.map_comp]

/-- Lifting a functor `C ⥤ D` that commutes with finite products to a functor between the
categories of group objects.-/
@[simp]
noncomputable def map : GroupObject C ⥤ GroupObject D where
  obj X := map_obj F X
  map f := map_map F f
  map_id X := by ext; simp
  map_comp f g := by ext; simp

noncomputable abbrev groupYoneda : GroupObject C ⥤ GroupObject (Cᵒᵖ ⥤ Type v) :=
  map (yoneda (C := C))

/-- Lifting a functor `C ⥤ D` that commutes with finite products to a functor between the
categories of group objects is compatible with the forgetful functors from the categories of
groups objects to the original categories.-/
@[simp]
noncomputable def map_comp_forget :
    map F ⋙ GroupObject.forget D ≅ GroupObject.forget C ⋙ F :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)
  (fun _ ↦ by simp only [map, Functor.comp_obj, GroupObject.forget_obj, map_obj_X,
    Functor.comp_map, GroupObject.forget_map, map_map_hom, Iso.refl_hom, Category.comp_id,
    Category.id_comp])

variable (C)

/-- If `F : C ⥤ C` is the identity functor, then its lift to categories of group objects
is isomorphic (actually equal) to the identity functor.-/
@[simps!]
noncomputable def mapIdIso : map (𝟭 C) ≅ 𝟭 (GroupObject C) := by
  refine NatIso.ofComponents ?_ ?_
  · intro X
    refine GroupObject.isoOfIso (Iso.refl _) ?_ ?_ ?_
    · simp only [Functor.id_obj, map, map_obj_X, map_obj_one, PreservesTerminal.iso_inv,
      Functor.id_map, Iso.refl_hom, Category.comp_id, IsIso.inv_comp_eq]
      rw [Subsingleton.elim (terminalComparison (𝟭 C)) (𝟙 _)]
      erw [Category.id_comp]
    · simp only [map, map_obj_X, Functor.id_obj, map_obj_mul, PreservesLimitPair.iso_inv,
      Functor.id_map, Iso.refl_hom, Category.comp_id, prod.map_id_id, Category.id_comp,
      IsIso.inv_comp_eq]
      suffices h : prodComparison (𝟭 C) X.X X.X = 𝟙 _ by
        rw [h]; erw [Category.id_comp]
      ext
      · erw [prodComparison_fst]; simp only [Functor.id_obj, Functor.id_map, Category.id_comp]
      · erw [prodComparison_snd]; simp only [Functor.id_obj, Functor.id_map, Category.id_comp]
    · simp only [map, map_obj_X, Functor.id_obj, map_obj_inv, Functor.id_map, Iso.refl_hom,
      Category.comp_id, Category.id_comp]
  · aesop_cat


variable {C}
variable (G)

/-- The construction `map` is compatible with composition of functors.-/
@[simps!]
noncomputable def mapCompIso : map (F ⋙ G) ≅
    map F ⋙ map G := by
  refine NatIso.ofComponents ?_ ?_
  · intro X
    refine GroupObject.isoOfIso (Iso.refl _) ?_ ?_ ?_
    · simp only [map, Functor.comp_obj, map_obj_X, map_obj_one, PreservesTerminal.iso_inv,
      Functor.comp_map, Iso.refl_hom, Category.comp_id, Functor.map_comp, Functor.map_inv,
      IsIso.eq_inv_comp]
      suffices h : G.map (terminalComparison F) ≫ terminalComparison G ≫
        CategoryTheory.inv (terminalComparison (F ⋙ G)) = 𝟙 _ by
        · rw [← Category.assoc (terminalComparison G) _ _, ← Category.assoc, h,
            Category.id_comp]
      rw [← Category.assoc, IsIso.comp_inv_eq, Category.id_comp]
      exact Subsingleton.elim _ _
    · simp only [map, map_obj_X, Functor.comp_obj, map_obj_mul, PreservesLimitPair.iso_inv,
      Functor.comp_map, Iso.refl_hom, Category.comp_id, prod.map_id_id, Functor.map_comp,
      Functor.map_inv, Category.id_comp, IsIso.eq_inv_comp]
      suffices h : G.map (prodComparison F X.X X.X) ≫ prodComparison G (F.obj X.X) (F.obj X.X) ≫
        CategoryTheory.inv (prodComparison (F ⋙ G) X.X X.X) = 𝟙 _ by
        · rw [← Category.assoc (prodComparison G (F.obj X.X) (F.obj X.X)) _ _, ← Category.assoc,
          h, Category.id_comp]
      rw [← Category.assoc, IsIso.comp_inv_eq, Category.id_comp]
      ext
      · simp only [Category.assoc, prodComparison_fst, Functor.comp_obj]
        erw [prodComparison_fst]; rw [← Functor.map_comp, prodComparison_fst, Functor.comp_map]
      · simp only [Category.assoc, prodComparison_snd, Functor.comp_obj]
        erw [prodComparison_snd]; rw [← Functor.map_comp, prodComparison_snd, Functor.comp_map]
    · simp only [map, map_obj_X, Functor.comp_obj, map_obj_inv, Functor.comp_map, Iso.refl_hom,
      Category.comp_id, Category.id_comp]
  · aesop_cat

/-- If `F : C ⥤ D` is faithful, then so is the induced functor `map F` on
group objects.-/
lemma map_faithful [F.Faithful] : (map F).Faithful where
  map_injective := by
    intro X Y f g
    dsimp; intro eq; ext
    apply_fun (fun h ↦ h.hom) at eq
    dsimp at eq
    exact F.map_injective eq

/-- If `F : C ⥤ D` is fully faithful, then the induced functor `map F` on
group objects is full (it is also faithful by `map_faithful`).-/
lemma map_full [F.Faithful] [F.Full] : (map F).Full where
  map_surjective := by
    intro X Y h
    obtain ⟨f, hf⟩ := F.map_surjective h.hom
    existsi {hom := f, one_hom := ?_, mul_hom := ?_, inv_hom := ?_}
    · refine F.map_injective (Epi.left_cancellation (f := (PreservesTerminal.iso F).inv) _ _ ?_)
      simp only [PreservesTerminal.iso_inv, Functor.map_comp, hf, map, IsIso.eq_inv_comp,
        IsIso.hom_inv_id_assoc]
      have := h.one_hom
      simp only [map, map_obj_X, map_obj_one, PreservesTerminal.iso_inv, Category.assoc,
        IsIso.eq_inv_comp, IsIso.hom_inv_id_assoc] at this
      exact this
    · refine F.map_injective (Epi.left_cancellation (f := (PreservesLimitPair.iso F _ _).inv)
        _ _ ?_)
      simp only [PreservesLimitPair.iso_inv, Functor.map_comp, IsIso.eq_inv_comp,
        IsIso.hom_inv_id_assoc]
      have := h.mul_hom
      simp only [map, map_obj_X, map_obj_mul, PreservesLimitPair.iso_inv, Category.assoc,
        IsIso.inv_comp_eq] at this
      rw [← Category.assoc, ← hf, ← prodComparison_natural] at this
      simp only [Category.assoc, IsIso.hom_inv_id_assoc] at this
      exact this
    · refine F.map_injective ?_
      simp only [Functor.map_comp, hf]
      have := h.inv_hom
      simp only [map, map_obj_X, map_obj_inv] at this
      exact this
    ext; simp only [map, map_obj_X, map_map_hom, hf]

variable {G}

@[simp]
noncomputable def map₂ (α : G ⟶ G') : map G ⟶ map G' := by
  refine { app := ?_, naturality := ?_}
  · intro X; dsimp
    refine {hom := α.app X.X, one_hom := ?_, mul_hom := ?_, inv_hom := ?_}
    · dsimp
      rw [Category.assoc, α.naturality, ← Category.assoc]
      congr 1
      simp only [PreservesTerminal.iso_inv, IsIso.inv_comp_eq, IsIso.eq_comp_inv]
      exact Subsingleton.elim _ _
    · simp only [map_obj_X, map_obj_mul, PreservesLimitPair.iso_inv, Category.assoc,
      NatTrans.naturality, IsIso.inv_comp_eq]
      slice_rhs 1 2 => rw [prodComparison_natTrans]
      simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    · simp only [map_obj_X, map_obj_inv, NatTrans.naturality]
  · aesop_cat

variable (C D)

/-- The construction `map`, as a functor from the category of functors `C ⥤ D`
that respect finite limits to the category of functors `GroupObject C ⥤ GroupObject D`.-/
noncomputable def mapAsFunctor :
    FullSubcategory (fun (F : C ⥤ D) ↦ Nonempty (PreservesFiniteProducts F)) ⥤
    GroupObject C ⥤ GroupObject D where
  obj F := @map _ _ _ _ _ _ F.1 (Classical.choice F.2)
  map := by
    intro F G α
    exact @map₂ _ _ _ _ _ _ F.1 G.1 (Classical.choice F.2)
      (Classical.choice G.2) α

variable {C D}

variable {F F'}

lemma mapComp_naturality_left (α : F ⟶ F') :
    map₂ (whiskerRight α G) ≫ (mapCompIso F' G).hom =
    (mapCompIso F G).hom ≫ whiskerRight (map₂ α) (map G) := by
  aesop_cat

variable (F)

lemma mapComp_naturality_right (α : G ⟶ G') :
    map₂ (whiskerLeft F α) ≫ (mapCompIso F G').hom =
    (mapCompIso F G).hom ≫ whiskerLeft (map F) (map₂ α) := by
  aesop_cat

lemma map₂_id : map₂ (𝟙 F) = 𝟙 (map F) := by
  aesop_cat

variable {F''}

lemma map₂_comp (α : F ⟶ F') (β : F' ⟶ F'') :
    map₂ (α ≫ β) = map₂ α ≫ map₂ β := by
  aesop_cat

variable {F}

lemma map₂_associator : map₂ (Functor.associator F G H).hom ≫
    (mapCompIso F (G ⋙ H)).hom ≫ whiskerLeft (map F)
    (mapCompIso G H).hom = (mapCompIso (F ⋙ G) H).hom ≫
    whiskerRight (mapCompIso F G).hom
    (map H) ≫ (Functor.associator (map F) (map G)
    (map H)).hom := by
  aesop_cat

variable (F)

lemma map₂_leftUnitor :
    map₂ F.leftUnitor.hom = (mapCompIso (𝟭 C) F).hom ≫
    whiskerRight (mapIdIso C).hom (map F) ≫
    (map F).leftUnitor.hom := by
  aesop_cat

lemma map₂_rightUnitor :
    map₂ F.rightUnitor.hom = (mapCompIso F (𝟭 D)).hom ≫
    whiskerLeft (map F) (mapIdIso D).hom ≫
    (map F).rightUnitor.hom := by
  aesop_cat

end CategoryTheory.GroupObjectFunctor
