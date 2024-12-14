import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

namespace Adjunction

open CategoryTheory Category Functor

variable {C : Type u₁} {D : Type u₂} [Category.{v₁, u₁} C] [Category.{v₂, u₂} D]
  [Preadditive C] [Preadditive D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

/-- If we have an adjunction `adj : F ⊣ G` of functors between preadditive categories,
and if `F` is additive, then the hom set equivalence upgrades to an `AddEquiv`.-/
def homAddEquiv_of_left_adjoint_additive [F.Additive] (X : C) (Y : D) :
    AddEquiv (F.obj X ⟶ Y) (X ⟶ G.obj Y) :=
  {
    adj.homEquiv X Y with
    map_add' := by
      intro f g
      simp only [Equiv.toFun_as_coe]
      apply (adj.homEquiv X Y).symm.injective
      rw [Equiv.symm_apply_apply, adj.homEquiv_symm_apply, Functor.map_add, Preadditive.add_comp,
      ← adj.homEquiv_symm_apply, ← adj.homEquiv_symm_apply, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply]
  }

@[simp]
lemma homAddEquiv_of_left_adjoint_additive_apply [F.Additive] (X : C) (Y : D) (f : F.obj X ⟶ Y) :
    adj.homAddEquiv_of_left_adjoint_additive X Y f = adj.homEquiv X Y f := rfl

@[simp]
lemma homAddEquiv_of_left_adjoint_additive_symm_apply [F.Additive] (X : C) (Y : D)
    (f : X ⟶ G.obj Y) :
    (adj.homAddEquiv_of_left_adjoint_additive X Y).symm f = (adj.homEquiv X Y).symm f := rfl

/-- If we have an adjunction `adj : F ⊣ G` of functors between preadditive categories,
and if `G` is additive, then the hom set equivalence upgrades to an `AddEquiv`.-/
def homAddEquiv_of_right_adjoint_additive [G.Additive] (X : C) (Y : D) :
    AddEquiv (F.obj X ⟶ Y) (X ⟶ G.obj Y) :=
  {
    adj.homEquiv X Y with
    map_add' := by
      intro f g
      simp only [Equiv.toFun_as_coe, homEquiv_apply, Functor.map_add, Preadditive.comp_add]
  }

@[simp]
lemma homAddEquiv_of_right_adjoint_additive_apply [G.Additive] (X : C) (Y : D) (f : F.obj X ⟶ Y) :
    adj.homAddEquiv_of_right_adjoint_additive X Y f = adj.homEquiv X Y f := rfl

@[simp]
lemma homAddEquiv_of_right_adjoint_additive_symm_apply [G.Additive] (X : C) (Y : D)
    (f : X ⟶ G.obj Y) :
    (adj.homAddEquiv_of_right_adjoint_additive X Y).symm f = (adj.homEquiv X Y).symm f := rfl

/-- If we have an adjunction `adj : F ⊣ G` of functors between preadditive categories,
and if `F` is additive, then the hom set equivalence upgrades to an isomorphism between
the additive groups `F.obj X ⟶ Y` and `X ⟶ G.obj Y`, seen as objects of
`AddCommGrp.{max v₁ v₂}`.-/
def homAddEquiv_of_left_adjoint_additive_ulift [F.Additive] (X : C) (Y : D) :
    AddCommGrp.uliftFunctor.{max v₁ v₂}.obj (AddCommGrp.of (F.obj X ⟶ Y)) ≅
    AddCommGrp.uliftFunctor.{max v₁ v₂}.obj (AddCommGrp.of (X ⟶ G.obj Y)) :=
  ((AddEquiv.ulift.trans (adj.homAddEquiv_of_left_adjoint_additive X Y)).trans
  AddEquiv.ulift.symm).toAddCommGrpIso

@[simp]
lemma homAddEquiv_of_left_adjoint_additive_ulift_hom [F.Additive] (X : C) (Y : D)
    (f : F.obj X ⟶ Y) :
    (adj.homAddEquiv_of_left_adjoint_additive_ulift X Y).hom {down := f} =
    {down := adj.homEquiv X Y f} := rfl

@[simp]
lemma homAddEquiv_of_left_adjoint_additive_ulift_inv [F.Additive] (X : C) (Y : D)
    (f : X ⟶ G.obj Y) :
    (adj.homAddEquiv_of_left_adjoint_additive_ulift X Y).inv {down := f} =
    {down := (adj.homEquiv X Y).symm f} := rfl

/-- If we have an adjunction `adj : F ⊣ G` of functors between preadditive categories,
and if `G` is additive, then the hom set equivalence upgrades to an isomorphism between
the additive groups `F.obj X ⟶ Y` and `X ⟶ G.obj Y`, seen as objects of
`AddCommGrp.{max v₁ v₂}`.-/
@[simp]
def homAddEquiv_of_right_adjoint_additive_ulift [G.Additive] (X : C) (Y : D) :
    AddCommGrp.uliftFunctor.{max v₁ v₂}.obj (AddCommGrp.of (F.obj X ⟶ Y)) ≅
    AddCommGrp.uliftFunctor.{max v₁ v₂}.obj (AddCommGrp.of (X ⟶ G.obj Y)) :=
  ((AddEquiv.ulift.trans (adj.homAddEquiv_of_right_adjoint_additive X Y)).trans
  AddEquiv.ulift.symm).toAddCommGrpIso

@[simp]
lemma homAddEquiv_of_right_adjoint_additive_ulift_hom [G.Additive] (X : C) (Y : D)
    (f : F.obj X ⟶ Y) :
    (adj.homAddEquiv_of_right_adjoint_additive_ulift X Y).hom {down := f} =
    {down := adj.homEquiv X Y f} := rfl

@[simp]
lemma homAddEquiv_of_right_adjoint_additive_ulift_inv [G.Additive] (X : C) (Y : D)
    (f : X ⟶ G.obj Y) :
    (adj.homAddEquiv_of_right_adjoint_additive_ulift X Y).inv {down := f} =
    {down := (adj.homEquiv X Y).symm f} := rfl

/-- If we have an adjunction `adj : F ⊣ G` of functors between preadditive categories,
and if `F` is additive, then the hom set equivalence upgrades to an isomorphism between
`G ⋙ preadditiveYoneda` and `preadditiveYoneda ⋙ F`, once we throw in the ncessary
universe lifting functors.-/
@[simps!]
def compPreadditiveYonedaIso_of_left_adjoint_additive [F.Additive] :
    G ⋙ preadditiveYoneda ⋙ (whiskeringRight _ _ _).obj AddCommGrp.uliftFunctor.{max v₁ v₂} ≅
    preadditiveYoneda ⋙ (whiskeringLeft _ _ _).obj F.op ⋙
    (whiskeringRight _ _ _).obj AddCommGrp.uliftFunctor.{max v₁ v₂} := by
  refine NatIso.ofComponents ?_ ?_
  · intro Y
    refine NatIso.ofComponents
      (fun X ↦ (adj.homAddEquiv_of_left_adjoint_additive_ulift (Opposite.unop X) Y).symm) ?_
    intro _ _ _
    ext _
    change (adj.homAddEquiv_of_left_adjoint_additive_ulift (Opposite.unop _) _).inv
      {down := _} = _
    rw [homAddEquiv_of_left_adjoint_additive_ulift_inv]
    erw [adj.homEquiv_naturality_left_symm]
    rfl
  · intro _ _ _
    ext _ _
    change (adj.homAddEquiv_of_left_adjoint_additive_ulift (Opposite.unop _) _).inv {down := _} = _
    rw [homAddEquiv_of_left_adjoint_additive_ulift_inv]
    erw [adj.homEquiv_naturality_right_symm]
    rfl

/-- If we have an adjunction `adj : F ⊣ G` of functors between preadditive categories,
and if `G` is additive, then the hom set equivalence upgrades to an isomorphism between
`G ⋙ preadditiveYoneda` and `preadditiveYoneda ⋙ F`, once we throw in the ncessary
universe lifting functors.-/
@[simps!]
def compPreadditiveYonedaIso_of_right_adjoint_additive [G.Additive] :
    G ⋙ preadditiveYoneda ⋙ (whiskeringRight _ _ _).obj AddCommGrp.uliftFunctor.{max v₁ v₂} ≅
    preadditiveYoneda ⋙ (whiskeringLeft _ _ _).obj F.op ⋙
    (whiskeringRight _ _ _).obj AddCommGrp.uliftFunctor.{max v₁ v₂} := by
  refine NatIso.ofComponents ?_ ?_
  · intro Y
    refine NatIso.ofComponents
      (fun X ↦ (adj.homAddEquiv_of_right_adjoint_additive_ulift (Opposite.unop X) Y).symm) ?_
    intro _ _ _
    ext _
    change (adj.homAddEquiv_of_right_adjoint_additive_ulift (Opposite.unop _) _).inv
      {down := _} = _
    rw [homAddEquiv_of_right_adjoint_additive_ulift_inv]
    erw [adj.homEquiv_naturality_left_symm]
    rfl
  · intro _ _ _
    ext _ _
    change (adj.homAddEquiv_of_right_adjoint_additive_ulift (Opposite.unop _) _).inv {down := _} = _
    rw [homAddEquiv_of_right_adjoint_additive_ulift_inv]
    erw [adj.homEquiv_naturality_right_symm]
    rfl

end Adjunction

end CategoryTheory
