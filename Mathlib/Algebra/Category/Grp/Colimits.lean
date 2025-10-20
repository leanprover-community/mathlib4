/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Sophie Morel
-/
import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.Algebra.Group.Shrink
import Mathlib.CategoryTheory.ConcreteCategory.Elementwise
import Mathlib.Data.DFinsupp.BigOperators
import Mathlib.Data.DFinsupp.Small
import Mathlib.GroupTheory.QuotientGroup.Defs
/-!
# The category of additive commutative groups has all colimits.

This file constructs colimits in the category of additive commutative groups, as
quotients of finitely supported functions.

-/

universe u' w u v

open CategoryTheory Limits

namespace AddCommGrpCat

variable {J : Type u} [Category.{v} J] (F : J ⥤ AddCommGrpCat.{w})

namespace Colimits

/-!
We build the colimit of a diagram in `AddCommGrpCat` by constructing the
free group on the disjoint union of all the abelian groups in the diagram,
then taking the quotient by the abelian group laws within each abelian group,
and the identifications given by the morphisms in the diagram.
-/

/--
The relations between elements of the direct sum of the `F.obj j` given by the
morphisms in the diagram `J`.
-/
abbrev Relations [DecidableEq J] : AddSubgroup (DFinsupp (fun j ↦ F.obj j)) :=
  AddSubgroup.closure {x | ∃ (j j' : J) (u : j ⟶ j') (a : F.obj j),
    x = DFinsupp.single j' (F.map u a) - DFinsupp.single j a}

/--
The candidate for the colimit of `F`, defined as the quotient of the direct sum
of the commutative groups `F.obj j` by the relations given by the morphisms in
the diagram.
-/
def Quot [DecidableEq J] : Type (max u w) :=
  DFinsupp (fun j ↦ F.obj j) ⧸ Relations F

instance [DecidableEq J] : AddCommGroup (Quot F) :=
  QuotientAddGroup.Quotient.addCommGroup (Relations F)

/-- Inclusion of `F.obj j` into the candidate colimit.
-/
def Quot.ι [DecidableEq J] (j : J) : F.obj j →+ Quot F :=
  (QuotientAddGroup.mk' _).comp (DFinsupp.singleAddHom (fun j ↦ F.obj j) j)

lemma Quot.addMonoidHom_ext [DecidableEq J] {α : Type*} [AddMonoid α] {f g : Quot F →+ α}
    (h : ∀ (j : J) (x : F.obj j), f (Quot.ι F j x) = g (Quot.ι F j x)) : f = g :=
  QuotientAddGroup.addMonoidHom_ext _ (DFinsupp.addHom_ext h)

variable (c : Cocone F)

/-- (implementation detail) Part of the universal property of the colimit cocone, but without
assuming that `Quot F` lives in the correct universe. -/
def Quot.desc [DecidableEq J] : Quot.{w} F →+ c.pt := by
  refine QuotientAddGroup.lift _ (DFinsupp.sumAddHom fun x => (c.ι.app x).hom) ?_
  dsimp
  rw [AddSubgroup.closure_le]
  intro _ ⟨_, _, _, _, eq⟩
  rw [eq]
  simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, DFinsupp.sumAddHom_single]
  change (F.map _ ≫ c.ι.app _) _ - _ = 0
  rw [c.ι.naturality]
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, sub_self]

@[simp]
lemma Quot.ι_desc [DecidableEq J] (j : J) (x : F.obj j) :
    Quot.desc F c (Quot.ι F j x) = c.ι.app j x := by
  dsimp [desc, ι]
  erw [QuotientAddGroup.lift_mk']
  simp

@[simp]
lemma Quot.map_ι [DecidableEq J] {j j' : J} {f : j ⟶ j'} (x : F.obj j) :
    Quot.ι F j' (F.map f x) = Quot.ι F j x := by
  dsimp [ι]
  refine eq_of_sub_eq_zero ?_
  erw [← (QuotientAddGroup.mk' (Relations F)).map_sub, ← AddMonoidHom.mem_ker]
  rw [QuotientAddGroup.ker_mk']
  simp only [DFinsupp.singleAddHom_apply]
  exact AddSubgroup.subset_closure ⟨j, j', f, x, rfl⟩

/--
The obvious additive map from `Quot F` to `Quot (F ⋙ uliftFunctor.{u'})`.
-/
def quotToQuotUlift [DecidableEq J] : Quot F →+ Quot (F ⋙ uliftFunctor.{u'}) := by
  refine QuotientAddGroup.lift (Relations F) (DFinsupp.sumAddHom (fun j ↦ (Quot.ι _ j).comp
    AddEquiv.ulift.symm.toAddMonoidHom)) ?_
  rw [AddSubgroup.closure_le]
  intro _ hx
  obtain ⟨j, j', u, a, rfl⟩ := hx
  rw [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, DFinsupp.sumAddHom_single,
    DFinsupp.sumAddHom_single]
  change Quot.ι (F ⋙ uliftFunctor) j' ((F ⋙ uliftFunctor).map u (AddEquiv.ulift.symm a)) - _ = _
  rw [Quot.map_ι]
  dsimp
  rw [sub_self]

lemma quotToQuotUlift_ι [DecidableEq J] (j : J) (x : F.obj j) :
    quotToQuotUlift F (Quot.ι F j x) = Quot.ι _ j (ULift.up x) := by
  dsimp [quotToQuotUlift, Quot.ι]
  conv_lhs => erw [AddMonoidHom.comp_apply (QuotientAddGroup.mk' (Relations F))
    (DFinsupp.singleAddHom _ j), QuotientAddGroup.lift_mk']
  simp only [DFinsupp.singleAddHom_apply, DFinsupp.sumAddHom_single, AddMonoidHom.coe_comp,
    AddMonoidHom.coe_coe, Function.comp_apply]
  rfl

/--
The obvious additive map from `Quot (F ⋙ uliftFunctor.{u'})` to `Quot F`.
-/
def quotUliftToQuot [DecidableEq J] : Quot (F ⋙ uliftFunctor.{u'}) →+ Quot F := by
  refine QuotientAddGroup.lift (Relations (F ⋙ uliftFunctor))
    (DFinsupp.sumAddHom (fun j ↦ (Quot.ι _ j).comp AddEquiv.ulift.toAddMonoidHom)) ?_
  rw [AddSubgroup.closure_le]
  intro _ hx
  obtain ⟨j, j', u, a, rfl⟩ := hx
  simp

lemma quotUliftToQuot_ι [DecidableEq J] (j : J) (x : (F ⋙ uliftFunctor.{u'}).obj j) :
    quotUliftToQuot F (Quot.ι _ j x) = Quot.ι F j x.down := by
  dsimp [quotUliftToQuot, Quot.ι]
  conv_lhs => erw [AddMonoidHom.comp_apply (QuotientAddGroup.mk' (Relations (F ⋙ uliftFunctor)))
    (DFinsupp.singleAddHom _ j), QuotientAddGroup.lift_mk']
  simp only [Functor.comp_obj, uliftFunctor_obj, DFinsupp.singleAddHom_apply,
    DFinsupp.sumAddHom_single, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe, Function.comp_apply]
  rfl

/--
The additive equivalence between `Quot F` and `Quot (F ⋙ uliftFunctor.{u'})`.
-/
@[simp]
def quotQuotUliftAddEquiv [DecidableEq J] : Quot F ≃+ Quot (F ⋙ uliftFunctor.{u'}) where
  toFun := quotToQuotUlift F
  invFun := quotUliftToQuot F
  left_inv x := by
    conv_rhs => rw [← AddMonoidHom.id_apply _ x]
    rw [← AddMonoidHom.comp_apply, Quot.addMonoidHom_ext F (f := (quotUliftToQuot F).comp
      (quotToQuotUlift F)) (fun j a ↦ ?_)]
    rw [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, quotToQuotUlift_ι, quotUliftToQuot_ι]
  right_inv x := by
    conv_rhs => rw [← AddMonoidHom.id_apply _ x]
    rw [← AddMonoidHom.comp_apply, Quot.addMonoidHom_ext _ (f := (quotToQuotUlift F).comp
      (quotUliftToQuot F)) (fun j a ↦ ?_)]
    rw [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, quotUliftToQuot_ι, quotToQuotUlift_ι]
    rfl
  map_add' _ _ := by simp

lemma Quot.desc_quotQuotUliftAddEquiv [DecidableEq J] (c : Cocone F) :
    (Quot.desc (F ⋙ uliftFunctor.{u'}) (uliftFunctor.{u'}.mapCocone c)).comp
    (quotQuotUliftAddEquiv F).toAddMonoidHom =
    AddEquiv.ulift.symm.toAddMonoidHom.comp (Quot.desc F c) := by
  refine Quot.addMonoidHom_ext _ (fun j a ↦ ?_)
  dsimp
  simp only [quotToQuotUlift_ι, Functor.comp_obj, uliftFunctor_obj, ι_desc, Functor.const_obj_obj,
    ι_desc]
  erw [Quot.ι_desc]
  rfl

/-- (implementation detail) A morphism of commutative additive groups `Quot F →+ A`
induces a cocone on `F` as long as the universes work out.
-/
@[simps]
def toCocone [DecidableEq J] {A : Type w} [AddCommGroup A] (f : Quot F →+ A) : Cocone F where
  pt := AddCommGrpCat.of A
  ι.app j := ofHom <| f.comp (Quot.ι F j)

lemma Quot.desc_toCocone_desc [DecidableEq J] {A : Type w} [AddCommGroup A] (f : Quot F →+ A)
    (hc : IsColimit c) : (hc.desc (toCocone F f)).hom.comp (Quot.desc F c) = f := by
  refine Quot.addMonoidHom_ext F (fun j x ↦ ?_)
  rw [AddMonoidHom.comp_apply, ι_desc]
  change (c.ι.app j ≫ hc.desc (toCocone F f)) _ = _
  rw [hc.fac]
  simp

lemma Quot.desc_toCocone_desc_app [DecidableEq J] {A : Type w} [AddCommGroup A] (f : Quot F →+ A)
    (hc : IsColimit c) (x : Quot F) : hc.desc (toCocone F f) (Quot.desc F c x) = f x := by
  conv_rhs => rw [← Quot.desc_toCocone_desc F c f hc]
  dsimp

/--
If `c` is a cocone of `F` such that `Quot.desc F c` is bijective, then `c` is a colimit
cocone of `F`.
-/
noncomputable def isColimit_of_bijective_desc [DecidableEq J]
     (h : Function.Bijective (Quot.desc F c)) : IsColimit c where
  desc s := AddCommGrpCat.ofHom ((Quot.desc F s).comp (AddEquiv.ofBijective
    (Quot.desc F c) h).symm.toAddMonoidHom)
  fac s j := by
    ext x
    dsimp
    conv_lhs => erw [← Quot.ι_desc F c j x]
    rw [← AddEquiv.ofBijective_apply _ h, AddEquiv.symm_apply_apply]
    simp only [Quot.ι_desc, Functor.const_obj_obj]
  uniq s m hm := by
    ext x
    obtain ⟨x, rfl⟩ := h.2 x
    dsimp
    rw [← AddEquiv.ofBijective_apply _ h, AddEquiv.symm_apply_apply]
    suffices eq : m.hom.comp (AddEquiv.ofBijective (Quot.desc F c) h) = Quot.desc F s by
      rw [← eq]; rfl
    exact Quot.addMonoidHom_ext F (by simp [← hm])

/-- (internal implementation) The colimit cocone of a functor `F`, implemented as a quotient of
`DFinsupp (fun j ↦ F.obj j)`, under the assumption that said quotient is small.
-/
@[simps pt ι_app]
noncomputable def colimitCocone [DecidableEq J] [Small.{w} (Quot.{w} F)] : Cocone F where
  pt := AddCommGrpCat.of (Shrink (Quot F))
  ι :=
    { app j :=
        AddCommGrpCat.ofHom (Shrink.addEquiv.symm.toAddMonoidHom.comp (Quot.ι F j))
      naturality _ _ _ := by
        ext
        dsimp
        change Shrink.addEquiv.symm _ = _
        rw [Quot.map_ι] }

@[simp]
theorem Quot.desc_colimitCocone [DecidableEq J] (F : J ⥤ AddCommGrpCat.{w}) [Small.{w} (Quot F)] :
    Quot.desc F (colimitCocone F) = (Shrink.addEquiv (α := Quot F)).symm.toAddMonoidHom := by
  refine Quot.addMonoidHom_ext F (fun j x ↦ ?_)
  simpa only [colimitCocone_pt, AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
    using Quot.ι_desc F (colimitCocone F) j x

/-- (internal implementation) The fact that the candidate colimit cocone constructed in
`colimitCocone` is the colimit.
-/
noncomputable def colimitCoconeIsColimit [DecidableEq J] [Small.{w} (Quot F)] :
    IsColimit (colimitCocone F) := by
  refine isColimit_of_bijective_desc F _ ?_
  rw [Quot.desc_colimitCocone]
  exact Shrink.addEquiv.symm.bijective

end Colimits

open Colimits

lemma hasColimit_of_small_quot [DecidableEq J] (h : Small.{w} (Quot F)) : HasColimit F :=
  ⟨_, colimitCoconeIsColimit F⟩

instance [DecidableEq J] [Small.{w} J] : Small.{w} (Quot F) :=
  small_of_surjective (QuotientAddGroup.mk'_surjective _)

instance hasColimit [Small.{w} J] (F : J ⥤ AddCommGrpCat.{w}) : HasColimit F := by
  classical
  exact hasColimit_of_small_quot F inferInstance


/--
If `J` is `w`-small, then any functor `J ⥤ AddCommGrpCat.{w}` has a colimit.
-/
instance hasColimitsOfShape [Small.{w} J] : HasColimitsOfShape J (AddCommGrpCat.{w}) where

/-- The category of additive commutative groups has all small colimits.
-/
instance (priority := 1300) hasColimitsOfSize [UnivLE.{u, w}] :
    HasColimitsOfSize.{v, u} (AddCommGrpCat.{w}) where

end AddCommGrpCat

namespace AddCommGrpCat

open QuotientAddGroup

/-- The categorical cokernel of a morphism in `AddCommGrpCat`
agrees with the usual group-theoretical quotient.
-/
noncomputable def cokernelIsoQuotient {G H : AddCommGrpCat.{u}} (f : G ⟶ H) :
    cokernel f ≅ AddCommGrpCat.of (H ⧸ AddMonoidHom.range f.hom) where
  hom := cokernel.desc f (ofHom (mk' _)) <| by
        ext x
        simp
  inv := ofHom <|
    QuotientAddGroup.lift _ (cokernel.π f).hom <| by
      rintro _ ⟨x, rfl⟩
      exact cokernel.condition_apply f x
  hom_inv_id := by
    refine coequalizer.hom_ext ?_
    simp only [coequalizer_as_cokernel, cokernel.π_desc_assoc, Category.comp_id]
    rfl
  inv_hom_id := by
    ext x
    dsimp only [hom_comp, hom_ofHom, hom_zero, AddMonoidHom.coe_comp, coe_mk',
      Function.comp_apply, AddMonoidHom.zero_apply, id_eq, lift_mk, hom_id, AddMonoidHom.coe_id]
    exact QuotientAddGroup.induction_on (α := H) x <| cokernel.π_desc_apply f _ _

end AddCommGrpCat
