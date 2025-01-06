/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Sophie Morel
-/
import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.Algebra.Equiv.TransferInstance
import Mathlib.CategoryTheory.ConcreteCategory.Elementwise
import Mathlib.Data.DFinsupp.BigOperators
import Mathlib.Data.DFinsupp.Small
import Mathlib.GroupTheory.QuotientGroup.Defs
/-!
# The category of additive commutative groups has all colimits.

This file constructs colimits in the categpry of additive commutative groups, as
quotients of finitely supported functions.

-/

universe w u v

open CategoryTheory Limits

namespace AddCommGrp

variable {J : Type u} [Category.{v} J] (F : J ⥤ AddCommGrp.{w})

namespace Colimits

/-!
We build the colimit of a diagram in `AddCommGrp` by constructing the
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
  refine QuotientAddGroup.lift _ (DFinsupp.sumAddHom c.ι.app) ?_
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

/-- (implementation detail) A morphism of commutative additive groups `Quot F →+ A`
induces a cocone on `F` as long as the universes work out.
-/
@[simps]
def toCocone [DecidableEq J] {A : Type w} [AddCommGroup A] (f : Quot F →+ A) : Cocone F where
  pt := AddCommGrp.of A
  ι := { app := fun j => f.comp (Quot.ι F j) }

lemma Quot.desc_toCocone_desc [DecidableEq J] {A : Type w} [AddCommGroup A] (f : Quot F →+ A)
    (hc : IsColimit c) : (hc.desc (toCocone F f)).comp (Quot.desc F c) = f := by
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
  desc s := AddCommGrp.ofHom ((Quot.desc F s).comp (AddEquiv.ofBijective
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
    suffices eq : m.comp (AddEquiv.ofBijective (Quot.desc F c) h) = Quot.desc F s by
      rw [← eq]; rfl
    exact Quot.addMonoidHom_ext F (by simp [← hm])

/-- (internal implementation) The colimit cocone of a functor `F`, implemented as a quotient of
`DFinsupp (fun j ↦ F.obj j)`, under the assumption that said quotient is small.
-/
@[simps]
noncomputable def colimitCocone [DecidableEq J] [Small.{w} (Quot.{w} F)] : Cocone F where
  pt := AddCommGrp.of (Shrink (Quot F))
  ι :=
    { app j :=
        AddCommGrp.ofHom (Shrink.addEquiv.symm.toAddMonoidHom.comp (Quot.ι F j))
      naturality _ _ _ := by
        ext
        dsimp
        simp only [Category.comp_id, ofHom_apply, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe,
          Function.comp_apply]
        change Shrink.addEquiv.symm _ = _
        rw [Quot.map_ι] }

@[simp]
theorem Quot.desc_colimitCocone [DecidableEq J] (F : J ⥤ AddCommGrp.{w}) [Small.{w} (Quot F)] :
    Quot.desc F (colimitCocone F) = (Shrink.addEquiv (α := Quot F)).symm.toAddMonoidHom := by
  refine Quot.addMonoidHom_ext F (fun j x ↦ ?_)
  simp only [colimitCocone_pt, coe_of, AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
  erw [Quot.ι_desc]
  simp

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

instance hasColimit [Small.{w} J] (F : J ⥤ AddCommGrp.{w}) : HasColimit F := by
  classical
  exact hasColimit_of_small_quot F inferInstance


/--
If `J` is `w`-small, then any functor `J ⥤ AddCommGrp.{w}` has a colimit.
-/
instance hasColimitsOfShape [Small.{w} J] : HasColimitsOfShape J (AddCommGrp.{w}) where

/-- The category of additive commutative groups has all small colimits.
-/
instance (priority := 1300) hasColimitsOfSize [UnivLE.{u, w}] :
    HasColimitsOfSize.{v, u} (AddCommGrp.{w}) where

end AddCommGrp

namespace AddCommGrp

open QuotientAddGroup

/-- The categorical cokernel of a morphism in `AddCommGrp`
agrees with the usual group-theoretical quotient.
-/
noncomputable def cokernelIsoQuotient {G H : AddCommGrp.{u}} (f : G ⟶ H) :
    cokernel f ≅ AddCommGrp.of (H ⧸ AddMonoidHom.range f) where
  hom := cokernel.desc f (mk' _) <| by
        ext x
        apply Quotient.sound
        apply leftRel_apply.mpr
        fconstructor
        · exact -x
        · simp only [add_zero, AddMonoidHom.map_neg]
  inv :=
    QuotientAddGroup.lift _ (cokernel.π f) <| by
      rintro _ ⟨x, rfl⟩
      exact cokernel.condition_apply f x
  hom_inv_id := by
    refine coequalizer.hom_ext ?_
    simp only [coequalizer_as_cokernel, cokernel.π_desc_assoc, Category.comp_id]
    rfl
  inv_hom_id := by
    ext x
    exact QuotientAddGroup.induction_on x <| cokernel.π_desc_apply f _ _

end AddCommGrp
