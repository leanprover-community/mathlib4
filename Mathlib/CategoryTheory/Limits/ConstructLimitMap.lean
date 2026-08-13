/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Comma.Final
public import Mathlib.CategoryTheory.Presentable.Basic

/-!
# Morphisms between (co)filtered (co)limits

Let `D : I ⥤ C` and `D' : I' ⥤ C` be cofiltered diagrams with limit cones `c` and `c'` and let
`f : c.pt ⟶ c'.pt` be an arbitrary morphism between the limits. We show that if `Hom(-, D'.obj i')`
preserves the colimit of `D.op`, then `f` is induced by a natural transformation of diagrams.
We also show the dual result.
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits

@[expose] public section

variable {C : Type u₁} [Category.{v₁} C] {I : Type u₂} [Category.{v₂} I]
  {I' : Type u₃} [Category.{v₃} I'] {D : I ⥤ C} {D' : I' ⥤ C}

namespace ConstructLimitMap

variable {c : Cone D} {c' : Cone D'} (hc : IsLimit c) (hc' : IsLimit c') (f : c.pt ⟶ c'.pt)

private abbrev left (c : Cone D) : I ⥤ Under c.pt :=
  c.toStructuredArrow ⋙ StructuredArrow.toUnder c.pt D

private abbrev right (c' : Cone D') (f : c.pt ⟶ c'.pt) : I' ⥤ Under c.pt :=
  (c'.toStructuredArrow ⋙ StructuredArrow.toUnder c'.pt D') ⋙ Under.map f

set_option backward.isDefEq.respectTransparency false in
/-- The tautological natural transformation on the comma category of `f`-compatible squares,
inducing `f` on limits (see `ConstructLimitMap.eq_isLimitMap`). -/
@[simps]
private def map : Comma.fst (left c) (right c' f) ⋙ D ⟶ Comma.snd (left c) (right c' f) ⋙ D' where
  app A := A.hom.right
  naturality _ _ u := by simpa using congrArg CommaMorphism.right u.w

variable [IsCofiltered I] [∀ i : I', PreservesColimit D.op (yoneda.obj (D'.obj i))]

include hc

set_option backward.isDefEq.respectTransparency false in
private lemma isCofiltered_costructuredArrow (i' : I') :
    IsCofiltered (CostructuredArrow (left c) ((right c' f).obj i')) := by
  refine isCofiltered_costructuredArrow_of_isCofiltered_of_exists _ _ ?_ ?_
  · obtain ⟨j, p, hp⟩ := exists_hom_of_preservesColimit_yoneda hc (f ≫ c'.π.app i')
    exact ⟨j, ⟨Under.homMk p hp⟩⟩
  · intro a s s'
    obtain ⟨j, t, ht⟩ := exists_eq_of_preservesColimit_yoneda_self (X := D'.obj i') (i := a) hc
      s.right s'.right ((Under.w s).trans (Under.w s').symm)
    exact ⟨j, t, by ext; simpa using ht⟩

private lemma initial_snd : (Comma.snd (left c) (right c' f)).Initial := by
  have (i' : I') : IsConnected (CostructuredArrow (left c) ((right c' f).obj i')) :=
    have := isCofiltered_costructuredArrow hc f i'
    IsCofiltered.isConnected _
  exact Comma.initial_snd_of_isConnected_costructuredArrow _ _

variable [IsCofiltered I']

end ConstructLimitMap

open ConstructLimitMap in
set_option backward.isDefEq.respectTransparency false in
/-- A morphism `f` between cofiltered limits, where every object of the target diagram is
presentable relative to the source diagram, is initially induced by a natural transformation of
diagrams. -/
lemma Limits.exists_eq_isLimitMap_of_preservesColimit_yoneda
    {c : Cone D} {c' : Cone D'} (hc : IsLimit c) (hc' : IsLimit c') (f : c.pt ⟶ c'.pt)
    [IsCofiltered I] [IsCofiltered I']
    [∀ i : I', PreservesColimit D.op (yoneda.obj (D'.obj i))] :
    ∃ (J : Type (max u₂ u₃ v₁))
      (_ : Category.{max v₂ v₃} J) (_ : IsCofiltered J) (G : J ⥤ I) (G' : J ⥤ I')
      (_ : G.Initial) (_ : G'.Initial) (g : G ⋙ D ⟶ G' ⋙ D'),
      f = IsLimit.map (c.whisker _) ((Functor.Initial.isLimitWhiskerEquiv _ _).symm hc') g := by
  have := isCofiltered_costructuredArrow hc f
  have := Comma.isCofiltered_of_isCofiltered_costructuredArrow (left c) (right c' f)
  have := Comma.initial_fst_of_isCofiltered_costructuredArrow (left c) (right c' f)
  have := ConstructLimitMap.initial_snd hc f
  refine ⟨_, inferInstance, inferInstance, _, _, inferInstance, inferInstance,
    ConstructLimitMap.map f, ?_⟩
  apply ((Functor.Initial.isLimitWhiskerEquiv _ _).symm hc').hom_ext
  intro A
  rw [IsLimit.map_π]
  exact (Under.w A.hom).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A morphism `f` between filtered colimits, where every object of the source diagram is
presentable relative to the target diagram, is finally induced by a natural transformation of
diagrams.is induced by a natural transformation of diagrams. -/
lemma Limits.exists_eq_isColimitMap_of_preservesColimit_coyoneda
    {c : Cocone D} {c' : Cocone D'} (hc : IsColimit c) (hc' : IsColimit c') (f : c.pt ⟶ c'.pt)
    [IsFiltered I] [IsFiltered I']
    [∀ i : I, PreservesColimit D' (coyoneda.obj (.op (D.obj i)))] :
    ∃ (J : Type (max u₂ u₃ v₁))
      (_ : Category.{max v₂ v₃} J) (_ : IsFiltered J) (G : J ⥤ I) (G' : J ⥤ I')
      (_ : G.Final) (_ : G'.Final) (g : G ⋙ D ⟶ G' ⋙ D'),
      f = IsColimit.map ((Functor.Final.isColimitWhiskerEquiv _ _).symm hc) (c'.whisker _) g := by
  have (i : Iᵒᵖ) : PreservesColimit D'.op.op (yoneda.obj (D.op.obj i)) := by
    suffices PreservesColimit (D'.op.op ⋙ unopUnop C) (coyoneda.obj (.op (D.obj i.unop))) from
      let iso : yoneda.obj (.op (D.obj i.unop)) ≅ unopUnop C ⋙ coyoneda.obj (.op (D.obj i.unop)) :=
        NatIso.ofComponents fun W ↦ (opEquiv _ _).toIso
      preservesColimit_of_natIso D'.op.op iso.symm
    rw [← Functor.Final.preservesColimit_comp_iff (opOp I')]
    let iso : opOp I' ⋙ D'.op.op ⋙ unopUnop C ≅ D' := .refl _
    exact preservesColimit_of_iso_diagram _ iso.symm
  obtain ⟨J, _, _, G, G', _, _, g, hg⟩ :=
    exists_eq_isLimitMap_of_preservesColimit_yoneda hc'.op hc.op f.op
  have := NatTrans.leftOp g
  refine ⟨Jᵒᵖ, inferInstance, inferInstance, G'.leftOp, G.leftOp, inferInstance, inferInstance,
    NatTrans.leftOp g, ?_⟩
  refine Quiver.Hom.op_inj ?_
  rw [hg]
  refine ((Functor.Initial.isLimitWhiskerEquiv G' c.op).symm hc.op).hom_ext fun k ↦ ?_
  rw [IsLimit.map_π]
  dsimp
  rw [← op_comp]
  simp [dsimp% ((Functor.Final.isColimitWhiskerEquiv G'.leftOp c).symm hc).ι_map]

end

end CategoryTheory
