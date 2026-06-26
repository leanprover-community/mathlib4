/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Comma.Final
public import Mathlib.CategoryTheory.Limits.ConeCategory
public import Mathlib.CategoryTheory.Presentable.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites

/-!
# Morphisms between (co)filtered (co)limits

Let `D : I ⥤ C` and `D' : I' ⥤ C` be cofiltered diagrams with limit cones `c` and `c'` and let
`f : c.pt ⟶ c'.pt` be an arbitrary morphism between the limits. We show that if every `D'.obj i'`
is cocompact relative to `D`, i.e. `yoneda.obj (D'.obj i')` preserves the colimit of `D.op`,
then `f` is induced by a natural transformation of diagrams: there exists a cofiltered category
`J` with initial functors `G : J ⥤ I` and `G' : J ⥤ I'` and a natural transformation
`g : G ⋙ D ⟶ G' ⋙ D'` inducing `f` on limits. See
`CategoryTheory.Limits.exists_eq_isLimitMap_of_preservesColimit_yoneda`.

We also show the dual result.
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits

@[expose] public section

variable {C : Type u₁} [Category.{v₁} C]
  {I : Type u₂} {I' : Type u₃} [Category.{v₂} I] [Category.{v₃} I']
  {D : I ⥤ C} {D' : I' ⥤ C}

namespace ConstructLimitMap

variable {c : Cone D} {c' : Cone D'} (hc : IsLimit c) (hc' : IsLimit c') (f : c.pt ⟶ c'.pt)

/-- (Implementation): `Limits.exists_eq_isLimitMap_of_preservesColimit_yoneda`. -/
private abbrev left (c : Cone D) : I ⥤ Under c.pt :=
  c.toStructuredArrow ⋙ StructuredArrow.toUnder c.pt D

/-- The diagram `D'` lifted along `f` to the under category of the cone point of `c`. This is
the right leg of the comma category indexing the levelwise construction of `f`. -/
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

set_option backward.isDefEq.respectTransparency false in
include hc in
private lemma isCofiltered_costructuredArrow (i' : I') :
    IsCofiltered (CostructuredArrow (left c) ((right c' f).obj i')) := by
  refine isCofiltered_costructuredArrow_of_isCofiltered_of_exists _ _ ?_ ?_
  · obtain ⟨j, p, hp⟩ := exists_hom_of_preservesColimit_yoneda hc (f ≫ c'.π.app i')
    exact ⟨j, ⟨Under.homMk p hp⟩⟩
  · intro a s s'
    obtain ⟨j, t, ht⟩ := exists_eq_of_preservesColimit_yoneda_self hc
      (show D.obj a ⟶ D'.obj i' from s.right) (show D.obj a ⟶ D'.obj i' from s'.right)
      ((Under.w s).trans (Under.w s').symm)
    exact ⟨j, t, by ext; simpa using ht⟩

include hc in
private lemma initial_snd : (Comma.snd (left c) (right c' f)).Initial := by
  have (i' : I') : IsConnected (CostructuredArrow (left c) ((right c' f).obj i')) :=
    have := isCofiltered_costructuredArrow hc f i'
    IsCofiltered.isConnected _
  exact Comma.initial_snd_of_isConnected_costructuredArrow _ _

variable [IsCofiltered I']

include hc in
private lemma isCofiltered : IsCofiltered (Comma (left c) (right c' f)) :=
  have := isCofiltered_costructuredArrow hc f
  Comma.isCofiltered_of_isCofiltered_costructuredArrow _ _

include hc in
private lemma initial_fst : (Comma.fst (left c) (right c' f)).Initial :=
  have := isCofiltered_costructuredArrow hc f
  Comma.initial_fst_of_isCofiltered_costructuredArrow _ _

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
  have := ConstructLimitMap.initial_fst hc f
  have := ConstructLimitMap.initial_snd hc f
  refine ⟨_, inferInstance, ConstructLimitMap.isCofiltered hc f, _, _, inferInstance, inferInstance,
    ConstructLimitMap.map f, ?_⟩
  apply ((Functor.Initial.isLimitWhiskerEquiv _ _).symm hc').hom_ext
  intro A
  rw [IsLimit.map_π]
  exact (Under.w A.hom).symm

set_option backward.isDefEq.respectTransparency false in
/-- A morphism `f` between filtered colimits, where every object of the source diagram is
compact relative to the target diagram, is induced by a natural transformation of diagrams
after restricting both index categories along final functors from a common filtered
category. -/
lemma Limits.exists_eq_isColimitMap_of_preservesColimit_coyoneda
    {c : Cocone D} {c' : Cocone D'} (hc : IsColimit c) (hc' : IsColimit c') (f : c.pt ⟶ c'.pt)
    [IsFiltered I] [IsFiltered I']
    [∀ i : I, PreservesColimit D' (coyoneda.obj (.op (D.obj i)))] :
    ∃ (J : Type (max u₂ u₃ v₁))
      (_ : Category.{max v₂ v₃} J) (_ : IsFiltered J) (G : J ⥤ I) (G' : J ⥤ I')
      (_ : G.Final) (_ : G'.Final) (g : G ⋙ D ⟶ G' ⋙ D'),
      f = IsColimit.map ((Functor.Final.isColimitWhiskerEquiv _ _).symm hc) (c'.whisker _) g := by
  have (i : Iᵒᵖ) : PreservesColimit D'.op.op (yoneda.obj (D.op.obj i)) := by
    let iso : yoneda.obj (.op (D.obj i.unop)) ≅ unopUnop C ⋙ coyoneda.obj (.op (D.obj i.unop)) :=
      NatIso.ofComponents fun W ↦ (opEquiv _ _).toIso
    suffices PreservesColimit (D'.op.op ⋙ unopUnop C) (coyoneda.obj (.op (D.obj i.unop))) from
      preservesColimit_of_natIso D'.op.op iso.symm
    let e : I'ᵒᵖᵒᵖ ≌ I' := opOpEquivalence I'
    refine ⟨fun {c} t => ⟨?_⟩⟩
    let t0 : IsColimit ((Cocone.whiskeringEquivalence e).inverse.obj c) :=
      (IsColimit.whiskerEquivalenceEquiv e).symm
        (t.ofIsoColimit ((Cocone.whiskeringEquivalence e).counitIso.app c).symm)
    exact ((isColimitOfPreserves _ t0).whiskerEquivalence e).ofIsoColimit
      ((Cocone.functoriality _ _).mapIso ((Cocone.whiskeringEquivalence e).counitIso.app c))
  obtain ⟨J, _, _, G, G', _, _, g, hg⟩ :=
    exists_eq_isLimitMap_of_preservesColimit_yoneda hc'.op hc.op f.op
  refine ⟨Jᵒᵖ, inferInstance, inferInstance, G'.leftOp, G.leftOp, inferInstance, inferInstance,
    NatTrans.leftOp g, ?_⟩
  refine Quiver.Hom.op_inj ?_
  rw [hg]
  refine ((Functor.Initial.isLimitWhiskerEquiv G' c.op).symm hc.op).hom_ext fun k ↦ ?_
  rw [IsLimit.map_π]
  rw [show (Cone.whisker G' c.op).π.app k
        = ((Cocone.whisker G'.leftOp c).ι.app (Opposite.op k)).op from rfl, ← op_comp,
    IsColimit.ι_map]
  simp
  rfl

end

end CategoryTheory
