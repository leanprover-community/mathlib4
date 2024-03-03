/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.FinallySmall
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Filtered.Small
import Mathlib.Logic.Small.Set
import Mathlib.CategoryTheory.Limits.FunctorToTypes
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.Limits.Preserves.Ulift

/-!
# Ind-objects

For a presheaf `A : Cᵒᵖ ⥤ Type v` we define the type `IndObjectPresentation A` of presentations
of `A` as a small filtered colimit of representable presheaves and define the predicate
`IsIndObject A` asserting that there is at least one such presentation.

A presheaf is an ind-object if and only if the category `CostructuredArrow yoneda A` is filtered
and finally small. In this way, `CostructuredArrow yoneda A` can be thought of the universal
indexing category for the representation of `A` as a small filtered colimit of representable
presheaves.

## Future work

There are various useful ways to understand natural transformations between ind-objects in terms
of their presentations.

The ind-objects form a locally `v`-small category `IndCategory C` which has numerous interesting
properties.

## Implementation notes

One might be tempted to introduce another universe parameter and consider being a `w`-ind-object
as a property of presheaves `C ⥤ TypeMax.{v, w}`. This comes with significant technical hurdles.
The recommended alternative is to consider ind-objects over `ULiftHom.{w} C` instead.

## References
* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Chapter 6
-/

universe w v u

namespace CategoryTheory.Limits

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- The data that witnesses that a presheaf `A` is an ind-object. It consists of a small
    filtered indexing category `I`, a diagram `F : I ⥤ C` and the data for a colimit cocone on
    `F ⋙ yoneda : I ⥤ Cᵒᵖ ⥤ Type v` with cocone point `A`. -/
structure IndObjectPresentation (A : Cᵒᵖ ⥤ Type v) where
  /-- The indexing category of the filtered colimit presentation -/
  I : Type v
  /-- The indexing category of the filtered colimit presentation -/
  [ℐ : SmallCategory I]
  [hI : IsFiltered I]
  /-- The diagram of the filtered colimit presentation -/
  F : I ⥤ C
  /-- Use `IndObjectPresentation.cocone` instead. -/
  ι : F ⋙ yoneda ⟶ (Functor.const I).obj A
  /-- Use `IndObjectPresenation.coconeIsColimit` instead. -/
  isColimit : IsColimit (Cocone.mk A ι)

namespace IndObjectPresentation

variable {A : Cᵒᵖ ⥤ Type v} (P : IndObjectPresentation A)

instance : SmallCategory P.I := P.ℐ
instance : IsFiltered P.I := P.hI

/-- The (colimit) cocone with cocone point `A`. -/
@[simps pt]
def cocone : Cocone (P.F ⋙ yoneda) where
  pt := A
  ι := P.ι

/-- `P.cocone` is a colimit cocone. -/
def coconeIsColimit : IsColimit P.cocone :=
  P.isColimit

/-- The canonical comparison functor between the indexing category of the presentation and the
    comma category `CostructuredArrow yoneda A`. This functor is always final. -/
@[simps! obj_left obj_right_as obj_hom map_left]
def toCostructuredArrow : P.I ⥤ CostructuredArrow yoneda A :=
  P.cocone.toCostructuredArrow ⋙ CostructuredArrow.pre _ _ _

instance : P.toCostructuredArrow.Final :=
  final_toCostructuredArrow_comp_pre _ P.coconeIsColimit

/-- Representable presheaves are (trivially) ind-objects. -/
@[simps]
def yoneda (X : C) : IndObjectPresentation (yoneda.obj X) where
  I := Discrete PUnit.{v + 1}
  F := Functor.fromPUnit X
  ι := { app := fun s => 𝟙 _ }
  isColimit :=
    { desc := fun s => s.ι.app ⟨PUnit.unit⟩
      uniq := fun s m h => h ⟨PUnit.unit⟩ }

end IndObjectPresentation

/-- A presheaf is called an ind-object if it can be written as a filtered colimit of representable
    presheaves. -/
structure IsIndObject (A : Cᵒᵖ ⥤ Type v) : Prop where
  mk' :: nonempty_presentation : Nonempty (IndObjectPresentation A)

theorem IsIndObject.mk {A : Cᵒᵖ ⥤ Type v} (P : IndObjectPresentation A) : IsIndObject A :=
  ⟨⟨P⟩⟩

/-- Representable presheaves are (trivially) ind-objects. -/
theorem isIndObject_yoneda (X : C) : IsIndObject (yoneda.obj X) :=
  .mk <| IndObjectPresentation.yoneda X

namespace IsIndObject

variable {A : Cᵒᵖ ⥤ Type v}

/-- Pick a presentation for an ind-object using choice. -/
noncomputable def presentation : IsIndObject A → IndObjectPresentation A
  | ⟨P⟩ => P.some

theorem isFiltered (h : IsIndObject A) : IsFiltered (CostructuredArrow yoneda A) :=
  IsFiltered.of_final h.presentation.toCostructuredArrow

theorem finallySmall (h : IsIndObject A) : FinallySmall.{v} (CostructuredArrow yoneda A) :=
  FinallySmall.mk' h.presentation.toCostructuredArrow

end IsIndObject

open IsFiltered.SmallFilteredIntermediate

theorem isIndObject_of_isFiltered_of_finallySmall (A : Cᵒᵖ ⥤ Type v)
    [IsFiltered (CostructuredArrow yoneda A)] [FinallySmall.{v} (CostructuredArrow yoneda A)] :
    IsIndObject A := by
  have h₁ : (factoring (fromFinalModel (CostructuredArrow yoneda A)) ⋙
      inclusion (fromFinalModel (CostructuredArrow yoneda A))).Final := Functor.final_of_natIso
    (factoringCompInclusion (fromFinalModel <| CostructuredArrow yoneda A)).symm
  have h₂ : Functor.Final (inclusion (fromFinalModel (CostructuredArrow yoneda A))) :=
    Functor.final_of_comp_full_faithful' (factoring _) (inclusion _)
  let c := (tautologicalCocone A).whisker (inclusion (fromFinalModel (CostructuredArrow yoneda A)))
  let hc : IsColimit c := (Functor.Final.isColimitWhiskerEquiv _ _).symm
    (isColimitTautologicalCocone A)
  have hq : Nonempty (FinalModel (CostructuredArrow yoneda A)) := Nonempty.map
    (Functor.Final.lift (fromFinalModel (CostructuredArrow yoneda A))) IsFiltered.nonempty
  exact ⟨_, inclusion (fromFinalModel _) ⋙ CostructuredArrow.proj yoneda A, c.ι, hc⟩

/-- The recognition theorem for ind-objects: `A : Cᵒᵖ ⥤ Type v` is an ind-object if and only if
    `CostructuredArrow yoneda A` is filtered and finally `v`-small.

    Theorem 6.1.5 of [Kashiwara2006] -/
theorem isIndObject_iff (A : Cᵒᵖ ⥤ Type v) : IsIndObject A ↔
    (IsFiltered (CostructuredArrow yoneda A) ∧ FinallySmall.{v} (CostructuredArrow yoneda A)) :=
  ⟨fun h => ⟨h.isFiltered, h.finallySmall⟩,
   fun ⟨_, _⟩ => isIndObject_of_isFiltered_of_finallySmall A⟩

-- section Experiments

-- variable {I : Type v} [SmallCategory I] [IsFilteredOrEmpty I] (F : I ⥤ Cᵒᵖ ⥤ Type v)
--   (hF : ∀ i, IsIndObject (F.obj i))

-- noncomputable def lhs : (CostructuredArrow yoneda (colimit F))ᵒᵖ ⥤ TypeMax.{u, v} :=
--   (CostructuredArrow.toOver _ _).op ⋙ yoneda.obj (Over.mk (𝟙 (colimit F)))

-- noncomputable def theOther (X : CostructuredArrow yoneda (colimit F)) : TypeMax.{u, v} :=
--   (CostructuredArrow.toOver _ _).obj X ⟶ Over.mk (𝟙 (colimit F))


-- -- Surely the ulift is a bad bad idea....
-- noncomputable def innermost (X : CostructuredArrow yoneda (colimit F)) (i : I) :
--     CostructuredArrow yoneda (F.obj i) ⥤ TypeMax.{u, v} :=
--   CostructuredArrow.map (colimit.ι F i) ⋙ coyoneda.obj (Opposite.op X) ⋙ uliftFunctor.{u}

-- noncomputable def next (X : CostructuredArrow yoneda (colimit F)) :
--     I ⥤ TypeMax.{u, v} where
--   obj i := limit (innermost F X i)
--   map := sorry
--   map_id := sorry
--   map_comp := sorry

-- end Experiments

section Good

variable {I : Type v} [SmallCategory I] [IsFiltered I] (F : I ⥤ Cᵒᵖ ⥤ Type v)
  (hF : ∀ i, IsIndObject (F.obj i))

variable {J : Type v} [SmallCategory J] [FinCategory J]

variable (G : J ⥤ CostructuredArrow yoneda (colimit F))

theorem step₁ : Nonempty <| limit <|
  G.op ⋙
    (CostructuredArrow.toOver yoneda (colimit F)).op ⋙
    yoneda.toPrefunctor.obj (Over.mk (𝟙 (colimit F))) := by
  refine ⟨Types.Limit.mk _ (fun j => Over.mkIdTerminal.from _) ?_⟩
  intros
  simp only [Functor.comp_obj, Functor.op_obj, Opposite.unop_op, yoneda_obj_obj, Functor.comp_map,
    Functor.op_map, Quiver.Hom.unop_op, yoneda_obj_map, IsTerminal.comp_from]

theorem step₂ : Nonempty <| limit <|
  G.op ⋙ (CostructuredArrow.toOver yoneda (colimit F)).op ⋙
    yoneda.obj (colimit.cocone F).toOver.pt :=
  step₁ _ _

theorem step₃ : Nonempty <| limit <|
  G.op ⋙ (CostructuredArrow.toOver yoneda (colimit F)).op ⋙
    yoneda.obj (colimit ((colimit.cocone F).toCostructuredArrow ⋙ CostructuredArrow.toOver _ _)) := by
  refine Nonempty.map ?_ (step₂ F G)
  let t : (colimit.cocone F).toOver.pt ≅ (colimit ((colimit.cocone F).toCostructuredArrow ⋙ CostructuredArrow.toOver _ _)) :=
    IsColimit.coconePointUniqueUpToIso (Over.isColimitToOver (colimit.isColimit F)) (colimit.isColimit _)
  let t' := whiskerLeft (G.op ⋙ (CostructuredArrow.toOver yoneda (colimit F)).op) (yoneda.map t.hom)
  exact limMap t'

@[simps! obj]
noncomputable def myFunctor : I ⥤ (Over (colimit.cocone F).pt)ᵒᵖ ⥤ Type (max u v) :=
  (colimit.cocone F).toCostructuredArrow ⋙ CostructuredArrow.toOver _ _ ⋙ yoneda

def curriedYonedaLemmaPt {C : Type u} [Category.{v} C] (P : Cᵒᵖ ⥤ Type v) :
    yoneda.op ⋙ yoneda.obj P ≅ P ⋙ uliftFunctor.{u} :=
  NatIso.ofComponents (fun X => yonedaSections _ _) (by
    intros X Y f
    ext g
    rw [← ULift.down_inj]
    simpa using congrFun (g.naturality f) (𝟙 _))

noncomputable def fullCurriedYonedaLemma (C : Type u) [Category.{v} C] :
    yoneda.op ⋙ coyoneda ≅ evaluation Cᵒᵖ (Type v) ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u} :=
  NatIso.ofComponents (fun X => NatIso.ofComponents (fun Y => yonedaSections _ _) (by aesop_cat)) (by
    intros X Y f
    dsimp
    ext g x
    dsimp
    rw [← ULift.down_inj]
    simpa using congrFun (x.naturality f) (𝟙 _))

noncomputable def want : (CostructuredArrow yoneda (colimit.cocone F).pt)ᵒᵖ ⥤ I ⥤ Type (max u v) :=
  yoneda.op ⋙ coyoneda ⋙ (whiskeringLeft _ _ _).obj
    ((colimit.cocone F).toCostructuredArrow ⋙ CostructuredArrow.toOver _ _ ⋙
        (overEquivPresheafCostructuredArrow (colimit.cocone F).pt).functor)
@[simps!]
noncomputable def want₂ : (CostructuredArrow yoneda (colimit.cocone F).pt)ᵒᵖ ⥤ I ⥤ Type (max u v) :=
  evaluation _ (Type v) ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{max u v} ⋙
    (whiskeringLeft _ _ _).obj
    ((colimit.cocone F).toCostructuredArrow ⋙ CostructuredArrow.toOver _ _ ⋙
        (overEquivPresheafCostructuredArrow (colimit.cocone F).pt).functor)

@[simps!]
noncomputable def hv : (CostructuredArrow yoneda (colimit.cocone F).pt)ᵒᵖ ⥤ I ⥤ Type (max u v) :=
  Functor.flip
      (((Cocone.toCostructuredArrow (colimit.cocone F) ⋙ CostructuredArrow.toOver F (colimit.cocone F).pt) ⋙
          (overEquivPresheafCostructuredArrow (colimit.cocone F).pt).functor) ⋙
        (whiskeringRight (CostructuredArrow yoneda (colimit.cocone F).pt)ᵒᵖ (Type v) (Type (max u v))).toPrefunctor.obj
          uliftFunctor.{max u v, v})

noncomputable def myIso : hv F ≅ want₂ F :=
  Iso.refl _

noncomputable def interchange :
  G.op ⋙ (CostructuredArrow.toOver yoneda (colimit.cocone F).pt).op ⋙
    yoneda.obj (colimit ((colimit.cocone F).toCostructuredArrow ⋙ CostructuredArrow.toOver _ _)) ≅
  G.op ⋙ (CostructuredArrow.toOver yoneda (colimit.cocone F).pt).op ⋙
    colimit (myFunctor F) := by
  dsimp only [myFunctor]
  refine isoWhiskerLeft G.op ((CostructuredArrow.toOverCompYoneda (colimit.cocone F).pt _) ≪≫ ?_)
  refine curriedYonedaLemmaPt _ ≪≫ ?_
  let u := isoWhiskerRight (preservesColimitIso (overEquivPresheafCostructuredArrow (colimit.cocone F).pt).functor
    (Cocone.toCostructuredArrow (colimit.cocone F) ⋙ CostructuredArrow.toOver F (colimit.cocone F).pt)) uliftFunctor
  refine u ≪≫ ?_
  refine isoWhiskerRight (colimitIsoFlipCompColim _) uliftFunctor ≪≫ ?_
  refine Functor.associator _ _ _ ≪≫ ?_
  refine isoWhiskerLeft _ (preservesColimitNatIso _) ≪≫ ?_
  refine (Functor.associator _ _ _).symm ≪≫ ?_
  refine isoWhiskerRight (flipCompWhiskeringRightObj _ _) _ ≪≫ ?_
  refine isoWhiskerRight (myIso F) colim ≪≫ ?_
  dsimp only [want₂]
  refine isoWhiskerRight (Functor.associator _ _ _).symm _ ≪≫ ?_

  let x := (fullCurriedYonedaLemma (CostructuredArrow yoneda (colimit.cocone F).pt)).symm
  refine isoWhiskerRight (isoWhiskerRight x _) _ ≪≫ ?_

  let a := (Functor.associator (Cocone.toCostructuredArrow (colimit.cocone F))
          (CostructuredArrow.toOver F (colimit.cocone F).pt)
            ((overEquivPresheafCostructuredArrow (colimit.cocone F).pt).functor)).symm
  let a' := (whiskeringLeft _ _ (Type (max u v))).mapIso a
  refine isoWhiskerRight (isoWhiskerLeft _ a') _ ≪≫ ?_
  clear u x a a'
  refine isoWhiskerRight (isoWhiskerLeft _ (whiskeringLeftComp _ _)) _ ≪≫ ?_
  refine isoWhiskerRight (Functor.associator _ _ _) _ ≪≫ ?_
  let y := CostructuredArrow.yoneda' (colimit.cocone F).pt

  refine isoWhiskerRight (isoWhiskerRight y.symm
    ((whiskeringLeft I (Over (colimit.cocone F).pt) (Type (max u v))).toPrefunctor.obj
            (Cocone.toCostructuredArrow (colimit.cocone F) ⋙ CostructuredArrow.toOver F (colimit.cocone F).pt))) colim ≪≫ ?_

  refine ?_ ≪≫ isoWhiskerLeft _ (colimitIsoFlipCompColim _).symm
  exact Iso.refl _

theorem step₄ : Nonempty <| limit <|
  G.op ⋙ (CostructuredArrow.toOver yoneda (colimit.cocone F).pt).op ⋙
    colimit ((colimit.cocone F).toCostructuredArrow ⋙ CostructuredArrow.toOver _ _ ⋙ yoneda) := by
  refine Nonempty.map ?_ (step₃ F G)
  exact limMap (interchange F G).hom

noncomputable def myBetterFunctor : I ⥤ Jᵒᵖ ⥤ Type (max u v) :=
  (colimit.cocone F).toCostructuredArrow ⋙ CostructuredArrow.toOver _ _ ⋙ yoneda ⋙
    (whiskeringLeft _ _ _).obj (G.op ⋙ (CostructuredArrow.toOver yoneda (colimit.cocone F).pt).op)

noncomputable def interchange₂ :
  G.op ⋙ (CostructuredArrow.toOver yoneda (colimit.cocone F).pt).op ⋙
    colimit ((colimit.cocone F).toCostructuredArrow ⋙ CostructuredArrow.toOver _ _ ⋙ yoneda) ≅
    colimit (myBetterFunctor F G) := by
  dsimp only [myBetterFunctor]
  refine isoWhiskerLeft _ (isoWhiskerLeft _ (colimitIsoFlipCompColim _)) ≪≫ ?_
  refine ?_ ≪≫ (colimitIsoFlipCompColim _).symm
  rfl

theorem step₅ : Nonempty <| limit <| colimit <| myBetterFunctor F G := by
  refine Nonempty.map ?_ (step₄ F G)
  exact limMap (interchange₂ F G).hom

theorem step₆ : Nonempty <| colimit <| limit <| (myBetterFunctor F G).flip := by
  let i := colimitLimitIsoMax (myBetterFunctor F G).flip
  refine Nonempty.map ?_ (step₅ F G)
  exact i.inv

theorem step₇ : ∃ i, Nonempty <| limit <| (myBetterFunctor F G).obj i := by
  obtain ⟨t⟩ := step₆ F G
  obtain ⟨i, y, -⟩ := Types.jointly_surjective'.{v, max u v} t
  refine ⟨i, ⟨?_⟩⟩
  let z := (limitObjIsoLimitCompEvaluation (myBetterFunctor F G).flip i).hom y
  let y := flipCompEvaluation (myBetterFunctor F G) i
  exact (lim.mapIso y).hom z

noncomputable def i : I := (step₇ F G).choose

theorem step₈ : Nonempty <| limit <| (myBetterFunctor F G).obj (i F G) :=
  (step₇ F G).choose_spec

noncomputable def pointwiseFunctor : Jᵒᵖ ⥤ Type (max u v) :=
  G.op ⋙ (CostructuredArrow.toOver yoneda (colimit.cocone F).pt).op ⋙
    yoneda.obj (Over.mk <| colimit.ι F (i F G))

noncomputable def betterIsoPointwise : (myBetterFunctor F G).obj (i F G) ≅ pointwiseFunctor F G :=
  Iso.refl _

theorem step₉ : Nonempty <| limit <| pointwiseFunctor F G :=
  step₈ F G

abbrev K : Type v := (hF (i F G)).presentation.I

noncomputable def Kc : Cocone ((hF (i F G)).presentation.F ⋙ yoneda) :=
  (hF (i F G)).presentation.cocone

noncomputable def Kcl : IsColimit (Kc F hF G) :=
  (hF (i F G)).presentation.coconeIsColimit

noncomputable example : SmallCategory (K F hF G) := inferInstance

@[pp_with_univ]
structure IsGood (K : Jᵒᵖ ⥤ Type w) : Prop where
  implies_nonempty : Nonempty (limit K) → ∃ Z, Nonempty (limit (G.op ⋙ yoneda.obj Z))

theorem IsGood.start (Z : CostructuredArrow yoneda (colimit F)) : IsGood.{v} F G (G.op ⋙ yoneda.obj Z) where
  implies_nonempty h := ⟨Z, h⟩

-- noncomputable def bla (i : I) :
--     CostructuredArrow yoneda (F.obj i) ⥤ (CostructuredArrow yoneda (colimit F))ᵒᵖ ⥤ Type v :=
--   CostructuredArrow.map (colimit.ι F i) ⋙ yoneda

-- noncomputable def bla₂ (i : I) : (CostructuredArrow yoneda (colimit F))ᵒᵖ ⥤ Type v :=
--   colimit (bla F i)

noncomputable def yeah (i : I) : Jᵒᵖ ⥤ (hF i).presentation.I ⥤ Type v :=
  G.op ⋙ coyoneda ⋙ (whiskeringLeft _ _ _).obj
    ((hF i).presentation.toCostructuredArrow ⋙ CostructuredArrow.map (colimit.ι F i))

-- @[simps]
-- noncomputable def nextFunctor (i : I) : (CostructuredArrow yoneda (colimit F))ᵒᵖ ⥤ TypeMax.{u, v} where
--   obj X := colimit (CostructuredArrow.map (colimit.ι F i) ⋙ coyoneda.obj X ⋙ uliftFunctor.{u})
--   map {X Y} η := colimMap
--     { app := fun Z x => ⟨η.unop ≫ x.down⟩
--       naturality := sorry }
--   map_id := sorry
--   map_comp := sorry

theorem IsGood.step₁ (i : I) : IsGood.{v} F G (colimit (yeah F hF G i).flip) where
  implies_nonempty h := by
    rcases h with ⟨x⟩
    let y := (colimitLimitIso (yeah F hF G i)).inv x
    obtain ⟨j, z, -⟩ := Types.jointly_surjective'.{v, v} y
    refine ⟨(CostructuredArrow.map (colimit.ι F i)).obj ((hF i).presentation.toCostructuredArrow.obj j), ?_⟩
    refine ⟨(preservesLimitIso ((evaluation _ _).obj j) (yeah F hF G i)).hom z⟩


theorem IsGood.goal : IsGood.{max u v} F G <|
    (G ⋙ CostructuredArrow.toOver yoneda (colimit F)).op ⋙ yoneda.obj (Over.mk (𝟙 (colimit F))) :=
  sorry

end Good

theorem isIndObject_colimit (I : Type v) [SmallCategory I] [IsFilteredOrEmpty I]
    (F : I ⥤ Cᵒᵖ ⥤ Type v) (hF : ∀ i, IsIndObject (F.obj i)) : IsIndObject (colimit F) := by
  suffices IsFiltered (CostructuredArrow yoneda (colimit F)) by
    refine (isIndObject_iff _).mpr ⟨this, ?_⟩
    have : ∀ i, ∃ (s : Set (CostructuredArrow yoneda (F.obj i))) (_ : Small.{v} s),
        ∀ i, ∃ j ∈ s, Nonempty (i ⟶ j) :=
      fun i => (hF i).finallySmall.exists_small_weakly_terminal_set
    choose s hs j hjs hj using this
    refine finallySmall_of_small_weakly_terminal_set
      (⋃ i, (CostructuredArrow.map (colimit.ι F i)).obj '' (s i)) (fun A => ?_)
    obtain ⟨i, y, hy⟩ := FunctorToTypes.jointly_surjective'.{v, v} F _ (yonedaEquiv A.hom)
    let y' : CostructuredArrow yoneda (F.obj i) := CostructuredArrow.mk (yonedaEquiv.symm y)
    obtain ⟨x⟩ := hj _ y'
    refine ⟨(CostructuredArrow.map (colimit.ι F i)).obj (j i y'), ?_, ⟨?_⟩⟩
    · simp only [Set.mem_iUnion, Set.mem_image]
      refine ⟨i, j i y', hjs _ _, rfl⟩
    · refine ?_ ≫ (CostructuredArrow.map (colimit.ι F i)).map x
      refine CostructuredArrow.homMk (𝟙 A.left) (yonedaEquiv.injective ?_)
      simp [-EmbeddingLike.apply_eq_iff_eq, hy, yonedaEquiv_comp]

  refine IsFiltered.iff_nonempty_limit.mpr (fun {J _ _} G => ?_)
  -- have h₁ : Nonempty ()
  refine (IsGood.goal F G).implies_nonempty ⟨?_⟩
  refine Types.Limit.mk _ (fun j => Over.mkIdTerminal.from _) ?_
  intros
  simp only [Functor.comp_obj, Functor.op_obj, Opposite.unop_op, yoneda_obj_obj, Functor.comp_map,
    Functor.op_map, Quiver.Hom.unop_op, yoneda_obj_map, IsTerminal.comp_from]

end CategoryTheory.Limits
