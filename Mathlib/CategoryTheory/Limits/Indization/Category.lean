/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Limits.Indization.Equalizers
import Mathlib.CategoryTheory.Limits.Indization.LocallySmall
import Mathlib.CategoryTheory.Limits.Indization.Products
import Mathlib.CategoryTheory.Limits.Preserves.Presheaf

/-!
# The category of Ind-objects

We define the `v`-category of Ind-objects of a category `C`, called `Ind C`, as well as the functors
`Ind.yoneda : C ⥤ Ind C` and `Ind.inclusion C : Ind C ⥤ Cᵒᵖ ⥤ Type v`.

For a small filtered category `I`, we also define `Ind.lim I : (I ⥤ C) ⥤ Ind C` and show that
it preserves finite limits and finite colimits.

This file will mainly collect results about ind-objects (stated in terms of `IsIndObject`) and
reinterpret them in terms of `Ind C`.

Adopting the theorem numbering of [Kashiwara2006], we show the following properties:

Limits:
* If `C` has products indexed by `α`, then `Ind C` has products indexed by `α`, and the functor
  `Ind C ⥤ Cᵒᵖ ⥤ Type v` creates such products (6.1.17),
* if `C` has equalizers, then `Ind C` has equalizers, and the functor `Ind C ⥤ Cᵒᵖ ⥤ Type v`
  creates them (6.1.17)
* if `C` has small limits (resp. finite limits), then `Ind C` has small limits (resp. finite limits)
  and the functor `Ind C ⥤ Cᵒᵖ ⥤ Type v` creates them (6.1.17),
* the functor `C ⥤ Ind C` preserves small limits (6.1.17).

Colimits:
* `Ind C` has filtered colimits (6.1.8), and the functor `Ind C ⥤ Cᵒᵖ ⥤ Type v` preserves filtered
  colimits,
* if `C` has coproducts indexed by a finite type `α`, then `Ind C` has coproducts indexed by `α`
  (6.1.18(ii)),
* if `C` has finite coproducts, then `Ind C` has small coproducts (6.1.18(ii)),
* if `C` has coequalizers, then `Ind C` has coequalizers (6.1.18(i)),
* if `C` has finite colimits, then `Ind C` has small colimits (6.1.18(iii)).
* `C ⥤ Ind C` preserves finite colimits (6.1.6),

Note that:
* the functor `Ind C ⥤ Cᵒᵖ ⥤ Type v` does not preserve any kind of colimit in general except for
  filtered colimits and
* the functor `C ⥤ Ind C` preserves finite colimits, but not infinite colimits in general.

## References
* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Chapter 6
-/

universe w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

variable (C) in
/-- The category of Ind-objects of `C`. -/
def Ind : Type (max u (v + 1)) :=
  ShrinkHoms (ObjectProperty.FullSubcategory (IsIndObject (C := C)))

noncomputable instance : Category.{v} (Ind C) :=
  inferInstanceAs <| Category.{v}
    (ShrinkHoms (ObjectProperty.FullSubcategory (IsIndObject (C := C))))

variable (C) in
/-- The defining properties of `Ind C` are that its morphisms live in `v` and that it is equivalent
to the full subcategory of `Cᵒᵖ ⥤ Type v` containing the ind-objects. -/
noncomputable def Ind.equivalence :
    Ind C ≌ ObjectProperty.FullSubcategory (IsIndObject (C := C)) :=
  (ShrinkHoms.equivalence _).symm

variable (C) in
/-- The canonical inclusion of ind-objects into presheaves. -/
protected noncomputable def Ind.inclusion : Ind C ⥤ Cᵒᵖ ⥤ Type v :=
  (Ind.equivalence C).functor ⋙ ObjectProperty.ι _

instance : (Ind.inclusion C).Full :=
  inferInstanceAs <| ((Ind.equivalence C).functor ⋙ ObjectProperty.ι _).Full

instance : (Ind.inclusion C).Faithful :=
  inferInstanceAs <| ((Ind.equivalence C).functor ⋙ ObjectProperty.ι _).Faithful

/-- The functor `Ind C ⥤ Cᵒᵖ ⥤ Type v` is fully faithful. -/
protected noncomputable def Ind.inclusion.fullyFaithful : (Ind.inclusion C).FullyFaithful :=
  .ofFullyFaithful _

/-- The inclusion of `C` into `Ind C` induced by the Yoneda embedding. -/
protected noncomputable def Ind.yoneda : C ⥤ Ind C :=
  ObjectProperty.lift _ CategoryTheory.yoneda isIndObject_yoneda ⋙ (Ind.equivalence C).inverse

instance : (Ind.yoneda (C := C)).Full :=
  inferInstanceAs <| Functor.Full <|
    ObjectProperty.lift _ CategoryTheory.yoneda isIndObject_yoneda ⋙ (Ind.equivalence C).inverse

instance : (Ind.yoneda (C := C)).Faithful :=
  inferInstanceAs <| Functor.Faithful <|
    ObjectProperty.lift _ CategoryTheory.yoneda isIndObject_yoneda ⋙ (Ind.equivalence C).inverse

/-- The functor `C ⥤ Ind C` is fully faithful. -/
protected noncomputable def Ind.yoneda.fullyFaithful : (Ind.yoneda (C := C)).FullyFaithful :=
  .ofFullyFaithful _

/-- The composition `C ⥤ Ind C ⥤ (Cᵒᵖ ⥤ Type v)` is just the Yoneda embedding. -/
noncomputable def Ind.yonedaCompInclusion : Ind.yoneda ⋙ Ind.inclusion C ≅ CategoryTheory.yoneda :=
  isoWhiskerLeft (ObjectProperty.lift _ _ _)
    (isoWhiskerRight (Ind.equivalence C).counitIso (ObjectProperty.ι _))

noncomputable instance {J : Type v} [SmallCategory J] [IsFiltered J] :
    CreatesColimitsOfShape J (Ind.inclusion C) :=
  letI _ : CreatesColimitsOfShape J (ObjectProperty.ι (IsIndObject (C := C))) :=
    createsColimitsOfShapeFullSubcategoryInclusion (closedUnderColimitsOfShape_of_colimit
      (isIndObject_colimit _ _))
  inferInstanceAs <|
    CreatesColimitsOfShape J ((Ind.equivalence C).functor ⋙ ObjectProperty.ι _)

instance : HasFilteredColimits (Ind C) where
  HasColimitsOfShape _ _ _ :=
    hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (Ind.inclusion C)

noncomputable instance {J : Type v} [HasLimitsOfShape (Discrete J) C] :
    CreatesLimitsOfShape (Discrete J) (Ind.inclusion C) :=
  letI _ : CreatesLimitsOfShape (Discrete J) (ObjectProperty.ι (IsIndObject (C := C))) :=
    createsLimitsOfShapeFullSubcategoryInclusion (closedUnderLimitsOfShape_of_limit
      (isIndObject_limit_of_discrete_of_hasLimitsOfShape _))
  inferInstanceAs <|
    CreatesLimitsOfShape (Discrete J) ((Ind.equivalence C).functor ⋙ ObjectProperty.ι _)

instance {J : Type v} [HasLimitsOfShape (Discrete J) C] :
    HasLimitsOfShape (Discrete J) (Ind C) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (Ind.inclusion C)

noncomputable instance [HasLimitsOfShape WalkingParallelPair C] :
    CreatesLimitsOfShape WalkingParallelPair (Ind.inclusion C) :=
  letI _ : CreatesLimitsOfShape WalkingParallelPair
      (ObjectProperty.ι (IsIndObject (C := C))) :=
    createsLimitsOfShapeFullSubcategoryInclusion
      (closedUnderLimitsOfShape_walkingParallelPair_isIndObject)
  inferInstanceAs <|
    CreatesLimitsOfShape WalkingParallelPair
      ((Ind.equivalence C).functor ⋙ ObjectProperty.ι _)

instance [HasLimitsOfShape WalkingParallelPair C] :
    HasLimitsOfShape WalkingParallelPair (Ind C) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (Ind.inclusion C)

noncomputable instance [HasFiniteLimits C] : CreatesFiniteLimits (Ind.inclusion C) :=
  letI _ : CreatesFiniteProducts (Ind.inclusion C) :=
    { creates _ _ := createsLimitsOfShapeOfEquiv (Discrete.equivalence Equiv.ulift) _  }
  createsFiniteLimitsOfCreatesEqualizersAndFiniteProducts (Ind.inclusion C)

instance [HasFiniteLimits C] : HasFiniteLimits (Ind C) :=
  hasFiniteLimits_of_hasLimitsLimits_of_createsFiniteLimits (Ind.inclusion C)

noncomputable instance [HasLimits C] : CreatesLimitsOfSize.{v, v} (Ind.inclusion C) :=
  createsLimitsOfSizeOfCreatesEqualizersAndProducts.{v, v} (Ind.inclusion C)

instance [HasLimits C] : HasLimits (Ind C) :=
  hasLimits_of_hasLimits_createsLimits (Ind.inclusion C)

instance : PreservesLimits (Ind.yoneda (C := C)) :=
  letI _ : PreservesLimitsOfSize.{v, v} (Ind.yoneda ⋙ Ind.inclusion C) :=
    preservesLimits_of_natIso Ind.yonedaCompInclusion.symm
  preservesLimits_of_reflects_of_preserves Ind.yoneda (Ind.inclusion C)

theorem Ind.isIndObject_inclusion_obj (X : Ind C) : IsIndObject ((Ind.inclusion C).obj X) :=
  X.2

/-- Pick a presentation of an ind-object `X` using choice. -/
noncomputable def Ind.presentation (X : Ind C) : IndObjectPresentation ((Ind.inclusion C).obj X) :=
  X.isIndObject_inclusion_obj.presentation

/-- An ind-object `X` is the colimit (in `Ind C`!) of the filtered diagram presenting it. -/
noncomputable def Ind.colimitPresentationCompYoneda (X : Ind C) :
    colimit (X.presentation.F ⋙ Ind.yoneda) ≅ X :=
  Ind.inclusion.fullyFaithful.isoEquiv.symm <| calc
    (Ind.inclusion C).obj (colimit (X.presentation.F ⋙ Ind.yoneda))
      ≅ colimit (X.presentation.F ⋙ Ind.yoneda ⋙ Ind.inclusion C) := preservesColimitIso _ _
    _ ≅ colimit (X.presentation.F ⋙ yoneda) :=
          HasColimit.isoOfNatIso (isoWhiskerLeft X.presentation.F Ind.yonedaCompInclusion)
    _ ≅ (Ind.inclusion C).obj X :=
          IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) X.presentation.isColimit

instance : RepresentablyCoflat (Ind.yoneda (C := C)) := by
  refine ⟨fun X => ?_⟩
  suffices IsFiltered (CostructuredArrow yoneda ((Ind.inclusion C).obj X)) from
    IsFiltered.of_equivalence
      ((CostructuredArrow.post Ind.yoneda (Ind.inclusion C) X).asEquivalence.trans
      (CostructuredArrow.mapNatIso Ind.yonedaCompInclusion)).symm
  exact ((isIndObject_iff _).1 (Ind.isIndObject_inclusion_obj X)).1

noncomputable instance : PreservesFiniteColimits (Ind.yoneda (C := C)) :=
  preservesFiniteColimits_of_coflat _

/-- This is the functor `(I ⥤ C) ⥤ Ind C` that sends a functor `F` to `colim (Y ∘ F)`, where `Y`
is the Yoneda embedding. It is known as "ind-lim" and denoted `“colim”` in [Kashiwara2006]. -/
protected noncomputable def Ind.lim (I : Type v) [SmallCategory I] [IsFiltered I] :
    (I ⥤ C) ⥤ Ind C :=
  (whiskeringRight _ _ _).obj Ind.yoneda ⋙ colim

/-- Computing ind-lims in `Ind C` is the same as computing them in `Cᵒᵖ ⥤ Type v`. -/
noncomputable def Ind.limCompInclusion {I : Type v} [SmallCategory I] [IsFiltered I] :
    Ind.lim I ⋙ Ind.inclusion C ≅ (whiskeringRight _ _ _).obj yoneda ⋙ colim := calc
  Ind.lim I ⋙ Ind.inclusion C
    ≅ (whiskeringRight _ _ _).obj Ind.yoneda ⋙ colim ⋙ Ind.inclusion C := Functor.associator _ _ _
  _ ≅ (whiskeringRight _ _ _).obj Ind.yoneda ⋙
      (whiskeringRight _ _ _).obj (Ind.inclusion C) ⋙ colim :=
    isoWhiskerLeft _ (preservesColimitNatIso _)
  _ ≅ ((whiskeringRight _ _ _).obj Ind.yoneda ⋙
      (whiskeringRight _ _ _).obj (Ind.inclusion C)) ⋙ colim := (Functor.associator _ _ _).symm
  _ ≅ (whiskeringRight _ _ _).obj (Ind.yoneda ⋙ Ind.inclusion C) ⋙ colim :=
    isoWhiskerRight (whiskeringRightObjCompIso _ _) colim
  _ ≅ (whiskeringRight _ _ _).obj yoneda ⋙ colim :=
    isoWhiskerRight ((whiskeringRight _ _ _).mapIso (Ind.yonedaCompInclusion)) colim

instance {α : Type w} [SmallCategory α] [FinCategory α] [HasLimitsOfShape α C] {I : Type v}
    [SmallCategory I] [IsFiltered I] :
    PreservesLimitsOfShape α (Ind.lim I : (I ⥤ C) ⥤ _) :=
  haveI : PreservesLimitsOfShape α (Ind.lim I ⋙ Ind.inclusion C) :=
    preservesLimitsOfShape_of_natIso Ind.limCompInclusion.symm
  preservesLimitsOfShape_of_reflects_of_preserves _ (Ind.inclusion C)

instance {α : Type w} [SmallCategory α] [FinCategory α] [HasColimitsOfShape α C] {I : Type v}
    [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape α (Ind.lim I : (I ⥤ C) ⥤ _) :=
  inferInstanceAs (PreservesColimitsOfShape α (_ ⋙ colim))

instance {α : Type v} [Finite α] [HasColimitsOfShape (Discrete α) C] :
    HasColimitsOfShape (Discrete α) (Ind C) := by
  refine ⟨fun F => ?_⟩
  let I : α → Type v := fun s => (F.obj ⟨s⟩).presentation.I
  let G : ∀ s, I s ⥤ C := fun s => (F.obj ⟨s⟩).presentation.F
  let iso : Discrete.functor (fun s => Pi.eval I s ⋙ G s) ⋙
      (whiskeringRight _ _ _).obj Ind.yoneda ⋙ colim ≅ F := by
    refine Discrete.natIso (fun s => ?_)
    refine (Functor.Final.colimitIso (Pi.eval I s.as) (G s.as ⋙ Ind.yoneda)) ≪≫ ?_
    exact Ind.colimitPresentationCompYoneda _
  -- The actual proof happens during typeclass resolution in the following line, which deduces
  -- ```
  -- HasColimit Discrete.functor (fun s => Pi.eval I s ⋙ G s) ⋙
  --    (whiskeringRight _ _ _).obj Ind.yoneda ⋙ colim
  -- ```
  -- from the fact that finite limits commute with filtered colimits and from the fact that
  -- `Ind.yoneda` preserves finite colimits.
  exact hasColimit_of_iso iso.symm

instance [HasFiniteCoproducts C] : HasCoproducts.{v} (Ind C) :=
  have : HasFiniteCoproducts (Ind C) :=
    ⟨fun _ => hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift)⟩
  hasCoproducts_of_finite_and_filtered

/-- Given an `IndParallelPairPresentation f g`, we can understand the parallel pair `(f, g)` as
the colimit of `(P.φ, P.ψ)` in `Ind C`. -/
noncomputable def IndParallelPairPresentation.parallelPairIsoParallelPairCompIndYoneda
    {A B : Ind C} {f g : A ⟶ B}
    (P : IndParallelPairPresentation ((Ind.inclusion _).map f) ((Ind.inclusion _).map g)) :
    parallelPair f g ≅ parallelPair P.φ P.ψ ⋙ Ind.lim P.I :=
  ((whiskeringRight WalkingParallelPair _ _).obj (Ind.inclusion C)).preimageIso <|
    diagramIsoParallelPair _ ≪≫
      P.parallelPairIsoParallelPairCompYoneda ≪≫
      isoWhiskerLeft (parallelPair _ _) Ind.limCompInclusion.symm

instance [HasColimitsOfShape WalkingParallelPair C] :
    HasColimitsOfShape WalkingParallelPair (Ind C) := by
  refine ⟨fun F => ?_⟩
  obtain ⟨P⟩ := nonempty_indParallelPairPresentation (F.obj WalkingParallelPair.zero).2
    (F.obj WalkingParallelPair.one).2 (Ind.inclusion _ |>.map <| F.map WalkingParallelPairHom.left)
    (Ind.inclusion _ |>.map <| F.map WalkingParallelPairHom.right)
  exact hasColimit_of_iso (diagramIsoParallelPair _ ≪≫ P.parallelPairIsoParallelPairCompIndYoneda)

instance [HasFiniteColimits C] : HasColimits (Ind C) :=
  has_colimits_of_hasCoequalizers_and_coproducts

/-- A way to understand morphisms in `Ind C`: every morphism is induced by a natural transformation
of diagrams. -/
theorem Ind.exists_nonempty_arrow_mk_iso_ind_lim {A B : Ind C} {f : A ⟶ B} :
    ∃ (I : Type v) (_ : SmallCategory I) (_ : IsFiltered I) (F G : I ⥤ C) (φ : F ⟶ G),
      Nonempty (Arrow.mk f ≅ Arrow.mk ((Ind.lim _).map φ)) := by
  obtain ⟨P⟩ := nonempty_indParallelPairPresentation A.2 B.2
    (Ind.inclusion _ |>.map f) (Ind.inclusion _ |>.map f)
  refine ⟨P.I, inferInstance, inferInstance, P.F₁, P.F₂, P.φ, ⟨Arrow.isoMk ?_ ?_ ?_⟩⟩
  · exact P.parallelPairIsoParallelPairCompIndYoneda.app WalkingParallelPair.zero
  · exact P.parallelPairIsoParallelPairCompIndYoneda.app WalkingParallelPair.one
  · simpa using
      (P.parallelPairIsoParallelPairCompIndYoneda.hom.naturality WalkingParallelPairHom.left).symm

section Small

variable (C : Type u) [SmallCategory C] [HasFiniteColimits C]

/-- For small finitely cocomplete categories `C : Type u`, the category of Ind-objects `Ind C` is
equivalent to the category of left-exact functors `Cᵒᵖ ⥤ Type u` -/
noncomputable def Ind.leftExactFunctorEquivalence : Ind C ≌ LeftExactFunctor Cᵒᵖ (Type u) :=
  (Ind.equivalence _).trans <| ObjectProperty.fullSubcategoryCongr
    (by ext; apply isIndObject_iff_preservesFiniteLimits)

end Small

end CategoryTheory
