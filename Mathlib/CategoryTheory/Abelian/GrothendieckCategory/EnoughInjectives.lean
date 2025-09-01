/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ColimCoyoneda
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Monomorphisms
import Mathlib.CategoryTheory.Abelian.Monomorphisms
import Mathlib.CategoryTheory.Preadditive.Injective.LiftingProperties
import Mathlib.CategoryTheory.SmallObject.Basic
import Mathlib.CategoryTheory.Subobject.HasCardinalLT
import Mathlib.Order.TransfiniteIteration

/-!
# Grothendieck abelian categories have enough injectives

Let `C` be a Grothendieck abelian category. In this file, we formalize
the theorem by Grothendieck that `C` has enough injectives.

We recall that injective objects can be characterized in terms of
lifting properties (see the file `Preadditive.Injective.LiftingProperties`):
an object `I : C` is injective iff the morphism `I ⟶ 0` has the right lifting
property with respect to all monomorphisms.

The main technical lemma in this file is the lemma
`generatingMonomorphisms_rlp` which states that
if `G` is a generator of `C`, then a morphism `X ⟶ Y` has the right
lifting property with respect to the inclusions of subobjects of `G`
iff it has the right lifting property with respect to all
monomorphisms. Then, we can apply the small object argument
to the family of morphisms `generatingMonomorphisms G`
which consists of the inclusions of subobjects of `G`. When it is
applied to the morphism `X ⟶ 0`, the factorization given by the
small object is a factorization `X ⟶ I ⟶ 0` where `I` is
injective (because `I ⟶ 0` has the expected right lifting properties),
and `X ⟶ I` is a monomorphism because it is a transfinite composition
of monomorphisms (this uses the axiom AB5).

The proof of the technical lemma `generatingMonomorphisms_rlp` that
was formalized is not exactly the same as in the mathematical literature.
Assume that `p : X ⟶ Y` has the lifting property with respect to
monomorphisms in the family `generatingMonomorphisms G`.
We would like to show that `p` has the right lifting property with
respect to any monomorphism `i : A ⟶ B`. In various sources,
given a commutative square with `i` on the left and `p` on the right,
the ordered set of subobjects `A'` of `B` containing `A` equipped
with a lifting `A' ⟶ X` is introduced. The existence of a lifting `B ⟶ X`
is usually obtained by applying Zorn's lemma in this situation.
Here, we split the argument into two separate facts:
* any monomorphism `A ⟶ B` is a transfinite composition of pushouts of monomorphisms in
  `generatingMonomorphisms G` (see `generatingMonomorphisms.exists_transfiniteCompositionOfShape`);
* the class of morphisms that have the left lifting property with respect to `p` is stable under
  transfinite composition (see the file `SmallObject.TransfiniteCompositionLifting`).

## References

- [Alexander Grothendieck, *Sur quelques points d'algèbre homologique*][grothendieck-1957]

-/

universe w v u

namespace CategoryTheory

open Category Limits ZeroObject

variable {C : Type u} [Category.{v} C]

namespace IsGrothendieckAbelian

/-- Given an object `G : C`, this is the family of morphisms in `C`
given by the inclusions of all subobjects of `G`. If `G` is a separator,
and `C` is a Grothendieck abelian category, then any monomorphism in `C`
is a transfinite composition of pushouts of monomorphisms in this family
(see `generatingMonomorphisms.exists_transfiniteCompositionOfShape`). -/
def generatingMonomorphisms (G : C) : MorphismProperty C :=
  MorphismProperty.ofHoms (fun (X : Subobject G) ↦ X.arrow)

instance (G : C) [Small.{w} (Subobject G)] :
    MorphismProperty.IsSmall.{w} (generatingMonomorphisms G) := by
  dsimp [generatingMonomorphisms]
  infer_instance

lemma generatingMonomorphisms_le_monomorphisms (G : C) :
    generatingMonomorphisms G ≤ MorphismProperty.monomorphisms C := by
  rintro _ _ _ ⟨X⟩
  exact inferInstanceAs (Mono _)

variable (G : C)

lemma isomorphisms_le_pushouts_generatingMonomorphisms [HasZeroMorphisms C] :
    MorphismProperty.isomorphisms C ≤ (generatingMonomorphisms G).pushouts :=
  MorphismProperty.isomorphisms_le_pushouts _
    (fun _ ↦ ⟨_, _, _, ⟨⊤⟩, 0, inferInstance⟩)

variable [Abelian C]

namespace generatingMonomorphisms

variable {G} (hG : IsSeparator G)

include hG

/-- If `p : X ⟶ Y` is a monomorphism that is not an isomorphism, there exists
a subobject `X'` of `Y` containing `X` (but different from `X`) such that
the inclusion `X ⟶ X'` is a pushout of a monomorphism in the family
`generatingMonomorphisms G`. -/
lemma exists_pushouts
    {X Y : C} (p : X ⟶ Y) [Mono p] (hp : ¬ IsIso p) :
    ∃ (X' : C) (i : X ⟶ X') (p' : X' ⟶ Y) (_ : (generatingMonomorphisms G).pushouts i)
      (_ : ¬ IsIso i) (_ : Mono p'), i ≫ p' = p := by
  rw [hG.isDetector.isIso_iff_of_mono] at hp
  simp only [coyoneda_obj_obj, coyoneda_obj_map, Set.mem_singleton_iff, forall_eq,
    Function.Surjective, not_forall, not_exists] at hp
  -- `f : G ⟶ Y` is a monomorphism the image of which is not contained in `X`
  obtain ⟨f, hf⟩ := hp
  -- we use the subobject `X'` of `Y` that is generated by the images of `p : X ⟶ Y`
  -- and `f : G ⟶ Y`: this is the pushout of `p` and `f` along their pullback
  refine ⟨pushout (pullback.fst p f) (pullback.snd p f), pushout.inl _ _,
    pushout.desc p f pullback.condition,
    ⟨_, _, _, (Subobject.underlyingIso _).hom ≫ pullback.fst _ _,
    pushout.inr _ _, ⟨Subobject.mk (pullback.snd p f)⟩,
    (IsPushout.of_hasPushout (pullback.fst p f) (pullback.snd p f)).of_iso
      ((Subobject.underlyingIso _).symm) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (by simp) (by simp) (by simp) (by simp)⟩, ?_, ?_, by simp⟩
  · intro h
    rw [isIso_iff_yoneda_map_bijective] at h
    obtain ⟨a, ha⟩ := (h G).2 (pushout.inr _ _)
    exact hf a (by simpa using ha =≫ pushout.desc p f pullback.condition)
  · exact (IsPushout.of_hasPushout _ _).mono_of_isPullback_of_mono
      (IsPullback.of_hasPullback p f) _ (by simp) (by simp)

lemma exists_larger_subobject {X : C} (A : Subobject X) (hA : A ≠ ⊤) :
    ∃ (A' : Subobject X) (h : A < A'),
      (generatingMonomorphisms G).pushouts (Subobject.ofLE A A' h.le) := by
  induction' A using Subobject.ind with Y f _
  obtain ⟨X', i, p', hi, hi', hp', fac⟩ := exists_pushouts hG f
    (by simpa only [Subobject.isIso_iff_mk_eq_top] using hA)
  refine ⟨Subobject.mk p', Subobject.mk_lt_mk_of_comm i fac hi',
    (MorphismProperty.arrow_mk_iso_iff _ ?_).2 hi⟩
  refine Arrow.isoMk (Subobject.underlyingIso f) (Subobject.underlyingIso p') ?_
  dsimp
  simp only [← cancel_mono p', assoc, fac,
    Subobject.underlyingIso_hom_comp_eq_mk, Subobject.ofLE_arrow]

variable {X : C}

open Classical in
/-- Assuming `G : C` is a generator, `X : C`, and `A : Subobject X`,
this is a subobject of `X` which is `⊤` if `A = ⊤`, and otherwise
it is a larger subobject given by the lemma `exists_larger_subobject`.
The inclusion of `A` in `largerSubobject hG A` is a pushout of
a monomorphism in the family `generatingMonomorphisms G`
(see `pushouts_ofLE_le_largerSubobject`). -/
noncomputable def largerSubobject (A : Subobject X) : Subobject X :=
  if hA : A = ⊤ then ⊤ else (exists_larger_subobject hG A hA).choose

variable (X) in
@[simp]
lemma largerSubobject_top : largerSubobject hG (⊤ : Subobject X) = ⊤ := dif_pos rfl

lemma lt_largerSubobject (A : Subobject X) (hA : A ≠ ⊤) :
    A < largerSubobject hG A := by
  dsimp only [largerSubobject]
  rw [dif_neg hA]
  exact (exists_larger_subobject hG A hA).choose_spec.choose

lemma le_largerSubobject (A : Subobject X) :
    A ≤ largerSubobject hG A := by
  by_cases hA : A = ⊤
  · subst hA
    simp only [largerSubobject_top, le_refl]
  · exact (lt_largerSubobject hG A hA).le

lemma pushouts_ofLE_le_largerSubobject (A : Subobject X) :
      (generatingMonomorphisms G).pushouts
        (Subobject.ofLE _ _ (le_largerSubobject hG A)) := by
  by_cases hA : A = ⊤
  · subst hA
    have := (Subobject.isIso_arrow_iff_eq_top (largerSubobject hG (⊤ : Subobject X))).2 (by simp)
    exact (MorphismProperty.arrow_mk_iso_iff _
      (Arrow.isoMk (asIso (Subobject.arrow _)) (asIso (Subobject.arrow _)) (by simp))).2
        (isomorphisms_le_pushouts_generatingMonomorphisms G (𝟙 X)
          (MorphismProperty.isomorphisms.infer_property _))
  · refine (MorphismProperty.arrow_mk_iso_iff _ ?_).1
      (exists_larger_subobject hG A hA).choose_spec.choose_spec
    exact Arrow.isoMk (Iso.refl _)
      (Subobject.isoOfEq _ _ ((by simp [largerSubobject, dif_neg hA])))

variable [IsGrothendieckAbelian.{w} C]

lemma top_mem_range (A₀ : Subobject X) {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J]
    [WellFoundedLT J] (hJ : HasCardinalLT (Subobject X) (Cardinal.mk J)) :
    ∃ (j : J), transfiniteIterate (largerSubobject hG) j A₀ = ⊤ :=
  top_mem_range_transfiniteIterate (largerSubobject hG) A₀ (lt_largerSubobject hG) (by simp)
    (fun h ↦ by simpa [hasCardinalLT_iff_cardinal_mk_lt] using hJ.of_injective _ h)

lemma exists_ordinal (A₀ : Subobject X) :
    ∃ (o : Ordinal.{w}) (j : o.toType), transfiniteIterate (largerSubobject hG) j A₀ = ⊤ := by
  let κ := Order.succ (Cardinal.mk (Shrink.{w} (Subobject X)))
  have : OrderBot κ.ord.toType := Ordinal.toTypeOrderBot (by
    simp only [ne_eq, Cardinal.ord_eq_zero]
    apply Cardinal.succ_ne_zero)
  exact ⟨κ.ord, top_mem_range hG A₀ (lt_of_lt_of_le (Order.lt_succ _) (by simp [κ]))⟩

section

variable (A₀ : Subobject X) (J : Type w) [LinearOrder J] [OrderBot J] [SuccOrder J]
  [WellFoundedLT J]

/-- Let `C` be a Grothendieck abelian category with a generator (`hG`),
`X : C`, `A₀ : Subobject X`. Let `J` be a well-ordered type. This is
the functor `J ⥤ MonoOver X` which corresponds to the evaluation
at `A₀` of the transfinite iteration of the map
`largerSubobject hG : Subobject X → Subobject X`. -/
@[simps]
noncomputable def functorToMonoOver : J ⥤ MonoOver X where
  obj j := MonoOver.mk' (transfiniteIterate (largerSubobject hG) j A₀).arrow
  map {j j'} f := MonoOver.homMk (Subobject.ofLE _ _
      (monotone_transfiniteIterate _ _ (le_largerSubobject hG) (leOfHom f)))

/-- The functor `J ⥤ C` induced by `functorToMonoOver hG A₀ J : J ⥤ MonoOver X`. -/
noncomputable abbrev functor : J ⥤ C :=
  functorToMonoOver hG A₀ J ⋙ MonoOver.forget _ ⋙ Over.forget _

instance : (functor hG A₀ J).IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨by
    have := hm.nonempty_Iio.to_subtype
    let c := (Set.principalSegIio m).cocone (functorToMonoOver hG A₀ J ⋙ MonoOver.forget _)
    have : Mono c.pt.hom := by dsimp [c]; infer_instance
    apply IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup
      ((Set.principalSegIio m).monotone.functor ⋙ functorToMonoOver hG A₀ J) c
    dsimp [c]
    simp only [Subobject.mk_arrow]
    exact transfiniteIterate_limit (largerSubobject hG) A₀ m hm⟩

variable {J} in
/-- For any `j`, the map `(functor hG A₀ J).map (homOfLE bot_le : ⊥ ⟶ j)`
is a transfinite composition of pushouts of monomorphisms in the
family `generatingMonomorphisms G`. -/
noncomputable def transfiniteCompositionOfShapeMapFromBot (j : J) :
    (generatingMonomorphisms G).pushouts.TransfiniteCompositionOfShape (Set.Iic j)
    ((functor hG A₀ J).map (homOfLE bot_le : ⊥ ⟶ j)) where
  F := (Set.initialSegIic j).monotone.functor ⋙ functor hG A₀ J
  isoBot := Iso.refl _
  incl :=
    { app k := (functor hG A₀ J).map (homOfLE k.2)
      naturality k k' h := by simp [MonoOver.forget] }
  isColimit := colimitOfDiagramTerminal isTerminalTop _
  map_mem k hk := by
    dsimp [MonoOver.forget]
    convert pushouts_ofLE_le_largerSubobject hG
      (transfiniteIterate (largerSubobject hG) k.1 A₀) using 2
    all_goals
      rw [Set.Iic.succ_eq_of_not_isMax hk,
        transfiniteIterate_succ _ _ _ (Set.not_isMax_coe _ hk)]

end

variable {A : C} {f : A ⟶ X} [Mono f]

/-- If `transfiniteIterate (largerSubobject hG) j (Subobject.mk f) = ⊤`,
then the monomorphism `f` is a transfinite composition of pushouts of
monomorphisms in the family `generatingMonomorphisms G`. -/
noncomputable def transfiniteCompositionOfShapeOfEqTop
    {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J] {j : J}
    (hj : transfiniteIterate (largerSubobject hG) j (Subobject.mk f) = ⊤) :
    (generatingMonomorphisms G).pushouts.TransfiniteCompositionOfShape (Set.Iic j) f := by
  let t := transfiniteIterate (largerSubobject hG) j (Subobject.mk f)
  have := (Subobject.isIso_arrow_iff_eq_top t).2 hj
  apply (transfiniteCompositionOfShapeMapFromBot hG (Subobject.mk f) j).ofArrowIso
  refine Arrow.isoMk ((Subobject.isoOfEq _ _ (transfiniteIterate_bot _ _) ≪≫
    Subobject.underlyingIso f)) (asIso t.arrow) ?_
  dsimp [MonoOver.forget]
  rw [assoc, Subobject.underlyingIso_hom_comp_eq_mk, Subobject.ofLE_arrow,
    Subobject.ofLE_arrow]

variable (f)

/-- Let `C` be a Grothendieck abelian category. Assume that `G : C` is a generator
of `C`. Then, any morphism in `C` is a transfinite composition of pushouts
of monomorphisms in the family `generatingMonomorphisms G` which consists
of the inclusions of the subobjects of `G`. -/
lemma exists_transfiniteCompositionOfShape :
    ∃ (J : Type w) (_ : LinearOrder J) (_ : OrderBot J) (_ : SuccOrder J)
        (_ : WellFoundedLT J),
    Nonempty ((generatingMonomorphisms G).pushouts.TransfiniteCompositionOfShape J f) := by
  obtain ⟨o, j, hj⟩ := exists_ordinal hG (Subobject.mk f)
  letI : OrderBot o.toType := Ordinal.toTypeOrderBot (by
    simpa only [← Ordinal.toType_nonempty_iff_ne_zero] using Nonempty.intro j)
  exact ⟨_, _, _, _, _, ⟨transfiniteCompositionOfShapeOfEqTop hG hj⟩⟩

end generatingMonomorphisms

open MorphismProperty

variable {G}

lemma generatingMonomorphisms_rlp [IsGrothendieckAbelian.{w} C] (hG : IsSeparator G) :
    (generatingMonomorphisms G).rlp = (monomorphisms C).rlp := by
  apply le_antisymm
  · intro X Y p hp A B i (_ : Mono i)
    obtain ⟨J, _, _, _, _, ⟨h⟩⟩ :=
      generatingMonomorphisms.exists_transfiniteCompositionOfShape hG i
    exact transfiniteCompositionsOfShape_le_llp_rlp _ _ _ h.mem _ (by simpa)
  · exact antitone_rlp (generatingMonomorphisms_le_monomorphisms _)

open MorphismProperty

variable [IsGrothendieckAbelian.{w} C]

instance : HasSmallObjectArgument.{w} (generatingMonomorphisms G) := by
  obtain ⟨κ, hκ', hκ⟩ := HasCardinalLT.exists_regular_cardinal.{w} (Subobject G)
  have : Fact κ.IsRegular := ⟨hκ'⟩
  letI := Cardinal.toTypeOrderBot hκ'.ne_zero
  exact ⟨κ, inferInstance, inferInstance,
    { preservesColimit {A B X Y} i hi f hf := by
        let hf' : (monomorphisms C).TransfiniteCompositionOfShape κ.ord.toType f :=
          { toTransfiniteCompositionOfShape := hf.toTransfiniteCompositionOfShape
            map_mem j hj := by
              have := (hf.attachCells j hj).pushouts_coproducts
              simp only [ofHoms_homFamily] at this
              refine (?_ : _ ≤ monomorphisms C) _ this
              simp only [pushouts_le_iff, coproducts_le_iff]
              exact generatingMonomorphisms_le_monomorphisms G }
        have (j j' : κ.ord.toType) (φ : j ⟶ j') : Mono (hf'.F.map φ) := hf'.mem_map φ
        apply preservesColimit_coyoneda_obj_of_mono (Y := hf'.F) (κ := κ)
        obtain ⟨S⟩ := hi
        exact Subobject.hasCardinalLT_of_mono hκ S.arrow }⟩

lemma llp_rlp_monomorphisms (hG : IsSeparator G) :
    (monomorphisms C).rlp.llp = monomorphisms C := by
  refine le_antisymm ?_ (le_llp_rlp _)
  rw [← generatingMonomorphisms_rlp hG, llp_rlp_of_hasSmallObjectArgument]
  trans (transfiniteCompositions.{w} (coproducts.{w} (monomorphisms C)).pushouts).retracts
  · apply retracts_monotone
    apply transfiniteCompositions_monotone
    apply pushouts_monotone
    apply coproducts_monotone
    apply generatingMonomorphisms_le_monomorphisms
  · simp

instance : HasFunctorialFactorization (monomorphisms C) (monomorphisms C).rlp := by
  have hG := isSeparator_separator C
  rw [← generatingMonomorphisms_rlp hG, ← llp_rlp_monomorphisms hG,
    ← generatingMonomorphisms_rlp hG]
  infer_instance

/-- A (functorial) factorization of any morphisms in a Grothendieck abelian category
as a monomorphism followed by a morphism which has the right lifting property
with respect to all monomorphisms. -/
noncomputable abbrev monoMapFactorizationDataRlp {X Y : C} (f : X ⟶ Y) :
    MapFactorizationData (monomorphisms C) (monomorphisms C).rlp f :=
  (functorialFactorizationData _ _).factorizationData f

instance {X Y : C} (f : X ⟶ Y) :
    Mono (monoMapFactorizationDataRlp f).i :=
  (monoMapFactorizationDataRlp f).hi

instance {X : C} : Injective (monoMapFactorizationDataRlp (0 : X ⟶ 0)).Z := by
  let fac := (monoMapFactorizationDataRlp (0 : X ⟶ 0))
  simpa only [injective_iff_rlp_monomorphisms_zero,
    (isZero_zero C).eq_of_tgt fac.p 0] using fac.hp

/-- A Grothendieck abelian category has enough injectives. -/
@[stacks 079H]
instance enoughInjectives : EnoughInjectives C where
  presentation X := ⟨{ J := _, f := (monoMapFactorizationDataRlp (0 : X ⟶ 0)).i }⟩

end IsGrothendieckAbelian

end CategoryTheory
