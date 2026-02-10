/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# The canonical topology on a category

We define the finest (largest) Grothendieck topology for which a given presheaf `P` is a sheaf.
This is well defined since if `P` is a sheaf for a topology `J`, then it is a sheaf for any
coarser (smaller) topology. Nonetheless we define the topology explicitly by specifying its sieves:
A sieve `S` on `X` is covering for `finestTopologySingle P` iff
  for any `f : Y ⟶ X`, `P` satisfies the sheaf axiom for `S.pullback f`.
Showing that this is a genuine Grothendieck topology (namely that it satisfies the transitivity
axiom) forms the bulk of this file.

This generalises to a set of presheaves, giving the topology `finestTopology Ps` which is the
finest topology for which every presheaf in `Ps` is a sheaf.
Using `Ps` as the set of representable presheaves defines the `canonicalTopology`: the finest
topology for which every representable is a sheaf.

A Grothendieck topology is called `Subcanonical` if it is smaller than the canonical topology,
equivalently it is subcanonical iff every representable presheaf is a sheaf.

## References
* https://ncatlab.org/nlab/show/canonical+topology
* https://ncatlab.org/nlab/show/subcanonical+coverage
* https://stacks.math.columbia.edu/tag/00Z9
* https://math.stackexchange.com/a/358709/
-/

@[expose] public section


universe w v u

namespace CategoryTheory

open CategoryTheory Category Limits Sieve

variable {C : Type u} [Category.{v} C]

variable {P : Cᵒᵖ ⥤ Type v} {X : C} (J : GrothendieckTopology C)

namespace Sheaf

@[deprecated (since := "2026-02-06")] alias isSheafFor_bind := Presieve.isSheafFor_bind

@[deprecated (since := "2026-02-06")] alias isSheafFor_trans := Presieve.isSheafFor_trans

/-- Construct the finest (largest) Grothendieck topology for which the given presheaf is a sheaf. -/
@[stacks 00Z9 "This is a special case of the Stacks entry, but following a different
proof (see the Stacks comments)."]
def finestTopologySingle (P : Cᵒᵖ ⥤ Type v) : GrothendieckTopology C where
  sieves X S := ∀ (Y) (f : Y ⟶ X), Presieve.IsSheafFor P (S.pullback f : Presieve Y)
  top_mem' X Y f := by
    rw [Sieve.pullback_top]
    exact Presieve.isSheafFor_top P
  pullback_stable' X Y S f hS Z g := by
    rw [← pullback_comp]
    apply hS
  transitive' X S hS R hR Z g := by
    -- This is the hard part of the construction, showing that the given set of sieves satisfies
    -- the transitivity axiom.
    refine Presieve.isSheafFor_trans P (pullback g S) _ (hS Z g) ?_ ?_
    · intro Y f _
      rw [← pullback_comp]
      apply (hS _ _).isSeparatedFor
    · intro Y f hf
      have := hR hf _ (𝟙 _)
      rw [pullback_id, pullback_comp] at this
      apply this

/-- Construct the finest (largest) Grothendieck topology for which all the given presheaves are
sheaves. -/
@[stacks 00Z9 "Equal to that Stacks construction"]
def finestTopology (Ps : Set (Cᵒᵖ ⥤ Type v)) : GrothendieckTopology C :=
  sInf (finestTopologySingle '' Ps)

/-- Check that if `P ∈ Ps`, then `P` is indeed a sheaf for the finest topology on `Ps`. -/
theorem sheaf_for_finestTopology (Ps : Set (Cᵒᵖ ⥤ Type v)) (h : P ∈ Ps) :
    Presieve.IsSheaf (finestTopology Ps) P := fun X S hS => by
  simpa using hS _ ⟨⟨_, _, ⟨_, h, rfl⟩, rfl⟩, rfl⟩ _ (𝟙 _)

/--
Check that if each `P ∈ Ps` is a sheaf for `J`, then `J` is a subtopology of `finestTopology Ps`.
-/
theorem le_finestTopology (Ps : Set (Cᵒᵖ ⥤ Type v)) (J : GrothendieckTopology C)
    (hJ : ∀ P ∈ Ps, Presieve.IsSheaf J P) : J ≤ finestTopology Ps := by
  rintro X S hS _ ⟨⟨_, _, ⟨P, hP, rfl⟩, rfl⟩, rfl⟩
  intro Y f
  -- this can't be combined with the previous because the `subst` is applied at the end
  exact hJ P hP (S.pullback f) (J.pullback_stable f hS)

/-- The `canonicalTopology` on a category is the finest (largest) topology for which every
representable presheaf is a sheaf. -/
@[stacks 00ZA]
def canonicalTopology (C : Type u) [Category.{v} C] : GrothendieckTopology C :=
  finestTopology (Set.range yoneda.obj)

/-- `yoneda.obj X` is a sheaf for the canonical topology. -/
theorem isSheaf_yoneda_obj (X : C) : Presieve.IsSheaf (canonicalTopology C) (yoneda.obj X) :=
  fun _ _ hS => sheaf_for_finestTopology _ (Set.mem_range_self _) _ hS

/-- A representable functor is a sheaf for the canonical topology. -/
theorem isSheaf_of_isRepresentable (P : Cᵒᵖ ⥤ Type w) [P.IsRepresentable] :
    Presieve.IsSheaf (canonicalTopology C) P := by
  rw [← Presieve.isSheaf_comp_uliftFunctor_iff]
  refine Presieve.isSheaf_iso (canonicalTopology C) (P ⋙ uliftFunctor.{v}).uliftYonedaReprXIso ?_
  rw [← isSheaf_iff_isSheaf_of_type]
  refine GrothendieckTopology.HasSheafCompose.isSheaf _ ?_
  rw [isSheaf_iff_isSheaf_of_type]
  exact isSheaf_yoneda_obj _

end Sheaf

namespace GrothendieckTopology

open Sheaf

/-- A subcanonical topology is a topology which is smaller than the canonical topology.
Equivalently, a topology is subcanonical iff every representable is a sheaf.
-/
class Subcanonical (J : GrothendieckTopology C) : Prop where
  le_canonical : J ≤ canonicalTopology C

lemma le_canonical (J : GrothendieckTopology C) [Subcanonical J] : J ≤ canonicalTopology C :=
  Subcanonical.le_canonical

instance : (canonicalTopology C).Subcanonical where
  le_canonical := le_rfl

namespace Subcanonical

/-- If every functor `yoneda.obj X` is a `J`-sheaf, then `J` is subcanonical. -/
theorem of_isSheaf_yoneda_obj (J : GrothendieckTopology C)
    (h : ∀ X, Presieve.IsSheaf J (yoneda.obj X)) : Subcanonical J where
  le_canonical := le_finestTopology _ _ (by rintro P ⟨X, rfl⟩; apply h)

/-- If `J` is subcanonical, then any representable is a `J`-sheaf. -/
theorem isSheaf_of_isRepresentable {J : GrothendieckTopology C} [Subcanonical J]
    (P : Cᵒᵖ ⥤ Type w) [P.IsRepresentable] : Presieve.IsSheaf J P :=
  Presieve.isSheaf_of_le _ J.le_canonical (Sheaf.isSheaf_of_isRepresentable P)

end Subcanonical

variable (J : GrothendieckTopology C)

/--
If `J` is subcanonical, we obtain a "Yoneda" functor from the defining site
into the sheaf category.
-/
@[simps]
def yoneda [J.Subcanonical] : C ⥤ Sheaf J (Type v) where
  obj X := ⟨CategoryTheory.yoneda.obj X, by
    rw [isSheaf_iff_isSheaf_of_type]
    apply Subcanonical.isSheaf_of_isRepresentable⟩
  map f := ⟨CategoryTheory.yoneda.map f⟩

/-- Variant of the Yoneda embedding which allows a raise in the universe level
for the category of types. -/
@[pp_with_univ, simps!]
def uliftYoneda [J.Subcanonical] : C ⥤ Sheaf J (Type max v w) :=
  J.yoneda ⋙ sheafCompose J uliftFunctor.{w}

@[deprecated (since := "2025-11-10")] alias yonedaULift := uliftYoneda

/-- If `C` is a category with `[Category.{max w v} C]`, this is the isomorphism
`uliftYoneda.{w} (C := C) ≅ yoneda`. -/
@[simps!]
def uliftYonedaIsoYoneda {C : Type u} [Category.{max w v} C] (J : GrothendieckTopology C)
    [J.Subcanonical] :
    GrothendieckTopology.uliftYoneda.{w} J ≅ J.yoneda :=
  NatIso.ofComponents (fun _ => (fullyFaithfulSheafToPresheaf J _).preimageIso
    (NatIso.ofComponents (fun _ ↦ Equiv.ulift.toIso)))

variable [Subcanonical J]

/--
The yoneda embedding into the presheaf category factors through the one
to the sheaf category.
-/
def yonedaCompSheafToPresheaf :
    J.yoneda ⋙ sheafToPresheaf J (Type v) ≅ CategoryTheory.yoneda :=
  Iso.refl _

/-- A variant of `yonedaCompSheafToPresheaf` with a raise in the universe level. -/
@[simps!]
def uliftYonedaCompSheafToPresheaf :
    GrothendieckTopology.uliftYoneda.{w} J ⋙ sheafToPresheaf J (Type max v w) ≅
      CategoryTheory.uliftYoneda.{w} :=
  Iso.refl _

/-- The yoneda functor into the sheaf category is fully faithful -/
def yonedaFullyFaithful : (J.yoneda).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful (G := sheafToPresheaf J (Type v)) Yoneda.fullyFaithful

instance : (J.yoneda).Full := (J.yonedaFullyFaithful).full

instance : (J.yoneda).Faithful := (J.yonedaFullyFaithful).faithful

/-- A variant of `yonedaFullyFaithful` with a raise in the universe level. -/
def fullyFaithfulUliftYoneda : (GrothendieckTopology.uliftYoneda.{w} J).FullyFaithful :=
  J.yonedaFullyFaithful.comp (fullyFaithfulSheafCompose J fullyFaithfulULiftFunctor)

instance : (GrothendieckTopology.uliftYoneda.{w} J).Full :=
  (J.fullyFaithfulUliftYoneda).full

instance : (GrothendieckTopology.uliftYoneda.{w} J).Faithful :=
  (J.fullyFaithfulUliftYoneda).faithful

end GrothendieckTopology

end CategoryTheory
