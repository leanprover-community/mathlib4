/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import Mathlib.CategoryTheory.Sites.SheafOfTypes

/-!

# Coverages

A coverage `K` on a category `C` is a set of presieves associated to every object `X : C`,
called "covering presieves".
This collection must satisfy a certain "pullback compatibility" condition, saying that
whenever `S` is a covering presieve on `X` and `f : Y ⟶ X` is a morphism, then there exists
some covering sieve `T` on `Y` such that `T` factors through `S` along `f`.

The main difference between a coverage and a Grothendieck pretopology is that we *do not*
require `C` to have pullbacks.
This is useful, for example, when we want to consider the Grothendieck topology on the category
of extremally disconnected sets in the context of condensed mathematics.

A more concrete example: If `ℬ` is a basis for a topology on a type `X` (in the sense of
`TopologicalSpace.IsTopologicalBasis`) then it naturally induces a coverage on `Opens X`
whose associated Grothendieck topology is the one induced by the topology
on `X` generated by `ℬ`. (Project: Formalize this!)

## Main Definitions and Results:

All definitions are in the `CategoryTheory` namespace.

- `Coverage C`: The type of coverages on `C`.
- `Coverage.ofGrothendieck C`: A function which associates a coverage to any Grothendieck topology.
- `Coverage.toGrothendieck C`: A function which associates a Grothendieck topology to any coverage.
- `Coverage.gi`: The two functions above form a Galois insertion.
- `Presieve.isSheaf_coverage`: Given `K : Coverage C` with associated
  Grothendieck topology `J`, a `Type _`-valued presheaf on `C` is a sheaf for `K` if and only if
  it is a sheaf for `J`.

# References
We don't follow any particular reference, but the arguments can probably be distilled from
the following sources:
- [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.1.
- [nLab, *Coverage*](https://ncatlab.org/nlab/show/coverage)
-/

namespace CategoryTheory

variable {C : Type _} [Category C]

namespace Presieve

/--
Given a morphism `f : Y ⟶ X`, a presieve `S` on `Y` and presieve `T` on `X`,
we say that *`S` factors through `T` along `f`*, written `S.FactorsThruAlong T f`,
provided that for any morphism `g : Z ⟶ Y` in `S`, there exists some
morphism `e : W ⟶ X` in `T` and some morphism `i : Z ⟶ W` such that the obvious
square commutes: `i ≫ e = g ≫ f`.

This is used in the definition of a coverage.
-/
def FactorsThruAlong {X Y : C} (S : Presieve Y) (T : Presieve X) (f : Y ⟶ X) : Prop :=
  ∀ ⦃Z : C⦄ ⦃g : Z ⟶ Y⦄, S g →
  ∃ (W : C) (i : Z ⟶ W) (e : W ⟶ X), T e ∧ i ≫ e = g ≫ f

/--
Given `S T : Presieve X`, we say that `S` factors through `T` if any morphism in `S`
factors through some morphism in `T`.

The lemma `Presieve.isSheafFor_of_factorsThru` gives a *sufficient* condition for a
presheaf to be a sheaf for a presieve `T`, in terms of `S.FactorsThru T`, provided
that the presheaf is a sheaf for `S`.
-/
def FactorsThru {X : C} (S T : Presieve X) : Prop :=
  ∀ ⦃Z : C⦄ ⦃g : Z ⟶ X⦄, S g →
  ∃ (W : C) (i : Z ⟶ W) (e : W ⟶ X), T e ∧ i ≫ e = g

@[simp]
lemma factorsThruAlong_id {X : C} (S T : Presieve X) :
    S.FactorsThruAlong T (𝟙 X) ↔ S.FactorsThru T := by
  simp [FactorsThruAlong, FactorsThru]

lemma factorsThru_of_le {X : C} (S T : Presieve X) (h : S ≤ T) :
    S.FactorsThru T :=
  fun Y g hg => ⟨Y, 𝟙 _, g, h _ hg, by simp⟩

lemma le_of_factorsThru_sieve {X : C} (S : Presieve X) (T : Sieve X) (h : S.FactorsThru T) :
    S ≤ T := by
  rintro Y f hf
  obtain ⟨W, i, e, h1, rfl⟩ := h hf
  exact T.downward_closed h1 _

lemma factorsThru_top {X : C} (S : Presieve X) : S.FactorsThru ⊤ :=
  factorsThru_of_le _ _ le_top

lemma isSheafFor_of_factorsThru
    {X : C} {S T : Presieve X}
    (P : Cᵒᵖ ⥤ Type w)
    (H : S.FactorsThru T) (hS : S.IsSheafFor P)
    (h : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, T f → ∃ (R : Presieve Y),
      R.IsSeparatedFor P ∧ R.FactorsThruAlong S f):
    T.IsSheafFor P := by
  simp only [←Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor] at *
  choose W i e h1 h2 using H
  refine ⟨?_, fun x hx => ?_⟩
  · intro x y₁ y₂ h₁ h₂
    refine hS.1.ext (fun Y g hg => ?_)
    simp only [← h2 hg, op_comp, P.map_comp, types_comp_apply, h₁ _ (h1 _ ), h₂ _ (h1  _)]
  let y : S.FamilyOfElements P := fun Y g hg => P.map (i _).op (x (e hg) (h1 _))
  have hy : y.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ h
    rw [← types_comp_apply (P.map (i h₁).op) (P.map g₁.op),
      ← types_comp_apply (P.map (i h₂).op) (P.map g₂.op),
      ← P.map_comp, ← op_comp, ← P.map_comp, ← op_comp]
    apply hx
    simp only [h2, h, Category.assoc]
  let ⟨_, h2'⟩ := hS
  obtain ⟨z, hz⟩ := h2' y hy
  refine ⟨z, fun Y g hg => ?_⟩
  obtain ⟨R, hR1, hR2⟩ := h hg
  choose WW ii ee hh1 hh2 using hR2
  refine hR1.ext (fun Q t ht => ?_)
  rw [← types_comp_apply (P.map g.op) (P.map t.op), ← P.map_comp, ← op_comp, ← hh2 ht,
    op_comp, P.map_comp, types_comp_apply, hz _ (hh1 _),
    ← types_comp_apply _ (P.map (ii ht).op), ← P.map_comp, ← op_comp]
  apply hx
  simp only [Category.assoc, h2, hh2]


end Presieve

variable (C) in
/--
The type `Coverage C` of coverages on `C`.
A coverage is a collection of *covering* presieves on every object `X : C`,
which satisfies a *pullback compatibility* condition.
Explicitly, this condition says that whenever `S` is a covering presieve for `X` and
`f : Y ⟶ X` is a morphism, then there exists some covering presieve `T` for `Y`
such that `T` factors through `S` along `f`.
-/
@[ext]
structure Coverage where
  /-- The collection of covering presieves for an object `X`. -/
  covering : ∀ (X : C), Set (Presieve X)
  /-- Given any covering sieve `S` on `X` and a morphism `f : Y ⟶ X`, there exists
    some covering sieve `T` on `Y` such that `T` factors through `S` along `f`. -/
  pullback : ∀ ⦃X Y : C⦄ (f : Y ⟶ X) (S : Presieve X) (_ : S ∈ covering X),
    ∃ (T : Presieve Y), T ∈ covering Y ∧ T.FactorsThruAlong S f

namespace Coverage

instance : CoeFun (Coverage C) (fun _ => (X : C) → Set (Presieve X)) where
  coe := covering

variable (C) in
/--
Associate a coverage to any Grothendieck topology.
If `J` is a Grothendieck topology, and `K` is the associated coverage, then a presieve
`S` is a covering presieve for `K` if and only if the sieve that it generates is a
covering sieve for `J`.
-/
def ofGrothendieck (J : GrothendieckTopology C) : Coverage C where
  covering X := { S | Sieve.generate S ∈ J X }
  pullback := by
    intro X Y f S (hS : Sieve.generate S ∈ J X)
    refine ⟨(Sieve.generate S).pullback f, ?_, fun Z g h => h⟩
    dsimp
    rw [Sieve.generate_sieve]
    exact J.pullback_stable _ hS

lemma ofGrothendieck_iff {X : C} {S : Presieve X} (J : GrothendieckTopology C) :
    S ∈ ofGrothendieck _ J X ↔ Sieve.generate S ∈ J X := Iff.rfl

/--
An auxiliary definition used to define the Grothendieck topology associated to a
coverage. See `Coverage.toGrothendieck`.
-/
inductive saturate (K : Coverage C) : (X : C) → Sieve X → Prop where
  | of (X : C) (S : Presieve X) (hS : S ∈ K X) : saturate K X (Sieve.generate S)
  | top (X : C) : saturate K X ⊤
  | transitive (X : C) (R S : Sieve X) :
    saturate K X R →
    (∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, R f → saturate K Y (S.pullback f)) →
    saturate K X S

lemma eq_top_pullback {X Y : C} {S T : Sieve X} (h : S ≤ T) (f : Y ⟶ X) (hf : S f) :
    T.pullback f = ⊤ := by
  ext Z ; intro g
  simp only [Sieve.pullback_apply, Sieve.top_apply, iff_true]
  apply h
  apply S.downward_closed
  exact hf

lemma saturate_of_superset (K : Coverage C) {X : C} {S T : Sieve X} (h : S ≤ T)
    (hS : saturate K X S) : saturate K X T := by
  apply saturate.transitive _ _ _ hS
  intro Y g hg
  rw [eq_top_pullback (h := h)]
  · apply saturate.top
  · assumption

variable (C) in
/--
The Grothendieck topology associated to a coverage `K`.
It is defined *inductively* as follows:
1. If `S` is a covering presieve for `K`, then the sieve generated by `S` is a covering
  sieve for the associated Grothendieck topology.
2. The top sieves are in the associated Grothendieck topology.
3. Add all sieves required by the *local character* axiom of a Grothendieck topology.

The pullback compatibility condition for a coverage ensures that the
associated Grothendieck topology is pullback stable, and so an additional constructor
in the inductive construction is not needed.
-/
def toGrothendieck (K : Coverage C) : GrothendieckTopology C where
  sieves := saturate K
  top_mem' := .top
  pullback_stable' := by
    intro X Y S f hS
    induction hS generalizing Y with
    | of X S hS =>
      obtain ⟨R,hR1,hR2⟩ := K.pullback f S hS
      suffices Sieve.generate R ≤ (Sieve.generate S).pullback f from
        saturate_of_superset _ this (saturate.of _ _ hR1)
      rintro Z g ⟨W, i, e, h1, h2⟩
      obtain ⟨WW, ii, ee, hh1, hh2⟩ := hR2 h1
      refine ⟨WW, i ≫ ii, ee, hh1, ?_⟩
      simp only [hh2, reassoc_of% h2, Category.assoc]
    | top X => apply saturate.top
    | transitive X R S _ hS H1 _ =>
      apply saturate.transitive
      apply H1 f
      intro Z g hg
      rw [← Sieve.pullback_comp]
      exact hS hg
  transitive' X S hS R hR := .transitive _ _ _ hS hR

instance : PartialOrder (Coverage C) where
  le A B := A.covering ≤ B.covering
  le_refl A X := le_refl _
  le_trans A B C h1 h2 X := le_trans (h1 X) (h2 X)
  le_antisymm A B h1 h2 := Coverage.ext A B <| funext <|
    fun X => le_antisymm (h1 X) (h2 X)

variable (C) in
/--
The two constructions `Coverage.toGrothendieck` and `Coverage.ofGrothendieck` form
a Galois insertion.
-/
def gi : GaloisInsertion (toGrothendieck C) (ofGrothendieck C) where
  choice K _ := toGrothendieck _ K
  choice_eq := fun _ _ => rfl
  le_l_u J X S hS := by
    rw [← Sieve.generate_sieve S]
    apply saturate.of
    dsimp [ofGrothendieck]
    rwa [Sieve.generate_sieve S]
  gc K J := by
    constructor
    · intro H X S hS
      exact H _ <| saturate.of _ _ hS
    · intro H X S hS
      induction hS with
      | of X S hS => exact H _ hS
      | top => apply J.top_mem
      | transitive X R S _ _ H1 H2 => exact J.transitive H1 _ H2

/--
An alternative characterization of the Grothendieck topology associated to a coverage `K`:
it is the infimum of all Grothendieck topologies whose associated coverage contains `K`.
-/
theorem toGrothendieck_eq_sInf (K : Coverage C) : toGrothendieck _ K =
    sInf {J | K ≤ ofGrothendieck _ J } := by
  apply le_antisymm
  · apply le_sInf ; intro J hJ
    intro X S hS
    induction hS with
    | of X S hS => apply hJ ; assumption
    | top => apply J.top_mem
    | transitive X R S _ _ H1 H2 => exact J.transitive H1 _ H2
  · apply sInf_le
    intro X S hS
    apply saturate.of _ _ hS

end Coverage

open Coverage

namespace Presieve

/--
The main theorem of this file: Given a coverage `K` on `C`,
a `Type _`-valued presheaf on `C` is a sheaf for `K` if and only if it is a sheaf for
the associated Grothendieck topology.
-/
theorem isSheaf_coverage (K : Coverage C) (P : Cᵒᵖ ⥤ Type w) :
    Presieve.IsSheaf (toGrothendieck _ K) P ↔
    (∀ {X : C} (R : Presieve X), R ∈ K X → Presieve.IsSheafFor P R) := by
  constructor
  · intro H X R hR
    rw [Presieve.isSheafFor_iff_generate]
    apply H _ <| saturate.of _ _ hR
  · intro H X S hS
    -- This is the key point of the proof:
    -- We must generalize the induction in the correct way.
    suffices ∀ ⦃Y : C⦄ (f : Y ⟶ X), Presieve.IsSheafFor P (S.pullback f).arrows by
      simpa using this (f := 𝟙 _)
    induction hS with
    | of X S hS =>
      intro Y f
      obtain ⟨T, hT1, hT2⟩ := K.pullback f S hS
      apply Presieve.isSheafFor_of_factorsThru (S := T)
      · intro Z g hg
        obtain ⟨W, i, e, h1, h2⟩ := hT2 hg
        exact ⟨Z, 𝟙 _, g, ⟨W, i, e, h1, h2⟩, by simp⟩
      · apply H ; assumption
      · intro Z g _
        obtain ⟨R, hR1, hR2⟩ := K.pullback g _ hT1
        refine ⟨R, (H _ hR1).isSeparatedFor, hR2⟩
    | top => intros ; simpa using Presieve.isSheafFor_top_sieve _
    | transitive X R S _ _ H1 H2 =>
      intro Y f
      simp only [← Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor] at *
      choose H1 H1' using H1
      choose H2 H2' using H2
      refine ⟨?_, fun x hx => ?_⟩
      · intro x t₁ t₂ h₁ h₂
        refine (H1 f).ext (fun Z g hg => ?_)
        refine (H2 hg (𝟙 _)).ext (fun ZZ gg hgg => ?_)
        simp only [Sieve.pullback_id, Sieve.pullback_apply] at hgg
        simp only [← types_comp_apply]
        rw [← P.map_comp, ← op_comp, h₁, h₂]
        simpa only [Sieve.pullback_apply, Category.assoc] using hgg
      let y : ∀ ⦃Z : C⦄ (g : Z ⟶ Y),
        ((S.pullback (g ≫ f)).pullback (𝟙 _)).arrows.FamilyOfElements P :=
        fun Z g ZZ gg hgg => x (gg ≫ g) (by simpa using hgg)
      have hy : ∀ ⦃Z : C⦄ (g : Z ⟶ Y), (y g).Compatible := by
        intro Z g Y₁ Y₂ ZZ g₁ g₂ f₁ f₂ h₁ h₂ h
        rw [hx]
        rw [reassoc_of% h]
      choose z hz using fun ⦃Z : C⦄ ⦃g : Z ⟶ Y⦄ (hg : R.pullback f g) =>
        H2' hg (𝟙 _) (y g) (hy g)
      let q : (R.pullback f).arrows.FamilyOfElements P := fun Z g hg => z hg
      have hq : q.Compatible := by
        intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ h
        apply (H2 h₁ g₁).ext
        intro ZZ gg hgg
        simp only [← types_comp_apply]
        rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp, hz, hz]
        · dsimp ; congr 1 ; simp only [Category.assoc, h]
        · simpa [reassoc_of% h] using hgg
        · simpa using hgg
      obtain ⟨t, ht⟩ := H1' f q hq
      refine ⟨t, fun Z g hg => ?_⟩
      refine (H1 (g ≫ f)).ext (fun ZZ gg hgg => ?_)
      rw [← types_comp_apply _ (P.map gg.op), ← P.map_comp, ← op_comp, ht]
      swap ; simpa using hgg
      refine (H2 hgg (𝟙 _)).ext (fun ZZZ ggg hggg => ?_)
      rw [← types_comp_apply _ (P.map ggg.op), ← P.map_comp, ← op_comp, hz]
      swap ; simpa using hggg
      refine (H2 hgg ggg).ext (fun ZZZZ gggg _ => ?_)
      rw [← types_comp_apply _ (P.map gggg.op), ← P.map_comp, ← op_comp]
      apply hx
      simp

end Presieve

end CategoryTheory
