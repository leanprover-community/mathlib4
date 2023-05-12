/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.sites.canonical
! leanprover-community/mathlib commit 9e7c80f638149bfb3504ba8ff48dfdbfc949fb1a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Sites.SheafOfTypes

/-!
# The canonical topology on a category

We define the finest (largest) Grothendieck topology for which a given presheaf `P` is a sheaf.
This is well defined since if `P` is a sheaf for a topology `J`, then it is a sheaf for any
coarser (smaller) topology. Nonetheless we define the topology explicitly by specifying its sieves:
A sieve `S` on `X` is covering for `finest_topology_single P` iff
  for any `f : Y ⟶ X`, `P` satisfies the sheaf axiom for `S.pullback f`.
Showing that this is a genuine Grothendieck topology (namely that it satisfies the transitivity
axiom) forms the bulk of this file.

This generalises to a set of presheaves, giving the topology `finest_topology Ps` which is the
finest topology for which every presheaf in `Ps` is a sheaf.
Using `Ps` as the set of representable presheaves defines the `canonical_topology`: the finest
topology for which every representable is a sheaf.

A Grothendieck topology is called `subcanonical` if it is smaller than the canonical topology,
equivalently it is subcanonical iff every representable presheaf is a sheaf.

## References
* https://ncatlab.org/nlab/show/canonical+topology
* https://ncatlab.org/nlab/show/subcanonical+coverage
* https://stacks.math.columbia.edu/tag/00Z9
* https://math.stackexchange.com/a/358709/
-/


universe v u

namespace CategoryTheory

open CategoryTheory Category Limits Sieve Classical

variable {C : Type u} [Category.{v} C]

namespace Sheaf

variable {P : Cᵒᵖ ⥤ Type v}

variable {X Y : C} {S : Sieve X} {R : Presieve X}

variable (J J₂ : GrothendieckTopology C)

/--
To show `P` is a sheaf for the binding of `U` with `B`, it suffices to show that `P` is a sheaf for
`U`, that `P` is a sheaf for each sieve in `B`, and that it is separated for any pullback of any
sieve in `B`.

This is mostly an auxiliary lemma to show `is_sheaf_for_trans`.
Adapted from [Elephant], Lemma C2.1.7(i) with suggestions as mentioned in
https://math.stackexchange.com/a/358709/
-/
theorem isSheafFor_bind (P : Cᵒᵖ ⥤ Type v) (U : Sieve X) (B : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, U f → Sieve Y)
    (hU : Presieve.IsSheafFor P U) (hB : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), Presieve.IsSheafFor P (B hf))
    (hB' :
      ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (h : U f) ⦃Z⦄ (g : Z ⟶ Y), Presieve.IsSeparatedFor P ((B h).pullback g)) :
    Presieve.IsSheafFor P (Sieve.bind U B) :=
  by
  intro s hs
  let y : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), presieve.family_of_elements P (B hf) := fun Y f hf Z g hg =>
    s _ (presieve.bind_comp _ _ hg)
  have hy : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), (y hf).Compatible :=
    by
    intro Y f H Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ comm
    apply hs
    apply reassoc_of comm
  let t : presieve.family_of_elements P U := fun Y f hf => (hB hf).amalgamate (y hf) (hy hf)
  have ht : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), (y hf).IsAmalgamation (t f hf) := fun Y f hf =>
    (hB hf).IsAmalgamation _
  have hT : t.compatible := by
    rw [presieve.compatible_iff_sieve_compatible]
    intro Z W f h hf
    apply (hB (U.downward_closed hf h)).IsSeparatedFor.ext
    intro Y l hl
    apply (hB' hf (l ≫ h)).ext
    intro M m hm
    have : bind U B (m ≫ l ≫ h ≫ f) :=
      by
      have : bind U B _ := presieve.bind_comp f hf hm
      simpa using this
    trans s (m ≫ l ≫ h ≫ f) this
    · have := ht (U.downward_closed hf h) _ ((B _).downward_closed hl m)
      rw [op_comp, functor_to_types.map_comp_apply] at this
      rw [this]
      change s _ _ = s _ _
      simp
    · have : s _ _ = _ := (ht hf _ hm).symm
      simp only [assoc] at this
      rw [this]
      simp
  refine' ⟨hU.amalgamate t hT, _, _⟩
  · rintro Z _ ⟨Y, f, g, hg, hf, rfl⟩
    rw [op_comp, functor_to_types.map_comp_apply, presieve.is_sheaf_for.valid_glue _ _ _ hg]
    apply ht hg _ hf
  · intro y hy
    apply hU.is_separated_for.ext
    intro Y f hf
    apply (hB hf).IsSeparatedFor.ext
    intro Z g hg
    rw [← functor_to_types.map_comp_apply, ← op_comp, hy _ (presieve.bind_comp _ _ hg),
      hU.valid_glue _ _ hf, ht hf _ hg]
#align category_theory.sheaf.is_sheaf_for_bind CategoryTheory.Sheaf.isSheafFor_bind

/-- Given two sieves `R` and `S`, to show that `P` is a sheaf for `S`, we can show:
* `P` is a sheaf for `R`
* `P` is a sheaf for the pullback of `S` along any arrow in `R`
* `P` is separated for the pullback of `R` along any arrow in `S`.

This is mostly an auxiliary lemma to construct `finest_topology`.
Adapted from [Elephant], Lemma C2.1.7(ii) with suggestions as mentioned in
https://math.stackexchange.com/a/358709
-/
theorem isSheafFor_trans (P : Cᵒᵖ ⥤ Type v) (R S : Sieve X) (hR : Presieve.IsSheafFor P R)
    (hR' : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : S f), Presieve.IsSeparatedFor P (R.pullback f))
    (hS : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : R f), Presieve.IsSheafFor P (S.pullback f)) :
    Presieve.IsSheafFor P S :=
  by
  have : (bind R fun Y f hf => S.pullback f : presieve X) ≤ S :=
    by
    rintro Z f ⟨W, f, g, hg, hf : S _, rfl⟩
    apply hf
  apply presieve.is_sheaf_for_subsieve_aux P this
  apply is_sheaf_for_bind _ _ _ hR hS
  · intro Y f hf Z g
    dsimp
    rw [← pullback_comp]
    apply (hS (R.downward_closed hf _)).IsSeparatedFor
  · intro Y f hf
    have : sieve.pullback f (bind R fun T (k : T ⟶ X) (hf : R k) => pullback k S) = R.pullback f :=
      by
      ext (Z g)
      constructor
      · rintro ⟨W, k, l, hl, _, comm⟩
        rw [pullback_apply, ← comm]
        simp [hl]
      · intro a
        refine' ⟨Z, 𝟙 Z, _, a, _⟩
        simp [hf]
    rw [this]
    apply hR' hf
#align category_theory.sheaf.is_sheaf_for_trans CategoryTheory.Sheaf.isSheafFor_trans

/-- Construct the finest (largest) Grothendieck topology for which the given presheaf is a sheaf.

This is a special case of https://stacks.math.columbia.edu/tag/00Z9, but following a different
proof (see the comments there).
-/
def finestTopologySingle (P : Cᵒᵖ ⥤ Type v) : GrothendieckTopology C
    where
  sieves X S := ∀ (Y) (f : Y ⟶ X), Presieve.IsSheafFor P (S.pullback f)
  top_mem' X Y f := by
    rw [sieve.pullback_top]
    exact presieve.is_sheaf_for_top_sieve P
  pullback_stable' X Y S f hS Z g := by
    rw [← pullback_comp]
    apply hS
  transitive' X S hS R hR Z g :=
    by
    -- This is the hard part of the construction, showing that the given set of sieves satisfies
    -- the transitivity axiom.
    refine' is_sheaf_for_trans P (pullback g S) _ (hS Z g) _ _
    · intro Y f hf
      rw [← pullback_comp]
      apply (hS _ _).IsSeparatedFor
    · intro Y f hf
      have := hR hf _ (𝟙 _)
      rw [pullback_id, pullback_comp] at this
      apply this
#align category_theory.sheaf.finest_topology_single CategoryTheory.Sheaf.finestTopologySingle

/--
Construct the finest (largest) Grothendieck topology for which all the given presheaves are sheaves.

This is equal to the construction of <https://stacks.math.columbia.edu/tag/00Z9>.
-/
def finestTopology (Ps : Set (Cᵒᵖ ⥤ Type v)) : GrothendieckTopology C :=
  infₛ (finestTopologySingle '' Ps)
#align category_theory.sheaf.finest_topology CategoryTheory.Sheaf.finestTopology

/-- Check that if `P ∈ Ps`, then `P` is indeed a sheaf for the finest topology on `Ps`. -/
theorem sheaf_for_finestTopology (Ps : Set (Cᵒᵖ ⥤ Type v)) (h : P ∈ Ps) :
    Presieve.IsSheaf (finestTopology Ps) P := fun X S hS => by
  simpa using hS _ ⟨⟨_, _, ⟨_, h, rfl⟩, rfl⟩, rfl⟩ _ (𝟙 _)
#align category_theory.sheaf.sheaf_for_finest_topology CategoryTheory.Sheaf.sheaf_for_finestTopology

/--
Check that if each `P ∈ Ps` is a sheaf for `J`, then `J` is a subtopology of `finest_topology Ps`.
-/
theorem le_finestTopology (Ps : Set (Cᵒᵖ ⥤ Type v)) (J : GrothendieckTopology C)
    (hJ : ∀ P ∈ Ps, Presieve.IsSheaf J P) : J ≤ finestTopology Ps :=
  by
  rintro X S hS _ ⟨⟨_, _, ⟨P, hP, rfl⟩, rfl⟩, rfl⟩
  intro Y f
  -- this can't be combined with the previous because the `subst` is applied at the end
  exact hJ P hP (S.pullback f) (J.pullback_stable f hS)
#align category_theory.sheaf.le_finest_topology CategoryTheory.Sheaf.le_finestTopology

/-- The `canonical_topology` on a category is the finest (largest) topology for which every
representable presheaf is a sheaf.

See <https://stacks.math.columbia.edu/tag/00ZA>
-/
def canonicalTopology (C : Type u) [Category.{v} C] : GrothendieckTopology C :=
  finestTopology (Set.range yoneda.obj)
#align category_theory.sheaf.canonical_topology CategoryTheory.Sheaf.canonicalTopology

/-- `yoneda.obj X` is a sheaf for the canonical topology. -/
theorem isSheaf_yoneda_obj (X : C) : Presieve.IsSheaf (canonicalTopology C) (yoneda.obj X) :=
  fun Y S hS => sheaf_for_finestTopology _ (Set.mem_range_self _) _ hS
#align category_theory.sheaf.is_sheaf_yoneda_obj CategoryTheory.Sheaf.isSheaf_yoneda_obj

/-- A representable functor is a sheaf for the canonical topology. -/
theorem isSheaf_of_representable (P : Cᵒᵖ ⥤ Type v) [P.Representable] :
    Presieve.IsSheaf (canonicalTopology C) P :=
  Presieve.isSheaf_iso (canonicalTopology C) P.reprW (isSheaf_yoneda_obj _)
#align category_theory.sheaf.is_sheaf_of_representable CategoryTheory.Sheaf.isSheaf_of_representable

/-- A subcanonical topology is a topology which is smaller than the canonical topology.
Equivalently, a topology is subcanonical iff every representable is a sheaf.
-/
def Subcanonical (J : GrothendieckTopology C) : Prop :=
  J ≤ canonicalTopology C
#align category_theory.sheaf.subcanonical CategoryTheory.Sheaf.Subcanonical

namespace Subcanonical

/-- If every functor `yoneda.obj X` is a `J`-sheaf, then `J` is subcanonical. -/
theorem of_yoneda_isSheaf (J : GrothendieckTopology C)
    (h : ∀ X, Presieve.IsSheaf J (yoneda.obj X)) : Subcanonical J :=
  le_finestTopology _ _
    (by
      rintro P ⟨X, rfl⟩
      apply h)
#align category_theory.sheaf.subcanonical.of_yoneda_is_sheaf CategoryTheory.Sheaf.Subcanonical.of_yoneda_isSheaf

/-- If `J` is subcanonical, then any representable is a `J`-sheaf. -/
theorem isSheaf_of_representable {J : GrothendieckTopology C} (hJ : Subcanonical J)
    (P : Cᵒᵖ ⥤ Type v) [P.Representable] : Presieve.IsSheaf J P :=
  Presieve.isSheaf_of_le _ hJ (isSheaf_of_representable P)
#align category_theory.sheaf.subcanonical.is_sheaf_of_representable CategoryTheory.Sheaf.Subcanonical.isSheaf_of_representable

end Subcanonical

end Sheaf

end CategoryTheory

