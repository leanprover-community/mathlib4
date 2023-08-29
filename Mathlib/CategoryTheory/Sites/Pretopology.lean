/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Sites.Grothendieck

#align_import category_theory.sites.pretopology from "leanprover-community/mathlib"@"9e7c80f638149bfb3504ba8ff48dfdbfc949fb1a"

/-!
# Grothendieck pretopologies

Definition and lemmas about Grothendieck pretopologies.
A Grothendieck pretopology for a category `C` is a set of families of morphisms with fixed codomain,
satisfying certain closure conditions.

We show that a pretopology generates a genuine Grothendieck topology, and every topology has
a maximal pretopology which generates it.

The pretopology associated to a topological space is defined in `Spaces.lean`.

## Tags

coverage, pretopology, site

## References

* [nLab, *Grothendieck pretopology*](https://ncatlab.org/nlab/show/Grothendieck+pretopology)
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
* [Stacks, *00VG*](https://stacks.math.columbia.edu/tag/00VG)
-/


universe v u

noncomputable section

namespace CategoryTheory

open CategoryTheory Category Limits Presieve

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

variable (C)

/--
A (Grothendieck) pretopology on `C` consists of a collection of families of morphisms with a fixed
target `X` for every object `X` in `C`, called "coverings" of `X`, which satisfies the following
three axioms:
1. Every family consisting of a single isomorphism is a covering family.
2. The collection of covering families is stable under pullback.
3. Given a covering family, and a covering family on each domain of the former, the composition
   is a covering family.

In some sense, a pretopology can be seen as Grothendieck topology with weaker saturation conditions,
in that each covering is not necessarily downward closed.

See: https://ncatlab.org/nlab/show/Grothendieck+pretopology, or
https://stacks.math.columbia.edu/tag/00VH, or [MM92] Chapter III, Section 2, Definition 2.
Note that Stacks calls a category together with a pretopology a site, and [MM92] calls this
a basis for a topology.
-/
@[ext]
structure Pretopology where
  coverings : ∀ X : C, Set (Presieve X)
  has_isos : ∀ ⦃X Y⦄ (f : Y ⟶ X) [IsIso f], Presieve.singleton f ∈ coverings X
  pullbacks : ∀ ⦃X Y⦄ (f : Y ⟶ X) (S), S ∈ coverings X → pullbackArrows f S ∈ coverings Y
  Transitive :
    ∀ ⦃X : C⦄ (S : Presieve X) (Ti : ∀ ⦃Y⦄ (f : Y ⟶ X), S f → Presieve Y),
      S ∈ coverings X → (∀ ⦃Y⦄ (f) (H : S f), Ti f H ∈ coverings Y) → S.bind Ti ∈ coverings X
#align category_theory.pretopology CategoryTheory.Pretopology

namespace Pretopology

instance : CoeFun (Pretopology C) fun _ => ∀ X : C, Set (Presieve X) :=
  ⟨coverings⟩

variable {C}

instance LE : LE (Pretopology C) where
  le K₁ K₂ := (K₁ : ∀ X : C, Set (Presieve X)) ≤ K₂

theorem le_def {K₁ K₂ : Pretopology C} : K₁ ≤ K₂ ↔ (K₁ : ∀ X : C, Set (Presieve X)) ≤ K₂ :=
  Iff.rfl
#align category_theory.pretopology.le_def CategoryTheory.Pretopology.le_def

variable (C)

instance : PartialOrder (Pretopology C) :=
  { Pretopology.LE with
    le_refl := fun K => le_def.mpr le_rfl
    le_trans := fun K₁ K₂ K₃ h₁₂ h₂₃ => le_def.mpr (le_trans h₁₂ h₂₃)
    le_antisymm := fun K₁ K₂ h₁₂ h₂₁ => Pretopology.ext _ _ (le_antisymm h₁₂ h₂₁) }

instance : OrderTop (Pretopology C) where
  top :=
    { coverings := fun _ => Set.univ
      has_isos := fun _ _ _ _ => Set.mem_univ _
      pullbacks := fun _ _ _ _ _ => Set.mem_univ _
      Transitive := fun _ _ _ _ _ => Set.mem_univ _ }
  le_top _ _ _ _ := Set.mem_univ _

instance : Inhabited (Pretopology C) :=
  ⟨⊤⟩

/-- A pretopology `K` can be completed to a Grothendieck topology `J` by declaring a sieve to be
`J`-covering if it contains a family in `K`.

See <https://stacks.math.columbia.edu/tag/00ZC>, or [MM92] Chapter III, Section 2, Equation (2).
-/
def toGrothendieck (K : Pretopology C) : GrothendieckTopology C where
  sieves X S := ∃ R ∈ K X, R ≤ (S : Presieve _)
  top_mem' X := ⟨Presieve.singleton (𝟙 _), K.has_isos _, fun _ _ _ => ⟨⟩⟩
  pullback_stable' X Y S g := by
    rintro ⟨R, hR, RS⟩
    -- ⊢ Sieve.pullback g S ∈ (fun X S => ∃ R, R ∈ coverings K X ∧ R ≤ S.arrows) Y
    refine' ⟨_, K.pullbacks g _ hR, _⟩
    -- ⊢ pullbackArrows g R ≤ (Sieve.pullback g S).arrows
    rw [← Sieve.sets_iff_generate, Sieve.pullbackArrows_comm]
    -- ⊢ Sieve.pullback g (Sieve.generate R) ≤ Sieve.pullback g S
    apply Sieve.pullback_monotone
    -- ⊢ Sieve.generate R ≤ S
    rwa [Sieve.giGenerate.gc]
    -- 🎉 no goals
  transitive' := by
    rintro X S ⟨R', hR', RS⟩ R t
    -- ⊢ R ∈ (fun X S => ∃ R, R ∈ coverings K X ∧ R ≤ S.arrows) X
    choose t₁ t₂ t₃ using t
    -- ⊢ R ∈ (fun X S => ∃ R, R ∈ coverings K X ∧ R ≤ S.arrows) X
    refine' ⟨_, K.Transitive _ _ hR' fun _ f hf => t₂ (RS _ hf), _⟩
    -- ⊢ (Presieve.bind R' fun x f hf => t₁ (_ : f ∈ S.arrows)) ≤ R.arrows
    rintro Y _ ⟨Z, g, f, hg, hf, rfl⟩
    -- ⊢ g ≫ f ∈ R.arrows
    apply t₃ (RS _ hg) _ hf
    -- 🎉 no goals
#align category_theory.pretopology.to_grothendieck CategoryTheory.Pretopology.toGrothendieck

theorem mem_toGrothendieck (K : Pretopology C) (X S) :
    S ∈ toGrothendieck C K X ↔ ∃ R ∈ K X, R ≤ (S : Presieve X) :=
  Iff.rfl
#align category_theory.pretopology.mem_to_grothendieck CategoryTheory.Pretopology.mem_toGrothendieck

/-- The largest pretopology generating the given Grothendieck topology.

See [MM92] Chapter III, Section 2, Equations (3,4).
-/
def ofGrothendieck (J : GrothendieckTopology C) : Pretopology C where
  coverings X R := Sieve.generate R ∈ J X
  has_isos X Y f i := J.covering_of_eq_top (by simp)
                                               -- 🎉 no goals
  pullbacks X Y f R hR := by
    simp only [Set.mem_def, Sieve.pullbackArrows_comm]
    -- ⊢ GrothendieckTopology.sieves J Y (Sieve.pullback f (Sieve.generate R))
    apply J.pullback_stable f hR
    -- 🎉 no goals
  Transitive X S Ti hS hTi := by
    apply J.transitive hS
    -- ⊢ ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, (Sieve.generate S).arrows f → Sieve.pullback f (Sieve …
    intro Y f
    -- ⊢ (Sieve.generate S).arrows f → Sieve.pullback f (Sieve.generate (Presieve.bin …
    rintro ⟨Z, g, f, hf, rfl⟩
    -- ⊢ Sieve.pullback (g ≫ f) (Sieve.generate (Presieve.bind S Ti)) ∈ GrothendieckT …
    rw [Sieve.pullback_comp]
    -- ⊢ Sieve.pullback g (Sieve.pullback f (Sieve.generate (Presieve.bind S Ti))) ∈  …
    apply J.pullback_stable g
    -- ⊢ Sieve.pullback f (Sieve.generate (Presieve.bind S Ti)) ∈ GrothendieckTopolog …
    apply J.superset_covering _ (hTi _ hf)
    -- ⊢ Sieve.generate (Ti f hf) ≤ Sieve.pullback f (Sieve.generate (Presieve.bind S …
    rintro Y g ⟨W, h, g, hg, rfl⟩
    -- ⊢ (Sieve.pullback f (Sieve.generate (Presieve.bind S Ti))).arrows (h ≫ g)
    exact ⟨_, h, _, ⟨_, _, _, hf, hg, rfl⟩, by simp⟩
    -- 🎉 no goals
#align category_theory.pretopology.of_grothendieck CategoryTheory.Pretopology.ofGrothendieck

/-- We have a galois insertion from pretopologies to Grothendieck topologies. -/
def gi : GaloisInsertion (toGrothendieck C) (ofGrothendieck C) where
  gc K J := by
    constructor
    -- ⊢ toGrothendieck C K ≤ J → K ≤ ofGrothendieck C J
    · intro h X R hR
      -- ⊢ R ∈ coverings (ofGrothendieck C J) X
      exact h _ ⟨_, hR, Sieve.le_generate R⟩
      -- 🎉 no goals
    · rintro h X S ⟨R, hR, RS⟩
      -- ⊢ S ∈ GrothendieckTopology.sieves J X
      apply J.superset_covering _ (h _ hR)
      -- ⊢ Sieve.generate R ≤ S
      rwa [Sieve.giGenerate.gc]
      -- 🎉 no goals
  le_l_u J X S hS := ⟨S, J.superset_covering (Sieve.le_generate S.arrows) hS, le_rfl⟩
  choice x _ := toGrothendieck C x
  choice_eq _ _ := rfl
#align category_theory.pretopology.gi CategoryTheory.Pretopology.gi

/--
The trivial pretopology, in which the coverings are exactly singleton isomorphisms. This topology is
also known as the indiscrete, coarse, or chaotic topology.

See <https://stacks.math.columbia.edu/tag/07GE>
-/
def trivial : Pretopology C where
  coverings X S := ∃ (Y : _) (f : Y ⟶ X) (_ : IsIso f), S = Presieve.singleton f
  has_isos X Y f i := ⟨_, _, i, rfl⟩
  pullbacks X Y f S := by
    rintro ⟨Z, g, i, rfl⟩
    -- ⊢ pullbackArrows f (Presieve.singleton g) ∈ (fun X S => ∃ Y f x, S = Presieve. …
    refine' ⟨pullback g f, pullback.snd, _, _⟩
    -- ⊢ IsIso pullback.snd
    · refine' ⟨⟨pullback.lift (f ≫ inv g) (𝟙 _) (by simp), ⟨_, by aesop_cat⟩⟩⟩
      -- ⊢ pullback.snd ≫ pullback.lift (f ≫ inv g) (𝟙 Y) (_ : (f ≫ inv g) ≫ g = 𝟙 Y ≫  …
      ext
      -- ⊢ (pullback.snd ≫ pullback.lift (f ≫ inv g) (𝟙 Y) (_ : (f ≫ inv g) ≫ g = 𝟙 Y ≫ …
      · rw [assoc, pullback.lift_fst, ← pullback.condition_assoc]
        -- ⊢ pullback.fst ≫ g ≫ inv g = 𝟙 (pullback g f) ≫ pullback.fst
        simp
        -- 🎉 no goals
      · simp
        -- 🎉 no goals
    · apply pullback_singleton
      -- 🎉 no goals
  Transitive := by
    rintro X S Ti ⟨Z, g, i, rfl⟩ hS
    -- ⊢ Presieve.bind (Presieve.singleton g) Ti ∈ (fun X S => ∃ Y f x, S = Presieve. …
    rcases hS g (singleton_self g) with ⟨Y, f, i, hTi⟩
    -- ⊢ Presieve.bind (Presieve.singleton g) Ti ∈ (fun X S => ∃ Y f x, S = Presieve. …
    refine' ⟨_, f ≫ g, _, _⟩
    -- ⊢ IsIso (f ≫ g)
    · infer_instance
      -- 🎉 no goals
    -- Porting note: the next four lines were just "ext (W k)"
    apply funext
    -- ⊢ ∀ (x : C), Presieve.bind (Presieve.singleton g) Ti = Presieve.singleton (f ≫ …
    rintro W
    -- ⊢ Presieve.bind (Presieve.singleton g) Ti = Presieve.singleton (f ≫ g)
    apply Set.ext
    -- ⊢ ∀ (x : W ⟶ X), x ∈ Presieve.bind (Presieve.singleton g) Ti ↔ x ∈ Presieve.si …
    rintro k
    -- ⊢ k ∈ Presieve.bind (Presieve.singleton g) Ti ↔ k ∈ Presieve.singleton (f ≫ g)
    constructor
    -- ⊢ k ∈ Presieve.bind (Presieve.singleton g) Ti → k ∈ Presieve.singleton (f ≫ g)
    · rintro ⟨V, h, k, ⟨_⟩, hh, rfl⟩
      -- ⊢ h ≫ g ∈ Presieve.singleton (f ≫ g)
      rw [hTi] at hh
      -- ⊢ h ≫ g ∈ Presieve.singleton (f ≫ g)
      cases hh
      -- ⊢ f ≫ g ∈ Presieve.singleton (f ≫ g)
      apply singleton.mk
      -- 🎉 no goals
    · rintro ⟨_⟩
      -- ⊢ f ≫ g ∈ Presieve.bind (Presieve.singleton g) Ti
      refine' bind_comp g singleton.mk _
      -- ⊢ Ti g (_ : Presieve.singleton g g) f
      rw [hTi]
      -- ⊢ Presieve.singleton f f
      apply singleton.mk
      -- 🎉 no goals
#align category_theory.pretopology.trivial CategoryTheory.Pretopology.trivial

instance : OrderBot (Pretopology C) where
  bot := trivial C
  bot_le K X R := by
    rintro ⟨Y, f, hf, rfl⟩
    -- ⊢ Presieve.singleton f ∈ coverings K X
    exact K.has_isos f
    -- 🎉 no goals

/-- The trivial pretopology induces the trivial grothendieck topology. -/
theorem toGrothendieck_bot : toGrothendieck C ⊥ = ⊥ :=
  (gi C).gc.l_bot
#align category_theory.pretopology.to_grothendieck_bot CategoryTheory.Pretopology.toGrothendieck_bot

end Pretopology

end CategoryTheory
