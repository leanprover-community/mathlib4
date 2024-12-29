/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Sites.Grothendieck

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

open Category Limits Presieve

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
  transitive :
    ∀ ⦃X : C⦄ (S : Presieve X) (Ti : ∀ ⦃Y⦄ (f : Y ⟶ X), S f → Presieve Y),
      S ∈ coverings X → (∀ ⦃Y⦄ (f) (H : S f), Ti f H ∈ coverings Y) → S.bind Ti ∈ coverings X

namespace Pretopology

instance : CoeFun (Pretopology C) fun _ => ∀ X : C, Set (Presieve X) :=
  ⟨coverings⟩

variable {C}

instance LE : LE (Pretopology C) where
  le K₁ K₂ := (K₁ : ∀ X : C, Set (Presieve X)) ≤ K₂

theorem le_def {K₁ K₂ : Pretopology C} : K₁ ≤ K₂ ↔ (K₁ : ∀ X : C, Set (Presieve X)) ≤ K₂ :=
  Iff.rfl

variable (C)

instance : PartialOrder (Pretopology C) :=
  { Pretopology.LE with
    le_refl := fun _ => le_def.mpr le_rfl
    le_trans := fun _ _ _ h₁₂ h₂₃ => le_def.mpr (le_trans h₁₂ h₂₃)
    le_antisymm := fun _ _ h₁₂ h₂₁ => Pretopology.ext (le_antisymm h₁₂ h₂₁) }

instance orderTop : OrderTop (Pretopology C) where
  top :=
    { coverings := fun _ => Set.univ
      has_isos := fun _ _ _ _ => Set.mem_univ _
      pullbacks := fun _ _ _ _ _ => Set.mem_univ _
      transitive := fun _ _ _ _ _ => Set.mem_univ _ }
  le_top _ _ _ _ := Set.mem_univ _

instance : Inhabited (Pretopology C) :=
  ⟨⊤⟩

/-- A pretopology `K` can be completed to a Grothendieck topology `J` by declaring a sieve to be
`J`-covering if it contains a family in `K`.

See <https://stacks.math.columbia.edu/tag/00ZC>, or [MM92] Chapter III, Section 2, Equation (2).
-/
def toGrothendieck (K : Pretopology C) : GrothendieckTopology C where
  sieves X S := ∃ R ∈ K X, R ≤ (S : Presieve _)
  top_mem' _ := ⟨Presieve.singleton (𝟙 _), K.has_isos _, fun _ _ _ => ⟨⟩⟩
  pullback_stable' X Y S g := by
    rintro ⟨R, hR, RS⟩
    refine ⟨_, K.pullbacks g _ hR, ?_⟩
    rw [← Sieve.generate_le_iff, Sieve.pullbackArrows_comm]
    apply Sieve.pullback_monotone
    rwa [Sieve.giGenerate.gc]
  transitive' := by
    rintro X S ⟨R', hR', RS⟩ R t
    choose t₁ t₂ t₃ using t
    refine ⟨_, K.transitive _ _ hR' fun _ f hf => t₂ (RS _ hf), ?_⟩
    rintro Y _ ⟨Z, g, f, hg, hf, rfl⟩
    apply t₃ (RS _ hg) _ hf

theorem mem_toGrothendieck (K : Pretopology C) (X S) :
    S ∈ toGrothendieck C K X ↔ ∃ R ∈ K X, R ≤ (S : Presieve X) :=
  Iff.rfl

/-- The largest pretopology generating the given Grothendieck topology.

See [MM92] Chapter III, Section 2, Equations (3,4).
-/
def ofGrothendieck (J : GrothendieckTopology C) : Pretopology C where
  coverings X R := Sieve.generate R ∈ J X
  has_isos X Y f i := J.covering_of_eq_top (by simp)
  pullbacks X Y f R hR := by
    simp only [Set.mem_def, Sieve.pullbackArrows_comm]
    apply J.pullback_stable f hR
  transitive X S Ti hS hTi := by
    apply J.transitive hS
    intro Y f
    rintro ⟨Z, g, f, hf, rfl⟩
    rw [Sieve.pullback_comp]
    apply J.pullback_stable g
    apply J.superset_covering _ (hTi _ hf)
    rintro Y g ⟨W, h, g, hg, rfl⟩
    exact ⟨_, h, _, ⟨_, _, _, hf, hg, rfl⟩, by simp⟩

/-- We have a galois insertion from pretopologies to Grothendieck topologies. -/
def gi : GaloisInsertion (toGrothendieck C) (ofGrothendieck C) where
  gc K J := by
    constructor
    · intro h X R hR
      exact h _ ⟨_, hR, Sieve.le_generate R⟩
    · rintro h X S ⟨R, hR, RS⟩
      apply J.superset_covering _ (h _ hR)
      rwa [Sieve.giGenerate.gc]
  le_l_u J _ S hS := ⟨S, J.superset_covering (Sieve.le_generate S.arrows) hS, le_rfl⟩
  choice x _ := toGrothendieck C x
  choice_eq _ _ := rfl

lemma mem_ofGrothendieck (t : GrothendieckTopology C) {X : C} (S : Presieve X) :
    S ∈ ofGrothendieck C t X ↔ Sieve.generate S ∈ t X :=
  Iff.rfl

/--
The trivial pretopology, in which the coverings are exactly singleton isomorphisms. This topology is
also known as the indiscrete, coarse, or chaotic topology.

See <https://stacks.math.columbia.edu/tag/07GE>
-/
def trivial : Pretopology C where
  coverings X S := ∃ (Y : _) (f : Y ⟶ X) (_ : IsIso f), S = Presieve.singleton f
  has_isos _ _ _ i := ⟨_, _, i, rfl⟩
  pullbacks X Y f S := by
    rintro ⟨Z, g, i, rfl⟩
    refine ⟨pullback g f, pullback.snd _ _, ?_, ?_⟩
    · refine ⟨⟨pullback.lift (f ≫ inv g) (𝟙 _) (by simp), ⟨?_, by aesop_cat⟩⟩⟩
      ext
      · rw [assoc, pullback.lift_fst, ← pullback.condition_assoc]
        simp
      · simp
    · apply pullback_singleton
  transitive := by
    rintro X S Ti ⟨Z, g, i, rfl⟩ hS
    rcases hS g (singleton_self g) with ⟨Y, f, i, hTi⟩
    refine ⟨_, f ≫ g, ?_, ?_⟩
    · infer_instance
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): the next four lines were just "ext (W k)"
    apply funext
    rintro W
    apply Set.ext
    rintro k
    constructor
    · rintro ⟨V, h, k, ⟨_⟩, hh, rfl⟩
      rw [hTi] at hh
      cases hh
      apply singleton.mk
    · rintro ⟨_⟩
      refine bind_comp g singleton.mk ?_
      rw [hTi]
      apply singleton.mk

instance orderBot : OrderBot (Pretopology C) where
  bot := trivial C
  bot_le K X R := by
    rintro ⟨Y, f, hf, rfl⟩
    exact K.has_isos f

/-- The trivial pretopology induces the trivial grothendieck topology. -/
theorem toGrothendieck_bot : toGrothendieck C ⊥ = ⊥ :=
  (gi C).gc.l_bot

instance : InfSet (Pretopology C) where
  sInf T := {
    coverings := sInf (coverings '' T)
    has_isos := fun X Y f _ ↦ by
      simp only [sInf_apply, Set.iInf_eq_iInter, Set.iInter_coe_set, Set.mem_image,
        Set.iInter_exists,
        Set.biInter_and', Set.iInter_iInter_eq_right, Set.mem_iInter]
      intro t _
      exact t.has_isos f
    pullbacks := fun X Y f S hS ↦ by
      simp only [sInf_apply, Set.iInf_eq_iInter, Set.iInter_coe_set, Set.mem_image,
        Set.iInter_exists, Set.biInter_and', Set.iInter_iInter_eq_right, Set.mem_iInter] at hS ⊢
      intro t ht
      exact t.pullbacks f S (hS t ht)
    transitive := fun X S Ti hS hTi ↦ by
      simp only [sInf_apply, Set.iInf_eq_iInter, Set.iInter_coe_set, Set.mem_image,
        Set.iInter_exists, Set.biInter_and', Set.iInter_iInter_eq_right, Set.mem_iInter] at hS hTi ⊢
      intro t ht
      exact t.transitive S Ti (hS t ht) (fun Y f H ↦ hTi f H t ht)
  }

lemma mem_sInf (T : Set (Pretopology C)) {X : C} (S : Presieve X) :
    S ∈ sInf T X ↔ ∀ t ∈ T, S ∈ t X := by
  show S ∈ sInf (Pretopology.coverings '' T) X ↔ _
  simp

lemma sInf_ofGrothendieck (T : Set (GrothendieckTopology C)) :
    ofGrothendieck C (sInf T) = sInf (ofGrothendieck C '' T) := by
  ext X S
  simp [mem_sInf, mem_ofGrothendieck, GrothendieckTopology.mem_sInf]

lemma isGLB_sInf (T : Set (Pretopology C)) : IsGLB T (sInf T) :=
  IsGLB.of_image (f := coverings) Iff.rfl (_root_.isGLB_sInf _)

/-- The complete lattice structure on pretopologies. This is induced by the `InfSet` instance, but
with good definitional equalities for `⊥`, `⊤` and `⊓`. -/
instance : CompleteLattice (Pretopology C) where
  __ := orderBot C
  __ := orderTop C
  inf t₁ t₂ := {
    coverings := fun X ↦ t₁.coverings X ∩ t₂.coverings X
    has_isos := fun _ _ f _ ↦
      ⟨t₁.has_isos f, t₂.has_isos f⟩
    pullbacks := fun _ _ f S hS ↦
      ⟨t₁.pullbacks f S hS.left, t₂.pullbacks f S hS.right⟩
    transitive := fun _ S Ti hS hTi ↦
      ⟨t₁.transitive S Ti hS.left (fun _ f H ↦ (hTi f H).left),
        t₂.transitive S Ti hS.right (fun _ f H ↦ (hTi f H).right)⟩
  }
  inf_le_left _ _ _ _ hS := hS.left
  inf_le_right _ _ _ _ hS := hS.right
  le_inf _ _ _ hts htr X _ hS := ⟨hts X hS, htr X hS⟩
  __ := completeLatticeOfInf _ (isGLB_sInf C)

lemma mem_inf (t₁ t₂ : Pretopology C) {X : C} (S : Presieve X) :
    S ∈ (t₁ ⊓ t₂) X ↔ S ∈ t₁ X ∧ S ∈ t₂ X :=
  Iff.rfl

end Pretopology

end CategoryTheory
