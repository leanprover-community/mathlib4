/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Sites.Grothendieck
public import Mathlib.CategoryTheory.Sites.Precoverage

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
set_option backward.defeqAttrib.useBackward true

@[expose] public section


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

See: https://ncatlab.org/nlab/show/Grothendieck+pretopology or [MM92] Chapter III,
Section 2, Definition 2. -/
@[ext, stacks 00VH "Note that Stacks calls a category together with a pretopology a site,
and [MM92] calls this a basis for a topology."]
structure Pretopology extends Precoverage C where
  /-- For all `X : C`, the coverings of `X` (sets of families of morphisms with target `X`) -/
  has_isos : ∀ ⦃X Y⦄ (f : Y ⟶ X) [IsIso f], Presieve.singleton f ∈ coverings X
  pullbacks : ∀ ⦃X Y⦄ (f : Y ⟶ X) (S), S ∈ coverings X → pullbackArrows f S ∈ coverings Y
  transitive :
    ∀ ⦃X : C⦄ (S : Presieve X) (Ti : ∀ ⦃Y⦄ (f : Y ⟶ X), S f → Presieve Y),
      S ∈ coverings X → (∀ ⦃Y⦄ (f) (H : S f), Ti f H ∈ coverings Y) → S.bind Ti ∈ coverings X

namespace Pretopology

instance : CoeFun (Pretopology C) fun _ => ∀ X : C, Set (Presieve X) :=
  ⟨fun J ↦ J.coverings⟩

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

variable {C}

/-- A pretopology `K` can be completed to a Grothendieck topology `J` by declaring a sieve to be
`J`-covering if it contains a family in `K`.

See also [MM92] Chapter III, Section 2, Equation (2).
-/
@[stacks 00ZC]
def toGrothendieck (K : Pretopology C) : GrothendieckTopology C where
  sieves X := {S | ∃ R ∈ K X, R ≤ (S : Presieve _)}
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
    refine ⟨_, K.transitive _ _ hR' fun _ f hf => t₂ (RS _ _ hf), ?_⟩
    rintro Y _ ⟨Z, g, f, hg, hf, rfl⟩
    apply t₃ (RS _ _ hg) _ _ hf

theorem mem_toGrothendieck (K : Pretopology C) (X S) :
    S ∈ toGrothendieck K X ↔ ∃ R ∈ K X, R ≤ (S : Presieve X) :=
  Iff.rfl

end Pretopology

variable {C} in
/-- The largest pretopology generating the given Grothendieck topology.

See [MM92] Chapter III, Section 2, Equations (3,4).
-/
def GrothendieckTopology.toPretopology (J : GrothendieckTopology C) : Pretopology C where
  coverings X := {R | Sieve.generate R ∈ J X}
  has_isos X Y f i := J.covering_of_eq_top (by simp)
  pullbacks X Y f R hR := by simpa [Sieve.pullbackArrows_comm] using J.pullback_stable f hR
  transitive X S Ti hS hTi := by
    apply J.transitive hS
    intro Y f
    rintro ⟨Z, g, f, hf, rfl⟩
    rw [Sieve.pullback_comp]
    apply J.pullback_stable g
    apply J.superset_covering _ (hTi _ hf)
    rintro Y g ⟨W, h, g, hg, rfl⟩
    exact ⟨_, h, _, ⟨_, _, _, hf, hg, rfl⟩, by simp⟩

/-- We have a Galois insertion from pretopologies to Grothendieck topologies. -/
def Pretopology.gi : GaloisInsertion
    (toGrothendieck (C := C)) (GrothendieckTopology.toPretopology (C := C)) where
  gc K J := by
    constructor
    · intro h X R hR
      exact h _ ⟨_, hR, Sieve.le_generate R⟩
    · rintro h X S ⟨R, hR, RS⟩
      apply J.superset_covering _ (h _ hR)
      rwa [Sieve.giGenerate.gc]
  le_l_u J _ S hS := ⟨S, J.superset_covering (Sieve.le_generate S.arrows) hS, le_rfl⟩
  choice x _ := toGrothendieck x
  choice_eq _ _ := rfl

lemma GrothendieckTopology.mem_toPretopology (t : GrothendieckTopology C) {X : C} (S : Presieve X) :
    S ∈ t.toPretopology X ↔ Sieve.generate S ∈ t X :=
  Iff.rfl

namespace Pretopology

set_option backward.isDefEq.respectTransparency false in
/--
The trivial pretopology, in which the coverings are exactly singleton isomorphisms. This topology is
also known as the indiscrete, coarse, or chaotic topology. -/
@[stacks 07GE]
def trivial : Pretopology C where
  coverings X := {S | ∃ (Y : _) (f : Y ⟶ X) (_ : IsIso f), S = Presieve.singleton f}
  has_isos _ _ _ i := ⟨_, _, i, rfl⟩
  pullbacks X Y f S := by
    rintro ⟨Z, g, i, rfl⟩
    refine ⟨pullback g f, pullback.snd _ _, ?_, ?_⟩
    · refine ⟨⟨pullback.lift (f ≫ inv g) (𝟙 _) (by simp), ⟨?_, by simp⟩⟩⟩
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
    intro W
    ext K
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

/-- The trivial pretopology induces the trivial Grothendieck topology. -/
theorem toGrothendieck_bot : toGrothendieck (C := C) ⊥ = ⊥ :=
  (gi C).gc.l_bot

@[gcongr]
lemma toGrothendieck_mono {J K : Pretopology C} (h : J ≤ K) : J.toGrothendieck ≤ K.toGrothendieck :=
  fun _ _ ⟨R, hR, hle⟩ ↦ ⟨R, h _ hR, hle⟩

instance : InfSet (Pretopology C) where
  sInf T := {
    coverings := sInf ((fun J ↦ J.coverings) '' T)
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
  change S ∈ sInf ((fun J : Pretopology C ↦ J.coverings) '' T) X ↔ _
  simp

lemma sInf_ofGrothendieck (T : Set (GrothendieckTopology C)) :
    (sInf T).toPretopology = sInf (GrothendieckTopology.toPretopology '' T) := by
  ext X S
  simp [mem_sInf, GrothendieckTopology.mem_toPretopology, GrothendieckTopology.mem_sInf]

lemma isGLB_sInf (T : Set (Pretopology C)) : IsGLB T (sInf T) :=
  IsGLB.of_image (f := fun J ↦ J.coverings) Iff.rfl (_root_.isGLB_sInf _)

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

/-- If `J` is a precoverage that has isomorphisms and is stable under composition and
base change, it defines a pretopology. -/
@[simps toPrecoverage]
def Precoverage.toPretopology [Limits.HasPullbacks C] (J : Precoverage C) [J.HasIsos]
    [J.IsStableUnderBaseChange] [J.IsStableUnderComposition] : Pretopology C where
  __ := J
  has_isos X Y f hf := mem_coverings_of_isIso f
  pullbacks X Y f R hR := J.pullbackArrows_mem f hR
  transitive X R Ti hR hTi := by
    obtain ⟨ι, Z, g, rfl⟩ := R.exists_eq_ofArrows
    choose κ W p hp using fun ⦃Y⦄ (f : Y ⟶ X) hf ↦ (Ti f hf).exists_eq_ofArrows
    have : (Presieve.ofArrows Z g).bind Ti =
        .ofArrows (fun ij : Σ i, κ (g i) ⟨i⟩ ↦ W _ _ ij.2) (fun ij ↦ p _ _ ij.2 ≫ g ij.1) := by
      apply le_antisymm
      · rintro T u ⟨S, v, w, ⟨i⟩, hv, rfl⟩
        rw [hp] at hv
        obtain ⟨j⟩ := hv
        exact .mk <| Sigma.mk (β := fun i : ι ↦ κ (g i) ⟨i⟩) i j
      · rintro T u ⟨ij⟩
        use Z ij.1, p (g ij.1) ⟨ij.1⟩ ij.2, g ij.1, ⟨ij.1⟩
        rw [hp]
        exact ⟨⟨_⟩, rfl⟩
    rw [this]
    refine J.comp_mem_coverings (Y := fun (i : ι) (j : κ (g i) ⟨i⟩) ↦ W _ _ j)
      (g := fun i j ↦ p _ _ j) _ hR fun i ↦ ?_
    rw [← hp]
    exact hTi _ _

end CategoryTheory
