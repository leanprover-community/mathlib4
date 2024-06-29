/-
Copyright (c) 2020 Bhavik Mehta, E. W. Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, E. W. Ayers
-/
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Order.Copy
import Mathlib.Data.Set.Subsingleton

#align_import category_theory.sites.grothendieck from "leanprover-community/mathlib"@"14b69e9f3c16630440a2cbd46f1ddad0d561dee7"

/-!
# Grothendieck topologies

Definition and lemmas about Grothendieck topologies.
A Grothendieck topology for a category `C` is a set of sieves on each object `X` satisfying
certain closure conditions.

Alternate versions of the axioms (in arrow form) are also described.
Two explicit examples of Grothendieck topologies are given:
* The dense topology
* The atomic topology
as well as the complete lattice structure on Grothendieck topologies (which gives two additional
explicit topologies: the discrete and trivial topologies.)

A pretopology, or a basis for a topology is defined in
`Mathlib/CategoryTheory/Sites/Pretopology.lean`. The topology associated
to a topological space is defined in `Mathlib/CategoryTheory/Sites/Spaces.lean`.

## Tags

Grothendieck topology, coverage, pretopology, site

## References

* [nLab, *Grothendieck topology*](https://ncatlab.org/nlab/show/Grothendieck+topology)
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]

## Implementation notes

We use the definition of [nlab] and [MM92][] (Chapter III, Section 2), where Grothendieck topologies
are saturated collections of morphisms, rather than the notions of the Stacks project (00VG) and
the Elephant, in which topologies are allowed to be unsaturated, and are then completed.
TODO (BM): Add the definition from Stacks, as a pretopology, and complete to a topology.

This is so that we can produce a bijective correspondence between Grothendieck topologies on a
small category and Lawvere-Tierney topologies on its presheaf topos, as well as the equivalence
between Grothendieck topoi and left exact reflective subcategories of presheaf toposes.
-/


universe v₁ u₁ v u

namespace CategoryTheory

open CategoryTheory Category

variable (C : Type u) [Category.{v} C]

/-- The definition of a Grothendieck topology: a set of sieves `J X` on each object `X` satisfying
three axioms:
1. For every object `X`, the maximal sieve is in `J X`.
2. If `S ∈ J X` then its pullback along any `h : Y ⟶ X` is in `J Y`.
3. If `S ∈ J X` and `R` is a sieve on `X`, then provided that the pullback of `R` along any arrow
   `f : Y ⟶ X` in `S` is in `J Y`, we have that `R` itself is in `J X`.

A sieve `S` on `X` is referred to as `J`-covering, (or just covering), if `S ∈ J X`.

See <https://stacks.math.columbia.edu/tag/00Z4>, or [nlab], or [MM92][] Chapter III, Section 2,
Definition 1.
-/
structure GrothendieckTopology where
  /-- A Grothendieck topology on `C` consists of a set of sieves for each object `X`,
    which satisfy some axioms. -/
  sieves : ∀ X : C, Set (Sieve X)
  /-- The sieves associated to each object must contain the top sieve.
    Use `GrothendieckTopology.top_mem`. -/
  top_mem' : ∀ X, ⊤ ∈ sieves X
  /-- Stability under pullback. Use `GrothendieckTopology.pullback_stable`. -/
  pullback_stable' : ∀ ⦃X Y : C⦄ ⦃S : Sieve X⦄ (f : Y ⟶ X), S ∈ sieves X → S.pullback f ∈ sieves Y
  /-- Transitivity of sieves in a Grothendieck topology.
    Use `GrothendieckTopology.transitive`. -/
  transitive' :
    ∀ ⦃X⦄ ⦃S : Sieve X⦄ (_ : S ∈ sieves X) (R : Sieve X),
      (∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → R.pullback f ∈ sieves Y) → R ∈ sieves X
#align category_theory.grothendieck_topology CategoryTheory.GrothendieckTopology

namespace GrothendieckTopology

instance : CoeFun (GrothendieckTopology C) fun _ => ∀ X : C, Set (Sieve X) :=
  ⟨sieves⟩

variable {C}
variable {X Y : C} {S R : Sieve X}
variable (J : GrothendieckTopology C)

/-- An extensionality lemma in terms of the coercion to a pi-type.
We prove this explicitly rather than deriving it so that it is in terms of the coercion rather than
the projection `.sieves`.
-/
@[ext]
theorem ext {J₁ J₂ : GrothendieckTopology C} (h : (J₁ : ∀ X : C, Set (Sieve X)) = J₂) :
    J₁ = J₂ := by
  cases J₁
  cases J₂
  congr
#align category_theory.grothendieck_topology.ext CategoryTheory.GrothendieckTopology.ext

/-
Porting note: This is now a syntactic tautology.
@[simp]
theorem mem_sieves_iff_coe : S ∈ J.sieves X ↔ S ∈ J X :=
  Iff.rfl
#align category_theory.grothendieck_topology.mem_sieves_iff_coe CategoryTheory.GrothendieckTopology.mem_sieves_iff_coe
-/

/-- Also known as the maximality axiom. -/
@[simp]
theorem top_mem (X : C) : ⊤ ∈ J X :=
  J.top_mem' X
#align category_theory.grothendieck_topology.top_mem CategoryTheory.GrothendieckTopology.top_mem

/-- Also known as the stability axiom. -/
@[simp]
theorem pullback_stable (f : Y ⟶ X) (hS : S ∈ J X) : S.pullback f ∈ J Y :=
  J.pullback_stable' f hS
#align category_theory.grothendieck_topology.pullback_stable CategoryTheory.GrothendieckTopology.pullback_stable

theorem transitive (hS : S ∈ J X) (R : Sieve X) (h : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → R.pullback f ∈ J Y) :
    R ∈ J X :=
  J.transitive' hS R h
#align category_theory.grothendieck_topology.transitive CategoryTheory.GrothendieckTopology.transitive

theorem covering_of_eq_top : S = ⊤ → S ∈ J X := fun h => h.symm ▸ J.top_mem X
#align category_theory.grothendieck_topology.covering_of_eq_top CategoryTheory.GrothendieckTopology.covering_of_eq_top

/-- If `S` is a subset of `R`, and `S` is covering, then `R` is covering as well.

See <https://stacks.math.columbia.edu/tag/00Z5> (2), or discussion after [MM92] Chapter III,
Section 2, Definition 1.
-/
theorem superset_covering (Hss : S ≤ R) (sjx : S ∈ J X) : R ∈ J X := by
  apply J.transitive sjx R fun Y f hf => _
  intros Y f hf
  apply covering_of_eq_top
  rw [← top_le_iff, ← S.pullback_eq_top_of_mem hf]
  apply Sieve.pullback_monotone _ Hss
#align category_theory.grothendieck_topology.superset_covering CategoryTheory.GrothendieckTopology.superset_covering

/-- The intersection of two covering sieves is covering.

See <https://stacks.math.columbia.edu/tag/00Z5> (1), or [MM92] Chapter III,
Section 2, Definition 1 (iv).
-/
theorem intersection_covering (rj : R ∈ J X) (sj : S ∈ J X) : R ⊓ S ∈ J X := by
  apply J.transitive rj _ fun Y f Hf => _
  intros Y f hf
  rw [Sieve.pullback_inter, R.pullback_eq_top_of_mem hf]
  simp [sj]
#align category_theory.grothendieck_topology.intersection_covering CategoryTheory.GrothendieckTopology.intersection_covering

@[simp]
theorem intersection_covering_iff : R ⊓ S ∈ J X ↔ R ∈ J X ∧ S ∈ J X :=
  ⟨fun h => ⟨J.superset_covering inf_le_left h, J.superset_covering inf_le_right h⟩, fun t =>
    intersection_covering _ t.1 t.2⟩
#align category_theory.grothendieck_topology.intersection_covering_iff CategoryTheory.GrothendieckTopology.intersection_covering_iff

theorem bind_covering {S : Sieve X} {R : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → Sieve Y} (hS : S ∈ J X)
    (hR : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (H : S f), R H ∈ J Y) : Sieve.bind S R ∈ J X :=
  J.transitive hS _ fun _ f hf => superset_covering J (Sieve.le_pullback_bind S R f hf) (hR hf)
#align category_theory.grothendieck_topology.bind_covering CategoryTheory.GrothendieckTopology.bind_covering

/-- The sieve `S` on `X` `J`-covers an arrow `f` to `X` if `S.pullback f ∈ J Y`.
This definition is an alternate way of presenting a Grothendieck topology.
-/
def Covers (S : Sieve X) (f : Y ⟶ X) : Prop :=
  S.pullback f ∈ J Y
#align category_theory.grothendieck_topology.covers CategoryTheory.GrothendieckTopology.Covers

theorem covers_iff (S : Sieve X) (f : Y ⟶ X) : J.Covers S f ↔ S.pullback f ∈ J Y :=
  Iff.rfl
#align category_theory.grothendieck_topology.covers_iff CategoryTheory.GrothendieckTopology.covers_iff

theorem covering_iff_covers_id (S : Sieve X) : S ∈ J X ↔ J.Covers S (𝟙 X) := by simp [covers_iff]
#align category_theory.grothendieck_topology.covering_iff_covers_id CategoryTheory.GrothendieckTopology.covering_iff_covers_id

/-- The maximality axiom in 'arrow' form: Any arrow `f` in `S` is covered by `S`. -/
theorem arrow_max (f : Y ⟶ X) (S : Sieve X) (hf : S f) : J.Covers S f := by
  rw [Covers, (Sieve.pullback_eq_top_iff_mem f).1 hf]
  apply J.top_mem
#align category_theory.grothendieck_topology.arrow_max CategoryTheory.GrothendieckTopology.arrow_max

/-- The stability axiom in 'arrow' form: If `S` covers `f` then `S` covers `g ≫ f` for any `g`. -/
theorem arrow_stable (f : Y ⟶ X) (S : Sieve X) (h : J.Covers S f) {Z : C} (g : Z ⟶ Y) :
    J.Covers S (g ≫ f) := by
  rw [covers_iff] at h ⊢
  simp [h, Sieve.pullback_comp]
#align category_theory.grothendieck_topology.arrow_stable CategoryTheory.GrothendieckTopology.arrow_stable

/-- The transitivity axiom in 'arrow' form: If `S` covers `f` and every arrow in `S` is covered by
`R`, then `R` covers `f`.
-/
theorem arrow_trans (f : Y ⟶ X) (S R : Sieve X) (h : J.Covers S f) :
    (∀ {Z : C} (g : Z ⟶ X), S g → J.Covers R g) → J.Covers R f := by
  intro k
  apply J.transitive h
  intro Z g hg
  rw [← Sieve.pullback_comp]
  apply k (g ≫ f) hg
#align category_theory.grothendieck_topology.arrow_trans CategoryTheory.GrothendieckTopology.arrow_trans

theorem arrow_intersect (f : Y ⟶ X) (S R : Sieve X) (hS : J.Covers S f) (hR : J.Covers R f) :
    J.Covers (S ⊓ R) f := by simpa [covers_iff] using And.intro hS hR
#align category_theory.grothendieck_topology.arrow_intersect CategoryTheory.GrothendieckTopology.arrow_intersect

variable (C)

/-- The trivial Grothendieck topology, in which only the maximal sieve is covering. This topology is
also known as the indiscrete, coarse, or chaotic topology.

See [MM92] Chapter III, Section 2, example (a), or
https://en.wikipedia.org/wiki/Grothendieck_topology#The_discrete_and_indiscrete_topologies
-/
def trivial : GrothendieckTopology C where
  sieves X := {⊤}
  top_mem' X := rfl
  pullback_stable' X Y S f hf := by
    rw [Set.mem_singleton_iff] at hf ⊢
    simp [hf]
  transitive' X S hS R hR := by
    rw [Set.mem_singleton_iff, ← Sieve.id_mem_iff_eq_top] at hS
    simpa using hR hS
#align category_theory.grothendieck_topology.trivial CategoryTheory.GrothendieckTopology.trivial

/-- The discrete Grothendieck topology, in which every sieve is covering.

See https://en.wikipedia.org/wiki/Grothendieck_topology#The_discrete_and_indiscrete_topologies.
-/
def discrete : GrothendieckTopology C where
  sieves X := Set.univ
  top_mem' := by simp
  pullback_stable' X Y f := by simp
  transitive' := by simp
#align category_theory.grothendieck_topology.discrete CategoryTheory.GrothendieckTopology.discrete

variable {C}

theorem trivial_covering : S ∈ trivial C X ↔ S = ⊤ :=
  Set.mem_singleton_iff
#align category_theory.grothendieck_topology.trivial_covering CategoryTheory.GrothendieckTopology.trivial_covering

/-- See <https://stacks.math.columbia.edu/tag/00Z6> -/
instance instLEGrothendieckTopology : LE (GrothendieckTopology C) where
  le J₁ J₂ := (J₁ : ∀ X : C, Set (Sieve X)) ≤ (J₂ : ∀ X : C, Set (Sieve X))

theorem le_def {J₁ J₂ : GrothendieckTopology C} : J₁ ≤ J₂ ↔ (J₁ : ∀ X : C, Set (Sieve X)) ≤ J₂ :=
  Iff.rfl
#align category_theory.grothendieck_topology.le_def CategoryTheory.GrothendieckTopology.le_def

/-- See <https://stacks.math.columbia.edu/tag/00Z6> -/
instance : PartialOrder (GrothendieckTopology C) :=
  { instLEGrothendieckTopology with
    le_refl := fun J₁ => le_def.mpr le_rfl
    le_trans := fun J₁ J₂ J₃ h₁₂ h₂₃ => le_def.mpr (le_trans h₁₂ h₂₃)
    le_antisymm := fun J₁ J₂ h₁₂ h₂₁ => GrothendieckTopology.ext (le_antisymm h₁₂ h₂₁) }

/-- See <https://stacks.math.columbia.edu/tag/00Z7> -/
instance : InfSet (GrothendieckTopology C) where
  sInf T :=
    { sieves := sInf (sieves '' T)
      top_mem' := by
        rintro X S ⟨⟨_, J, hJ, rfl⟩, rfl⟩
        simp
      pullback_stable' := by
        rintro X Y S hS f _ ⟨⟨_, J, hJ, rfl⟩, rfl⟩
        apply J.pullback_stable _ (f _ ⟨⟨_, _, hJ, rfl⟩, rfl⟩)
      transitive' := by
        rintro X S hS R h _ ⟨⟨_, J, hJ, rfl⟩, rfl⟩
        apply
          J.transitive (hS _ ⟨⟨_, _, hJ, rfl⟩, rfl⟩) _ fun Y f hf => h hf _ ⟨⟨_, _, hJ, rfl⟩, rfl⟩ }

/-- See <https://stacks.math.columbia.edu/tag/00Z7> -/
theorem isGLB_sInf (s : Set (GrothendieckTopology C)) : IsGLB s (sInf s) := by
  refine @IsGLB.of_image _ _ _ _ sieves ?_ _ _ ?_
  · intros
    rfl
  · exact _root_.isGLB_sInf _
#align category_theory.grothendieck_topology.is_glb_Inf CategoryTheory.GrothendieckTopology.isGLB_sInf

/-- Construct a complete lattice from the `Inf`, but make the trivial and discrete topologies
definitionally equal to the bottom and top respectively.
-/
instance : CompleteLattice (GrothendieckTopology C) :=
  CompleteLattice.copy (completeLatticeOfInf _ isGLB_sInf) _ rfl (discrete C)
    (by
      apply le_antisymm
      · exact @CompleteLattice.le_top _ (completeLatticeOfInf _ isGLB_sInf) (discrete C)
      · intro X S _
        apply Set.mem_univ)
    (trivial C)
    (by
      apply le_antisymm
      · intro X S hS
        rw [trivial_covering] at hS
        apply covering_of_eq_top _ hS
      · exact @CompleteLattice.bot_le _ (completeLatticeOfInf _ isGLB_sInf) (trivial C))
    _ rfl _ rfl _ rfl sInf rfl

instance : Inhabited (GrothendieckTopology C) :=
  ⟨⊤⟩

@[simp]
theorem trivial_eq_bot : trivial C = ⊥ :=
  rfl
#align category_theory.grothendieck_topology.trivial_eq_bot CategoryTheory.GrothendieckTopology.trivial_eq_bot

@[simp]
theorem discrete_eq_top : discrete C = ⊤ :=
  rfl
#align category_theory.grothendieck_topology.discrete_eq_top CategoryTheory.GrothendieckTopology.discrete_eq_top

@[simp]
theorem bot_covering : S ∈ (⊥ : GrothendieckTopology C) X ↔ S = ⊤ :=
  trivial_covering
#align category_theory.grothendieck_topology.bot_covering CategoryTheory.GrothendieckTopology.bot_covering

@[simp]
theorem top_covering : S ∈ (⊤ : GrothendieckTopology C) X :=
  ⟨⟩
#align category_theory.grothendieck_topology.top_covering CategoryTheory.GrothendieckTopology.top_covering

theorem bot_covers (S : Sieve X) (f : Y ⟶ X) : (⊥ : GrothendieckTopology C).Covers S f ↔ S f := by
  rw [covers_iff, bot_covering, ← Sieve.pullback_eq_top_iff_mem]
#align category_theory.grothendieck_topology.bot_covers CategoryTheory.GrothendieckTopology.bot_covers

@[simp]
theorem top_covers (S : Sieve X) (f : Y ⟶ X) : (⊤ : GrothendieckTopology C).Covers S f := by
  simp [covers_iff]
#align category_theory.grothendieck_topology.top_covers CategoryTheory.GrothendieckTopology.top_covers

/-- The dense Grothendieck topology.

See https://ncatlab.org/nlab/show/dense+topology, or [MM92] Chapter III, Section 2, example (e).
-/
def dense : GrothendieckTopology C where
  sieves X S := ∀ {Y : C} (f : Y ⟶ X), ∃ (Z : _) (g : Z ⟶ Y), S (g ≫ f)
  top_mem' X Y f := ⟨Y, 𝟙 Y, ⟨⟩⟩
  pullback_stable' := by
    intro X Y S h H Z f
    rcases H (f ≫ h) with ⟨W, g, H'⟩
    exact ⟨W, g, by simpa⟩
  transitive' := by
    intro X S H₁ R H₂ Y f
    rcases H₁ f with ⟨Z, g, H₃⟩
    rcases H₂ H₃ (𝟙 Z) with ⟨W, h, H₄⟩
    exact ⟨W, h ≫ g, by simpa using H₄⟩
#align category_theory.grothendieck_topology.dense CategoryTheory.GrothendieckTopology.dense

theorem dense_covering : S ∈ dense X ↔ ∀ {Y} (f : Y ⟶ X), ∃ (Z : _) (g : Z ⟶ Y), S (g ≫ f) :=
  Iff.rfl
#align category_theory.grothendieck_topology.dense_covering CategoryTheory.GrothendieckTopology.dense_covering

/--
A category satisfies the right Ore condition if any span can be completed to a commutative square.
NB. Any category with pullbacks obviously satisfies the right Ore condition, see
`right_ore_of_pullbacks`.
-/
def RightOreCondition (C : Type u) [Category.{v} C] : Prop :=
  ∀ {X Y Z : C} (yx : Y ⟶ X) (zx : Z ⟶ X), ∃ (W : _) (wy : W ⟶ Y) (wz : W ⟶ Z), wy ≫ yx = wz ≫ zx
#align category_theory.grothendieck_topology.right_ore_condition CategoryTheory.GrothendieckTopology.RightOreCondition

theorem right_ore_of_pullbacks [Limits.HasPullbacks C] : RightOreCondition C := fun _ _ =>
  ⟨_, _, _, Limits.pullback.condition⟩
#align category_theory.grothendieck_topology.right_ore_of_pullbacks CategoryTheory.GrothendieckTopology.right_ore_of_pullbacks

/-- The atomic Grothendieck topology: a sieve is covering iff it is nonempty.
For the pullback stability condition, we need the right Ore condition to hold.

See https://ncatlab.org/nlab/show/atomic+site, or [MM92] Chapter III, Section 2, example (f).
-/
def atomic (hro : RightOreCondition C) : GrothendieckTopology C where
  sieves X S := ∃ (Y : _) (f : Y ⟶ X), S f
  top_mem' X := ⟨_, 𝟙 _, ⟨⟩⟩
  pullback_stable' := by
    rintro X Y S h ⟨Z, f, hf⟩
    rcases hro h f with ⟨W, g, k, comm⟩
    refine ⟨_, g, ?_⟩
    simp [comm, hf]
  transitive' := by
    rintro X S ⟨Y, f, hf⟩ R h
    rcases h hf with ⟨Z, g, hg⟩
    exact ⟨_, _, hg⟩
#align category_theory.grothendieck_topology.atomic CategoryTheory.GrothendieckTopology.atomic


/-- `J.Cover X` denotes the poset of covers of `X` with respect to the
Grothendieck topology `J`. -/
-- Porting note: Lean 3 inferred `Type max u v`, Lean 4 by default gives `Type (max 0 u v)`
def Cover (X : C) : Type max u v :=
  { S : Sieve X // S ∈ J X } -- deriving Preorder
#align category_theory.grothendieck_topology.cover CategoryTheory.GrothendieckTopology.Cover

-- Porting note: `deriving` didn't work above, so we add the preorder instance manually.
instance (X : C) : Preorder (J.Cover X) :=
  show Preorder {S : Sieve X // S ∈ J X} from inferInstance

namespace Cover

variable {J}

/-
Porting note: Lean complains that this is a dangerous instance.
I'm commenting this out since the `CoeFun` instance below is what we
use 99% of the time anyway.

instance : Coe (J.Cover X) (Sieve X) :=
  ⟨fun S => S.1⟩
-/

/-
Porting note (#11445): Added this def as a replacement for the "dangerous" `Coe` above.
-/
/-- The sieve associated to a term of `J.Cover X`. -/
def sieve (S : J.Cover X) : Sieve X := S.1

/-
Porting note: This somehow yields different behavior than the better instance below. Why?!

With this instance, we have to write `S _ f` but with the uncommented one, we can write `S f`
as expected.

instance : CoeFun (J.Cover X) fun _ => ∀ ⦃Y⦄ (_ : Y ⟶ X), Prop :=
  ⟨fun S _ f => (S : Sieve X) f⟩
-/

instance : CoeFun (J.Cover X) fun _ => ∀ ⦃Y⦄ (_ : Y ⟶ X), Prop :=
  ⟨fun S => S.sieve⟩

/-
Porting note: This is now a syntactic tautology.

@[simp]
theorem coe_fun_coe (S : J.Cover X) (f : Y ⟶ X) : S.sieve f = S f :=
  rfl
#align category_theory.grothendieck_topology.cover.coe_fun_coe CategoryTheory.GrothendieckTopology.Cover.coe_fun_coe
-/

theorem condition (S : J.Cover X) : S.sieve ∈ J X :=
  S.2
#align category_theory.grothendieck_topology.cover.condition CategoryTheory.GrothendieckTopology.Cover.condition

@[ext]
theorem ext (S T : J.Cover X) (h : ∀ ⦃Y⦄ (f : Y ⟶ X), S f ↔ T f) : S = T :=
  Subtype.ext <| Sieve.ext h
#align category_theory.grothendieck_topology.cover.ext CategoryTheory.GrothendieckTopology.Cover.ext

instance : OrderTop (J.Cover X) :=
  { (inferInstance : Preorder (J.Cover X)) with
    top := ⟨⊤, J.top_mem _⟩
    le_top := fun S Y f _ => by tauto }

instance : SemilatticeInf (J.Cover X) :=
  { (inferInstance : Preorder _) with
    inf := fun S T => ⟨S.sieve ⊓ T.sieve,
      J.intersection_covering S.condition T.condition⟩
    le_antisymm := fun S T h1 h2 => ext _ _ fun {Y} f => ⟨by apply h1, by apply h2⟩
    inf_le_left := fun S T Y f hf => hf.1
    inf_le_right := fun S T Y f hf => hf.2
    le_inf := fun S T W h1 h2 Y f h => ⟨h1 _ h, h2 _ h⟩ }

instance : Inhabited (J.Cover X) :=
  ⟨⊤⟩

/-- An auxiliary structure, used to define `S.index`. -/
-- Porting note(#5171): this linter isn't ported yet.
-- @[nolint has_nonempty_instance]
@[ext]
structure Arrow (S : J.Cover X) where
  /-- The source of the arrow. -/
  Y : C
  /-- The arrow itself. -/
  f : Y ⟶ X
  /-- The given arrow is contained in the given sieve. -/
  hf : S f
#align category_theory.grothendieck_topology.cover.arrow CategoryTheory.GrothendieckTopology.Cover.Arrow

/-- Relation between two elements in `S.arrow`, the data of which
involves a commutative square. -/
@[ext]
structure Arrow.Relation {S : J.Cover X} (I₁ I₂ : S.Arrow) where
  /-- The source of the arrows defining the relation. -/
  Z : C
  /-- The first arrow defining the relation. -/
  g₁ : Z ⟶ I₁.Y
  /-- The second arrow defining the relation. -/
  g₂ : Z ⟶ I₂.Y
  /-- The relation itself. -/
  w : g₁ ≫ I₁.f = g₂ ≫ I₂.f := by aesop_cat

attribute [reassoc] Arrow.Relation.w

/-- Given `I : S.Arrow` and a morphism `g : Z ⟶ I.Y`, this is the arrow in `S.Arrow`
corresponding to `g ≫ I.f`. -/
@[simps]
def Arrow.precomp {S : J.Cover X} (I : S.Arrow) {Z : C} (g : Z ⟶ I.Y) : S.Arrow :=
  ⟨Z, g ≫ I.f, S.1.downward_closed I.hf g⟩

/-- Given `I : S.Arrow` and a morphism `g : Z ⟶ I.Y`, this is the obvious relation
from `I.precomp g` to `I`. -/
@[simps]
def Arrow.precompRelation {S : J.Cover X} (I : S.Arrow) {Z : C} (g : Z ⟶ I.Y) :
    (I.precomp g).Relation I where
  g₁ := 𝟙 _
  g₂ := g

/-- Map an `Arrow` along a refinement `S ⟶ T`. -/
@[simps]
def Arrow.map {S T : J.Cover X} (I : S.Arrow) (f : S ⟶ T) : T.Arrow :=
  ⟨I.Y, I.f, f.le _ I.hf⟩
#align category_theory.grothendieck_topology.cover.arrow.map CategoryTheory.GrothendieckTopology.Cover.Arrow.map

/-- Map an `Arrow.Relation` along a refinement `S ⟶ T`. -/
@[simps]
def Arrow.Relation.map {S T : J.Cover X} {I₁ I₂ : S.Arrow}
    (r : I₁.Relation I₂) (f : S ⟶ T) : (I₁.map f).Relation (I₂.map f) where
  w := r.w

/-- Pull back a cover along a morphism. -/
def pullback (S : J.Cover X) (f : Y ⟶ X) : J.Cover Y :=
  ⟨Sieve.pullback f S.sieve, J.pullback_stable _ S.condition⟩
#align category_theory.grothendieck_topology.cover.pullback CategoryTheory.GrothendieckTopology.Cover.pullback

/-- An arrow of `S.pullback f` gives rise to an arrow of `S`. -/
@[simps]
def Arrow.base {f : Y ⟶ X} {S : J.Cover X} (I : (S.pullback f).Arrow) : S.Arrow :=
  ⟨I.Y, I.f ≫ f, I.hf⟩
#align category_theory.grothendieck_topology.cover.arrow.base CategoryTheory.GrothendieckTopology.Cover.Arrow.base

/-- A relation of `S.pullback f` gives rise to a relation of `S`. -/
def Arrow.Relation.base
    {f : Y ⟶ X} {S : J.Cover X} {I₁ I₂ : (S.pullback f).Arrow}
    (r : I₁.Relation I₂) : I₁.base.Relation I₂.base where
  g₁ := r.g₁
  g₂ := r.g₂
  w := by simp [r.w_assoc]

@[simp]
theorem coe_pullback {Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (S : J.Cover X) :
    (S.pullback f) g ↔ S (g ≫ f) :=
  Iff.rfl
#align category_theory.grothendieck_topology.cover.coe_pullback CategoryTheory.GrothendieckTopology.Cover.coe_pullback

/-- The isomorphism between `S` and the pullback of `S` w.r.t. the identity. -/
def pullbackId (S : J.Cover X) : S.pullback (𝟙 X) ≅ S :=
  eqToIso <| Cover.ext _ _ fun Y f => by simp
#align category_theory.grothendieck_topology.cover.pullback_id CategoryTheory.GrothendieckTopology.Cover.pullbackId

/-- Pulling back with respect to a composition is the composition of the pullbacks. -/
def pullbackComp {X Y Z : C} (S : J.Cover X) (f : Z ⟶ Y) (g : Y ⟶ X) :
    S.pullback (f ≫ g) ≅ (S.pullback g).pullback f :=
  eqToIso <| Cover.ext _ _ fun Y f => by simp
#align category_theory.grothendieck_topology.cover.pullback_comp CategoryTheory.GrothendieckTopology.Cover.pullbackComp

/-- Combine a family of covers over a cover. -/
def bind {X : C} (S : J.Cover X) (T : ∀ I : S.Arrow, J.Cover I.Y) : J.Cover X :=
  ⟨Sieve.bind S.sieve fun Y f hf => (T ⟨Y, f, hf⟩).sieve,
    J.bind_covering S.condition fun _ _ _ => (T _).condition⟩
#align category_theory.grothendieck_topology.cover.bind CategoryTheory.GrothendieckTopology.Cover.bind

/-- The canonical morphism from `S.bind T` to `T`. -/
def bindToBase {X : C} (S : J.Cover X) (T : ∀ I : S.Arrow, J.Cover I.Y) : S.bind T ⟶ S :=
  homOfLE <| by
    rintro Y f ⟨Z, e1, e2, h1, _, h3⟩
    rw [← h3]
    apply Sieve.downward_closed
    exact h1
#align category_theory.grothendieck_topology.cover.bind_to_base CategoryTheory.GrothendieckTopology.Cover.bindToBase

/-- An arrow in bind has the form `A ⟶ B ⟶ X` where `A ⟶ B` is an arrow in `T I` for some `I`.
 and `B ⟶ X` is an arrow of `S`. This is the object `B`. -/
noncomputable def Arrow.middle {X : C} {S : J.Cover X} {T : ∀ I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : C :=
  I.hf.choose
#align category_theory.grothendieck_topology.cover.arrow.middle CategoryTheory.GrothendieckTopology.Cover.Arrow.middle

/-- An arrow in bind has the form `A ⟶ B ⟶ X` where `A ⟶ B` is an arrow in `T I` for some `I`.
 and `B ⟶ X` is an arrow of `S`. This is the hom `A ⟶ B`. -/
noncomputable def Arrow.toMiddleHom {X : C} {S : J.Cover X} {T : ∀ I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : I.Y ⟶ I.middle :=
  I.hf.choose_spec.choose
#align category_theory.grothendieck_topology.cover.arrow.to_middle_hom CategoryTheory.GrothendieckTopology.Cover.Arrow.toMiddleHom

/-- An arrow in bind has the form `A ⟶ B ⟶ X` where `A ⟶ B` is an arrow in `T I` for some `I`.
 and `B ⟶ X` is an arrow of `S`. This is the hom `B ⟶ X`. -/
noncomputable def Arrow.fromMiddleHom {X : C} {S : J.Cover X} {T : ∀ I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : I.middle ⟶ X :=
  I.hf.choose_spec.choose_spec.choose
#align category_theory.grothendieck_topology.cover.arrow.from_middle_hom CategoryTheory.GrothendieckTopology.Cover.Arrow.fromMiddleHom

theorem Arrow.from_middle_condition {X : C} {S : J.Cover X} {T : ∀ I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : S I.fromMiddleHom :=
  I.hf.choose_spec.choose_spec.choose_spec.choose
#align category_theory.grothendieck_topology.cover.arrow.from_middle_condition CategoryTheory.GrothendieckTopology.Cover.Arrow.from_middle_condition

/-- An arrow in bind has the form `A ⟶ B ⟶ X` where `A ⟶ B` is an arrow in `T I` for some `I`.
 and `B ⟶ X` is an arrow of `S`. This is the hom `B ⟶ X`, as an arrow. -/
noncomputable def Arrow.fromMiddle {X : C} {S : J.Cover X} {T : ∀ I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : S.Arrow :=
  ⟨_, I.fromMiddleHom, I.from_middle_condition⟩
#align category_theory.grothendieck_topology.cover.arrow.from_middle CategoryTheory.GrothendieckTopology.Cover.Arrow.fromMiddle

theorem Arrow.to_middle_condition {X : C} {S : J.Cover X} {T : ∀ I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : (T I.fromMiddle) I.toMiddleHom :=
  I.hf.choose_spec.choose_spec.choose_spec.choose_spec.1
#align category_theory.grothendieck_topology.cover.arrow.to_middle_condition CategoryTheory.GrothendieckTopology.Cover.Arrow.to_middle_condition

/-- An arrow in bind has the form `A ⟶ B ⟶ X` where `A ⟶ B` is an arrow in `T I` for some `I`.
 and `B ⟶ X` is an arrow of `S`. This is the hom `A ⟶ B`, as an arrow. -/
noncomputable def Arrow.toMiddle {X : C} {S : J.Cover X} {T : ∀ I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : (T I.fromMiddle).Arrow :=
  ⟨_, I.toMiddleHom, I.to_middle_condition⟩
#align category_theory.grothendieck_topology.cover.arrow.to_middle CategoryTheory.GrothendieckTopology.Cover.Arrow.toMiddle

theorem Arrow.middle_spec {X : C} {S : J.Cover X} {T : ∀ I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : I.toMiddleHom ≫ I.fromMiddleHom = I.f :=
  I.hf.choose_spec.choose_spec.choose_spec.choose_spec.2
#align category_theory.grothendieck_topology.cover.arrow.middle_spec CategoryTheory.GrothendieckTopology.Cover.Arrow.middle_spec

/-- An auxiliary structure, used to define `S.index`. -/
-- Porting note(#5171): this linter isn't ported yet.
-- @[nolint has_nonempty_instance, ext]
@[ext]
structure Relation (S : J.Cover X) where
  /-- The first arrow. -/
  fst : S.Arrow
  /-- The second arrow. -/
  snd : S.Arrow
  /-- The relation between the two arrows. -/
  r : fst.Relation snd

/-- Constructor for `Cover.Relation` which takes as an input
`r : I₁.Relation I₂` with `I₁ I₂ : S.Arrow`. -/
@[simps]
def Relation.mk' {S : J.Cover X} {fst snd : S.Arrow} (r : fst.Relation snd) :
    S.Relation where
  r := r

-- This is used extensively in `Plus.lean`, etc.
-- We place this definition here as it will be used in `Sheaf.lean` as well.
/-- To every `S : J.Cover X` and presheaf `P`, associate a `MulticospanIndex`. -/
@[simps]
def index {D : Type u₁} [Category.{v₁} D] (S : J.Cover X) (P : Cᵒᵖ ⥤ D) :
    Limits.MulticospanIndex D where
  L := S.Arrow
  R := S.Relation
  fstTo I := I.fst
  sndTo I := I.snd
  left I := P.obj (Opposite.op I.Y)
  right I := P.obj (Opposite.op I.r.Z)
  fst I := P.map I.r.g₁.op
  snd I := P.map I.r.g₂.op
#align category_theory.grothendieck_topology.cover.index CategoryTheory.GrothendieckTopology.Cover.index

/-- The natural multifork associated to `S : J.Cover X` for a presheaf `P`.
Saying that this multifork is a limit is essentially equivalent to the sheaf condition at the
given object for the given covering sieve. See `Sheaf.lean` for an equivalent sheaf condition
using this.
-/
abbrev multifork {D : Type u₁} [Category.{v₁} D] (S : J.Cover X) (P : Cᵒᵖ ⥤ D) :
    Limits.Multifork (S.index P) :=
  Limits.Multifork.ofι _ (P.obj (Opposite.op X)) (fun I => P.map I.f.op)
    (by
      intro I
      dsimp
      simp only [← P.map_comp, ← op_comp, I.r.w])
#align category_theory.grothendieck_topology.cover.multifork CategoryTheory.GrothendieckTopology.Cover.multifork

/-- The canonical map from `P.obj (op X)` to the multiequalizer associated to a covering sieve,
assuming such a multiequalizer exists. This will be used in `Sheaf.lean` to provide an equivalent
sheaf condition in terms of multiequalizers. -/
noncomputable abbrev toMultiequalizer {D : Type u₁} [Category.{v₁} D] (S : J.Cover X)
    (P : Cᵒᵖ ⥤ D) [Limits.HasMultiequalizer (S.index P)] :
    P.obj (Opposite.op X) ⟶ Limits.multiequalizer (S.index P) :=
  Limits.Multiequalizer.lift _ _ (fun I => P.map I.f.op)
    (by
      intro I
      dsimp only [index, Relation.fst, Relation.snd]
      simp only [← P.map_comp, ← op_comp, I.r.w])
#align category_theory.grothendieck_topology.cover.to_multiequalizer CategoryTheory.GrothendieckTopology.Cover.toMultiequalizer

end Cover

/-- Pull back a cover along a morphism. -/
@[simps obj]
def pullback (f : Y ⟶ X) : J.Cover X ⥤ J.Cover Y where
  obj S := S.pullback f
  map f := (Sieve.pullback_monotone _ f.le).hom
#align category_theory.grothendieck_topology.pullback CategoryTheory.GrothendieckTopology.pullback

/-- Pulling back along the identity is naturally isomorphic to the identity functor. -/
def pullbackId (X : C) : J.pullback (𝟙 X) ≅ 𝟭 _ :=
  NatIso.ofComponents fun S => S.pullbackId
#align category_theory.grothendieck_topology.pullback_id CategoryTheory.GrothendieckTopology.pullbackId

/-- Pulling back along a composition is naturally isomorphic to
the composition of the pullbacks. -/
def pullbackComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    J.pullback (f ≫ g) ≅ J.pullback g ⋙ J.pullback f :=
  NatIso.ofComponents fun S => S.pullbackComp f g
#align category_theory.grothendieck_topology.pullback_comp CategoryTheory.GrothendieckTopology.pullbackComp

end GrothendieckTopology

end CategoryTheory
