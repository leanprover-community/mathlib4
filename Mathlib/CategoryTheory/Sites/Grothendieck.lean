/-
Copyright (c) 2020 Bhavik Mehta, Edward Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Edward Ayers
-/
module

public import Mathlib.CategoryTheory.Sites.Sieves
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Copy
public import Mathlib.Data.Set.Subsingleton

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

@[expose] public section


universe v₁ u₁ v u

namespace CategoryTheory

open Category

variable (C : Type u) [Category.{v} C]

/-- The definition of a Grothendieck topology: a set of sieves `J X` on each object `X` satisfying
three axioms:
1. For every object `X`, the maximal sieve is in `J X`.
2. If `S ∈ J X` then its pullback along any `h : Y ⟶ X` is in `J Y`.
3. If `S ∈ J X` and `R` is a sieve on `X`, then provided that the pullback of `R` along any arrow
   `f : Y ⟶ X` in `S` is in `J Y`, we have that `R` itself is in `J X`.

A sieve `S` on `X` is referred to as `J`-covering, (or just covering), if `S ∈ J X`.

See also [nlab] or [MM92] Chapter III, Section 2, Definition 1. -/
@[stacks 00Z4]
structure GrothendieckTopology where
  /-- A Grothendieck topology on `C` consists of a set of sieves for each object `X`,
  which satisfy some axioms. -/
  sieves : ∀ X : C, Set (Sieve X)
  /-- The sieves associated to each object must contain the top sieve.
  Use `GrothendieckTopology.top_mem`. -/
  top_mem' : ∀ X, ⊤ ∈ sieves X
  /-- Stability under pullback. Use `GrothendieckTopology.pullback_stable`. -/
  pullback_stable' : ∀ ⦃X Y : C⦄ ⦃S : Sieve X⦄ (f : Y ⟶ X), S ∈ sieves X → S.pullback f ∈ sieves Y
  /-- Transitivity of sieves in a Grothendieck topology. Use `GrothendieckTopology.transitive`. -/
  transitive' :
    ∀ ⦃X⦄ ⦃S : Sieve X⦄ (_ : S ∈ sieves X) (R : Sieve X),
      (∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → R.pullback f ∈ sieves Y) → R ∈ sieves X

namespace GrothendieckTopology

instance : DFunLike (GrothendieckTopology C) C (fun X ↦ Set (Sieve X)) where
  coe J X := sieves J X
  coe_injective' J₁ J₂ h := by cases J₁; cases J₂; congr

variable {C}
variable {X Y : C} {S R : Sieve X}
variable (J : GrothendieckTopology C)

/-- An extensionality lemma in terms of the coercion to a pi-type.
We prove this explicitly rather than deriving it so that it is in terms of the coercion rather than
the projection `.sieves`.
-/
@[ext]
theorem ext {J₁ J₂ : GrothendieckTopology C} (h : (J₁ : ∀ X : C, Set (Sieve X)) = J₂) : J₁ = J₂ :=
  DFunLike.coe_injective h

@[simp]
theorem mem_sieves_iff_coe : S ∈ J.sieves X ↔ S ∈ J X :=
  Iff.rfl

/-- Also known as the maximality axiom. -/
@[simp, grind .]
theorem top_mem (X : C) : ⊤ ∈ J X :=
  J.top_mem' X

/-- Also known as the stability axiom. -/
@[simp, grind .]
theorem pullback_stable (f : Y ⟶ X) (hS : S ∈ J X) : S.pullback f ∈ J Y :=
  J.pullback_stable' f hS

variable {J} in
@[simp]
lemma pullback_mem_iff_of_isIso {i : X ⟶ Y} [IsIso i] {S : Sieve Y} :
    S.pullback i ∈ J _ ↔ S ∈ J _ := by
  refine ⟨fun H ↦ ?_, J.pullback_stable i⟩
  convert J.pullback_stable (inv i) H
  rw [← Sieve.pullback_comp, IsIso.inv_hom_id, Sieve.pullback_id]

@[grind .]
theorem transitive (hS : S ∈ J X) (R : Sieve X) (h : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → R.pullback f ∈ J Y) :
    R ∈ J X :=
  J.transitive' hS R h

theorem covering_of_eq_top : S = ⊤ → S ∈ J X := fun h => h.symm ▸ J.top_mem X

/-- Given a `GrothendieckTopology` and a set of sieves `s` that is equal, form a new
`GrothendieckTopology` whose set of sieves is definitionally equal to `s`. -/
def copy (J : GrothendieckTopology C) (s : ∀ X : C, Set (Sieve X)) (h : J.sieves = s) :
    GrothendieckTopology C where
  sieves := s
  top_mem' := h ▸ J.top_mem'
  pullback_stable' := h ▸ J.pullback_stable'
  transitive' := h ▸ J.transitive'

@[simp]
theorem sieves_copy {J : GrothendieckTopology C} {s : ∀ X : C, Set (Sieve X)} {h : J.sieves = s} :
    (J.copy s h).sieves = s :=
  rfl

@[simp]
theorem coe_copy {J : GrothendieckTopology C} {s : ∀ X : C, Set (Sieve X)} {h : J.sieves = s} :
    ⇑(J.copy s h) = s :=
  rfl

theorem copy_eq {J : GrothendieckTopology C} {s : ∀ X : C, Set (Sieve X)} {h : J.sieves = s} :
    J.copy s h = J :=
  GrothendieckTopology.ext h.symm

/-- If `S` is a subset of `R`, and `S` is covering, then `R` is covering as well.

See also discussion after [MM92] Chapter III, Section 2, Definition 1. -/
@[stacks 00Z5 "(2)"]
theorem superset_covering (Hss : S ≤ R) (sjx : S ∈ J X) : R ∈ J X := by
  apply J.transitive sjx R fun Y f hf => _
  intro Y f hf
  apply covering_of_eq_top
  rw [← top_le_iff, ← S.pullback_eq_top_of_mem hf]
  apply Sieve.pullback_monotone _ Hss

/-- The intersection of two covering sieves is covering.

See also [MM92] Chapter III, Section 2, Definition 1 (iv). -/
@[stacks 00Z5 "(1)"]
theorem intersection_covering (rj : R ∈ J X) (sj : S ∈ J X) : R ⊓ S ∈ J X := by
  apply J.transitive rj _ fun Y f Hf => _
  intro Y f hf
  rw [Sieve.pullback_inter, R.pullback_eq_top_of_mem hf]
  simp [sj]

@[simp]
theorem intersection_covering_iff : R ⊓ S ∈ J X ↔ R ∈ J X ∧ S ∈ J X :=
  ⟨fun h => ⟨J.superset_covering inf_le_left h, J.superset_covering inf_le_right h⟩, fun t =>
    intersection_covering _ t.1 t.2⟩

theorem bind_covering {S : Sieve X} {R : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → Sieve Y} (hS : S ∈ J X)
    (hR : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (H : S f), R H ∈ J Y) : Sieve.bind S R ∈ J X :=
  J.transitive hS _ fun _ f hf => superset_covering J (Sieve.le_pullback_bind S R f hf) (hR hf)

lemma bindOfArrows {ι : Type*} {X : C} {Z : ι → C} {f : ∀ i, Z i ⟶ X} {R : ∀ i, Presieve (Z i)}
    (h : Sieve.ofArrows Z f ∈ J X) (hR : ∀ i, Sieve.generate (R i) ∈ J _) :
    Sieve.generate (Presieve.bindOfArrows Z f R) ∈ J X := by
  refine J.superset_covering (Presieve.bind_ofArrows_le_bindOfArrows _ _ _) ?_
  exact J.bind_covering h fun _ _ _ ↦ J.pullback_stable _ (hR _)

/-- The sieve `S` on `X` `J`-covers an arrow `f` to `X` if `S.pullback f ∈ J Y`.
This definition is an alternate way of presenting a Grothendieck topology.
-/
def Covers (S : Sieve X) (f : Y ⟶ X) : Prop :=
  S.pullback f ∈ J Y

theorem covers_iff (S : Sieve X) (f : Y ⟶ X) : J.Covers S f ↔ S.pullback f ∈ J Y :=
  Iff.rfl

theorem covering_iff_covers_id (S : Sieve X) : S ∈ J X ↔ J.Covers S (𝟙 X) := by simp [covers_iff]

/-- The maximality axiom in 'arrow' form: Any arrow `f` in `S` is covered by `S`. -/
theorem arrow_max (f : Y ⟶ X) (S : Sieve X) (hf : S f) : J.Covers S f := by
  rw [Covers, (Sieve.mem_iff_pullback_eq_top f).1 hf]
  apply J.top_mem

/-- The stability axiom in 'arrow' form: If `S` covers `f` then `S` covers `g ≫ f` for any `g`. -/
theorem arrow_stable (f : Y ⟶ X) (S : Sieve X) (h : J.Covers S f) {Z : C} (g : Z ⟶ Y) :
    J.Covers S (g ≫ f) := by
  rw [covers_iff] at h ⊢
  simp [h, Sieve.pullback_comp]

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

theorem arrow_intersect (f : Y ⟶ X) (S R : Sieve X) (hS : J.Covers S f) (hR : J.Covers R f) :
    J.Covers (S ⊓ R) f := by simpa [covers_iff] using And.intro hS hR

variable (C)

/-- The trivial Grothendieck topology, in which only the maximal sieve is covering. This topology is
also known as the indiscrete, coarse, or chaotic topology.

See [MM92] Chapter III, Section 2, example (a), or
https://en.wikipedia.org/wiki/Grothendieck_topology#The_discrete_and_indiscrete_topologies
-/
def trivial : GrothendieckTopology C where
  sieves _ := {⊤}
  top_mem' _ := rfl
  pullback_stable' X Y S f hf := by
    rw [Set.mem_singleton_iff] at hf ⊢
    simp [hf]
  transitive' X S hS R hR := by
    rw [Set.mem_singleton_iff, ← Sieve.id_mem_iff_eq_top] at hS
    simpa using hR hS

/-- The discrete Grothendieck topology, in which every sieve is covering.

See https://en.wikipedia.org/wiki/Grothendieck_topology#The_discrete_and_indiscrete_topologies.
-/
def discrete : GrothendieckTopology C where
  sieves _ := Set.univ
  top_mem' := by simp
  pullback_stable' X Y f := by simp
  transitive' := by simp

variable {C}

theorem trivial_covering : S ∈ trivial C X ↔ S = ⊤ :=
  Set.mem_singleton_iff

@[stacks 00Z6]
instance instLEGrothendieckTopology : LE (GrothendieckTopology C) where
  le J₁ J₂ := (J₁ : ∀ X : C, Set (Sieve X)) ≤ (J₂ : ∀ X : C, Set (Sieve X))

theorem le_def {J₁ J₂ : GrothendieckTopology C} : J₁ ≤ J₂ ↔ (J₁ : ∀ X : C, Set (Sieve X)) ≤ J₂ :=
  Iff.rfl

@[stacks 00Z6]
instance : PartialOrder (GrothendieckTopology C) :=
  { instLEGrothendieckTopology with
    le_refl := fun _ => le_def.mpr le_rfl
    le_trans := fun _ _ _ h₁₂ h₂₃ => le_def.mpr (le_trans h₁₂ h₂₃)
    le_antisymm := fun _ _ h₁₂ h₂₁ => GrothendieckTopology.ext (le_antisymm h₁₂ h₂₁) }

@[stacks 00Z7]
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

lemma mem_sInf (s : Set (GrothendieckTopology C)) {X : C} (S : Sieve X) :
    S ∈ sInf s X ↔ ∀ t ∈ s, S ∈ t X := by
  change S ∈ sInf (sieves '' s) X ↔ _
  simp

@[stacks 00Z7]
theorem isGLB_sInf (s : Set (GrothendieckTopology C)) : IsGLB s (sInf s) := by
  refine @IsGLB.of_image _ _ _ _ sieves ?_ _ _ ?_
  · rfl
  · exact _root_.isGLB_sInf _

/-- Construct a complete lattice from the `Inf`, but make the trivial and discrete topologies
definitionally equal to the bottom and top respectively.
-/
instance : CompleteLattice (GrothendieckTopology C) :=
  CompleteLattice.copy (completeLatticeOfInf _ isGLB_sInf) _ rfl (discrete C)
    (by
      apply le_antisymm
      · exact (completeLatticeOfInf _ isGLB_sInf).le_top (discrete C)
      · intro X S _
        apply Set.mem_univ)
    (trivial C)
    (by
      apply le_antisymm
      · intro X S hS
        rw [trivial_covering] at hS
        apply covering_of_eq_top _ hS
      · exact (completeLatticeOfInf _ isGLB_sInf).bot_le (trivial C))
    _ rfl _ rfl _ rfl sInf rfl

instance : Inhabited (GrothendieckTopology C) :=
  ⟨⊤⟩

@[simp]
theorem trivial_eq_bot : trivial C = ⊥ :=
  rfl

@[simp]
theorem discrete_eq_top : discrete C = ⊤ :=
  rfl

@[simp]
theorem bot_covering : S ∈ (⊥ : GrothendieckTopology C) X ↔ S = ⊤ :=
  trivial_covering

@[simp]
theorem top_covering : S ∈ (⊤ : GrothendieckTopology C) X :=
  ⟨⟩

theorem bot_covers (S : Sieve X) (f : Y ⟶ X) : (⊥ : GrothendieckTopology C).Covers S f ↔ S f := by
  rw [covers_iff, bot_covering, ← Sieve.mem_iff_pullback_eq_top]

@[simp]
theorem top_covers (S : Sieve X) (f : Y ⟶ X) : (⊤ : GrothendieckTopology C).Covers S f := by
  simp [covers_iff]

set_option backward.isDefEq.respectTransparency false in
lemma eq_top_iff (J : GrothendieckTopology C) : J = ⊤ ↔ ∀ X, ⊥ ∈ J X := by
  refine ⟨fun h ↦ h ▸ by simp, fun h ↦ ?_⟩
  rw [_root_.eq_top_iff]
  intro X S _
  exact J.superset_covering bot_le (h X)

lemma eq_top_of_isEmpty [IsEmpty C] (J : GrothendieckTopology C) : J = ⊤ := by
  rw [eq_top_iff]
  intro X
  exact IsEmpty.elim ‹IsEmpty C› X

@[simp]
lemma bot_eq_top_iff_isEmpty : (⊥ : GrothendieckTopology C) = ⊤ ↔ IsEmpty C := by
  refine ⟨fun h ↦ ⟨fun X ↦ ?_⟩, fun h ↦ eq_top_of_isEmpty _⟩
  apply bot_ne_top (α := Sieve X)
  simp only [← GrothendieckTopology.bot_covering, h, top_covering]

@[simp]
lemma bot_lt_top_iff_nonempty : (⊥ : GrothendieckTopology C) < ⊤ ↔ Nonempty C := by
  contrapose!
  simp

/-- The dense Grothendieck topology.

See https://ncatlab.org/nlab/show/dense+topology, or [MM92] Chapter III, Section 2, example (e).
-/
def dense : GrothendieckTopology C where
  sieves X := {S | ∀ {Y : C} (f : Y ⟶ X), ∃ (Z : _) (g : Z ⟶ Y), S (g ≫ f)}
  top_mem' _ Y _ := ⟨Y, 𝟙 Y, ⟨⟩⟩
  pullback_stable' := by
    intro X Y S h H Z f
    rcases H (f ≫ h) with ⟨W, g, H'⟩
    exact ⟨W, g, by simpa⟩
  transitive' := by
    intro X S H₁ R H₂ Y f
    rcases H₁ f with ⟨Z, g, H₃⟩
    rcases H₂ H₃ (𝟙 Z) with ⟨W, h, H₄⟩
    exact ⟨W, h ≫ g, by simpa using H₄⟩

theorem dense_covering : S ∈ dense X ↔ ∀ {Y} (f : Y ⟶ X), ∃ (Z : _) (g : Z ⟶ Y), S (g ≫ f) :=
  Iff.rfl

/--
A category satisfies the right Ore condition if any span can be completed to a commutative square.
NB. Any category with pullbacks obviously satisfies the right Ore condition, see
`right_ore_of_pullbacks`.
-/
def RightOreCondition (C : Type u) [Category.{v} C] : Prop :=
  ∀ {X Y Z : C} (yx : Y ⟶ X) (zx : Z ⟶ X), ∃ (W : _) (wy : W ⟶ Y) (wz : W ⟶ Z), wy ≫ yx = wz ≫ zx

theorem right_ore_of_pullbacks [Limits.HasPullbacks C] : RightOreCondition C := fun _ _ =>
  ⟨_, _, _, Limits.pullback.condition⟩

/-- The atomic Grothendieck topology: a sieve is covering iff it is nonempty.
For the pullback stability condition, we need the right Ore condition to hold.

See https://ncatlab.org/nlab/show/atomic+site, or [MM92] Chapter III, Section 2, example (f).
-/
def atomic (hro : RightOreCondition C) : GrothendieckTopology C where
  sieves X := {S | ∃ (Y : _) (f : Y ⟶ X), S f}
  top_mem' _ := ⟨_, 𝟙 _, ⟨⟩⟩
  pullback_stable' := by
    rintro X Y S h ⟨Z, f, hf⟩
    rcases hro h f with ⟨W, g, k, comm⟩
    refine ⟨_, g, ?_⟩
    simp [comm, hf]
  transitive' := by
    rintro X S ⟨Y, f, hf⟩ R h
    rcases h hf with ⟨Z, g, hg⟩
    exact ⟨_, _, hg⟩


/-- `J.Cover X` denotes the poset of covers of `X` with respect to the
Grothendieck topology `J`. -/
def Cover (X : C) : Type max u v :=
  { S : Sieve X // S ∈ J X }
deriving Preorder

namespace Cover

variable {J}

instance : CoeOut (J.Cover X) (Sieve X) := ⟨fun S => S.1⟩

instance : CoeFun (J.Cover X) fun _ => ∀ ⦃Y⦄ (_ : Y ⟶ X), Prop := ⟨fun S => (S : Sieve X)⟩

theorem condition (S : J.Cover X) : (S : Sieve X) ∈ J X := S.2

@[ext]
theorem ext (S T : J.Cover X) (h : ∀ ⦃Y⦄ (f : Y ⟶ X), S f ↔ T f) : S = T :=
  Subtype.ext <| Sieve.ext h

instance : OrderTop (J.Cover X) :=
  { (inferInstance : Preorder (J.Cover X)) with
    top := ⟨⊤, J.top_mem _⟩
    le_top := fun _ _ _ _ => by tauto }

instance : SemilatticeInf (J.Cover X) :=
  { (inferInstance : Preorder _) with
    inf := fun S T => ⟨S ⊓ T, J.intersection_covering S.condition T.condition⟩
    le_antisymm := fun _ _ h1 h2 => ext _ _ fun {Y} f => ⟨by apply h1, by apply h2⟩
    inf_le_left := fun _ _ _ _ hf => hf.1
    inf_le_right := fun _ _ _ _ hf => hf.2
    le_inf := fun _ _ _ h1 h2 _ _ h => ⟨h1 _ h, h2 _ h⟩ }

instance : Inhabited (J.Cover X) :=
  ⟨⊤⟩

/-- An auxiliary structure, used to define `S.index`. -/
@[ext]
structure Arrow (S : J.Cover X) where
  /-- The source of the arrow. -/
  Y : C
  /-- The arrow itself. -/
  f : Y ⟶ X
  /-- The given arrow is contained in the given sieve. -/
  hf : S f

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
  w : g₁ ≫ I₁.f = g₂ ≫ I₂.f := by cat_disch

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
  Z := (I.precomp g).Y
  g₁ := 𝟙 _
  g₂ := g

/-- Map an `Arrow` along a refinement `S ⟶ T`. -/
@[simps]
def Arrow.map {S T : J.Cover X} (I : S.Arrow) (f : S ⟶ T) : T.Arrow :=
  ⟨I.Y, I.f, f.le _ I.hf⟩

/-- Map an `Arrow.Relation` along a refinement `S ⟶ T`. -/
@[simps]
def Arrow.Relation.map {S T : J.Cover X} {I₁ I₂ : S.Arrow}
    (r : I₁.Relation I₂) (f : S ⟶ T) : (I₁.map f).Relation (I₂.map f) :=
  { r with }

/-- Pull back a cover along a morphism. -/
def pullback (S : J.Cover X) (f : Y ⟶ X) : J.Cover Y :=
  ⟨Sieve.pullback f S, J.pullback_stable _ S.condition⟩

/-- An arrow of `S.pullback f` gives rise to an arrow of `S`. -/
@[simps]
def Arrow.base {f : Y ⟶ X} {S : J.Cover X} (I : (S.pullback f).Arrow) : S.Arrow :=
  ⟨I.Y, I.f ≫ f, I.hf⟩

/-- A relation of `S.pullback f` gives rise to a relation of `S`. -/
def Arrow.Relation.base
    {f : Y ⟶ X} {S : J.Cover X} {I₁ I₂ : (S.pullback f).Arrow}
    (r : I₁.Relation I₂) : I₁.base.Relation I₂.base :=
  { r with w := by simp [r.w_assoc] }

@[simp]
theorem coe_pullback {Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (S : J.Cover X) :
    (S.pullback f) g ↔ S (g ≫ f) :=
  Iff.rfl

/-- The isomorphism between `S` and the pullback of `S` w.r.t. the identity. -/
def pullbackId (S : J.Cover X) : S.pullback (𝟙 X) ≅ S :=
  eqToIso <| Cover.ext _ _ fun Y f => by simp

/-- Pulling back with respect to a composition is the composition of the pullbacks. -/
def pullbackComp {X Y Z : C} (S : J.Cover X) (f : Z ⟶ Y) (g : Y ⟶ X) :
    S.pullback (f ≫ g) ≅ (S.pullback g).pullback f :=
  eqToIso <| Cover.ext _ _ fun Y f => by simp

/-- Combine a family of covers over a cover. -/
def bind {X : C} (S : J.Cover X) (T : ∀ I : S.Arrow, J.Cover I.Y) : J.Cover X :=
  ⟨Sieve.bind S fun Y f hf => T ⟨Y, f, hf⟩,
    J.bind_covering S.condition fun _ _ _ => (T { Y := _, f := _, hf := _ }).condition⟩

/-- The canonical morphism from `S.bind T` to `T`. -/
def bindToBase {X : C} (S : J.Cover X) (T : ∀ I : S.Arrow, J.Cover I.Y) : S.bind T ⟶ S :=
  homOfLE <| by
    rintro Y f ⟨Z, e1, e2, h1, _, h3⟩
    rw [← h3]
    apply Sieve.downward_closed
    exact h1

/-- An arrow in bind has the form `A ⟶ B ⟶ X` where `A ⟶ B` is an arrow in `T I` for some `I`.
and `B ⟶ X` is an arrow of `S`. This is the object `B`. -/
noncomputable def Arrow.middle {X : C} {S : J.Cover X} {T : ∀ I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : C :=
  I.hf.choose

/-- An arrow in bind has the form `A ⟶ B ⟶ X` where `A ⟶ B` is an arrow in `T I` for some `I`.
and `B ⟶ X` is an arrow of `S`. This is the hom `A ⟶ B`. -/
noncomputable def Arrow.toMiddleHom {X : C} {S : J.Cover X} {T : ∀ I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : I.Y ⟶ I.middle :=
  I.hf.choose_spec.choose

/-- An arrow in bind has the form `A ⟶ B ⟶ X` where `A ⟶ B` is an arrow in `T I` for some `I`.
and `B ⟶ X` is an arrow of `S`. This is the hom `B ⟶ X`. -/
noncomputable def Arrow.fromMiddleHom {X : C} {S : J.Cover X} {T : ∀ I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : I.middle ⟶ X :=
  I.hf.choose_spec.choose_spec.choose

theorem Arrow.from_middle_condition {X : C} {S : J.Cover X} {T : ∀ I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : S I.fromMiddleHom :=
  I.hf.choose_spec.choose_spec.choose_spec.choose

/-- An arrow in bind has the form `A ⟶ B ⟶ X` where `A ⟶ B` is an arrow in `T I` for some `I`.
and `B ⟶ X` is an arrow of `S`. This is the hom `B ⟶ X`, as an arrow. -/
noncomputable def Arrow.fromMiddle {X : C} {S : J.Cover X} {T : ∀ I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : S.Arrow :=
  ⟨_, I.fromMiddleHom, I.from_middle_condition⟩

theorem Arrow.to_middle_condition {X : C} {S : J.Cover X} {T : ∀ I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : (T I.fromMiddle) I.toMiddleHom :=
  I.hf.choose_spec.choose_spec.choose_spec.choose_spec.1

/-- An arrow in bind has the form `A ⟶ B ⟶ X` where `A ⟶ B` is an arrow in `T I` for some `I`.
and `B ⟶ X` is an arrow of `S`. This is the hom `A ⟶ B`, as an arrow. -/
noncomputable def Arrow.toMiddle {X : C} {S : J.Cover X} {T : ∀ I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : (T I.fromMiddle).Arrow :=
  ⟨_, I.toMiddleHom, I.to_middle_condition⟩

theorem Arrow.middle_spec {X : C} {S : J.Cover X} {T : ∀ I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : I.toMiddleHom ≫ I.fromMiddleHom = I.f :=
  I.hf.choose_spec.choose_spec.choose_spec.choose_spec.2

/-- An auxiliary structure, used to define `S.index`. -/
@[ext]
structure Relation (S : J.Cover X) where
  /-- The first arrow. -/
  {fst : S.Arrow}
  /-- The second arrow. -/
  {snd : S.Arrow}
  /-- The relation between the two arrows. -/
  r : fst.Relation snd

/-- Constructor for `Cover.Relation` which takes as an input
`r : I₁.Relation I₂` with `I₁ I₂ : S.Arrow`. -/
@[simps]
def Relation.mk' {S : J.Cover X} {fst snd : S.Arrow} (r : fst.Relation snd) :
    S.Relation where
  fst := fst
  snd := snd
  r := r


/-- The shape of the multiequalizer diagrams associated to `S : J.Cover X`. -/
@[simps]
def shape (S : J.Cover X) : Limits.MulticospanShape where
  L := S.Arrow
  R := S.Relation
  fst I := I.fst
  snd I := I.snd

-- This is used extensively in `Plus.lean`, etc.
-- We place this definition here as it will be used in `Sheaf.lean` as well.
/-- To every `S : J.Cover X` and presheaf `P`, associate a `MulticospanIndex`. -/
@[simps]
def index {D : Type u₁} [Category.{v₁} D] (S : J.Cover X) (P : Cᵒᵖ ⥤ D) :
    Limits.MulticospanIndex S.shape D where
  left I := P.obj (Opposite.op I.Y)
  right I := P.obj (Opposite.op I.r.Z)
  fst I := P.map I.r.g₁.op
  snd I := P.map I.r.g₂.op

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

/-- The canonical map from `P.obj (op X)` to the multiequalizer associated to a covering sieve,
assuming such a multiequalizer exists. This will be used in `Sheaf.lean` to provide an equivalent
sheaf condition in terms of multiequalizers. -/
noncomputable abbrev toMultiequalizer {D : Type u₁} [Category.{v₁} D] (S : J.Cover X)
    (P : Cᵒᵖ ⥤ D) [Limits.HasMultiequalizer (S.index P)] :
    P.obj (Opposite.op X) ⟶ Limits.multiequalizer (S.index P) :=
  Limits.Multiequalizer.lift _ _ (fun I => P.map I.f.op)
    (by
      intro I
      dsimp only [shape, index, Relation.fst, Relation.snd]
      simp only [← P.map_comp, ← op_comp, I.r.w])

end Cover

/-- Pull back a cover along a morphism. -/
@[simps obj]
def pullback (f : Y ⟶ X) : J.Cover X ⥤ J.Cover Y where
  obj S := S.pullback f
  map f := (Sieve.pullback_monotone _ f.le).hom

/-- Pulling back along the identity is naturally isomorphic to the identity functor. -/
def pullbackId (X : C) : J.pullback (𝟙 X) ≅ 𝟭 _ :=
  NatIso.ofComponents fun S => S.pullbackId

/-- Pulling back along a composition is naturally isomorphic to
the composition of the pullbacks. -/
def pullbackComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    J.pullback (f ≫ g) ≅ J.pullback g ⋙ J.pullback f :=
  NatIso.ofComponents fun S => S.pullbackComp f g

end GrothendieckTopology

end CategoryTheory
