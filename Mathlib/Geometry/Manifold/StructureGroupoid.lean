/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Data.EReal.Operations
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-!
# Structure groupoids

This file contains the definitions and properties of structure groupoids, i.e., sets of open partial
homeomorphisms stable under composition and inverse. These are used to define charted spaces (and
hence manifolds). See the file `Mathlib.Geometry.Manifold.ChartedSpace` for more details.

## Main definitions

* `StructureGroupoid H` : a subset of open partial homeomorphisms of `H` stable under composition,
  inverse and restriction (ex: partial diffeomorphisms).
* `continuousGroupoid H` : the groupoid of all open partial homeomorphisms of `H`.

Additional useful definitions:

* `Pregroupoid H` : a subset of partial maps of `H` stable under composition and
  restriction, but not inverse (ex: smooth maps)
* `Pregroupoid.groupoid` : construct a groupoid from a pregroupoid, by requiring that a map and
  its inverse both belong to the pregroupoid (ex: construct diffeos from smooth maps)

## Notation

In the scope `Manifold`, we denote the composition of open partial homeomorphisms with `≫ₕ`, and the
composition of partial equivs with `≫`.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Topology

variable {H : Type*}

/- Notational shortcut for the composition of open partial homeomorphisms and partial equivs, i.e.,
`OpenPartialHomeomorph.trans` and `PartialEquiv.trans`.
Note that, as is usual for equivs, the composition is from left to right, hence the direction of
the arrow. -/
@[inherit_doc] scoped[Manifold] infixr:100 " ≫ₕ " => OpenPartialHomeomorph.trans

@[inherit_doc] scoped[Manifold] infixr:100 " ≫ " => PartialEquiv.trans

open Set OpenPartialHomeomorph Manifold

/-! ### Structure groupoids -/

section Groupoid

/-! One could add to the definition of a structure groupoid the fact that the restriction of an
element of the groupoid to any open set still belongs to the groupoid.
(This is in Kobayashi-Nomizu.)
I am not sure I want this, for instance on `H × E` where `E` is a vector space, and the groupoid is
made of functions respecting the fibers and linear in the fibers (so that a charted space over this
groupoid is naturally a vector bundle) I prefer that the members of the groupoid are always
defined on sets of the form `s × E`. There is a typeclass `ClosedUnderRestriction` for groupoids
which have the restriction property.

The only nontrivial requirement is locality: if an open partial homeomorphism belongs to the
groupoid around each point in its domain of definition, then it belongs to the groupoid. Without
this requirement, the composition of structomorphisms does not have to be a structomorphism. Note
that this implies that an open partial homeomorphism with empty source belongs to any structure
groupoid, as it trivially satisfies this condition.

There is also a technical point, related to the fact that an open partial homeomorphism is by
definition a global map which is a homeomorphism when restricted to its source subset (and its
values outside of the source are not relevant). Therefore, we also require that being a member of
the groupoid only depends on the values on the source.

We use primes in the structure names as we will reformulate them below (without primes) using a
`Membership` instance, writing `e ∈ G` instead of `e ∈ G.members`.
-/


/-- A structure groupoid is a set of open partial homeomorphisms of a topological space stable under
composition and inverse. They appear in the definition of the smoothness class of a manifold. -/
structure StructureGroupoid (H : Type*) [TopologicalSpace H] where
  /-- Members of the structure groupoid are open partial homeomorphisms. -/
  members : Set (OpenPartialHomeomorph H H)
  /-- Structure groupoids are stable under composition. -/
  trans' : ∀ e e' : OpenPartialHomeomorph H H, e ∈ members → e' ∈ members → e ≫ₕ e' ∈ members
  /-- Structure groupoids are stable under inverse. -/
  symm' : ∀ e : OpenPartialHomeomorph H H, e ∈ members → e.symm ∈ members
  /-- The identity morphism lies in the structure groupoid. -/
  id_mem' : OpenPartialHomeomorph.refl H ∈ members
  /-- Let `e` be an open partial homeomorphism. If for every `x ∈ e.source`, the restriction of e
  to some open set around `x` lies in the groupoid, then `e` lies in the groupoid. -/
  locality' : ∀ e : OpenPartialHomeomorph H H,
    (∀ x ∈ e.source, ∃ s, IsOpen s ∧ x ∈ s ∧ e.restr s ∈ members) → e ∈ members
  /-- Membership in a structure groupoid respects the equivalence of open partial homeomorphisms. -/
  mem_of_eqOnSource' : ∀ e e' : OpenPartialHomeomorph H H, e ∈ members → e' ≈ e → e' ∈ members

variable [TopologicalSpace H]

instance : Membership (OpenPartialHomeomorph H H) (StructureGroupoid H) :=
  ⟨fun (G : StructureGroupoid H) (e : OpenPartialHomeomorph H H) ↦ e ∈ G.members⟩

instance (H : Type*) [TopologicalSpace H] :
    SetLike (StructureGroupoid H) (OpenPartialHomeomorph H H) where
  coe s := s.members
  coe_injective' N O h := by cases N; cases O; congr

instance : Min (StructureGroupoid H) :=
  ⟨fun G G' => StructureGroupoid.mk
    (members := G.members ∩ G'.members)
    (trans' := fun e e' he he' =>
      ⟨G.trans' e e' he.left he'.left, G'.trans' e e' he.right he'.right⟩)
    (symm' := fun e he => ⟨G.symm' e he.left, G'.symm' e he.right⟩)
    (id_mem' := ⟨G.id_mem', G'.id_mem'⟩)
    (locality' := by
      intro e hx
      apply (mem_inter_iff e G.members G'.members).mpr
      refine And.intro (G.locality' e ?_) (G'.locality' e ?_)
      all_goals
        intro x hex
        rcases hx x hex with ⟨s, hs⟩
        use s
        refine And.intro hs.left (And.intro hs.right.left ?_)
      · exact hs.right.right.left
      · exact hs.right.right.right)
    (mem_of_eqOnSource' := fun e e' he hee' =>
      ⟨G.mem_of_eqOnSource' e e' he.left hee', G'.mem_of_eqOnSource' e e' he.right hee'⟩)⟩

instance : InfSet (StructureGroupoid H) :=
  ⟨fun S => StructureGroupoid.mk
    (members := ⋂ s ∈ S, s.members)
    (trans' := by
      simp only [mem_iInter]
      intro e e' he he' i hi
      exact i.trans' e e' (he i hi) (he' i hi))
    (symm' := by
      simp only [mem_iInter]
      intro e he i hi
      exact i.symm' e (he i hi))
    (id_mem' := by
      simp only [mem_iInter]
      intro i _
      exact i.id_mem')
    (locality' := by
      simp only [mem_iInter]
      intro e he i hi
      refine i.locality' e ?_
      intro x hex
      rcases he x hex with ⟨s, hs⟩
      exact ⟨s, ⟨hs.left, ⟨hs.right.left, hs.right.right i hi⟩⟩⟩)
    (mem_of_eqOnSource' := by
      simp only [mem_iInter]
      intro e e' he he'e
      exact fun i hi => i.mem_of_eqOnSource' e e' (he i hi) he'e)⟩

theorem StructureGroupoid.trans (G : StructureGroupoid H) {e e' : OpenPartialHomeomorph H H}
    (he : e ∈ G) (he' : e' ∈ G) : e ≫ₕ e' ∈ G :=
  G.trans' e e' he he'

theorem StructureGroupoid.symm (G : StructureGroupoid H) {e : OpenPartialHomeomorph H H}
    (he : e ∈ G) : e.symm ∈ G :=
  G.symm' e he

theorem StructureGroupoid.id_mem (G : StructureGroupoid H) : OpenPartialHomeomorph.refl H ∈ G :=
  G.id_mem'

theorem StructureGroupoid.locality (G : StructureGroupoid H) {e : OpenPartialHomeomorph H H}
    (h : ∀ x ∈ e.source, ∃ s, IsOpen s ∧ x ∈ s ∧ e.restr s ∈ G) : e ∈ G :=
  G.locality' e h

theorem StructureGroupoid.mem_of_eqOnSource (G : StructureGroupoid H)
    {e e' : OpenPartialHomeomorph H H} (he : e ∈ G) (h : e' ≈ e) : e' ∈ G :=
  G.mem_of_eqOnSource' e e' he h

theorem StructureGroupoid.mem_iff_of_eqOnSource {G : StructureGroupoid H}
    {e e' : OpenPartialHomeomorph H H} (h : e ≈ e') : e ∈ G ↔ e' ∈ G :=
  ⟨fun he ↦ G.mem_of_eqOnSource he (Setoid.symm h), fun he' ↦ G.mem_of_eqOnSource he' h⟩

/-- Partial order on the set of groupoids, given by inclusion of the members of the groupoid. -/
instance StructureGroupoid.partialOrder : PartialOrder (StructureGroupoid H) :=
  PartialOrder.lift StructureGroupoid.members fun a b h ↦ by
    cases a
    cases b
    dsimp at h
    induction h
    rfl

theorem StructureGroupoid.le_iff {G₁ G₂ : StructureGroupoid H} : G₁ ≤ G₂ ↔ ∀ e, e ∈ G₁ → e ∈ G₂ :=
  Iff.rfl

/-- The trivial groupoid, containing only the identity (and maps with empty source, as this is
necessary from the definition). -/
def idGroupoid (H : Type*) [TopologicalSpace H] : StructureGroupoid H where
  members := {OpenPartialHomeomorph.refl H} ∪ { e : OpenPartialHomeomorph H H | e.source = ∅ }
  trans' e e' he he' := by
    rcases he with he | he
    · simpa only [mem_singleton_iff.1 he, refl_trans]
    · have : (e ≫ₕ e').source ⊆ e.source := sep_subset _ _
      rw [he] at this
      have : e ≫ₕ e' ∈ { e : OpenPartialHomeomorph H H | e.source = ∅ } := eq_bot_iff.2 this
      exact (mem_union _ _ _).2 (Or.inr this)
  symm' e he := by
    rcases (mem_union _ _ _).1 he with E | E
    · simp [mem_singleton_iff.mp E]
    · right
      simpa only [e.toPartialEquiv.image_source_eq_target.symm, mfld_simps] using E
  id_mem' := mem_union_left _ rfl
  locality' e he := by
    rcases e.source.eq_empty_or_nonempty with h | h
    · right
      exact h
    · left
      rcases h with ⟨x, hx⟩
      rcases he x hx with ⟨s, open_s, xs, hs⟩
      have x's : x ∈ (e.restr s).source := by
        rw [restr_source, open_s.interior_eq]
        exact ⟨hx, xs⟩
      rcases hs with hs | hs
      · replace hs : OpenPartialHomeomorph.restr e s = OpenPartialHomeomorph.refl H := by
          simpa only using hs
        have : (e.restr s).source = univ := by
          rw [hs]
          simp
        have : e.toPartialEquiv.source ∩ interior s = univ := this
        have : univ ⊆ interior s := by
          rw [← this]
          exact inter_subset_right
        have : s = univ := by rwa [open_s.interior_eq, univ_subset_iff] at this
        simpa only [this, restr_univ] using hs
      · exfalso
        rw [mem_setOf_eq] at hs
        rwa [hs] at x's
  mem_of_eqOnSource' e e' he he'e := by
    rcases he with he | he
    · left
      have : e = e' := by
        refine eq_of_eqOnSource_univ (Setoid.symm he'e) ?_ ?_ <;>
          rw [Set.mem_singleton_iff.1 he] <;> rfl
      rwa [← this]
    · right
      have he : e.toPartialEquiv.source = ∅ := he
      rwa [Set.mem_setOf_eq, EqOnSource.source_eq he'e]

/-- Every structure groupoid contains the identity groupoid. -/
instance instStructureGroupoidOrderBot : OrderBot (StructureGroupoid H) where
  bot := idGroupoid H
  bot_le := by
    intro u f hf
    have hf :
        f ∈ {OpenPartialHomeomorph.refl H} ∪ { e : OpenPartialHomeomorph H H | e.source = ∅ } :=
      hf
    simp only [singleton_union, mem_setOf_eq, mem_insert_iff] at hf
    rcases hf with hf | hf
    · rw [hf]
      apply u.id_mem
    · apply u.locality
      intro x hx
      rw [hf, mem_empty_iff_false] at hx
      exact hx.elim

instance : Inhabited (StructureGroupoid H) := ⟨idGroupoid H⟩

/-- To construct a groupoid, one may consider classes of open partial homeomorphisms such that
both the function and its inverse have some property. If this property is stable under composition,
one gets a groupoid. `Pregroupoid` bundles the properties needed for this construction, with the
groupoid of smooth functions with smooth inverses as an application. -/
structure Pregroupoid (H : Type*) [TopologicalSpace H] where
  /-- Property describing membership in this groupoid: the pregroupoid "contains"
  all functions `H → H` having the pregroupoid property on some `s : Set H` -/
  property : (H → H) → Set H → Prop
  /-- The pregroupoid property is stable under composition -/
  comp : ∀ {f g u v}, property f u → property g v →
    IsOpen u → IsOpen v → IsOpen (u ∩ f ⁻¹' v) → property (g ∘ f) (u ∩ f ⁻¹' v)
  /-- Pregroupoids contain the identity map (on `univ`) -/
  id_mem : property id univ
  /-- The pregroupoid property is "local", in the sense that `f` has the pregroupoid property on `u`
  iff its restriction to each open subset of `u` has it -/
  locality :
    ∀ {f u}, IsOpen u → (∀ x ∈ u, ∃ v, IsOpen v ∧ x ∈ v ∧ property f (u ∩ v)) → property f u
  /-- If `f = g` on `u` and `property f u`, then `property g u` -/
  congr : ∀ {f g : H → H} {u}, IsOpen u → (∀ x ∈ u, g x = f x) → property f u → property g u

/-- Construct a groupoid of partial homeos for which the map and its inverse have some property,
from a pregroupoid asserting that this property is stable under composition. -/
def Pregroupoid.groupoid (PG : Pregroupoid H) : StructureGroupoid H where
  members :=
    { e : OpenPartialHomeomorph H H | PG.property e e.source ∧ PG.property e.symm e.target }
  trans' e e' he he' := by
    constructor
    · apply PG.comp he.1 he'.1 e.open_source e'.open_source
      apply e.continuousOn_toFun.isOpen_inter_preimage e.open_source e'.open_source
    · apply PG.comp he'.2 he.2 e'.open_target e.open_target
      apply e'.continuousOn_invFun.isOpen_inter_preimage e'.open_target e.open_target
  symm' _ he := ⟨he.2, he.1⟩
  id_mem' := ⟨PG.id_mem, PG.id_mem⟩
  locality' e he := by
    constructor
    · refine PG.locality e.open_source fun x xu ↦ ?_
      rcases he x xu with ⟨s, s_open, xs, hs⟩
      refine ⟨s, s_open, xs, ?_⟩
      convert hs.1 using 1
      dsimp [OpenPartialHomeomorph.restr]
      rw [s_open.interior_eq]
    · refine PG.locality e.open_target fun x xu ↦ ?_
      rcases he (e.symm x) (e.map_target xu) with ⟨s, s_open, xs, hs⟩
      refine ⟨e.target ∩ e.symm ⁻¹' s, ?_, ⟨xu, xs⟩, ?_⟩
      · exact ContinuousOn.isOpen_inter_preimage e.continuousOn_invFun e.open_target s_open
      · rw [← inter_assoc, inter_self]
        convert hs.2 using 1
        dsimp [OpenPartialHomeomorph.restr]
        rw [s_open.interior_eq]
  mem_of_eqOnSource' e e' he ee' := by
    constructor
    · apply PG.congr e'.open_source ee'.2
      simp only [ee'.1, he.1]
    · have A := EqOnSource.symm' ee'
      apply PG.congr e'.symm.open_source A.2
      convert he.2 using 1
      rw [A.1, symm_toPartialEquiv, PartialEquiv.symm_source]

theorem mem_groupoid_of_pregroupoid {PG : Pregroupoid H} {e : OpenPartialHomeomorph H H} :
    e ∈ PG.groupoid ↔ PG.property e e.source ∧ PG.property e.symm e.target :=
  Iff.rfl

theorem groupoid_of_pregroupoid_le (PG₁ PG₂ : Pregroupoid H)
    (h : ∀ f s, PG₁.property f s → PG₂.property f s) : PG₁.groupoid ≤ PG₂.groupoid := by
  refine StructureGroupoid.le_iff.2 fun e he ↦ ?_
  rw [mem_groupoid_of_pregroupoid] at he ⊢
  exact ⟨h _ _ he.1, h _ _ he.2⟩

theorem mem_pregroupoid_of_eqOnSource (PG : Pregroupoid H) {e e' : OpenPartialHomeomorph H H}
    (he' : e ≈ e') (he : PG.property e e.source) : PG.property e' e'.source := by
  rw [← he'.1]
  exact PG.congr e.open_source he'.eqOn.symm he

/-- The pregroupoid of all partial maps on a topological space `H`. -/
abbrev continuousPregroupoid (H : Type*) [TopologicalSpace H] : Pregroupoid H where
  property _ _ := True
  comp _ _ _ _ _ := trivial
  id_mem := trivial
  locality _ _ := trivial
  congr _ _ _ := trivial

instance (H : Type*) [TopologicalSpace H] : Inhabited (Pregroupoid H) :=
  ⟨continuousPregroupoid H⟩

/-- The groupoid of all open partial homeomorphisms on a topological space `H`. -/
def continuousGroupoid (H : Type*) [TopologicalSpace H] : StructureGroupoid H :=
  Pregroupoid.groupoid (continuousPregroupoid H)

/-- Every structure groupoid is contained in the groupoid of all open partial homeomorphisms. -/
instance instStructureGroupoidOrderTop : OrderTop (StructureGroupoid H) where
  top := continuousGroupoid H
  le_top _ _ _ := ⟨trivial, trivial⟩

instance : CompleteLattice (StructureGroupoid H) :=
  { SetLike.instPartialOrder,
    completeLatticeOfInf _ (by
      exact fun s =>
      ⟨fun S Ss F hF => mem_iInter₂.mp hF S Ss,
      fun T Tl F fT => mem_iInter₂.mpr (fun i his => Tl his fT)⟩) with
    le := (· ≤ ·)
    lt := (· < ·)
    bot := instStructureGroupoidOrderBot.bot
    bot_le := instStructureGroupoidOrderBot.bot_le
    top := instStructureGroupoidOrderTop.top
    le_top := instStructureGroupoidOrderTop.le_top
    inf := (· ⊓ ·)
    le_inf := fun _ _ _ h₁₂ h₁₃ _ hm ↦ ⟨h₁₂ hm, h₁₃ hm⟩
    inf_le_left := fun _ _ _ ↦ And.left
    inf_le_right := fun _ _ _ ↦ And.right }

/-- A groupoid is closed under restriction if it contains all restrictions of its element local
homeomorphisms to open subsets of the source. -/
class ClosedUnderRestriction (G : StructureGroupoid H) : Prop where
  closedUnderRestriction :
    ∀ {e : OpenPartialHomeomorph H H}, e ∈ G → ∀ s : Set H, IsOpen s → e.restr s ∈ G

theorem closedUnderRestriction' {G : StructureGroupoid H} [ClosedUnderRestriction G]
    {e : OpenPartialHomeomorph H H} (he : e ∈ G) {s : Set H} (hs : IsOpen s) : e.restr s ∈ G :=
  ClosedUnderRestriction.closedUnderRestriction he s hs

/-- The trivial restriction-closed groupoid, containing only open partial homeomorphisms equivalent
to the restriction of the identity to the various open subsets. -/
def idRestrGroupoid : StructureGroupoid H where
  members := { e | ∃ (s : Set H) (h : IsOpen s), e ≈ OpenPartialHomeomorph.ofSet s h }
  trans' := by
    rintro e e' ⟨s, hs, hse⟩ ⟨s', hs', hse'⟩
    refine ⟨s ∩ s', hs.inter hs', ?_⟩
    have := OpenPartialHomeomorph.EqOnSource.trans' hse hse'
    rwa [OpenPartialHomeomorph.ofSet_trans_ofSet] at this
  symm' := by
    rintro e ⟨s, hs, hse⟩
    refine ⟨s, hs, ?_⟩
    rw [← ofSet_symm]
    exact OpenPartialHomeomorph.EqOnSource.symm' hse
  id_mem' := ⟨univ, isOpen_univ, by simp only [mfld_simps, refl]⟩
  locality' := by
    intro e h
    refine ⟨e.source, e.open_source, by simp only [mfld_simps], ?_⟩
    intro x hx
    rcases h x hx with ⟨s, hs, hxs, s', hs', hes'⟩
    have hes : x ∈ (e.restr s).source := by
      rw [e.restr_source]
      refine ⟨hx, ?_⟩
      rw [hs.interior_eq]
      exact hxs
    simpa only [mfld_simps] using OpenPartialHomeomorph.EqOnSource.eqOn hes' hes
  mem_of_eqOnSource' := by
    rintro e e' ⟨s, hs, hse⟩ hee'
    exact ⟨s, hs, Setoid.trans hee' hse⟩

theorem idRestrGroupoid_mem {s : Set H} (hs : IsOpen s) : ofSet s hs ∈ @idRestrGroupoid H _ :=
  ⟨s, hs, refl _⟩

/-- The trivial restriction-closed groupoid is indeed `ClosedUnderRestriction`. -/
instance closedUnderRestriction_idRestrGroupoid : ClosedUnderRestriction (@idRestrGroupoid H _) :=
  ⟨by
    rintro e ⟨s', hs', he⟩ s hs
    use s' ∩ s, hs'.inter hs
    refine Setoid.trans (OpenPartialHomeomorph.EqOnSource.restr he s) ?_
    exact ⟨by simp only [hs.interior_eq, mfld_simps], by simp only [mfld_simps, eqOn_refl]⟩⟩

/-- A groupoid is closed under restriction if and only if it contains the trivial restriction-closed
groupoid. -/
theorem closedUnderRestriction_iff_id_le (G : StructureGroupoid H) :
    ClosedUnderRestriction G ↔ idRestrGroupoid ≤ G := by
  constructor
  · intro _i
    rw [StructureGroupoid.le_iff]
    rintro e ⟨s, hs, hes⟩
    refine G.mem_of_eqOnSource ?_ hes
    convert closedUnderRestriction' G.id_mem hs
    ext <;> simp [hs.interior_eq]
  · intro h
    constructor
    intro e he s hs
    rw [← ofSet_trans (e : OpenPartialHomeomorph H H) hs]
    refine G.trans ?_ he
    apply StructureGroupoid.le_iff.mp h
    exact idRestrGroupoid_mem hs

/-- The groupoid of all open partial homeomorphisms on a topological space `H`
is closed under restriction. -/
instance : ClosedUnderRestriction (continuousGroupoid H) :=
  (closedUnderRestriction_iff_id_le _).mpr le_top

end Groupoid
