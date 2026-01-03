/-
Copyright (c) 2025 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module

public import Mathlib.Order.PFilter
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Ideal Filters

An **ideal filter** is a filter in the lattice of ideals of a ring `A`.

## Main definitions

* `IdealFilter A`: the type of an ideal filter on a ring `A`.
* `IsUniform F` : a filter `F` is uniform if whenever `I` is an ideal in the filter, then for all
  `a : A`, the left ideal `{x | x * a ∈ I}` belongs to `F`.
* `IsTorsionElem` : Given a filter `F`, an element, `m`, of an `A`-module, `M`, is `F`-torsion if
  there exists an ideal `L` in `F` that annihilates `m`.
* `IsTorsion` : Given a filter `F`, an `A`-module, `M`, is `F`-torsion if every element is torsion.
* `gabrielComposition` : Given two filters `F` and `G`, the Gabriel composition of `F` and `G` is
  the set of ideals `L` of `A` such that there exists an ideal `K` in `G` with `K/L` `F`-torsion.
  This is again a filter.
* `IsGabriel F` : a filter `F` is a Gabriel filter if it is uniform and satisfies axiom T4:
  for all `I : Ideal A`, if there exists `J ∈ F` such that for all `a ∈ J` the left ideal
  `{x | x * a ∈ I}` is in `F`, then `I ∈ F`.

## Main statements

* `isGabriel_iff`: a filter is Gabriel iff it is uniform and `F • F = F`.

## Notation

* `F • G`: the Gabriel composition of ideal filters `F` and `G`, defined by
  `gabrielComposition F G`.

## Implementation notes

In the classical literature (e.g. Stenström), *right linear topologies* on a ring are often
described via filters of open **right** ideals, and the terminology is frequently abused by
identifying the topology with its filter of ideals.

In this development we work systematically with **left ideals**. Accordingly, Stenström’s
right-ideal construction `(L : x) = {a ∈ A | x * a ∈ L}` is replaced by the left ideal
`{a | a * x ∈ L}`, implemented using preimages under right multiplication.

With this convention, uniform filters correspond to linear (additive) topologies, while the
additional Gabriel condition (axiom T4) imposes an algebraic saturation property that does not
change the induced topology.

## References

* [Bo Stenström, Rings and Modules of Quotients][stenstrom1971]
* [Bo Stenström, Rings of Quotients][stenstrom1975]
* [nLab: Uniform filter](https://ncatlab.org/nlab/show/uniform+filter)
* [nLab: Gabriel filter](https://ncatlab.org/nlab/show/Gabriel+filter)
* [nLab: Gabriel composition](https://ncatlab.org/nlab/show/Gabriel+composition+of+filters)

## Tags

ring theory, ideal, filter, uniform filter, Gabriel filter, torsion theory
-/

@[expose] public section

open scoped Pointwise

universe u v

/-- `IdealFilter A` is the type of `Order.PFilter`s on the lattice of ideals of `A`. -/
abbrev IdealFilter (A : Type u) [Ring A] := Order.PFilter (Ideal A)

namespace IdealFilter

variable {A : Type u} [Ring A]

/-- The left ideal `{x | x * a ∈ I}`, i.e. the preimage of `I` under right multiplication by `a`. -/
def comap_mulRight (I : Ideal A) (a : A) :
    Ideal A := Submodule.comap (LinearMap.mulRight A a) I

lemma mem_comap_mulRight (I : Ideal A) (a x : A) :
    x ∈ comap_mulRight I a ↔ x * a ∈ I := Iff.of_eq rfl

/-- A filter of ideals is *uniform* if for every `I ∈ F` and `a : A`, `{x ∈ A | x * a ∈ I} ∈ F`. -/
structure IsUniform (F : IdealFilter A) : Prop where
  /-- If `I ∈ F`, then for every `a : A`, so is the left ideal `{x ∈ A | x * a ∈ I}`. -/
  comap_mul_right_closed {I : Ideal A} (h_I : I ∈ F) (a : A) :
    comap_mulRight I a ∈ F

namespace IsUniform

/-- Convenience lemma for `comap_mul_right_closed`. -/
lemma comap_mulRight_mem {F : IdealFilter A} (h : F.IsUniform) {I : Ideal A} (h_I : I ∈ F) (a : A) :
    comap_mulRight I a ∈ F :=
  h.comap_mul_right_closed h_I a

end IsUniform

/-- We say that an element `m : M` is `F`-torsion if it is annihilated by some ideal belonging to
the filter `F`.  That is, there exists `L ∈ F` such that every `a ∈ L` satisfies
`a • m = 0`. -/
def IsTorsionElem (F : IdealFilter A)
    {M : Type v} [AddCommMonoid M] [Module A M] (m : M) : Prop :=
  ∃ L ∈ F, ∀ a ∈ L, a • m = 0

/-- We say that an `A`-module `M` is `F`-torsion if every element of `M` is `F`-torsion in the
sense of `IsTorsionElem`. -/
def IsTorsion (F : IdealFilter A)
    (M : Type v) [AddCommMonoid M] [Module A M] : Prop :=
  ∀ m : M, IsTorsionElem F m

/-- We say that the quotient `K/L` is `F`-torsion if every element `k ∈ K` is annihilated
(modulo `L`) by some ideal in `F`.  Equivalently, for each `k ∈ K` there exists `I ∈ F`
such that `I ≤ comap_mulRight L k`. That is to say, every `a ∈ I` satisfies `a * k ∈ L`.
This formulation avoids forming the quotient module explicitly. -/
def IsTorsionQuot (F : IdealFilter A) (L K : Ideal A) : Prop :=
  ∀ k ∈ K, ∃ I ∈ F, I ≤ comap_mulRight L k

/-- Intersecting the left ideal with `K` does not change `IsTorsionQuot` on the right. -/
lemma isTorsionQuot_inf_left_iff (F : IdealFilter A) (L K : Ideal A) :
    IsTorsionQuot F (L ⊓ K) K ↔ IsTorsionQuot F L K := by
  constructor
  · intro h k h_k
    rcases h k h_k with ⟨I, h_I, h_I_le⟩
    refine ⟨I, h_I, ?_⟩
    intro x h_x
    exact ((mem_comap_mulRight (L ⊓ K) k x).mp (h_I_le h_x)).left
  · intro h k h_k
    rcases h k h_k with ⟨I, h_I, h_I_le⟩
    refine ⟨I, h_I, ?_⟩
    intro x h_x
    exact ⟨(Submodule.mem_carrier L).mp (h_I_le h_x), Ideal.mul_mem_left K x h_k⟩

/-- Unfolding lemma for `IsTorsion`. -/
lemma isTorsion_def (F : IdealFilter A) (M : Type v) [AddCommMonoid M] [Module A M] :
    IsTorsion F M ↔ ∀ m : M, IsTorsionElem F m := Iff.rfl

/-- Unfolding lemma for `IsTorsionQuot`. -/
lemma isTorsionQuot_def (F : IdealFilter A) (L K : Ideal A) :
    IsTorsionQuot F L K ↔ ∀ k ∈ (K : Set A), ∃ I ∈ F, I ≤ comap_mulRight L k :=
  Iff.rfl

/-- For any filter `F` and ideal `I`, the quotient `I/I` is `F`-torsion in the sense of
`IsTorsionQuot`. -/
lemma isTorsionQuot_self (F : IdealFilter A) (I : Ideal A) :
    IsTorsionQuot F I I := by
  intro x h_x
  obtain ⟨J, h_J⟩ := F.nonempty
  refine ⟨J, h_J, ?_⟩
  intro y h_y
  rw[mem_comap_mulRight]
  exact Ideal.mul_mem_left I y h_x

/-- Monotonicity in the left ideal for `IsTorsionQuot`. -/
lemma IsTorsionQuot.mono_left {F : IdealFilter A}
    {I J K : Ideal A} (I_tors : IsTorsionQuot F I K) (I_leq_J : I ≤ J) : IsTorsionQuot F J K := by
  intro x h_x
  obtain ⟨L, ⟨L_in_F, h_L⟩⟩ := I_tors x h_x
  refine ⟨L, L_in_F, ?_⟩
  intro y h_y
  exact (mem_comap_mulRight J x y).mpr (I_leq_J (h_L h_y))

/-- `isPFilter_gabrielComposition` shows that the set defining `gabrielComposition` is a
`PFilter`. -/
lemma isPFilter_gabrielComposition (F G : IdealFilter A) :
    Order.IsPFilter {L : Ideal A | ∃ K ∈ G, F.IsTorsionQuot L K} := by
  refine Order.IsPFilter.of_def ?nonempty ?directed ?mem_of_le
  · obtain ⟨J, h_J⟩ := G.nonempty
    exact ⟨J, J, h_J, isTorsionQuot_self F J⟩
  · rintro I ⟨K, h_K, h_IK⟩ J ⟨L, h_L, h_JL⟩
    refine ⟨I ⊓ J, ?_, inf_le_left, inf_le_right⟩
    · refine ⟨K ⊓ L, ?_, ?_⟩
      · exact Order.PFilter.inf_mem h_K h_L
      · rintro x h_x
        rcases h_x with ⟨x_K, x_L⟩
        obtain ⟨K₁, h_K₁F, h_K₁⟩ := h_IK x x_K
        obtain ⟨K₂, h_K₂F, h_K₂⟩ := h_JL x x_L
        refine ⟨K₁ ⊓ K₂, Order.PFilter.inf_mem h_K₁F h_K₂F, ?_⟩
        rintro y ⟨h_y₁, h_y₂⟩
        rw[mem_comap_mulRight]
        exact ⟨(Submodule.mem_carrier I).mp (h_K₁ h_y₁), (Submodule.mem_carrier J).mp (h_K₂ h_y₂)⟩
  · intro I J h_IJ ⟨K, h_K, h_IK⟩
    exact ⟨K, h_K, h_IK.mono_left h_IJ⟩

/-- `gabrielComposition F G` is the Gabriel composition of ideal filters `F` and `G`. -/
def gabrielComposition (F G : IdealFilter A) : IdealFilter A :=
  (isPFilter_gabrielComposition F G).toPFilter

/-- `F • G` is the Gabriel composition of ideal filters `F` and `G`. -/
infixl:70 " • " => gabrielComposition

/-- A *Gabriel filter* is a filter satisfying `IsUniform` and axiom T4. -/
structure IsGabriel (F : IdealFilter A) extends F.IsUniform where
  /-- **Axiom T4 (Gabriel condition).** If there exists `J ∈ F` such that for all `x ∈ J`,
  the left ideal `comap_mulRight I x` belongs to `F`, then `I ∈ F`. -/
  gabriel_closed (I : Ideal A) (h : ∃ J ∈ F, ∀ x ∈ J, comap_mulRight I x ∈ F) : I ∈ F

/-- Characterization of Gabriel filters via `IsUniform` and idempotence of
`gabrielComposition`. -/
theorem isGabriel_iff (F : IdealFilter A) : F.IsGabriel ↔ F.IsUniform ∧ F • F = F := by
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨h₁, ?_⟩
    ext I
    constructor <;> intro h_I
    · rcases h_I with ⟨J,h_J, h_tors⟩
      unfold IsTorsionQuot at h_tors
      refine h₂ I ⟨J, h_J, ?_⟩
      intro x h_x
      rcases h_tors x h_x with ⟨K, h_K, h_incl⟩
      exact Order.PFilter.mem_of_le h_incl h_K
    · exact ⟨I, h_I, isTorsionQuot_self F I⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨h₁, ?_⟩
    rintro I ⟨J, h_J, h⟩
    rw [← h₂]
    refine ⟨J, h_J, ?_⟩
    intro x h_x
    refine ⟨comap_mulRight I x, ?_, ?_⟩
    · exact Order.PFilter.mem_of_mem_of_le (h x h_x) fun _ a ↦ a
    · exact Submodule.toAddSubmonoid_le.mp fun _ a ↦ a

end IdealFilter
