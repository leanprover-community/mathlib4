/-
Copyright (c) 2025 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module

public import Mathlib.Order.PFilter
public import Mathlib.RingTheory.Ideal.Colon

/-!
# Ideal Filters

An **ideal filter** is a filter in the lattice of ideals of a ring `A`.

## Main definitions

* `IdealFilter A`: the type of an ideal filter on a ring `A`.
* `IsUniform F` : a filter `F` is uniform if whenever `I` is an ideal in the filter, then for all
  `a : A`, the colon ideal `I.colon {a}` is in `F`.
* `IsTorsionElem` : Given a filter `F`, an element, `m`, of an `A`-module, `M`, is `F`-torsion if
  there exists an ideal `L` in `F` that annihilates `m`.
* `IsTorsion` : Given a filter `F`, an `A`-module, `M`, is `F`-torsion if every element is torsion.
* `gabrielComposition` : Given two filters `F` and `G`, the Gabriel composition of `F` and `G` is
  the set of ideals `L` of `A` such that there exists an ideal `K` in `G` with `K/L` `F`-torsion.
  This is again a filter.
* `IsGabriel F` : a filter `F` is a Gabriel filter if it is uniform and satisfies axiom T4:
  for all `I : Ideal A`, if there exists `J ∈ F` such that for all `a ∈ J` the colon ideal
  `I.colon {a}` is in `F`, then `I ∈ F`.

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
right-ideal construction `(L : a) = {x ∈ A | a * x ∈ L}` is replaced by the left ideal
`L.colon {a} = {a | x * a ∈ L}`, implemented using preimages under right multiplication.

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

/-- A filter of ideals is *uniform* if it is closed under colon by principal ideals. -/
structure IsUniform (F : IdealFilter A) : Prop where
  /-- If `I ∈ F`, then for every `a : A` the colon ideal `I.colon {a}`
  also belongs to `F`. -/
  colon_closed {I : Ideal A} (h_I : I ∈ F) (a : A) : (I.colon {a}) ∈ F

namespace IsUniform

/-- Convenience lemma for `colon_closed`. -/
lemma colon_mem {F : IdealFilter A} (h : F.IsUniform) {I : Ideal A} (h_I : I ∈ F) (a : A) :
    I.colon {a} ∈ F :=
  h.colon_closed h_I a

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
such that `I ≤ L.colon {k}`. That is to say, every `a ∈ I` satisfies `a * k ∈ L`.
This formulation avoids forming the quotient module explicitly. -/
def IsTorsionQuot (F : IdealFilter A) (L K : Ideal A) : Prop :=
  ∀ k ∈ K, ∃ I ∈ F, I ≤ L.colon {k}

/-- Intersecting the left ideal with `K` does not change `IsTorsionQuot` on the right. -/
lemma isTorsionQuot_inter_left_iff (F : IdealFilter A) (L K : Ideal A) :
    IsTorsionQuot F L K ↔ IsTorsionQuot F (L ⊓ K) K := by
  unfold IsTorsionQuot
  constructor <;>
  · intro h k h_k
    rcases h k h_k with ⟨I, h_I, h_I_le⟩
    have hcol : (L ⊓ K).colon {k} = Submodule.colon L {k} :=
      Submodule.colon_inf_eq_left_of_subset (Set.singleton_subset_iff.mpr h_k)
    exact ⟨I, h_I, (by simpa [hcol] using h_I_le)⟩

/-- Unfolding lemma for `IsTorsion`. -/
@[simp] lemma isTorsion_def (F : IdealFilter A) (M : Type v) [AddCommMonoid M] [Module A M] :
    IsTorsion F M ↔ ∀ m : M, IsTorsionElem F m :=
  Iff.rfl

/-- Unfolding lemma for `IsTorsionQuot`. -/
@[simp] lemma isTorsionQuot_def (F : IdealFilter A) (L K : Ideal A) :
    IsTorsionQuot F L K ↔ ∀ k ∈ (K : Set A), ∃ I ∈ F, I ≤ L.colon {k} :=
  Iff.rfl

/-- For any filter `F` and ideal `J`, the quotient `J/J` is `F`-torsion in the sense of
`IsTorsionQuot`. -/
lemma isTorsionQuot_self (F : IdealFilter A) (I : Ideal A) :
    IsTorsionQuot F I I := by
  intro x hx
  obtain ⟨J, h_J⟩ := F.nonempty
  exact ⟨J, h_J, le_of_le_of_eq le_top (by simpa [eq_comm])⟩


/-- Monotonicity in the left ideal for `IsTorsionQuot`. -/
lemma isTorsionQuot_mono_left (F : IdealFilter A)
    {I J K : Ideal A} (I_leq_J : I ≤ J) : IsTorsionQuot F I K → IsTorsionQuot F J K := by
  intro I_tors x h_x
  obtain ⟨L, ⟨L_in_F, h_L⟩⟩ := I_tors x h_x
  refine ⟨L, L_in_F, ?_⟩
  intro y h_y
  refine Submodule.mem_colon.mpr ?_
  intro a h_a
  exact I_leq_J (Submodule.mem_colon.mp (h_L h_y) a h_a)

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
        simpa using (⟨h_K₁ h_y₁, h_K₂ h_y₂⟩ : y ∈ I.colon {x} ⊓ J.colon {x})
  · intro I J h_IJ ⟨K, h_K, h_IK⟩
    exact ⟨K, h_K, isTorsionQuot_mono_left F h_IJ h_IK⟩

/-- `gabrielComposition F G` is the Gabriel composition of ideal filters `F` and `G`. -/
def gabrielComposition (F G : IdealFilter A) : IdealFilter A :=
  (isPFilter_gabrielComposition F G).toPFilter

/-- `F • G` is the Gabriel composition of ideal filters `F` and `G`. -/
scoped infixl:70 " • " => gabrielComposition

/-- A *Gabriel filter* is a filter satisfying `IsUniform` and axiom T4. -/
structure IsGabriel (F : IdealFilter A) extends F.IsUniform where
  /-- **Axiom T4 (Gabriel condition).** If there exists `J ∈ F` such that for all `x ∈ J`,
  the colon ideal `I.colon {x}` belongs to `F`, then `I ∈ F`. -/
  gabriel_closed (I : Ideal A) (h : ∃ J ∈ F, ∀ x ∈ J, I.colon {x} ∈ F) : I ∈ F

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
    rintro I ⟨J, h_J, h_colon⟩
    rw [← h₂]
    refine ⟨J, h_J, ?_⟩
    intro x h_x
    refine ⟨I.colon {x}, h_colon x h_x, by simp⟩

end IdealFilter
