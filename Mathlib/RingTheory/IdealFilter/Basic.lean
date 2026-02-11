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
`L.colon {a} = {a | x * a ∈ L}`.

With this convention, uniform filters correspond to linear (additive) topologies, while the
additional Gabriel condition (axiom T4) imposes an algebraic saturation property that does not
change the induced topology.

## References

* [Bo Stenström, *Rings and Modules of Quotients*][stenstrom1971]
* [Bo Stenström, *Rings of Quotients*][stenstrom1975]
* [nLab: Uniform filter](<https://ncatlab.org/nlab/show/uniform+filter>)
* [nLab: Gabriel filter](<https://ncatlab.org/nlab/show/Gabriel+filter>)
* [nLab: Gabriel composition](<https://ncatlab.org/nlab/show/Gabriel+composition+of+filters>)

## Tags

ring theory, ideal, filter, uniform filter, Gabriel filter, torsion theory
-/

@[expose] public section

open scoped Pointwise

/-- `IdealFilter A` is the type of `Order.PFilter`s on the lattice of ideals of `A`. -/
abbrev IdealFilter (A : Type*) [Ring A] := Order.PFilter (Ideal A)

namespace IdealFilter

variable {A : Type*} [Ring A]

/-- A filter of ideals is *uniform* if it is closed under colon by singletons. -/
class IsUniform (F : IdealFilter A) : Prop where
  /-- **Axiom T3.**  See [stenstrom1975]. -/
  colon_mem {I : Ideal A} (hI : I ∈ F) (a : A) : I.colon {a} ∈ F

/-- We say that an element `m : M` is `F`-torsion if it is annihilated by some ideal belonging to
the filter `F`. -/
def IsTorsionElem (F : IdealFilter A)
    {M : Type*} [AddCommMonoid M] [Module A M] (m : M) : Prop :=
  ∃ L ∈ F, ∀ a ∈ L, a • m = 0

/-- Module-level `F`-torsion: every element is `F`-torsion. -/
def IsTorsion (F : IdealFilter A)
    (M : Type*) [AddCommMonoid M] [Module A M] : Prop :=
  ∀ m : M, IsTorsionElem F m

/-- We say that the quotient `K/L` is `F`-torsion if every element `k ∈ K` is annihilated
(modulo `L`) by some ideal in `F`. Equivalently, for each `k ∈ K` there exists `I ∈ F`
such that `I ≤ L.colon {k}`. This formulation avoids forming the quotient module explicitly. -/
def IsTorsionQuot (F : IdealFilter A) (L K : Ideal A) : Prop :=
  ∀ k ∈ K, ∃ I ∈ F, I ≤ L.colon {k}

/-- Intersecting the left ideal with `K` does not change `IsTorsionQuot` on the right.
In particular, `IsTorsionQuot F L K` need not require `L ≤ K` for it is equivalent to asserting
the quotient `K / (L ⊓ K)` is `F`-torsion. -/
lemma isTorsionQuot_inter_left_iff {F : IdealFilter A} {L K : Ideal A} :
    IsTorsionQuot F (L ⊓ K) K ↔ IsTorsionQuot F L K := by
  constructor <;>
  · intro h k hk
    rcases h k hk with ⟨I, hI, hI_le⟩
    have hcol : (L ⊓ K).colon {k} = Submodule.colon L {k} :=
      Submodule.colon_inf_eq_left_of_subset (Set.singleton_subset_iff.mpr hk)
    exact ⟨I, hI, (by simpa [hcol] using hI_le)⟩


@[simp] lemma isTorsion_def (F : IdealFilter A) (M : Type*) [AddCommMonoid M] [Module A M] :
    IsTorsion F M ↔ ∀ m : M, IsTorsionElem F m :=
  Iff.rfl

@[simp] lemma isTorsionQuot_def {F : IdealFilter A} {L K : Ideal A} :
    IsTorsionQuot F L K ↔ ∀ k ∈ (K : Set A), ∃ I ∈ F, I ≤ L.colon {k} :=
  Iff.rfl

lemma isTorsionQuot_self (F : IdealFilter A) (I : Ideal A) :
    IsTorsionQuot F I I := by
  intro x hx
  obtain ⟨J, hJ⟩ := F.nonempty
  exact ⟨J, hJ, le_of_le_of_eq le_top (by simpa [eq_comm])⟩

lemma IsTorsionQuot.mono_left {F : IdealFilter A}
    {I J K : Ideal A} (hIJ : I ≤ J) (hIK : IsTorsionQuot F I K) : IsTorsionQuot F J K :=
  fun _ h ↦ (hIK _ h).imp fun _ ↦ And.imp_right (le_trans · (Submodule.colon_mono hIJ .rfl))

lemma IsTorsionQuot.anti_right {F : IdealFilter A}
    {I J K : Ideal A} (hJK : J ≤ K) (hIK : IsTorsionQuot F I K) : IsTorsionQuot F I J :=
  fun x hx ↦ hIK x (hJK hx)

lemma IsTorsionQuot.mono {F : IdealFilter A} {I J K L : Ideal A} (hIK : IsTorsionQuot F I K)
    (hIJ : I ≤ J) (hLK : L ≤ K) : IsTorsionQuot F J L :=
  (hIK.mono_left hIJ).anti_right hLK

lemma IsTorsionQuot.inf {F : IdealFilter A}
    {I J K : Ideal A} (hI : IsTorsionQuot F I K) (hJ : IsTorsionQuot F J K) :
    IsTorsionQuot F (I ⊓ J) K := by
  intro x hx
  obtain ⟨I', hI'F, hI'x⟩ := hI x hx
  obtain ⟨J', hJ'F, hJ'x⟩ := hJ x hx
  exact ⟨_, F.inf_mem hI'F hJ'F, (inf_le_inf hI'x hJ'x).trans Submodule.inf_colon.ge⟩

lemma isPFilter_gabrielComposition (F G : IdealFilter A) :
    Order.IsPFilter {L : Ideal A | ∃ K ∈ G, F.IsTorsionQuot L K} := by
  refine Order.IsPFilter.of_def ?nonempty ?directed ?mem_of_le
  · obtain ⟨J, hJ⟩ := G.nonempty
    exact ⟨J, J, hJ, isTorsionQuot_self F J⟩
  · rintro I ⟨K, hK, hIK⟩ J ⟨L, hL, hJL⟩
    refine ⟨I ⊓ J, ?_, inf_le_left, inf_le_right⟩
    exact ⟨K ⊓ L, G.inf_mem hK hL,
      (hIK.anti_right inf_le_left).inf (hJL.anti_right inf_le_right)⟩
  · intro I J hIJ ⟨K, hK, hIK⟩
    exact ⟨K, hK, hIK.mono_left hIJ⟩

/-- The Gabriel composition of ideal filters `F` and `G`.
See [nLab: Gabriel composition](<https://ncatlab.org/nlab/show/Gabriel+composition+of+filters>). -/
def gabrielComposition (F G : IdealFilter A) : IdealFilter A :=
  (isPFilter_gabrielComposition F G).toPFilter

/-- `F • G` is the Gabriel composition of ideal filters `F` and `G`. -/
scoped infixl:70 " • " => gabrielComposition

/-- An ideal filter is Gabriel if it satisfies `IsUniform` and axiom T4.
See [nLab: Gabriel filter](<https://ncatlab.org/nlab/show/Gabriel+filter>). -/
class IsGabriel (F : IdealFilter A) extends F.IsUniform where
  /-- **Axiom T4.** See [stenstrom1975]. -/
  gabriel_closed (I : Ideal A) (h : ∃ J ∈ F, ∀ x ∈ J, I.colon {x} ∈ F) : I ∈ F

/-- Characterization of Gabriel filters via `IsUniform` and idempotence of
`gabrielComposition`. -/
theorem isGabriel_iff (F : IdealFilter A) : F.IsGabriel ↔ F.IsUniform ∧ F • F = F := by
  constructor
  · intro hF
    refine ⟨hF.toIsUniform, ?_⟩
    ext I
    constructor <;> intro hI
    · rcases hI with ⟨J, hJ, htors⟩
      refine hF.gabriel_closed I ⟨J, hJ, fun x hx ↦ ?_⟩
      rcases htors x hx with ⟨K, hK, hincl⟩
      exact Order.PFilter.mem_of_le hincl hK
    · exact ⟨I, hI, isTorsionQuot_self F I⟩
  · rintro ⟨h₁, h₂⟩
    refine { toIsUniform := h₁, gabriel_closed := ?_ }
    rintro I ⟨J, hJ, hcolon⟩
    exact h₂.le ⟨J, hJ, fun x hx ↦ ⟨I.colon {x}, hcolon x hx, by simp⟩⟩

end IdealFilter
