/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.GroupTheory.Commensurable
public import Mathlib.GroupTheory.DoubleCoset

/-!
# Hecke rings: definitions

The abstract Hecke ring of a *Hecke pair* `(H, Δ)`, following [Shimura][shimura1971], Chapter 3,
and [Krieg][krieg1990], Chapter I. This file sets up the underlying types: the Hecke pair, the
double-coset quotient that indexes the ring, and the Hecke ring itself as formal
finitely-supported linear combinations of double cosets. The convolution product and the ring
structure are developed in later files.

The relevance of the submonoid `Δ` may not be immediately obvious; a natural example is
`H = GL₂(ℤ)` inside `G = GL₂(ℚ)` with `Δ` the submonoid of integral matrices with nonzero
determinant, which is the Hecke pair underlying the classical Hecke operators `T_n`.

## Main definitions

* `HeckePair G`: a Hecke pair, a subgroup `H` together with a submonoid `Δ` of `G`
  satisfying `H ≤ Δ ≤ commensurator H`.
* `HeckeCoset P`: the quotient of `Δ` by the relation `HgH = HhH`, i.e. the double cosets
  `H\Δ/H` forming the basis of the Hecke ring.
* `HeckeRing P Z`, notation `𝕋 P Z`: the Hecke ring with coefficients in `Z`, the
  finitely-supported `Z`-linear combinations of double cosets.

## Implementation notes

`HeckePair` is a bundled structure rather than an unbundled pair with an `IsHeckePair` Prop
class: the types `HeckeCoset P` and `𝕋 P Z` depend on the pair, and types depending on instance
arguments are brittle. Requiring `Δ` to be a submonoid rather than a subsemigroup loses no
generality, since `H ≤ Δ` already forces `1 ∈ Δ`.

The combinatorial layer behind the Hecke product (Shimura's multiplicity) is developed for
mixed double cosets `Γ₁gΓ₂` of arbitrary subgroups in later files; only the ring structure
itself is specific to a Hecke pair.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971]
* [A. Krieg, *Hecke algebras*][krieg1990]
-/

@[expose] public section

open Subgroup.Commensurable

variable {G : Type*} [Group G]

/-- A Hecke pair `(H, Δ)`: a subgroup `H` and a submonoid `Δ` of a group `G` satisfying
`H ≤ Δ ≤ commensurator H`. -/
@[ext]
structure HeckePair (G : Type*) [Group G] where
  /-- The subgroup `H` of the pair. -/
  H : Subgroup G
  /-- The submonoid `Δ` of elements commensurating `H`. -/
  Δ : Submonoid G
  /-- The subgroup `H` is contained in `Δ`. -/
  subgroup_le : H.toSubmonoid ≤ Δ
  /-- The submonoid `Δ` lies in the commensurator of `H`. -/
  le_commensurator : Δ ≤ (commensurator H).toSubmonoid

/-- The setoid on `Δ` identifying elements with the same double coset `HgH = HhH`, pulled back
from `DoubleCoset.setoid` along the inclusion `Δ ↪ G`.

This is a `def` rather than a global instance to avoid a `Setoid` diamond on `↥Δ` (the left-coset
setoid is another). Files that form `HeckeCoset`s opt in with `attribute [local instance]`; it is
marked `@[reducible]` so that opt-in is warning-free. -/
@[reducible] def HeckePair.doubleCosetSetoid (P : HeckePair G) : Setoid P.Δ :=
  (DoubleCoset.setoid (P.H : Set G) P.H).comap Subtype.val

/-- A Hecke double coset: an equivalence class of `Δ`-elements under `HgH = HhH`. This is the
basis type for the Hecke ring. -/
def HeckeCoset (P : HeckePair G) := Quotient P.doubleCosetSetoid

namespace HeckeCoset

variable (P : HeckePair G)

/-- The identity double coset `H1H = H`. -/
instance : One (HeckeCoset P) := ⟨Quotient.mk P.doubleCosetSetoid ⟨1, P.Δ.one_mem⟩⟩

instance : Inhabited (HeckeCoset P) := ⟨1⟩

lemma one_def : (1 : HeckeCoset P) = Quotient.mk P.doubleCosetSetoid ⟨1, P.Δ.one_mem⟩ := rfl

end HeckeCoset

/-- The Hecke ring with coefficients in `Z`, denoted `𝕋 P Z`: the finitely-supported `Z`-linear
combinations of double cosets. The coefficients `Z` need only carry a `Zero` for the type to make
sense; algebraic structure is added by the instances below at the weakest level each requires. -/
def HeckeRing (P : HeckePair G) (Z : Type*) [Zero Z] := HeckeCoset P →₀ Z

namespace HeckeRing

@[inherit_doc]
scoped notation "𝕋" => HeckeRing

variable (P : HeckePair G) (Z : Type*)

/-- Elements of `𝕋 P Z` are functions `HeckeCoset P → Z` (finitely supported). -/
instance [Zero Z] : FunLike (𝕋 P Z) (HeckeCoset P) Z :=
  inferInstanceAs (FunLike (HeckeCoset P →₀ Z) (HeckeCoset P) Z)

noncomputable instance [AddCommMonoid Z] : AddCommMonoid (𝕋 P Z) :=
  inferInstanceAs (AddCommMonoid (HeckeCoset P →₀ Z))

noncomputable instance [AddCommGroup Z] : AddCommGroup (𝕋 P Z) :=
  inferInstanceAs (AddCommGroup (HeckeCoset P →₀ Z))

@[ext]
lemma ext {P : HeckePair G} {Z : Type*} [Zero Z] {f g : 𝕋 P Z} (h : ∀ D, f D = g D) : f = g :=
  Finsupp.ext h

end HeckeRing
