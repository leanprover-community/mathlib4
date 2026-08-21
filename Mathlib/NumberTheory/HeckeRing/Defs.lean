/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.GroupTheory.Commensurable
public import Mathlib.GroupTheory.DoubleCoset

/-!
# Hecke rings: definitions

This file introduces the abstract Hecke ring of a *Hecke pair* `(H, Δ)` and, more generally, the
Hecke coset modules attached to a triple `(H₁, Δ, H₂)`, following [Shimura][shimura1971],
Chapter 3, and [Krieg][krieg1990], Chapter I. It sets up the underlying types: the compatibility
conditions `IsHeckeTriple Δ H₁ H₂` on a submonoid `Δ` of a group `G` and a pair of subgroups
of `G`, the double-coset quotient `HeckeCoset Δ H₁ H₂` of `Δ` by `H₁gH₂ = H₁hH₂`, and the Hecke
coset module `HeckeCosetModule Δ H₁ H₂ Z` of formal finitely-supported linear combinations of
double cosets.
The convolution product `HeckeCosetModule Δ H₁ H₂ Z × HeckeCosetModule Δ H₂ H₃ Z →
HeckeCosetModule Δ H₁ H₃ Z` and the ring structure on the diagonal Hecke ring `𝕋 Δ H Z` are
developed in later files.

The relevance of the submonoid `Δ` may not be immediately obvious; a natural example is
`H = GL₂(ℤ)` inside `G = GL₂(ℚ)` with `Δ` the submonoid of integral matrices with nonzero
determinant, which is the Hecke pair underlying the classical Hecke operators `T_n`. Mixed
subgroups `H₁ ≠ H₂` arise for Hecke operators between different levels, e.g. `H₁ = Γ₀(N)` and
`H₂ = Γ₀(M)` inside the same `Δ`.

## Main definitions

* `IsHeckeTriple Δ H₁ H₂`: `(H₁, Δ, H₂)` is a Hecke triple, i.e. `H₁ ≤ Δ`, `H₂ ≤ Δ`,
  `Commensurable H₁ H₂` and `Δ ≤ commensurator H₂`, making the double cosets `H₁\Δ/H₂` finite
  unions of left cosets. The classical Hecke pair `(H, Δ)` is the diagonal case
  `IsHeckeTriple Δ H H`.
* `HeckeCoset Δ H₁ H₂`: the quotient of `Δ` by the relation `H₁gH₂ = H₁hH₂`, i.e. the double
  cosets `H₁\Δ/H₂` forming the basis of the Hecke coset module.
* `HeckeCosetModule Δ H₁ H₂ Z`: the Hecke coset module with coefficients in `Z`, the
  finitely-supported `Z`-linear combinations of double cosets.
* `HeckeRing Δ H Z`, notation `𝕋 Δ H Z`: the Hecke ring, the diagonal case
  `HeckeCosetModule Δ H H Z` of the Hecke coset module.

## Implementation notes

The data `(Δ, H₁, H₂)` enters unbundled, with the compatibility conditions collected in the
Prop-valued class `IsHeckeTriple`: the types `HeckeCoset Δ H₁ H₂` and `HeckeCosetModule Δ H₁ H₂ Z`
are built from the data alone and depend on no proofs, and a single ambient `Δ` shared by all
levels
(as in [Shimura][shimura1971]) means products of double cosets over different subgroups,
`H₁g₁H₂ * H₂g₂H₃ ⊆ Δ`, need no compatibility hypotheses. The conditions are only needed for the
finiteness of the coset decompositions, which enters through the `Fintype` instance on
`DoubleCoset.DecompQuotient` in later files. Requiring `Δ` to be a submonoid rather than a
subsemigroup loses no generality, since `H₁ ≤ Δ` already forces `1 ∈ Δ`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971]
* [A. Krieg, *Hecke algebras*][krieg1990]
-/

@[expose] public section

open Subgroup Subgroup.Commensurable
open scoped Pointwise

variable {G : Type*} [Group G]

/-- A *Hecke triple* `(H₁, Δ, H₂)`: the compatibility conditions on a submonoid `Δ` and a pair
of subgroups `H₁, H₂` of `G` making the double cosets `H₁\Δ/H₂` finite unions of left cosets:
both subgroups are contained in `Δ`, they are commensurable, and `Δ` commensurates them. The
classical Hecke pair `(H, Δ)` of [Shimura][shimura1971], Chapter 3, is the diagonal case
`IsHeckeTriple Δ H H`. -/
class IsHeckeTriple (Δ : Submonoid G) (H₁ H₂ : Subgroup G) : Prop where
  /-- The left subgroup is contained in `Δ`. -/
  left_le : H₁.toSubmonoid ≤ Δ
  /-- The right subgroup is contained in `Δ`. -/
  right_le : H₂.toSubmonoid ≤ Δ
  /-- The two subgroups are commensurable. -/
  commensurable : Commensurable H₁ H₂
  /-- The submonoid `Δ` lies in the commensurator of the right subgroup (hence, the subgroups
  being commensurable, also in that of the left one; see `le_commensurator_left`). -/
  le_commensurator_right : Δ ≤ (commensurator H₂).toSubmonoid

namespace IsHeckeTriple

variable {Δ : Submonoid G} {H₁ H₂ H₃ : Subgroup G}

/-- The Hecke triple `(H, Δ, H)` coming from a pair `(H, Δ)` with `H ≤ Δ ≤ commensurator H`. -/
theorem of_diagonal {H : Subgroup G} (h : H.toSubmonoid ≤ Δ)
    (hc : Δ ≤ (commensurator H).toSubmonoid) : IsHeckeTriple Δ H H :=
  ⟨h, h, .refl H, hc⟩

/-- Elements of the left subgroup lie in `Δ`. -/
theorem mem_of_mem_left (H₂ : Subgroup G) [IsHeckeTriple Δ H₁ H₂] {x : G} (hx : x ∈ H₁) : x ∈ Δ :=
  left_le H₂ hx

/-- Elements of the right subgroup lie in `Δ`. -/
theorem mem_of_mem_right (H₁ : Subgroup G) [IsHeckeTriple Δ H₁ H₂] {x : G} (hx : x ∈ H₂) : x ∈ Δ :=
  right_le H₁ hx

/-- The submonoid `Δ` lies in the commensurator of the left subgroup. -/
theorem le_commensurator_left (H₂ : Subgroup G) [h : IsHeckeTriple Δ H₁ H₂] :
    Δ ≤ (commensurator H₁).toSubmonoid := by
  rw [h.commensurable.eq]
  exact h.le_commensurator_right

/-- Elements of `Δ` lie in the commensurator of the right subgroup. -/
theorem mem_commensurator_right (H₁ : Subgroup G) [IsHeckeTriple Δ H₁ H₂] (g : Δ) :
    (g : G) ∈ commensurator H₂ :=
  le_commensurator_right H₁ g.2

/-- Elements of `Δ` lie in the commensurator of the left subgroup. -/
theorem mem_commensurator_left (H₂ : Subgroup G) [IsHeckeTriple Δ H₁ H₂] (g : Δ) :
    (g : G) ∈ commensurator H₁ :=
  le_commensurator_left H₂ g.2

/-- Conjugating the right subgroup of a Hecke triple `(H₁, Δ, H₂)` by an element of `Δ` gives a
subgroup commensurable with the left one. -/
theorem commensurable_conjAct_right [IsHeckeTriple Δ H₁ H₂] (g : Δ) :
    Commensurable (ConjAct.toConjAct (g : G) • H₂) H₁ := by
  have hg : Commensurable (ConjAct.toConjAct (g : G) • H₂) H₂ := mem_commensurator_right H₁ g
  exact hg.trans (commensurable (Δ := Δ)).symm

/-- Hecke coset module data compose. Not an instance, since the middle subgroup cannot be
inferred from the goal. -/
theorem trans [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₃] :
    IsHeckeTriple Δ H₁ H₃ :=
  ⟨left_le H₂, right_le H₂,
    (commensurable (Δ := Δ) (H₁ := H₁) (H₂ := H₂)).trans
      (commensurable (Δ := Δ) (H₁ := H₂) (H₂ := H₃)),
    le_commensurator_right H₂⟩

/-- The left diagonal datum `(H₁, Δ, H₁)`. Not an instance, since `H₂` cannot be inferred. -/
theorem diag_left [IsHeckeTriple Δ H₁ H₂] : IsHeckeTriple Δ H₁ H₁ :=
  ⟨left_le H₂, left_le H₂, .refl H₁, le_commensurator_left H₂⟩

/-- The right diagonal datum `(H₂, Δ, H₂)`. Not an instance, since `H₁` cannot be inferred. -/
theorem diag_right [IsHeckeTriple Δ H₁ H₂] : IsHeckeTriple Δ H₂ H₂ :=
  ⟨right_le H₁, right_le H₁, .refl H₂, le_commensurator_right H₁⟩

end IsHeckeTriple

/-- The setoid on `Δ` identifying elements with the same double coset `H₁gH₂ = H₁hH₂`, pulled
back from `DoubleCoset.setoid` along the inclusion `Δ ↪ G`.

This is an `abbrev` rather than a global instance: the subgroups `H₁, H₂` cannot be inferred
from the submonoid `Δ`, so this cannot participate in instance search (and a global instance
would also create a `Setoid` diamond on `↥Δ` with the left-coset setoid). The quotient map is
`HeckeCoset.mk`. -/
abbrev HeckeCoset.setoid (Δ : Submonoid G) (H₁ H₂ : Subgroup G) : Setoid Δ :=
  (DoubleCoset.setoid (H₁ : Set G) H₂).comap Subtype.val

/-- A Hecke double coset: an equivalence class of `Δ`-elements under `H₁gH₂ = H₁hH₂`. This is
the basis type for the `HeckeCosetModule`. -/
def HeckeCoset (Δ : Submonoid G) (H₁ H₂ : Subgroup G) := Quotient (HeckeCoset.setoid Δ H₁ H₂)

namespace HeckeCoset

variable {Δ : Submonoid G}

/-- The double coset `H₁gH₂` of an element `g : Δ`. -/
def mk (H₁ H₂ : Subgroup G) (g : Δ) : HeckeCoset Δ H₁ H₂ :=
  Quotient.mk (setoid Δ H₁ H₂) g

variable (Δ) in
instance (H₁ H₂ : Subgroup G) : Inhabited (HeckeCoset Δ H₁ H₂) := ⟨mk H₁ H₂ ⟨1, Δ.one_mem⟩⟩

variable (Δ) in
/-- The identity double coset `H1H = H` of the diagonal (Hecke pair) case. -/
instance (H : Subgroup G) : One (HeckeCoset Δ H H) := ⟨mk H H ⟨1, Δ.one_mem⟩⟩

lemma one_def (H : Subgroup G) : (1 : HeckeCoset Δ H H) = mk H H ⟨1, Δ.one_mem⟩ := rfl

end HeckeCoset

/-- The Hecke coset module with coefficients in `Z`: the finitely-supported `Z`-linear
combinations of double cosets `H₁\Δ/H₂`. For `H₁ = H₂` this is the underlying module of the
Hecke ring `𝕋 Δ H Z` (see `HeckeRing`). The coefficients `Z` need only carry a `Zero` for the
type to make sense; algebraic structure is added by the instances below at the weakest level each
requires. -/
def HeckeCosetModule (Δ : Submonoid G) (H₁ H₂ : Subgroup G) (Z : Type*) [Zero Z] :=
  HeckeCoset Δ H₁ H₂ →₀ Z

/-- The Hecke ring `𝕋 Δ H Z` with coefficients in `Z`: the diagonal Hecke coset module
`HeckeCosetModule Δ H H Z`, the finitely-supported `Z`-linear combinations of double cosets
`H\Δ/H`. The convolution product making it a ring is developed in later files. -/
abbrev HeckeRing (Δ : Submonoid G) (H : Subgroup G) (Z : Type*) [Zero Z] :=
  HeckeCosetModule Δ H H Z

@[inherit_doc]
scoped[HeckeCosetModule] notation "𝕋" => HeckeRing

namespace HeckeCosetModule

variable (Δ : Submonoid G) (H₁ H₂ : Subgroup G) (Z : Type*)

/-- Elements of `HeckeCosetModule Δ H₁ H₂ Z` are functions `HeckeCoset Δ H₁ H₂ → Z` (finitely
supported). -/
instance [Zero Z] : FunLike (HeckeCosetModule Δ H₁ H₂ Z) (HeckeCoset Δ H₁ H₂) Z :=
  inferInstanceAs (FunLike (HeckeCoset Δ H₁ H₂ →₀ Z) (HeckeCoset Δ H₁ H₂) Z)

noncomputable instance [AddCommMonoid Z] : AddCommMonoid (HeckeCosetModule Δ H₁ H₂ Z) :=
  inferInstanceAs (AddCommMonoid (HeckeCoset Δ H₁ H₂ →₀ Z))

noncomputable instance [AddCommGroup Z] : AddCommGroup (HeckeCosetModule Δ H₁ H₂ Z) :=
  inferInstanceAs (AddCommGroup (HeckeCoset Δ H₁ H₂ →₀ Z))

/-- The sanctioned constructor of `HeckeCosetModule Δ H₁ H₂ Z` from a finitely-supported function
on double cosets. Build elements through `of` rather than relying on the definitional unfolding
`HeckeCosetModule Δ H₁ H₂ Z = (HeckeCoset Δ H₁ H₂ →₀ Z)`. -/
def of {Δ : Submonoid G} {H₁ H₂ : Subgroup G} {Z : Type*} [Zero Z] :
    (HeckeCoset Δ H₁ H₂ →₀ Z) ≃ HeckeCosetModule Δ H₁ H₂ Z :=
  Equiv.refl _

@[simp]
lemma of_apply {Δ : Submonoid G} {H₁ H₂ : Subgroup G} {Z : Type*} [Zero Z]
    (f : HeckeCoset Δ H₁ H₂ →₀ Z) (D : HeckeCoset Δ H₁ H₂) : of f D = f D :=
  rfl

@[ext]
lemma ext {Δ : Submonoid G} {H₁ H₂ : Subgroup G} {Z : Type*} [Zero Z]
    {f g : HeckeCosetModule Δ H₁ H₂ Z} (h : ∀ D, f D = g D) : f = g :=
  Finsupp.ext h

end HeckeCosetModule
