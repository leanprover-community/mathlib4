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

The abstract Hecke ring of a *Hecke pair* `(H, Δ)` and, more generally, the Hecke coset modules
attached to a triple `(H₁, Δ, H₂)`, following [Shimura][shimura1971], Chapter 3, and
[Krieg][krieg1990], Chapter I. This file sets up the underlying types: the compatibility
conditions `IsHeckeCosetModule Δ H₁ H₂` on a submonoid `Δ` and a pair of subgroups, the
double-coset quotient `HeckeCoset Δ H₁ H₂` of `Δ` by `H₁gH₂ = H₁hH₂`, and the Hecke coset module
`𝕋 Δ H₁ H₂ Z` of formal finitely-supported linear combinations of double cosets. The convolution
product `𝕋 Δ H₁ H₂ Z × 𝕋 Δ H₂ H₃ Z → 𝕋 Δ H₁ H₃ Z` and the ring structure on the diagonal
`𝕋 Δ H H Z` are developed in later files.

The relevance of the submonoid `Δ` may not be immediately obvious; a natural example is
`H = GL₂(ℤ)` inside `G = GL₂(ℚ)` with `Δ` the submonoid of integral matrices with nonzero
determinant, which is the Hecke pair underlying the classical Hecke operators `T_n`. Mixed
subgroups `H₁ ≠ H₂` arise for Hecke operators between different levels, e.g. `H₁ = Γ₀(N)` and
`H₂ = Γ₀(M)` inside the same `Δ`.

## Main definitions

* `IsHeckeCosetModule Δ H₁ H₂`: the compatibility conditions `H₁ ≤ Δ`, `H₂ ≤ Δ`,
  `Commensurable H₁ H₂` and `Δ ≤ commensurator H₂` making the double cosets `H₁\Δ/H₂` finite
  unions of left cosets. The classical Hecke pair `(H, Δ)` is the diagonal case
  `IsHeckeCosetModule Δ H H`.
* `HeckeCoset Δ H₁ H₂`: the quotient of `Δ` by the relation `H₁gH₂ = H₁hH₂`, i.e. the double
  cosets `H₁\Δ/H₂` forming the basis of the Hecke coset module.
* `HeckeCosetModule Δ H₁ H₂ Z`, notation `𝕋 Δ H₁ H₂ Z`: the Hecke coset module with
  coefficients in `Z`, the finitely-supported `Z`-linear combinations of double cosets. For
  `H₁ = H₂` this is the underlying module of the Hecke ring.

## Implementation notes

The data `(Δ, H₁, H₂)` enters unbundled, with the compatibility conditions collected in the
Prop-valued class `IsHeckeCosetModule`: the types `HeckeCoset Δ H₁ H₂` and `𝕋 Δ H₁ H₂ Z` are
built from the data alone and depend on no proofs, and a single ambient `Δ` shared by all levels
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

variable {G : Type*} [Group G]

/-- The compatibility conditions on a submonoid `Δ` and a pair of subgroups `H₁, H₂` of `G`
making the double cosets `H₁\Δ/H₂` finite unions of left cosets: both subgroups are contained
in `Δ`, they are commensurable, and `Δ` commensurates them. The classical Hecke pair `(H, Δ)`
of [Shimura][shimura1971], Chapter 3, is the diagonal case `IsHeckeCosetModule Δ H H`. -/
class IsHeckeCosetModule (Δ : Submonoid G) (H₁ H₂ : Subgroup G) : Prop where
  /-- The left subgroup is contained in `Δ`. -/
  left_le : H₁.toSubmonoid ≤ Δ
  /-- The right subgroup is contained in `Δ`. -/
  right_le : H₂.toSubmonoid ≤ Δ
  /-- The two subgroups are commensurable. -/
  commensurable : Commensurable H₁ H₂
  /-- The submonoid `Δ` lies in the commensurator of the right subgroup (hence, the subgroups
  being commensurable, also in that of the left one; see `le_commensurator_left`). -/
  le_commensurator : Δ ≤ (commensurator H₂).toSubmonoid

namespace IsHeckeCosetModule

variable {Δ : Submonoid G} {H₁ H₂ H₃ : Subgroup G}

/-- A Hecke pair `(H, Δ)` with `H ≤ Δ ≤ commensurator H` is the diagonal case. -/
theorem of_diagonal {H : Subgroup G} (h : H.toSubmonoid ≤ Δ)
    (hc : Δ ≤ (commensurator H).toSubmonoid) : IsHeckeCosetModule Δ H H :=
  ⟨h, h, .refl H, hc⟩

/-- Elements of the left subgroup lie in `Δ`. The right subgroup is explicit, since it cannot
be inferred. -/
theorem mem_left (H₂ : Subgroup G) [IsHeckeCosetModule Δ H₁ H₂] {x : G} (hx : x ∈ H₁) : x ∈ Δ :=
  left_le (H₂ := H₂) hx

/-- Elements of the right subgroup lie in `Δ`. The left subgroup is explicit, since it cannot
be inferred. -/
theorem mem_right (H₁ : Subgroup G) [IsHeckeCosetModule Δ H₁ H₂] {x : G} (hx : x ∈ H₂) : x ∈ Δ :=
  right_le (H₁ := H₁) hx

/-- The submonoid `Δ` also lies in the commensurator of the left subgroup. -/
theorem le_commensurator_left [IsHeckeCosetModule Δ H₁ H₂] :
    Δ ≤ (commensurator H₁).toSubmonoid := by
  rw [Subgroup.Commensurable.eq (commensurable (Δ := Δ) (H₁ := H₁) (H₂ := H₂))]
  exact le_commensurator H₁

/-- The reversed datum `(H₂, Δ, H₁)`. Not an instance, since instance search would loop. -/
theorem symm [IsHeckeCosetModule Δ H₁ H₂] : IsHeckeCosetModule Δ H₂ H₁ :=
  ⟨right_le (H₁ := H₁), left_le (H₂ := H₂), (commensurable (Δ := Δ)).symm,
    le_commensurator_left (H₂ := H₂)⟩

/-- Hecke coset module data compose. Not an instance, since the middle subgroup cannot be
inferred from the goal. -/
theorem trans [IsHeckeCosetModule Δ H₁ H₂] [IsHeckeCosetModule Δ H₂ H₃] :
    IsHeckeCosetModule Δ H₁ H₃ :=
  ⟨left_le (H₂ := H₂), right_le (H₁ := H₂),
    (commensurable (Δ := Δ) (H₁ := H₁) (H₂ := H₂)).trans
      (commensurable (Δ := Δ) (H₁ := H₂) (H₂ := H₃)),
    le_commensurator (H₁ := H₂)⟩

/-- The left diagonal datum `(H₁, Δ, H₁)`. Not an instance, since `H₂` cannot be inferred. -/
theorem diag_left [IsHeckeCosetModule Δ H₁ H₂] : IsHeckeCosetModule Δ H₁ H₁ :=
  ⟨left_le (H₂ := H₂), left_le (H₂ := H₂), .refl H₁, le_commensurator_left (H₂ := H₂)⟩

/-- The right diagonal datum `(H₂, Δ, H₂)`. Not an instance, since `H₁` cannot be inferred. -/
theorem diag_right [IsHeckeCosetModule Δ H₁ H₂] : IsHeckeCosetModule Δ H₂ H₂ :=
  ⟨right_le (H₁ := H₁), right_le (H₁ := H₁), .refl H₂, le_commensurator (H₁ := H₁)⟩

end IsHeckeCosetModule

/-- The setoid on `Δ` identifying elements with the same double coset `H₁gH₂ = H₁hH₂`, pulled
back from `DoubleCoset.setoid` along the inclusion `Δ ↪ G`.

This is a `def` rather than a global instance: the subgroups `H₁, H₂` cannot be inferred from
the type `↥Δ`, so this cannot participate in instance search (and a global instance would also
create a `Setoid` diamond on `↥Δ` with the left-coset setoid). The quotient map is
`HeckeCoset.mk`. -/
@[reducible] def HeckeCoset.setoid (Δ : Submonoid G) (H₁ H₂ : Subgroup G) : Setoid Δ :=
  (DoubleCoset.setoid (H₁ : Set G) H₂).comap Subtype.val

/-- A Hecke double coset: an equivalence class of `Δ`-elements under `H₁gH₂ = H₁hH₂`. This is
the basis type for the Hecke coset module. -/
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

/-- The Hecke coset module with coefficients in `Z`, denoted `𝕋 Δ H₁ H₂ Z`: the
finitely-supported `Z`-linear combinations of double cosets `H₁\Δ/H₂`. For `H₁ = H₂` this is the
underlying module of the Hecke ring. The coefficients `Z` need only carry a `Zero` for the type
to make sense; algebraic structure is added by the instances below at the weakest level each
requires. -/
def HeckeCosetModule (Δ : Submonoid G) (H₁ H₂ : Subgroup G) (Z : Type*) [Zero Z] :=
  HeckeCoset Δ H₁ H₂ →₀ Z

namespace HeckeCosetModule

@[inherit_doc]
scoped notation "𝕋" => HeckeCosetModule

variable (Δ : Submonoid G) (H₁ H₂ : Subgroup G) (Z : Type*)

/-- Elements of `𝕋 Δ H₁ H₂ Z` are functions `HeckeCoset Δ H₁ H₂ → Z` (finitely supported). -/
instance [Zero Z] : FunLike (𝕋 Δ H₁ H₂ Z) (HeckeCoset Δ H₁ H₂) Z :=
  inferInstanceAs (FunLike (HeckeCoset Δ H₁ H₂ →₀ Z) (HeckeCoset Δ H₁ H₂) Z)

noncomputable instance [AddCommMonoid Z] : AddCommMonoid (𝕋 Δ H₁ H₂ Z) :=
  inferInstanceAs (AddCommMonoid (HeckeCoset Δ H₁ H₂ →₀ Z))

noncomputable instance [AddCommGroup Z] : AddCommGroup (𝕋 Δ H₁ H₂ Z) :=
  inferInstanceAs (AddCommGroup (HeckeCoset Δ H₁ H₂ →₀ Z))

@[ext]
lemma ext {Δ : Submonoid G} {H₁ H₂ : Subgroup G} {Z : Type*} [Zero Z] {f g : 𝕋 Δ H₁ H₂ Z}
    (h : ∀ D, f D = g D) : f = g :=
  Finsupp.ext h

end HeckeCosetModule
