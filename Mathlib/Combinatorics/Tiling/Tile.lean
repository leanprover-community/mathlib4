/-
Copyright (c) 2026 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Set.Finite
public import Mathlib.GroupTheory.Coset.Basic

/-!
# Tiles for tilings

This file defines some basic concepts related to individual tiles for tilings in a discrete context
(with definitions in a continuous context to be developed separately but analogously).

Work in the field of tilings does not generally try to define or state things in any kind of maximal
generality, so it is necessary to adapt definitions and statements from the literature to produce
something that seems appropriately general for mathlib, covering a wide range of tiling-related
concepts found in the literature. Nevertheless, further generalization may prove of use as this work
is extended in future.

We work in the context of a space `X` acted on by a group `G`; the action is not required to be
faithful, although typically it is. In a discrete context, tiles are expected to cover the space, or
a subset of it being tiled when working with tilings not of the whole space, and the tiles are
pairwise disjoint. In a continuous context, definitions in the literature vary; the tiles may be
closed and cover the space with interiors required to be disjoint (as used by Grünbaum and Shephard
or Goodman-Strauss), or they may be required to be measurable and to partition it up to null sets
(as used by Greenfeld and Tao).

In general we are concerned not with a tiling in isolation but with tilings by some protoset of
tiles; thus we make definitions in the context of such a protoset, where copies of the tiles in the
tiling must be images of those tiles under the action of an element of the given group.

Where there are matching rules that say what combinations of tiles are considered as valid, these
are provided as separate hypotheses where required. Tiles in a protoset are commonly considered in
the literature to be marked in some way. When this is simply to distinguish two otherwise identical
tiles, this is represented by the use of different indices in the protoset. When this is to give a
tile fewer symmetries than it would otherwise have under the action of the given group, this is
represented by the symmetries specified in the `Prototile` being less than its full stabilizer.

The group `G` is throughout here a multiplicative group. Additive groups are also used in the
literature, typically when based on `ℤ`; to support the use of additive groups, `to_additive` could
be used with the theory here.

## Main definitions

* `Prototile G X`: A prototile in `X` as acted on by `G`, carrying the information of a subgroup of
  the stabilizer that says when two copies of the prototile are considered the same.

* `Protoset G X ιₚ`: An indexed family of prototiles.

* `PlacedTile ps`: An image of a tile in the protoset `ps`.

## References

* [Branko Grünbaum and G. C. Shephard, *Tilings and Patterns*][GrunbaumShephard1987]
* [Chaim Goodman-Strauss, *Open Questions in Tiling*][GoodmanStrauss2000]
* [Rachel Greenfeld and Terence Tao, *A counterexample to the periodic tiling
  conjecture*][GreenfeldTao2024]
-/


@[expose] public section

namespace DiscreteTiling

open Function
open scoped Pointwise

variable {G X ιₚ : Type*} [Group G] [MulAction G X]

variable (G X) in
/-- A `Prototile G X` describes a tile in `X`, copies of which under elements of `G` may be used in
tilings. Two copies related by an element of `symmetries` are considered the same; two copies not so
related, even if they have the same points, are considered distinct. -/
@[ext] structure Prototile where
  /-- The points in the prototile. Use the coercion to `Set X`, or `∈` on the `Prototile`, rather
      than using `carrier` directly. The coercion cannot use `SetLike` because it does not satisfy
      `coe_injective`. -/
  carrier : Set X
  /-- The group elements considered to be symmetries of the prototile. -/
  symmetries : Subgroup (MulAction.stabilizer G carrier)

namespace Prototile

instance : Inhabited (Prototile G X) where
  default := ⟨∅, ⊥⟩

instance : CoeOut (Prototile G X) (Set X) where
  coe := Prototile.carrier

attribute [coe] carrier

instance : Membership X (Prototile G X) where
  mem p x := x ∈ (p : Set X)

lemma coe_mk (c s) : (⟨c, s⟩ : Prototile G X) = c := rfl

@[simp] lemma mem_coe {x : X} {p : Prototile G X} : x ∈ (p : Set X) ↔ x ∈ p := Iff.rfl

end Prototile

variable (G X ιₚ) in
/-- A `Protoset G X ιₚ` is an indexed family of `Prototile G X`. This is a separate definition
rather than just using plain functions to facilitate defining associated API that can be used with
dot notation. -/
@[ext] structure Protoset where
  /-- The tiles in the protoset. Use the coercion to a function rather than using `tiles`
      directly. -/
  tiles : ιₚ → Prototile G X

namespace Protoset

instance : Inhabited (Protoset G X ιₚ) where
  default := ⟨fun _ ↦ default⟩

instance : CoeFun (Protoset G X ιₚ) (fun _ ↦ ιₚ → Prototile G X) where
  coe := tiles

attribute [coe] tiles

lemma coe_mk (t) : (⟨t⟩ : Protoset G X ιₚ) = t := rfl

@[simp, norm_cast] lemma coe_inj {ps₁ ps₂ : Protoset G X ιₚ} :
    (ps₁ : ιₚ → Prototile G X) = ps₂ ↔ ps₁ = ps₂ :=
  Protoset.ext_iff.symm

lemma coe_injective : Injective (Protoset.tiles : Protoset G X ιₚ → ιₚ → Prototile G X) :=
  fun _ _ ↦ coe_inj.1

end Protoset

variable {ps : Protoset G X ιₚ}

variable (ps) in
/-- A `PlacedTile ps` is an image of a tile in the protoset `p` under an element of the group `G`.
This is represented using a quotient so that images under group elements differing only by a
symmetry of the tile are equal. -/
@[ext] structure PlacedTile where
  /-- The index of the tile in the protoset. -/
  index : ιₚ
  /-- The group elements under which this tile is an image. -/
  groupElts : G ⧸ ((ps index).symmetries.map <| Subgroup.subtype _)

namespace PlacedTile

instance [Nonempty ιₚ] : Nonempty (PlacedTile ps) := ⟨⟨Classical.arbitrary _, (1 : G)⟩⟩

/-- An induction principle to deduce results for `PlacedTile` from those given an index and an
element of `G`, used with `induction pt using PlacedTile.induction_on`. -/
@[elab_as_elim] protected lemma induction_on {ppt : PlacedTile ps → Prop} (pt : PlacedTile ps)
    (h : ∀ i : ιₚ, ∀ gx : G, ppt ⟨i, gx⟩) : ppt pt := by
  rcases pt with ⟨i, gx⟩
  exact Quotient.inductionOn' gx (h i)

/-- An alternative extensionality principle for `PlacedTile` that avoids `HEq`, using existence of a
common group element. -/
lemma ext_iff_of_exists {pt₁ pt₂ : PlacedTile ps} :
    pt₁ = pt₂ ↔ pt₁.index = pt₂.index ∧ ∃ g, ⟦g⟧ = pt₁.groupElts ∧ ⟦g⟧ = pt₂.groupElts := by
  refine ⟨fun h ↦ ?_, fun ⟨h, g, hg₁, hg₂⟩ ↦ ?_⟩
  · subst h
    simp only [and_self, true_and]
    refine ⟨pt₁.groupElts.out, ?_⟩
    rw [Quotient.out_eq]
  · rcases pt₁ with ⟨i₁, g₁⟩
    rcases pt₂ with ⟨i₂, g₂⟩
    dsimp only at h
    subst h
    ext
    · rfl
    · exact heq_of_eq (hg₁.symm.trans hg₂)

/-- An alternative extensionality principle for `PlacedTile` that avoids `HEq`, using equality of
quotient preimages. -/
lemma ext_iff_of_preimage {pt₁ pt₂ : PlacedTile ps} :
    pt₁ = pt₂ ↔ pt₁.index = pt₂.index ∧
      (Quotient.mk _) ⁻¹' {pt₁.groupElts} = (Quotient.mk _) ⁻¹' {pt₂.groupElts} := by
  refine ⟨fun h ↦ ?_, fun ⟨hi, hq⟩ ↦ ?_⟩
  · subst h
    simp only [and_self]
  · rcases pt₁ with ⟨i₁, g₁⟩
    rcases pt₂ with ⟨i₂, g₂⟩
    dsimp only at hi
    subst hi
    ext
    · rfl
    · exact heq_of_eq (Set.singleton_eq_singleton_iff.1
        ((Set.preimage_eq_preimage Quotient.mk''_surjective).1 hq))

/-- Coercion from a `PlacedTile` to a set of points. Use the coercion rather than using `coeSet`
directly. -/
@[coe] def coeSet (pt : PlacedTile ps) : Set X :=
  Quotient.liftOn' pt.groupElts (fun g ↦ g • (ps pt.index : Set X))
    fun a b r ↦ by
      rw [QuotientGroup.leftRel_eq] at r
      simp only
      rw [eq_comm, ← inv_smul_eq_iff, smul_smul, ← MulAction.mem_stabilizer_iff]
      exact SetLike.le_def.1 (Subgroup.map_subtype_le _) r

instance : CoeOut (PlacedTile ps) (Set X) where
  coe := coeSet

instance : Membership X (PlacedTile ps) where
  mem p x := x ∈ (p : Set X)

@[simp] lemma mem_coe {x : X} {pt : PlacedTile ps} : x ∈ (pt : Set X) ↔ x ∈ pt := Iff.rfl

lemma coe_mk_mk (i : ιₚ) (g : G) : (⟨i, ⟦g⟧⟩ : PlacedTile ps) = g • (ps i : Set X) := rfl

lemma coe_mk_coe (i : ιₚ) (g : G) : (⟨i, g⟩ : PlacedTile ps) = g • (ps i : Set X) := rfl

lemma coe_nonempty_iff {pt : PlacedTile ps} :
    (pt : Set X).Nonempty ↔ (ps pt.index : Set X).Nonempty := by
  rcases pt with ⟨index, groupElts⟩
  simp only [coeSet]
  rw [← groupElts.out_eq', Quotient.liftOn'_mk'']
  simp

@[simp] lemma coe_mk_nonempty_iff {i : ιₚ} (g) :
    ((⟨i, g⟩ : PlacedTile ps) : Set X).Nonempty ↔ (ps i : Set X).Nonempty :=
  coe_nonempty_iff

lemma coe_finite_iff {pt : PlacedTile ps} :
    (pt : Set X).Finite ↔ (ps pt.index : Set X).Finite := by
  rcases pt with ⟨index, groupElts⟩
  simp only [coeSet]
  rw [← groupElts.out_eq', Quotient.liftOn'_mk'']
  simp

@[simp] lemma coe_mk_finite_iff {i : ιₚ} (g) :
    ((⟨i, g⟩ : PlacedTile ps) : Set X).Finite ↔ (ps i : Set X).Finite :=
  coe_finite_iff

instance : SMul G (PlacedTile ps) where
  smul g pt := Quotient.liftOn' pt.groupElts (fun h ↦ ⟨pt.index, g * h⟩)
    fun a b r ↦ by
      rw [QuotientGroup.leftRel_eq] at r
      refine PlacedTile.ext rfl ?_
      simpa [QuotientGroup.eq, ← mul_assoc] using r

@[simp] lemma smul_mk_mk (g h : G) (i : ιₚ) : g • (⟨i, ⟦h⟧⟩ : PlacedTile ps) = ⟨i, g * h⟩ := rfl

@[simp] lemma smul_mk_coe (g h : G) (i : ιₚ) : g • (⟨i, h⟩ : PlacedTile ps) = ⟨i, g * h⟩ := rfl

@[simp] lemma smul_index (g : G) (pt : PlacedTile ps) : (g • pt).index = pt.index := by
  induction pt using PlacedTile.induction_on
  rfl

@[simp] lemma coe_smul (g : G) (pt : PlacedTile ps) :
    (g • pt : PlacedTile ps) = g • (pt : Set X) := by
  induction pt using PlacedTile.induction_on
  simp [coeSet, mul_smul]

instance : MulAction G (PlacedTile ps) where
  __ : SMul G (PlacedTile ps) := inferInstance
  one_smul pt := by
    induction pt using PlacedTile.induction_on
    simp
  mul_smul x y pt := by
    induction pt using PlacedTile.induction_on
    simp [mul_assoc]

@[simp] lemma smul_mem_smul_iff (g : G) {x : X} {pt : PlacedTile ps} : g • x ∈ g • pt ↔ x ∈ pt := by
  rw [← mem_coe, coe_smul, Set.smul_mem_smul_set_iff, mem_coe]

lemma mem_smul_iff_smul_inv_mem {g : G} {x : X} {pt : PlacedTile ps} :
    x ∈ g • pt ↔ g⁻¹ • x ∈ pt := by
  simp_rw [← mem_coe, coe_smul, Set.mem_smul_set_iff_inv_smul_mem]

lemma mem_inv_smul_iff_smul_mem {g : G} {x : X} {pt : PlacedTile ps} :
    x ∈ g⁻¹ • pt ↔ g • x ∈ pt := by
  simp_rw [← mem_coe, coe_smul, Set.mem_inv_smul_set_iff]

end PlacedTile

end DiscreteTiling
