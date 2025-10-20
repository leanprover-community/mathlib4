/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Order.Atoms
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.AffineSpace.Defs

/-!
# Affine spaces

This file defines affine subspaces (over modules) and the affine span of a set of points.

## Main definitions

* `AffineSubspace k P` is the type of affine subspaces. Unlike affine spaces, affine subspaces are
  allowed to be empty, and lemmas that do not apply to empty affine subspaces have `Nonempty`
  hypotheses. There is a `CompleteLattice` structure on affine subspaces.
* `AffineSubspace.direction` gives the `Submodule` spanned by the pairwise differences of points
  in an `AffineSubspace`. There are various lemmas relating to the set of vectors in the
  `direction`, and relating the lattice structure on affine subspaces to that on their directions.
* `affineSpan` gives the affine subspace spanned by a set of points, with `vectorSpan` giving its
  direction. The `affineSpan` is defined in terms of `spanPoints`, which gives an explicit
  description of the points contained in the affine span; `spanPoints` itself should generally only
  be used when that description is required, with `affineSpan` being the main definition for other
  purposes. Two other descriptions of the affine span are proved equivalent: it is the `sInf` of
  affine subspaces containing the points, and (if `[Nontrivial k]`) it contains exactly those points
  that are affine combinations of points in the given set.

## Implementation notes

`outParam` is used in the definition of `AddTorsor V P` to make `V` an implicit argument (deduced
from `P`) in most cases. As for modules, `k` is an explicit argument rather than implied by `P` or
`V`.

This file only provides purely algebraic definitions and results. Those depending on analysis or
topology are defined elsewhere; see `Analysis.Normed.Affine.AddTorsor` and
`Topology.Algebra.Affine`.

## References

* https://en.wikipedia.org/wiki/Affine_space
* https://en.wikipedia.org/wiki/Principal_homogeneous_space
-/
noncomputable section

open Affine

open Set
open scoped Pointwise

section

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
variable [AffineSpace V P]

/-- The submodule spanning the differences of a (possibly empty) set of points. -/
def vectorSpan (s : Set P) : Submodule k V :=
  Submodule.span k (s -ᵥ s)

/-- The definition of `vectorSpan`, for rewriting. -/
theorem vectorSpan_def (s : Set P) : vectorSpan k s = Submodule.span k (s -ᵥ s) :=
  rfl

/-- `vectorSpan` is monotone. -/
theorem vectorSpan_mono {s₁ s₂ : Set P} (h : s₁ ⊆ s₂) : vectorSpan k s₁ ≤ vectorSpan k s₂ :=
  Submodule.span_mono (vsub_self_mono h)

variable (P) in
/-- The `vectorSpan` of the empty set is `⊥`. -/
@[simp]
theorem vectorSpan_empty : vectorSpan k (∅ : Set P) = (⊥ : Submodule k V) := by
  rw [vectorSpan_def, vsub_empty, Submodule.span_empty]

/-- The `vectorSpan` of a single point is `⊥`. -/
@[simp]
theorem vectorSpan_singleton (p : P) : vectorSpan k ({p} : Set P) = ⊥ := by simp [vectorSpan_def]

/-- The `s -ᵥ s` lies within the `vectorSpan k s`. -/
theorem vsub_set_subset_vectorSpan (s : Set P) : s -ᵥ s ⊆ ↑(vectorSpan k s) :=
  Submodule.subset_span

/-- Each pairwise difference is in the `vectorSpan`. -/
theorem vsub_mem_vectorSpan {s : Set P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) :
    p₁ -ᵥ p₂ ∈ vectorSpan k s :=
  vsub_set_subset_vectorSpan k s (vsub_mem_vsub hp₁ hp₂)

/-- The points in the affine span of a (possibly empty) set of points. Use `affineSpan` instead to
get an `AffineSubspace k P`. -/
def spanPoints (s : Set P) : Set P :=
  { p | ∃ p₁ ∈ s, ∃ v ∈ vectorSpan k s, p = v +ᵥ p₁ }

/-- A point in a set is in its affine span. -/
theorem mem_spanPoints (p : P) (s : Set P) : p ∈ s → p ∈ spanPoints k s
  | hp => ⟨p, hp, 0, Submodule.zero_mem _, (zero_vadd V p).symm⟩

/-- A set is contained in its `spanPoints`. -/
theorem subset_spanPoints (s : Set P) : s ⊆ spanPoints k s := fun p => mem_spanPoints k p s

/-- The `spanPoints` of a set is nonempty if and only if that set is. -/
@[simp]
theorem spanPoints_nonempty (s : Set P) : (spanPoints k s).Nonempty ↔ s.Nonempty := by
  constructor
  · contrapose
    rw [Set.not_nonempty_iff_eq_empty, Set.not_nonempty_iff_eq_empty]
    intro h
    simp [h, spanPoints]
  · exact fun h => h.mono (subset_spanPoints _ _)

/-- Adding a point in the affine span and a vector in the spanning submodule produces a point in the
affine span. -/
theorem vadd_mem_spanPoints_of_mem_spanPoints_of_mem_vectorSpan {s : Set P} {p : P} {v : V}
    (hp : p ∈ spanPoints k s) (hv : v ∈ vectorSpan k s) : v +ᵥ p ∈ spanPoints k s := by
  rcases hp with ⟨p₂, ⟨hp₂, ⟨v₂, ⟨hv₂, hv₂p⟩⟩⟩⟩
  rw [hv₂p, vadd_vadd]
  exact ⟨p₂, hp₂, v + v₂, (vectorSpan k s).add_mem hv hv₂, rfl⟩

/-- Subtracting two points in the affine span produces a vector in the spanning submodule. -/
theorem vsub_mem_vectorSpan_of_mem_spanPoints_of_mem_spanPoints {s : Set P} {p₁ p₂ : P}
    (hp₁ : p₁ ∈ spanPoints k s) (hp₂ : p₂ ∈ spanPoints k s) : p₁ -ᵥ p₂ ∈ vectorSpan k s := by
  rcases hp₁ with ⟨p₁a, ⟨hp₁a, ⟨v₁, ⟨hv₁, hv₁p⟩⟩⟩⟩
  rcases hp₂ with ⟨p₂a, ⟨hp₂a, ⟨v₂, ⟨hv₂, hv₂p⟩⟩⟩⟩
  rw [hv₁p, hv₂p, vsub_vadd_eq_vsub_sub (v₁ +ᵥ p₁a), vadd_vsub_assoc, add_comm, add_sub_assoc]
  have hv₁v₂ : v₁ - v₂ ∈ vectorSpan k s := (vectorSpan k s).sub_mem hv₁ hv₂
  refine (vectorSpan k s).add_mem ?_ hv₁v₂
  exact vsub_mem_vectorSpan k hp₁a hp₂a

end

/-- An `AffineSubspace k P` is a subset of an `AffineSpace V P` that, if not empty, has an affine
space structure induced by a corresponding subspace of the `Module k V`. -/
structure AffineSubspace (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V]
  [Module k V] [AffineSpace V P] where
  /-- The affine subspace seen as a subset. -/
  carrier : Set P
  smul_vsub_vadd_mem :
    ∀ (c : k) {p₁ p₂ p₃ : P},
      p₁ ∈ carrier → p₂ ∈ carrier → p₃ ∈ carrier → c • (p₁ -ᵥ p₂ : V) +ᵥ p₃ ∈ carrier

namespace Submodule

variable {k V : Type*} [Ring k] [AddCommGroup V] [Module k V]

/-- Reinterpret `p : Submodule k V` as an `AffineSubspace k V`. -/
def toAffineSubspace (p : Submodule k V) : AffineSubspace k V where
  carrier := p
  smul_vsub_vadd_mem _ _ _ _ h₁ h₂ h₃ := p.add_mem (p.smul_mem _ (p.sub_mem h₁ h₂)) h₃

end Submodule

namespace AffineSubspace

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AffineSpace V P]

instance : SetLike (AffineSubspace k P) P where
  coe := carrier
  coe_injective' p q _ := by cases p; cases q; congr

/-- A point is in an affine subspace coerced to a set if and only if it is in that affine
subspace. -/
theorem mem_coe (p : P) (s : AffineSubspace k P) : p ∈ (s : Set P) ↔ p ∈ s := by simp

variable {k P}

/-- The direction of an affine subspace is the submodule spanned by
the pairwise differences of points.  (Except in the case of an empty
affine subspace, where the direction is the zero submodule, every
vector in the direction is the difference of two points in the affine
subspace.) -/
def direction (s : AffineSubspace k P) : Submodule k V :=
  vectorSpan k (s : Set P)

/-- The direction equals the `vectorSpan`. -/
theorem direction_eq_vectorSpan (s : AffineSubspace k P) : s.direction = vectorSpan k (s : Set P) :=
  rfl

/-- Alternative definition of the direction when the affine subspace is nonempty. This is defined so
that the order on submodules (as used in the definition of `Submodule.span`) can be used in the
proof of `coe_direction_eq_vsub_set`, and is not intended to be used beyond that proof. -/
def directionOfNonempty {s : AffineSubspace k P} (h : (s : Set P).Nonempty) : Submodule k V where
  carrier := (s : Set P) -ᵥ s
  zero_mem' := by
    obtain ⟨p, hp⟩ := h
    exact vsub_self p ▸ vsub_mem_vsub hp hp
  add_mem' := by
    rintro _ _ ⟨p₁, hp₁, p₂, hp₂, rfl⟩ ⟨p₃, hp₃, p₄, hp₄, rfl⟩
    rw [← vadd_vsub_assoc]
    refine vsub_mem_vsub ?_ hp₄
    convert s.smul_vsub_vadd_mem 1 hp₁ hp₂ hp₃
    rw [one_smul]
  smul_mem' := by
    rintro c _ ⟨p₁, hp₁, p₂, hp₂, rfl⟩
    rw [← vadd_vsub (c • (p₁ -ᵥ p₂)) p₂]
    refine vsub_mem_vsub ?_ hp₂
    exact s.smul_vsub_vadd_mem c hp₁ hp₂ hp₂

/-- `direction_of_nonempty` gives the same submodule as `direction`. -/
theorem directionOfNonempty_eq_direction {s : AffineSubspace k P} (h : (s : Set P).Nonempty) :
    directionOfNonempty h = s.direction := by
  refine le_antisymm ?_ (Submodule.span_le.2 Set.Subset.rfl)
  rw [← SetLike.coe_subset_coe, directionOfNonempty, direction, Submodule.coe_set_mk,
    AddSubmonoid.coe_set_mk]
  exact vsub_set_subset_vectorSpan k _

/-- The set of vectors in the direction of a nonempty affine subspace is given by `vsub_set`. -/
theorem coe_direction_eq_vsub_set {s : AffineSubspace k P} (h : (s : Set P).Nonempty) :
    (s.direction : Set V) = (s : Set P) -ᵥ s :=
  directionOfNonempty_eq_direction h ▸ rfl

/-- A vector is in the direction of a nonempty affine subspace if and only if it is the subtraction
of two vectors in the subspace. -/
theorem mem_direction_iff_eq_vsub {s : AffineSubspace k P} (h : (s : Set P).Nonempty) (v : V) :
    v ∈ s.direction ↔ ∃ p₁ ∈ s, ∃ p₂ ∈ s, v = p₁ -ᵥ p₂ := by
  rw [← SetLike.mem_coe, coe_direction_eq_vsub_set h, Set.mem_vsub]
  simp only [SetLike.mem_coe, eq_comm]

/-- Adding a vector in the direction to a point in the subspace produces a point in the
subspace. -/
theorem vadd_mem_of_mem_direction {s : AffineSubspace k P} {v : V} (hv : v ∈ s.direction) {p : P}
    (hp : p ∈ s) : v +ᵥ p ∈ s := by
  rw [mem_direction_iff_eq_vsub ⟨p, hp⟩] at hv
  rcases hv with ⟨p₁, hp₁, p₂, hp₂, hv⟩
  rw [hv]
  convert s.smul_vsub_vadd_mem 1 hp₁ hp₂ hp
  rw [one_smul]

/-- Subtracting two points in the subspace produces a vector in the direction. -/
theorem vsub_mem_direction {s : AffineSubspace k P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) :
    p₁ -ᵥ p₂ ∈ s.direction :=
  vsub_mem_vectorSpan k hp₁ hp₂

/-- Adding a vector to a point in a subspace produces a point in the subspace if and only if the
vector is in the direction. -/
theorem vadd_mem_iff_mem_direction {s : AffineSubspace k P} (v : V) {p : P} (hp : p ∈ s) :
    v +ᵥ p ∈ s ↔ v ∈ s.direction :=
  ⟨fun h => by simpa using vsub_mem_direction h hp, fun h => vadd_mem_of_mem_direction h hp⟩

/-- Adding a vector in the direction to a point produces a point in the subspace if and only if
the original point is in the subspace. -/
theorem vadd_mem_iff_mem_of_mem_direction {s : AffineSubspace k P} {v : V} (hv : v ∈ s.direction)
    {p : P} : v +ᵥ p ∈ s ↔ p ∈ s := by
  refine ⟨fun h => ?_, fun h => vadd_mem_of_mem_direction hv h⟩
  convert vadd_mem_of_mem_direction (Submodule.neg_mem _ hv) h
  simp

/-- Given a point in an affine subspace, the set of vectors in its direction equals the set of
vectors subtracting that point on the right. -/
theorem coe_direction_eq_vsub_set_right {s : AffineSubspace k P} {p : P} (hp : p ∈ s) :
    (s.direction : Set V) = (· -ᵥ p) '' s := by
  rw [coe_direction_eq_vsub_set ⟨p, hp⟩]
  refine le_antisymm ?_ ?_
  · rintro v ⟨p₁, hp₁, p₂, hp₂, rfl⟩
    exact ⟨(p₁ -ᵥ p₂) +ᵥ p,
      vadd_mem_of_mem_direction (vsub_mem_direction hp₁ hp₂) hp, vadd_vsub _ _⟩
  · rintro v ⟨p₂, hp₂, rfl⟩
    exact ⟨p₂, hp₂, p, hp, rfl⟩

/-- Given a point in an affine subspace, the set of vectors in its direction equals the set of
vectors subtracting that point on the left. -/
theorem coe_direction_eq_vsub_set_left {s : AffineSubspace k P} {p : P} (hp : p ∈ s) :
    (s.direction : Set V) = (p -ᵥ ·) '' s := by
  ext v
  rw [SetLike.mem_coe, ← Submodule.neg_mem_iff, ← SetLike.mem_coe,
    coe_direction_eq_vsub_set_right hp, Set.mem_image, Set.mem_image]
  conv_lhs =>
    congr
    ext
    rw [← neg_vsub_eq_vsub_rev, neg_inj]

/-- Given a point in an affine subspace, a vector is in its direction if and only if it results from
subtracting that point on the right. -/
theorem mem_direction_iff_eq_vsub_right {s : AffineSubspace k P} {p : P} (hp : p ∈ s) (v : V) :
    v ∈ s.direction ↔ ∃ p₂ ∈ s, v = p₂ -ᵥ p := by
  rw [← SetLike.mem_coe, coe_direction_eq_vsub_set_right hp]
  exact ⟨fun ⟨p₂, hp₂, hv⟩ => ⟨p₂, hp₂, hv.symm⟩, fun ⟨p₂, hp₂, hv⟩ => ⟨p₂, hp₂, hv.symm⟩⟩

/-- Given a point in an affine subspace, a vector is in its direction if and only if it results from
subtracting that point on the left. -/
theorem mem_direction_iff_eq_vsub_left {s : AffineSubspace k P} {p : P} (hp : p ∈ s) (v : V) :
    v ∈ s.direction ↔ ∃ p₂ ∈ s, v = p -ᵥ p₂ := by
  rw [← SetLike.mem_coe, coe_direction_eq_vsub_set_left hp]
  exact ⟨fun ⟨p₂, hp₂, hv⟩ => ⟨p₂, hp₂, hv.symm⟩, fun ⟨p₂, hp₂, hv⟩ => ⟨p₂, hp₂, hv.symm⟩⟩

/-- Two affine subspaces are equal if they have the same points. -/
theorem coe_injective : Function.Injective ((↑) : AffineSubspace k P → Set P) :=
  SetLike.coe_injective

@[ext (iff := false)]
theorem ext {p q : AffineSubspace k P} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q :=
  SetLike.ext h

protected theorem ext_iff (s₁ s₂ : AffineSubspace k P) : s₁ = s₂ ↔ (s₁ : Set P) = s₂ :=
  SetLike.ext'_iff

/-- Two affine subspaces with the same direction and nonempty intersection are equal. -/
theorem ext_of_direction_eq {s₁ s₂ : AffineSubspace k P} (hd : s₁.direction = s₂.direction)
    (hn : ((s₁ : Set P) ∩ s₂).Nonempty) : s₁ = s₂ := by
  ext p
  have hq1 := Set.mem_of_mem_inter_left hn.some_mem
  have hq2 := Set.mem_of_mem_inter_right hn.some_mem
  constructor
  · intro hp
    rw [← vsub_vadd p hn.some]
    refine vadd_mem_of_mem_direction ?_ hq2
    rw [← hd]
    exact vsub_mem_direction hp hq1
  · intro hp
    rw [← vsub_vadd p hn.some]
    refine vadd_mem_of_mem_direction ?_ hq1
    rw [hd]
    exact vsub_mem_direction hp hq2

/-- Two affine subspaces with nonempty intersection are equal if and only if their directions are
equal. -/
theorem eq_iff_direction_eq_of_mem {s₁ s₂ : AffineSubspace k P} {p : P} (h₁ : p ∈ s₁)
    (h₂ : p ∈ s₂) : s₁ = s₂ ↔ s₁.direction = s₂.direction :=
  ⟨fun h => h ▸ rfl, fun h => ext_of_direction_eq h ⟨p, h₁, h₂⟩⟩

/-- Construct an affine subspace from a point and a direction. -/
def mk' (p : P) (direction : Submodule k V) : AffineSubspace k P where
  carrier := { q | q -ᵥ p ∈ direction }
  smul_vsub_vadd_mem c p₁ p₂ p₃ hp₁ hp₂ hp₃ := by
    simpa [vadd_vsub_assoc] using
      direction.add_mem (direction.smul_mem c (direction.sub_mem hp₁ hp₂)) hp₃

/-- A point lies in an affine subspace constructed from another point and a direction if and only
if their difference is in that direction. -/
@[simp]
theorem mem_mk' {p q : P} {direction : Submodule k V} : q ∈ mk' p direction ↔ q -ᵥ p ∈ direction :=
  Iff.rfl

/-- An affine subspace constructed from a point and a direction contains that point. -/
theorem self_mem_mk' (p : P) (direction : Submodule k V) : p ∈ mk' p direction := by
  simp

/-- An affine subspace constructed from a point and a direction contains the result of adding a
vector in that direction to that point. -/
theorem vadd_mem_mk' {v : V} (p : P) {direction : Submodule k V} (hv : v ∈ direction) :
    v +ᵥ p ∈ mk' p direction := by
  simpa

/-- An affine subspace constructed from a point and a direction is nonempty. -/
theorem mk'_nonempty (p : P) (direction : Submodule k V) : (mk' p direction : Set P).Nonempty :=
  ⟨p, self_mem_mk' p direction⟩

/-- The direction of an affine subspace constructed from a point and a direction. -/
@[simp]
theorem direction_mk' (p : P) (direction : Submodule k V) :
    (mk' p direction).direction = direction := by
  ext v
  rw [mem_direction_iff_eq_vsub (mk'_nonempty _ _)]
  constructor
  · rintro ⟨p₁, hp₁, p₂, hp₂, rfl⟩
    simpa using direction.sub_mem hp₁ hp₂
  · exact fun hv => ⟨v +ᵥ p, vadd_mem_mk' _ hv, p, self_mem_mk' _ _, (vadd_vsub _ _).symm⟩

@[deprecated (since := "2025-08-15")] alias mem_mk'_iff_vsub_mem := mem_mk'

/-- Constructing an affine subspace from a point in a subspace and that subspace's direction
yields the original subspace. -/
@[simp]
theorem mk'_eq {s : AffineSubspace k P} {p : P} (hp : p ∈ s) : mk' p s.direction = s :=
  ext_of_direction_eq (direction_mk' p s.direction) ⟨p, Set.mem_inter (self_mem_mk' _ _) hp⟩

/-- If an affine subspace contains a set of points, it contains the `spanPoints` of that set. -/
theorem spanPoints_subset_coe_of_subset_coe {s : Set P} {s₁ : AffineSubspace k P} (h : s ⊆ s₁) :
    spanPoints k s ⊆ s₁ := by
  rintro p ⟨p₁, hp₁, v, hv, hp⟩
  rw [hp]
  have hp₁s₁ : p₁ ∈ (s₁ : Set P) := Set.mem_of_mem_of_subset hp₁ h
  refine vadd_mem_of_mem_direction ?_ hp₁s₁
  have hs : vectorSpan k s ≤ s₁.direction := vectorSpan_mono k h
  rw [SetLike.le_def] at hs
  rw [← SetLike.mem_coe]
  exact Set.mem_of_mem_of_subset hv hs

end AffineSubspace

namespace Submodule

variable {k V : Type*} [Ring k] [AddCommGroup V] [Module k V]

@[simp]
theorem mem_toAffineSubspace {p : Submodule k V} {x : V} :
    x ∈ p.toAffineSubspace ↔ x ∈ p :=
  Iff.rfl

@[simp]
theorem toAffineSubspace_direction (s : Submodule k V) : s.toAffineSubspace.direction = s := by
  ext x; simp [← s.toAffineSubspace.vadd_mem_iff_mem_direction _ s.zero_mem]

end Submodule

section affineSpan

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AffineSpace V P]

/-- The affine span of a set of points is the smallest affine subspace containing those points.
(Actually defined here in terms of spans in modules.) -/
def affineSpan (s : Set P) : AffineSubspace k P where
  carrier := spanPoints k s
  smul_vsub_vadd_mem c _ _ _ hp₁ hp₂ hp₃ :=
    vadd_mem_spanPoints_of_mem_spanPoints_of_mem_vectorSpan k hp₃
      ((vectorSpan k s).smul_mem c
        (vsub_mem_vectorSpan_of_mem_spanPoints_of_mem_spanPoints k hp₁ hp₂))

/-- The affine span, converted to a set, is `spanPoints`. -/
@[simp]
theorem coe_affineSpan (s : Set P) : (affineSpan k s : Set P) = spanPoints k s :=
  rfl

/-- The condition for a point to be in the affine span, in terms of `vectorSpan`. -/
lemma mem_affineSpan_iff_exists {p : P} {s : Set P} : p ∈ affineSpan k s ↔
    ∃ p₁ ∈ s, ∃ v ∈ vectorSpan k s, p = v +ᵥ p₁ :=
  Iff.rfl

/-- A set is contained in its affine span. -/
theorem subset_affineSpan (s : Set P) : s ⊆ affineSpan k s :=
  subset_spanPoints k s

/-- The direction of the affine span is the `vectorSpan`. -/
theorem direction_affineSpan (s : Set P) : (affineSpan k s).direction = vectorSpan k s := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro v ⟨p₁, ⟨p₂, hp₂, v₁, hv₁, hp₁⟩, p₃, ⟨p₄, hp₄, v₂, hv₂, hp₃⟩, rfl⟩
    simp only [SetLike.mem_coe]
    rw [hp₁, hp₃, vsub_vadd_eq_vsub_sub, vadd_vsub_assoc]
    exact
      (vectorSpan k s).sub_mem ((vectorSpan k s).add_mem hv₁ (vsub_mem_vectorSpan k hp₂ hp₄)) hv₂
  · exact vectorSpan_mono k (subset_spanPoints k s)

/-- A point in a set is in its affine span. -/
theorem mem_affineSpan {p : P} {s : Set P} (hp : p ∈ s) : p ∈ affineSpan k s :=
  mem_spanPoints k p s hp

@[simp]
lemma vectorSpan_add_self (s : Set V) : (vectorSpan k s : Set V) + s = affineSpan k s := by
  ext
  simp [mem_add, spanPoints]
  aesop

variable {k}

/-- Adding a point in the affine span and a vector in the spanning submodule produces a point in the
affine span. -/
theorem vadd_mem_affineSpan_of_mem_affineSpan_of_mem_vectorSpan {s : Set P} {p : P} {v : V}
    (hp : p ∈ affineSpan k s) (hv : v ∈ vectorSpan k s) : v +ᵥ p ∈ affineSpan k s :=
  vadd_mem_spanPoints_of_mem_spanPoints_of_mem_vectorSpan k hp hv

/-- Subtracting two points in the affine span produces a vector in the spanning submodule. -/
theorem vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan {s : Set P} {p₁ p₂ : P}
    (hp₁ : p₁ ∈ affineSpan k s) (hp₂ : p₂ ∈ affineSpan k s) : p₁ -ᵥ p₂ ∈ vectorSpan k s :=
  vsub_mem_vectorSpan_of_mem_spanPoints_of_mem_spanPoints k hp₁ hp₂

/-- If an affine subspace contains a set of points, it contains the affine span of that set. -/
theorem affineSpan_le_of_subset_coe {s : Set P} {s₁ : AffineSubspace k P} (h : s ⊆ s₁) :
    affineSpan k s ≤ s₁ :=
  AffineSubspace.spanPoints_subset_coe_of_subset_coe h

end affineSpan

namespace AffineSubspace

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AffineSpace V P] {ι : Sort*}

instance : CompleteLattice (AffineSubspace k P) :=
  {
    PartialOrder.lift ((↑) : AffineSubspace k P → Set P)
      coe_injective with
    max := fun s₁ s₂ => affineSpan k (s₁ ∪ s₂)
    le_sup_left := fun _ _ =>
      Set.Subset.trans Set.subset_union_left (subset_spanPoints k _)
    le_sup_right := fun _ _ =>
      Set.Subset.trans Set.subset_union_right (subset_spanPoints k _)
    sup_le := fun _ _ _ hs₁ hs₂ => spanPoints_subset_coe_of_subset_coe (Set.union_subset hs₁ hs₂)
    min := fun s₁ s₂ =>
      mk (s₁ ∩ s₂) fun c _ _ _ hp₁ hp₂ hp₃ =>
        ⟨s₁.smul_vsub_vadd_mem c hp₁.1 hp₂.1 hp₃.1, s₂.smul_vsub_vadd_mem c hp₁.2 hp₂.2 hp₃.2⟩
    inf_le_left := fun _ _ => Set.inter_subset_left
    inf_le_right := fun _ _ => Set.inter_subset_right
    le_sInf := fun S s₁ hs₁ => by
      apply Set.subset_sInter
      rintro t ⟨s, _hs, rfl⟩
      exact Set.subset_iInter (hs₁ s)
    top :=
      { carrier := Set.univ
        smul_vsub_vadd_mem := fun _ _ _ _ _ _ _ => Set.mem_univ _ }
    le_top := fun _ _ _ => Set.mem_univ _
    bot :=
      { carrier := ∅
        smul_vsub_vadd_mem := fun _ _ _ _ => False.elim }
    bot_le := fun _ _ => False.elim
    sSup := fun s => affineSpan k (⋃ s' ∈ s, (s' : Set P))
    sInf := fun s =>
      mk (⋂ s' ∈ s, (s' : Set P)) fun c p₁ p₂ p₃ hp₁ hp₂ hp₃ =>
        Set.mem_iInter₂.2 fun s₂ hs₂ => by
          rw [Set.mem_iInter₂] at *
          exact s₂.smul_vsub_vadd_mem c (hp₁ s₂ hs₂) (hp₂ s₂ hs₂) (hp₃ s₂ hs₂)
    le_sSup := fun _ _ h => Set.Subset.trans (Set.subset_biUnion_of_mem h) (subset_spanPoints k _)
    sSup_le := fun _ _ h => spanPoints_subset_coe_of_subset_coe (Set.iUnion₂_subset h)
    sInf_le := fun _ _ => Set.biInter_subset_of_mem
    le_inf := fun _ _ _ => Set.subset_inter }

instance : Inhabited (AffineSubspace k P) :=
  ⟨⊤⟩

/-- The `≤` order on subspaces is the same as that on the corresponding sets. -/
theorem le_def (s₁ s₂ : AffineSubspace k P) : s₁ ≤ s₂ ↔ (s₁ : Set P) ⊆ s₂ :=
  Iff.rfl

/-- One subspace is less than or equal to another if and only if all its points are in the second
subspace. -/
theorem le_def' (s₁ s₂ : AffineSubspace k P) : s₁ ≤ s₂ ↔ ∀ p ∈ s₁, p ∈ s₂ :=
  Iff.rfl

/-- The `<` order on subspaces is the same as that on the corresponding sets. -/
theorem lt_def (s₁ s₂ : AffineSubspace k P) : s₁ < s₂ ↔ (s₁ : Set P) ⊂ s₂ :=
  Iff.rfl

/-- One subspace is not less than or equal to another if and only if it has a point not in the
second subspace. -/
theorem not_le_iff_exists (s₁ s₂ : AffineSubspace k P) : ¬s₁ ≤ s₂ ↔ ∃ p ∈ s₁, p ∉ s₂ :=
  Set.not_subset

/-- If a subspace is less than another, there is a point only in the second. -/
theorem exists_of_lt {s₁ s₂ : AffineSubspace k P} (h : s₁ < s₂) : ∃ p ∈ s₂, p ∉ s₁ :=
  Set.exists_of_ssubset h

/-- A subspace is less than another if and only if it is less than or equal to the second subspace
and there is a point only in the second. -/
theorem lt_iff_le_and_exists (s₁ s₂ : AffineSubspace k P) :
    s₁ < s₂ ↔ s₁ ≤ s₂ ∧ ∃ p ∈ s₂, p ∉ s₁ := by
  rw [lt_iff_le_not_ge, not_le_iff_exists]

/-- If an affine subspace is nonempty and contained in another with the same direction, they are
equal. -/
theorem eq_of_direction_eq_of_nonempty_of_le {s₁ s₂ : AffineSubspace k P}
    (hd : s₁.direction = s₂.direction) (hn : (s₁ : Set P).Nonempty) (hle : s₁ ≤ s₂) : s₁ = s₂ :=
  let ⟨p, hp⟩ := hn
  ext_of_direction_eq hd ⟨p, hp, hle hp⟩

variable (k V)

/-- The affine span is the `sInf` of subspaces containing the given points. -/
theorem affineSpan_eq_sInf (s : Set P) :
    affineSpan k s = sInf { s' : AffineSubspace k P | s ⊆ s' } :=
  le_antisymm (affineSpan_le_of_subset_coe <| Set.subset_iInter₂ fun _ => id)
    (sInf_le (subset_spanPoints k _))

variable (P)

/-- The Galois insertion formed by `affineSpan` and coercion back to a set. -/
protected def gi : GaloisInsertion (affineSpan k) ((↑) : AffineSubspace k P → Set P) where
  choice s _ := affineSpan k s
  gc s₁ _s₂ :=
    ⟨fun h => Set.Subset.trans (subset_spanPoints k s₁) h, affineSpan_le_of_subset_coe⟩
  le_l_u _ := subset_spanPoints k _
  choice_eq _ _ := rfl

/-- The span of the empty set is `⊥`. -/
@[simp]
theorem span_empty : affineSpan k (∅ : Set P) = ⊥ :=
  (AffineSubspace.gi k V P).gc.l_bot

/-- The span of `univ` is `⊤`. -/
@[simp]
theorem span_univ : affineSpan k (Set.univ : Set P) = ⊤ :=
  eq_top_iff.2 <| subset_affineSpan k _

variable {k V P}

theorem _root_.affineSpan_le {s : Set P} {Q : AffineSubspace k P} :
    affineSpan k s ≤ Q ↔ s ⊆ (Q : Set P) :=
  (AffineSubspace.gi k V P).gc _ _

variable (k V) {p₁ p₂ : P}

/-- The span of a union of sets is the sup of their spans. -/
theorem span_union (s t : Set P) : affineSpan k (s ∪ t) = affineSpan k s ⊔ affineSpan k t :=
  (AffineSubspace.gi k V P).gc.l_sup

/-- The span of a union of an indexed family of sets is the sup of their spans. -/
theorem span_iUnion {ι : Type*} (s : ι → Set P) :
    affineSpan k (⋃ i, s i) = ⨆ i, affineSpan k (s i) :=
  (AffineSubspace.gi k V P).gc.l_iSup

variable (P) in
/-- `⊤`, coerced to a set, is the whole set of points. -/
@[simp]
theorem top_coe : ((⊤ : AffineSubspace k P) : Set P) = Set.univ :=
  rfl

/-- All points are in `⊤`. -/
@[simp]
theorem mem_top (p : P) : p ∈ (⊤ : AffineSubspace k P) :=
  Set.mem_univ p

@[simp] lemma mk'_top (p : P) : mk' p (⊤ : Submodule k V) = ⊤ := by
  ext x
  simp [mem_mk']

variable (P)

/-- The direction of `⊤` is the whole module as a submodule. -/
@[simp]
theorem direction_top : (⊤ : AffineSubspace k P).direction = ⊤ := by
  obtain ⟨p⟩ := S.nonempty
  ext v
  refine ⟨imp_intro Submodule.mem_top, fun _hv => ?_⟩
  have hpv : ((v +ᵥ p) -ᵥ p : V) ∈ (⊤ : AffineSubspace k P).direction :=
    vsub_mem_direction (mem_top k V _) (mem_top k V _)
  rwa [vadd_vsub] at hpv

/-- `⊥`, coerced to a set, is the empty set. -/
@[simp]
theorem bot_coe : ((⊥ : AffineSubspace k P) : Set P) = ∅ :=
  rfl

theorem bot_ne_top : (⊥ : AffineSubspace k P) ≠ ⊤ := by
  intro contra
  rw [AffineSubspace.ext_iff, bot_coe, top_coe] at contra
  exact Set.empty_ne_univ contra

instance : Nontrivial (AffineSubspace k P) :=
  ⟨⟨⊥, ⊤, bot_ne_top k V P⟩⟩

theorem nonempty_of_affineSpan_eq_top {s : Set P} (h : affineSpan k s = ⊤) : s.Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  rintro rfl
  rw [AffineSubspace.span_empty] at h
  exact bot_ne_top k V P h

/-- If the affine span of a set is `⊤`, then the vector span of the same set is the `⊤`. -/
theorem vectorSpan_eq_top_of_affineSpan_eq_top {s : Set P} (h : affineSpan k s = ⊤) :
    vectorSpan k s = ⊤ := by rw [← direction_affineSpan, h, direction_top]

/-- For a nonempty set, the affine span is `⊤` iff its vector span is `⊤`. -/
theorem affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty {s : Set P} (hs : s.Nonempty) :
    affineSpan k s = ⊤ ↔ vectorSpan k s = ⊤ := by
  refine ⟨vectorSpan_eq_top_of_affineSpan_eq_top k V P, ?_⟩
  intro h
  suffices Nonempty (affineSpan k s) by
    obtain ⟨p, hp : p ∈ affineSpan k s⟩ := this
    rw [eq_iff_direction_eq_of_mem hp (mem_top k V p), direction_affineSpan, h, direction_top]
  obtain ⟨x, hx⟩ := hs
  exact ⟨⟨x, mem_affineSpan k hx⟩⟩

/-- For a non-trivial space, the affine span of a set is `⊤` iff its vector span is `⊤`. -/
theorem affineSpan_eq_top_iff_vectorSpan_eq_top_of_nontrivial {s : Set P} [Nontrivial P] :
    affineSpan k s = ⊤ ↔ vectorSpan k s = ⊤ := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · simp [hs, subsingleton_iff_bot_eq_top, AddTorsor.subsingleton_iff V P, not_subsingleton]
  · rw [affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty k V P hs]

theorem card_pos_of_affineSpan_eq_top {ι : Type*} [Fintype ι] {p : ι → P}
    (h : affineSpan k (range p) = ⊤) : 0 < Fintype.card ι := by
  obtain ⟨-, ⟨i, -⟩⟩ := nonempty_of_affineSpan_eq_top k V P h
  exact Fintype.card_pos_iff.mpr ⟨i⟩

-- An instance with better keys for the context
instance : Nonempty (⊤ : AffineSubspace k P) := inferInstanceAs (Nonempty (⊤ : Set P))

variable {P}

/-- No points are in `⊥`. -/
theorem notMem_bot (p : P) : p ∉ (⊥ : AffineSubspace k P) :=
  Set.notMem_empty p

@[deprecated (since := "2025-05-23")] alias not_mem_bot := notMem_bot

instance isEmpty_bot : IsEmpty (⊥ : AffineSubspace k P) :=
  Subtype.isEmpty_of_false fun _ ↦ notMem_bot _ _ _

variable (P)

/-- The direction of `⊥` is the submodule `⊥`. -/
@[simp]
theorem direction_bot : (⊥ : AffineSubspace k P).direction = ⊥ := by
  rw [direction_eq_vectorSpan, bot_coe, vectorSpan_def, vsub_empty, Submodule.span_empty]

variable {k V P}

@[simp]
theorem coe_eq_bot_iff (Q : AffineSubspace k P) : (Q : Set P) = ∅ ↔ Q = ⊥ :=
  coe_injective.eq_iff' (bot_coe _ _ _)

@[simp]
theorem coe_eq_univ_iff (Q : AffineSubspace k P) : (Q : Set P) = univ ↔ Q = ⊤ :=
  coe_injective.eq_iff' (top_coe _ _ _)

theorem nonempty_iff_ne_bot (Q : AffineSubspace k P) : (Q : Set P).Nonempty ↔ Q ≠ ⊥ := by
  rw [nonempty_iff_ne_empty]
  exact not_congr Q.coe_eq_bot_iff

theorem eq_bot_or_nonempty (Q : AffineSubspace k P) : Q = ⊥ ∨ (Q : Set P).Nonempty := by
  rw [nonempty_iff_ne_bot]
  apply eq_or_ne

instance [Subsingleton P] : IsSimpleOrder (AffineSubspace k P) where
  eq_bot_or_eq_top (s : AffineSubspace k P) := by
    rw [← coe_eq_bot_iff, ← coe_eq_univ_iff]
    rcases (s : Set P).eq_empty_or_nonempty with h | h
    · exact .inl h
    · exact .inr h.eq_univ

/-- A nonempty affine subspace is `⊤` if and only if its direction is `⊤`. -/
@[simp]
theorem direction_eq_top_iff_of_nonempty {s : AffineSubspace k P} (h : (s : Set P).Nonempty) :
    s.direction = ⊤ ↔ s = ⊤ := by
  constructor
  · intro hd
    rw [← direction_top k V P] at hd
    refine ext_of_direction_eq hd ?_
    simp [h]
  · rintro rfl
    simp

/-- The inf of two affine subspaces, coerced to a set, is the intersection of the two sets of
points. -/
@[simp]
theorem coe_inf (s₁ s₂ : AffineSubspace k P) : (s₁ ⊓ s₂ : Set P) = (s₁ : Set P) ∩ s₂ :=
  rfl

@[deprecated (since := "2025-08-31")] alias inf_coe := coe_inf

/-- A point is in the inf of two affine subspaces if and only if it is in both of them. -/
theorem mem_inf_iff (p : P) (s₁ s₂ : AffineSubspace k P) : p ∈ s₁ ⊓ s₂ ↔ p ∈ s₁ ∧ p ∈ s₂ :=
  Iff.rfl

/-- The direction of the inf of two affine subspaces is less than or equal to the inf of their
directions. -/
theorem direction_inf (s₁ s₂ : AffineSubspace k P) :
    (s₁ ⊓ s₂).direction ≤ s₁.direction ⊓ s₂.direction := by
  simp only [direction_eq_vectorSpan, vectorSpan_def]
  exact
    le_inf (sInf_le_sInf fun p hp => trans (vsub_self_mono inter_subset_left) hp)
      (sInf_le_sInf fun p hp => trans (vsub_self_mono inter_subset_right) hp)

/-- If two affine subspaces have a point in common, the direction of their inf equals the inf of
their directions. -/
theorem direction_inf_of_mem {s₁ s₂ : AffineSubspace k P} {p : P} (h₁ : p ∈ s₁) (h₂ : p ∈ s₂) :
    (s₁ ⊓ s₂).direction = s₁.direction ⊓ s₂.direction := by
  ext v
  rw [Submodule.mem_inf, ← vadd_mem_iff_mem_direction v h₁, ← vadd_mem_iff_mem_direction v h₂, ←
    vadd_mem_iff_mem_direction v ((mem_inf_iff p s₁ s₂).2 ⟨h₁, h₂⟩), mem_inf_iff]

/-- If two affine subspaces have a point in their inf, the direction of their inf equals the inf of
their directions. -/
theorem direction_inf_of_mem_inf {s₁ s₂ : AffineSubspace k P} {p : P} (h : p ∈ s₁ ⊓ s₂) :
    (s₁ ⊓ s₂).direction = s₁.direction ⊓ s₂.direction :=
  direction_inf_of_mem ((mem_inf_iff p s₁ s₂).1 h).1 ((mem_inf_iff p s₁ s₂).1 h).2

@[simp, norm_cast]
theorem coe_sInf (t : Set (AffineSubspace k P)) :
    ((sInf t : AffineSubspace k P) : Set P) = ⋂ s ∈ t, s :=
  rfl

theorem mem_sInf_iff (p : P) (t : Set (AffineSubspace k P)) : p ∈ sInf t ↔ ∀ s ∈ t, p ∈ s :=
  Set.mem_iInter₂

theorem direction_sInf (t : Set (AffineSubspace k P)) :
    direction (sInf t) ≤ ⨅ s ∈ t, s.direction := by
  simp only [direction_eq_vectorSpan, vectorSpan_def]
  exact le_iInf₂ fun s hs => Submodule.span_mono <| vsub_self_mono <| biInter_subset_of_mem hs

theorem direction_sInf_of_mem (t : Set (AffineSubspace k P)) (p : P) (h : ∀ s ∈ t, p ∈ s) :
    direction (sInf t) = ⨅ s ∈ t, s.direction := by
  apply (direction_sInf t).antisymm
  intro v hv
  rw [← vadd_mem_iff_mem_direction v ((mem_sInf_iff p t).mpr h), mem_sInf_iff]
  intro s hs
  rw [vadd_mem_iff_mem_direction v (h s hs)]
  simp only [Submodule.mem_iInf] at hv
  exact hv s hs

theorem direction_sInf_of_mem_sInf (t : Set (AffineSubspace k P)) (p : P) (h : p ∈ sInf t) :
    direction (sInf t) = ⨅ s ∈ t, s.direction :=
  direction_sInf_of_mem t p <| (mem_sInf_iff p t).mp h

@[simp, norm_cast]
theorem coe_iInf (s : ι → AffineSubspace k P) :
    ((iInf s : AffineSubspace k P) : Set P) = ⋂ i, s i := by
  rw [iInf, coe_sInf, Set.biInter_range]

theorem mem_iInf_iff (s : ι → AffineSubspace k P) (p : P) : p ∈ iInf s ↔ ∀ i, p ∈ s i := by
  rw [iInf, mem_sInf_iff, Set.forall_mem_range]

theorem direction_iInf (s : ι → AffineSubspace k P) :
    (iInf s).direction ≤ ⨅ i, (s i).direction := by
  apply (direction_sInf _).trans_eq
  rw [iInf_range]

theorem direction_iInf_of_mem (s : ι → AffineSubspace k P) (p : P) (h : ∀ i, p ∈ s i) :
    (iInf s).direction = ⨅ i, (s i).direction := by
  rw [iInf, direction_sInf_of_mem _ p ?_, iInf_range]
  rwa [Set.forall_mem_range]

theorem direction_iInf_of_mem_iInf (s : ι → AffineSubspace k P) (p : P) (h : p ∈ iInf s) :
    (iInf s).direction = ⨅ i, (s i).direction := by
  rw [iInf, direction_sInf_of_mem_sInf _ p h, iInf_range]

/-- If one affine subspace is less than or equal to another, the same applies to their
directions. -/
theorem direction_le {s₁ s₂ : AffineSubspace k P} (h : s₁ ≤ s₂) : s₁.direction ≤ s₂.direction := by
  simp only [direction_eq_vectorSpan, vectorSpan_def]
  exact vectorSpan_mono k h

/-- The sup of the directions of two affine subspaces is less than or equal to the direction of
their sup. -/
theorem sup_direction_le (s₁ s₂ : AffineSubspace k P) :
    s₁.direction ⊔ s₂.direction ≤ (s₁ ⊔ s₂).direction := by
  simp only [direction_eq_vectorSpan, vectorSpan_def]
  exact
    sup_le
      (sInf_le_sInf fun p hp => Set.Subset.trans (vsub_self_mono (le_sup_left : s₁ ≤ s₁ ⊔ s₂)) hp)
      (sInf_le_sInf fun p hp => Set.Subset.trans (vsub_self_mono (le_sup_right : s₂ ≤ s₁ ⊔ s₂)) hp)

/-- The sup of the directions of two nonempty affine subspaces with empty intersection is less than
the direction of their sup. -/
theorem sup_direction_lt_of_nonempty_of_inter_empty {s₁ s₂ : AffineSubspace k P}
    (h1 : (s₁ : Set P).Nonempty) (h2 : (s₂ : Set P).Nonempty) (he : (s₁ ∩ s₂ : Set P) = ∅) :
    s₁.direction ⊔ s₂.direction < (s₁ ⊔ s₂).direction := by
  obtain ⟨p₁, hp₁⟩ := h1
  obtain ⟨p₂, hp₂⟩ := h2
  rw [SetLike.lt_iff_le_and_exists]
  use sup_direction_le s₁ s₂, p₂ -ᵥ p₁,
    vsub_mem_direction ((le_sup_right : s₂ ≤ s₁ ⊔ s₂) hp₂) ((le_sup_left : s₁ ≤ s₁ ⊔ s₂) hp₁)
  intro h
  rw [Submodule.mem_sup] at h
  rcases h with ⟨v₁, hv₁, v₂, hv₂, hv₁v₂⟩
  rw [← sub_eq_zero, sub_eq_add_neg, neg_vsub_eq_vsub_rev, add_comm v₁, add_assoc, ←
    vadd_vsub_assoc, ← neg_neg v₂, add_comm, ← sub_eq_add_neg, ← vsub_vadd_eq_vsub_sub,
    vsub_eq_zero_iff_eq] at hv₁v₂
  refine Set.Nonempty.ne_empty ?_ he
  use v₁ +ᵥ p₁, vadd_mem_of_mem_direction hv₁ hp₁
  rw [hv₁v₂]
  exact vadd_mem_of_mem_direction (Submodule.neg_mem _ hv₂) hp₂

/-- If the directions of two nonempty affine subspaces span the whole module, they have nonempty
intersection. -/
theorem inter_nonempty_of_nonempty_of_sup_direction_eq_top {s₁ s₂ : AffineSubspace k P}
    (h1 : (s₁ : Set P).Nonempty) (h2 : (s₂ : Set P).Nonempty)
    (hd : s₁.direction ⊔ s₂.direction = ⊤) : ((s₁ : Set P) ∩ s₂).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hlt := sup_direction_lt_of_nonempty_of_inter_empty h1 h2 h
  rw [hd] at hlt
  exact not_top_lt hlt

/-- If the directions of two nonempty affine subspaces are complements of each other, they intersect
in exactly one point. -/
theorem inter_eq_singleton_of_nonempty_of_isCompl {s₁ s₂ : AffineSubspace k P}
    (h1 : (s₁ : Set P).Nonempty) (h2 : (s₂ : Set P).Nonempty)
    (hd : IsCompl s₁.direction s₂.direction) : ∃ p, (s₁ : Set P) ∩ s₂ = {p} := by
  obtain ⟨p, hp⟩ := inter_nonempty_of_nonempty_of_sup_direction_eq_top h1 h2 hd.sup_eq_top
  use p
  ext q
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hq1, hq2⟩
    have hqp : q -ᵥ p ∈ s₁.direction ⊓ s₂.direction :=
      ⟨vsub_mem_direction hq1 hp.1, vsub_mem_direction hq2 hp.2⟩
    rwa [hd.inf_eq_bot, Submodule.mem_bot, vsub_eq_zero_iff_eq] at hqp
  · exact fun h => h.symm ▸ hp

/-- Coercing a subspace to a set then taking the affine span produces the original subspace. -/
@[simp]
theorem affineSpan_coe (s : AffineSubspace k P) : affineSpan k (s : Set P) = s := by
  refine le_antisymm ?_ (subset_affineSpan _ _)
  rintro p ⟨p₁, hp₁, v, hv, rfl⟩
  exact vadd_mem_of_mem_direction hv hp₁

end AffineSubspace

section AffineSpace'

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AffineSpace V P]

variable {ι : Type*}

open AffineSubspace

section

variable {s : Set P}

/-- The affine span of a set is nonempty if and only if that set is. -/
theorem affineSpan_nonempty : (affineSpan k s : Set P).Nonempty ↔ s.Nonempty :=
  spanPoints_nonempty k s

alias ⟨_, _root_.Set.Nonempty.affineSpan⟩ := affineSpan_nonempty

/-- The affine span of a nonempty set is nonempty. -/
instance [Nonempty s] : Nonempty (affineSpan k s) :=
  ((nonempty_coe_sort.1 ‹_›).affineSpan _).to_subtype

/-- The affine span of a set is `⊥` if and only if that set is empty. -/
@[simp]
theorem affineSpan_eq_bot : affineSpan k s = ⊥ ↔ s = ∅ := by
  rw [← not_iff_not, ← Ne, ← Ne, ← nonempty_iff_ne_bot, affineSpan_nonempty,
    nonempty_iff_ne_empty]

@[simp]
theorem bot_lt_affineSpan : ⊥ < affineSpan k s ↔ s.Nonempty := by
  rw [bot_lt_iff_ne_bot, nonempty_iff_ne_empty]
  exact (affineSpan_eq_bot _).not

@[simp]
lemma affineSpan_eq_top_iff_nonempty_of_subsingleton [Subsingleton P] :
    affineSpan k s = ⊤ ↔ s.Nonempty := by
  rw [← bot_lt_affineSpan k, IsSimpleOrder.bot_lt_iff_eq_top]

end

variable {k}

/-- An induction principle for span membership. If `p` holds for all elements of `s` and is
preserved under certain affine combinations, then `p` holds for all elements of the span of `s`. -/
@[elab_as_elim]
theorem affineSpan_induction {x : P} {s : Set P} {p : P → Prop} (h : x ∈ affineSpan k s)
    (mem : ∀ x : P, x ∈ s → p x)
    (smul_vsub_vadd : ∀ (c : k) (u v w : P), p u → p v → p w → p (c • (u -ᵥ v) +ᵥ w)) : p x :=
  (affineSpan_le (Q := ⟨p, smul_vsub_vadd⟩)).mpr mem h

/-- A dependent version of `affineSpan_induction`. -/
@[elab_as_elim]
theorem affineSpan_induction' {s : Set P} {p : ∀ x, x ∈ affineSpan k s → Prop}
    (mem : ∀ (y) (hys : y ∈ s), p y (subset_affineSpan k _ hys))
    (smul_vsub_vadd : ∀ (c : k) (u hu v hv w hw), p u hu → p v hv → p w hw →
      p (c • (u -ᵥ v) +ᵥ w) (AffineSubspace.smul_vsub_vadd_mem _ _ hu hv hw))
    {x : P} (h : x ∈ affineSpan k s) : p x h := by
  suffices ∃ (hx : x ∈ affineSpan k s), p x hx from this.elim fun hx hc ↦ hc
  -- TODO: `induction h using affineSpan_induction` gives the error:
  -- extra targets for '@affineSpan_induction'
  -- It seems that the `induction` tactic has decided to ignore the clause
  -- `using affineSpan_induction` and use `Exists.rec` instead.
  refine affineSpan_induction h ?mem ?smul_vsub_vadd
  · exact fun y hy ↦ ⟨subset_affineSpan _ _ hy, mem y hy⟩
  · exact fun c u v w hu hv hw ↦
      hu.elim fun hu' hu ↦ hv.elim fun hv' hv ↦ hw.elim fun hw' hw ↦
        ⟨AffineSubspace.smul_vsub_vadd_mem _ _ hu' hv' hw',
              smul_vsub_vadd _ _ _ _ _ _ _ hu hv hw⟩

variable (k)

/-- The difference between two points lies in their `vectorSpan`. -/
theorem vsub_mem_vectorSpan_pair (p₁ p₂ : P) : p₁ -ᵥ p₂ ∈ vectorSpan k ({p₁, p₂} : Set P) :=
  vsub_mem_vectorSpan _ (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-- The difference between two points (reversed) lies in their `vectorSpan`. -/
theorem vsub_rev_mem_vectorSpan_pair (p₁ p₂ : P) : p₂ -ᵥ p₁ ∈ vectorSpan k ({p₁, p₂} : Set P) :=
  vsub_mem_vectorSpan _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)) (Set.mem_insert _ _)

variable {k}

/-- A multiple of the difference between two points lies in their `vectorSpan`. -/
theorem smul_vsub_mem_vectorSpan_pair (r : k) (p₁ p₂ : P) :
    r • (p₁ -ᵥ p₂) ∈ vectorSpan k ({p₁, p₂} : Set P) :=
  Submodule.smul_mem _ _ (vsub_mem_vectorSpan_pair k p₁ p₂)

/-- A multiple of the difference between two points (reversed) lies in their `vectorSpan`. -/
theorem smul_vsub_rev_mem_vectorSpan_pair (r : k) (p₁ p₂ : P) :
    r • (p₂ -ᵥ p₁) ∈ vectorSpan k ({p₁, p₂} : Set P) :=
  Submodule.smul_mem _ _ (vsub_rev_mem_vectorSpan_pair k p₁ p₂)

variable (k)

/-- The line between two points, as an affine subspace. -/
notation "line[" k ", " p₁ ", " p₂ "]" =>
  affineSpan k (insert p₁ (@singleton _ _ Set.instSingletonSet p₂))

/-- The first of two points lies in their affine span. -/
theorem left_mem_affineSpan_pair (p₁ p₂ : P) : p₁ ∈ line[k, p₁, p₂] :=
  mem_affineSpan _ (Set.mem_insert _ _)

/-- The second of two points lies in their affine span. -/
theorem right_mem_affineSpan_pair (p₁ p₂ : P) : p₂ ∈ line[k, p₁, p₂] :=
  mem_affineSpan _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))

variable {k}

/-- The span of two points that lie in an affine subspace is contained in that subspace. -/
theorem affineSpan_pair_le_of_mem_of_mem {p₁ p₂ : P} {s : AffineSubspace k P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) : line[k, p₁, p₂] ≤ s := by
  rw [affineSpan_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨hp₁, hp₂⟩

/-- One line is contained in another differing in the first point if the first point of the first
line is contained in the second line. -/
theorem affineSpan_pair_le_of_left_mem {p₁ p₂ p₃ : P} (h : p₁ ∈ line[k, p₂, p₃]) :
    line[k, p₁, p₃] ≤ line[k, p₂, p₃] :=
  affineSpan_pair_le_of_mem_of_mem h (right_mem_affineSpan_pair _ _ _)

/-- One line is contained in another differing in the second point if the second point of the
first line is contained in the second line. -/
theorem affineSpan_pair_le_of_right_mem {p₁ p₂ p₃ : P} (h : p₁ ∈ line[k, p₂, p₃]) :
    line[k, p₂, p₁] ≤ line[k, p₂, p₃] :=
  affineSpan_pair_le_of_mem_of_mem (left_mem_affineSpan_pair _ _ _) h

variable (k)

/-- `affineSpan` is monotone. -/
@[gcongr, mono]
theorem affineSpan_mono {s₁ s₂ : Set P} (h : s₁ ⊆ s₂) : affineSpan k s₁ ≤ affineSpan k s₂ :=
  affineSpan_le_of_subset_coe (Set.Subset.trans h (subset_affineSpan k _))

/-- Taking the affine span of a set, adding a point and taking the span again produces the same
results as adding the point to the set and taking the span. -/
theorem affineSpan_insert_affineSpan (p : P) (ps : Set P) :
    affineSpan k (insert p (affineSpan k ps : Set P)) = affineSpan k (insert p ps) := by
  rw [Set.insert_eq, Set.insert_eq, span_union, span_union, affineSpan_coe]

/-- If a point is in the affine span of a set, adding it to that set does not change the affine
span. -/
theorem affineSpan_insert_eq_affineSpan {p : P} {ps : Set P} (h : p ∈ affineSpan k ps) :
    affineSpan k (insert p ps) = affineSpan k ps := by
  rw [← mem_coe] at h
  rw [← affineSpan_insert_affineSpan, Set.insert_eq_of_mem h, affineSpan_coe]

variable {k}

/-- If a point is in the affine span of a set, adding it to that set does not change the vector
span. -/
theorem vectorSpan_insert_eq_vectorSpan {p : P} {ps : Set P} (h : p ∈ affineSpan k ps) :
    vectorSpan k (insert p ps) = vectorSpan k ps := by
  simp_rw [← direction_affineSpan, affineSpan_insert_eq_affineSpan _ h]

/-- When the affine space is also a vector space, the affine span is contained within the linear
span. -/
lemma affineSpan_le_toAffineSubspace_span {s : Set V} :
    affineSpan k s ≤ (Submodule.span k s).toAffineSubspace := by
  intro x hx
  simp only [SetLike.mem_coe, Submodule.mem_toAffineSubspace]
  induction hx using affineSpan_induction' with
  | mem x hx => exact Submodule.subset_span hx
  | smul_vsub_vadd c u _ v _ w _ hu hv hw =>
    simp only [vsub_eq_sub, vadd_eq_add]
    apply Submodule.add_mem _ _ hw
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hu hv)

lemma affineSpan_subset_span {s : Set V} :
    (affineSpan k s : Set V) ⊆  Submodule.span k s :=
  affineSpan_le_toAffineSubspace_span

-- TODO: We want this to be simp, but `affineSpan` gets simp-ed away to `spanPoints`!
-- Let's delete `spanPoints`
lemma affineSpan_insert_zero (s : Set V) :
    (affineSpan k (insert 0 s) : Set V) = Submodule.span k s := by
  rw [← Submodule.span_insert_zero]
  refine affineSpan_subset_span.antisymm ?_
  rw [← vectorSpan_add_self, vectorSpan_def]
  refine Subset.trans ?_ <| subset_add_left _ <| mem_insert ..
  gcongr
  exact subset_sub_left <| mem_insert ..

end AffineSpace'
