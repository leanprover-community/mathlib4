/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplicesSubcomplex
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.IsUniquelyCodimOneFace

/-!
# Pairings

In this file, we introduce the definition of a pairing for a subcomplex `A`
of a simplicial set `X`, following the ideas by Sean Moss,
*Another approach to the Kan-Quillen model structure*, who gave a
complete combinatorial characterization of strong (inner) anodyne extensions.
Strong (inner) anodyne extensions are transfinite compositions of pushouts of coproducts
of (inner) horn inclusions, i.e. this is similar to (inner) anodyne extensions but
without the stability property under retracts.

A pairing for `A` consists in the data of a partition of the nondegenerate
simplices of `X` not in `A` into type (I) simplices and type (II) simplices,
and of a bijection between the types of type (I) and type (II) simplices.
Indeed, the main observation is that when we attach a simplex along a horn
inclusion, exactly two nondegenerate simplices are added: this simplex,
and the unique face which is not in the image of the horn. The former shall be
considered as of type (I) and the latter as type (II).

We say that a pairing is *regular* (typeclass `Pairing.IsRegular`) when
- it is proper (`Pairing.IsProper`), i.e. any type (II) simplex is uniquely
a face of the corresponding type (I) simplex.
- a certain ancestrality relation is well founded.
When these conditions are satisfied, the inclusion `A.ι : A ⟶ X` is
a strong anodyne extension (TODO @joelriou), and the converse is also true
(if `A.ι` is a strong anodyne extension, then there is a regular pairing for `A` (TODO)).

## References
* [Sean Moss, *Another approach to the Kan-Quillen model structure*][moss-2020]

-/

universe u

namespace SSet.Subcomplex

variable {X : SSet.{u}} (A : X.Subcomplex)

/-- A pairing for a subcomplex `A` of a simplicial set `X` consists of a partition
of the nondegenerate simplices of `X` not in `A` in two types (I) and (II) of simplices,
and a bijection between the type (II) simplices and the type (I) simplices.
See the introduction of the file `AlgebraicTopology.SimplicialSet.AnodyneExtensions.Pairing`. -/
structure Pairing where
  /-- the set of type (I) simplices -/
  I : Set A.N
  /-- the set of type (II) simplices -/
  II : Set A.N
  inter : I ∩ II = ∅
  union : I ∪ II = Set.univ
  /-- a bijection from the type (II) simplices to the type (I) simplices -/
  p : II ≃ I

namespace Pairing

variable {A} (P : A.Pairing)

/-- A pairing is regular when each type (II) simplex
is uniquely a `1`-codimensional face of the corresponding (I)
simplex. -/
class IsProper where
  isUniquelyCodimOneFace (x : P.II) :
    S.IsUniquelyCodimOneFace x.1.toS (P.p x).1.toS

lemma isUniquelyCodimOneFace [P.IsProper] (x : P.II) :
    S.IsUniquelyCodimOneFace x.1.toS (P.p x).1.toS :=
  IsProper.isUniquelyCodimOneFace x

@[simp]
lemma dim_p [P.IsProper] (x : P.II) :
    (P.p x).1.dim = x.1.dim + 1 :=
  (P.isUniquelyCodimOneFace x).dim_eq

/-- The condition that a pairing only involves inner horns. -/
class IsInner [P.IsProper] : Prop where
  ne_zero (x : P.II) {d : ℕ} (hd : x.1.dim = d) :
    (P.isUniquelyCodimOneFace x).index hd ≠ 0
  ne_last (x : P.II) {d : ℕ} (hd : x.1.dim = d) :
    (P.isUniquelyCodimOneFace x).index hd ≠ Fin.last _

/-- The ancestrality relation on type (II) simplices. -/
def AncestralRel (x y : P.II) : Prop :=
  x ≠ y ∧ x.1 < (P.p y).1

variable {P} in
lemma AncestralRel.dim_le [P.IsProper] {x y : P.II} (hxy : P.AncestralRel x y) :
    x.1.dim ≤ y.1.dim := by
  simpa only [(P.isUniquelyCodimOneFace y).dim_eq, Nat.lt_succ_iff] using
    SSet.N.dim_lt_of_lt hxy.2

/-- A proper pairing is regular when the ancestrality relation
is well founded. -/
class IsRegular extends P.IsProper where
  wf : WellFounded P.AncestralRel

section

variable [P.IsRegular]

lemma wf : WellFounded P.AncestralRel := IsRegular.wf

instance : IsWellFounded _ P.AncestralRel where
  wf := P.wf

end

lemma exists_or (x : A.N) :
    ∃ (y : P.II), x = y ∨ x = P.p y := by
  have := Set.mem_univ x
  rw [← P.union, Set.mem_union] at this
  obtain h | h := this
  · obtain ⟨y, hy⟩ := P.p.surjective ⟨x, h⟩
    exact ⟨y, Or.inr (by rw [hy])⟩
  · exact ⟨⟨_, h⟩, Or.inl rfl⟩

lemma neq (x : P.I) (y : P.II) :
    x.1 ≠ y.1 := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  rintro rfl
  have : x ∈ P.I ∩ P.II := ⟨hx, hy⟩
  simp [P.inter] at this

end Pairing

end SSet.Subcomplex
