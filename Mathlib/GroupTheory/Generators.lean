/-
Copyright (c) 2026 Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su
-/
module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Group generators as data

## Main definitions

* `Group.Generators G α`: The generators of a group are given by a generating family indexed by `α`
and an assignment `val : α → G` such that `Subgroup.closure (Set.range val) = ⊤`.

## Main results

* `Group.Generators.hom_ext`: if two homomorphisms coincide on the elements of a generating family,
  then they are equal.
* `Group.fg_iff_nonempty_finite_generators`: a group is finitely generated if and only if it
  admits a finite generating family.

## Implementation notes

* The index type `α` is a parameter, not a field, following the pattern of `Algebra.Generators`.

* Unlike `Algebra.Generators`, this structure bundles no section of `FreeGroup.lift val`,
  it just bundles a proof of surjectivity.

## References

* [D. F. Holt, S. Rees, C. E. Röver, *Groups, Languages and Automata*][HoltReesRover2017], §1

## Tags

group generators, generating set, finitely generated
-/

@[expose] public section

variable {G H α β : Type*} [Group G] [Group H]

/-- The generators of a group are given by a generating family indexed by `α` and an assignment
`val : α → G` such that `Subgroup.closure (Set.range val) = ⊤`. -/
structure Group.Generators (G : Type*) [Group G] (α : Type*) where
  /-- The generating family itself: `val a` is the element of `G` indexed by `a : α`. -/
  val : α → G
  /-- The subgroup closure of the generators is the whole group. -/
  closure_eq_top : Subgroup.closure (Set.range val) = ⊤

namespace Group.Generators

variable (P : Group.Generators G α)

theorem lift_val_surjective : Function.Surjective (FreeGroup.lift P.val) :=
  FreeGroup.lift_surjective_iff_closure_range_eq_top.mpr P.closure_eq_top

/-- If two homomorphisms coincide on the elements of a generating family, then they are equal. -/
theorem hom_ext {M : Type*} [Monoid M] (f g : G →* M) (h : ∀ a, f (P.val a) = g (P.val a)) :
    f = g := MonoidHom.eq_of_eqOn_dense P.closure_eq_top (Set.forall_mem_range.mpr h)

/-- The generating family obtained using a generating set `S : Set G`. -/
def ofSet {S : Set G} (h : Subgroup.closure S = ⊤) :
    Group.Generators G S where
  val :=  Subtype.val
  closure_eq_top := by
    rwa [Subtype.range_coe]

@[simp]
lemma ofSet_val {S : Set G} (hS : Subgroup.closure S = ⊤) :
    (Group.Generators.ofSet hS).val = Subtype.val := rfl

/-- The transport of a generating family along a surjective homomorphism. -/
protected def map (f : G →* H) (hf : Function.Surjective f) :
    Group.Generators H α where
  val := f ∘ P.val
  closure_eq_top := by
    rw [Set.range_comp, ← MonoidHom.map_closure, P.closure_eq_top,
      Subgroup.map_top_of_surjective f hf]

@[simp]
lemma map_val (P : Group.Generators G α) (f : G →* H) (hf : Function.Surjective f) :
  (P.map f hf).val = f ∘ P.val := rfl

/-- The transport of a generating family along an equivalence of index types. -/
def reindex (P : Group.Generators G α) (e : β ≃ α) :
    Group.Generators G β where
  val := P.val ∘ e
  closure_eq_top := by
    rw [Set.range_comp, EquivLike.range_eq_univ, Set.image_univ, P.closure_eq_top]

@[simp]
lemma reindex_val (P : Group.Generators G α) (e : β ≃ α) :
    (P.reindex e).val = P.val ∘ e := rfl

/-- If `G` has a finite generating family, then `G` is finitely generated. -/
theorem fg [Finite α] (P : Group.Generators G α) : Group.FG G :=
  Group.fg_of_surjective P.lift_val_surjective

end Group.Generators

/-- A group is finitely generated if and only if it admits a finite generating family. -/
theorem Group.fg_iff_nonempty_finite_generators :
    Group.FG G ↔ ∃ n : ℕ, Nonempty (Group.Generators G (Fin n)) := by
  constructor
  · rintro ⟨S, hS⟩
    exact ⟨S.card, ⟨(Group.Generators.ofSet hS).reindex S.equivFin.symm⟩⟩
  · rintro ⟨n, ⟨P⟩⟩
    exact P.fg
