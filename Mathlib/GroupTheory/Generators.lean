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

* `Group.Generators G ι`: The generators of a group are given by a generating family indexed by `ι`
and an assignment `val : ι → G` such that `Subgroup.closure (Set.range val) = ⊤`.

## Main results

* `Group.Generators.hom_ext`: if two homomorphisms coincide on the elements of a generating family,
  then they are equal.
* `Group.fg_iff_nonempty_finite_generators`: a group is finitely generated if and only if it
  admits a finite generating family.

## Implementation notes

* The index type `ι` is a parameter, not a field, following the pattern of `Algebra.Generators`.
* Unlike `Algebra.Generators`, this structure bundles no section of `FreeGroup.lift val`,
  it just bundles a proof of surjectivity.

## References

* [D. F. Holt, S. Rees, C. E. Röver, *Groups, Languages and Automata*][HoltReesRover2017], §1

## Tags

group generators, generating set, finitely generated
-/

@[expose] public section

variable {G H ι ι' : Type*} [Group G] [Group H]

/-- The generators of a group are given by a generating family indexed by `ι` and an assignment
`val : ι → G` such that `Subgroup.closure (Set.range val) = ⊤`. -/
structure Group.Generators (G : Type*) [Group G] (ι : Type*) where
  /-- The generating family itself: `val i` is the element of `G` indexed by `i : ι`. -/
  val : ι → G
  /-- The subgroup closure of the generators is the whole group. -/
  closure_eq_top : Subgroup.closure (Set.range val) = ⊤

namespace Group.Generators

variable (P : Group.Generators G ι)

/-- The canonical surjection from the free group on the generators to `G`. -/
abbrev lift : FreeGroup ι →* G := FreeGroup.lift P.val

lemma lift_surjective : Function.Surjective P.lift :=
  FreeGroup.lift_surjective_iff_closure_range_eq_top.mpr P.closure_eq_top

@[deprecated (since := "2026-08-21")]
alias lift_val_surjective := lift_surjective

@[simp]
lemma range_lift_eq_top : P.lift.range = ⊤ := MonoidHom.range_eq_top.mpr P.lift_surjective

/-- If two homomorphisms coincide on the elements of a generating family, then they are equal. -/
theorem hom_ext {M : Type*} [Monoid M] (f g : G →* M) (h : ∀ i, f (P.val i) = g (P.val i)) :
    f = g := MonoidHom.eq_of_eqOn_dense P.closure_eq_top (Set.forall_mem_range.mpr h)

/-- The generating family obtained using a generating set `S : Set G`. -/
def ofSet {S : Set G} (h : Subgroup.closure S = ⊤) : Group.Generators G S where
  val := Subtype.val
  closure_eq_top := by rwa [Subtype.range_coe]

@[simp]
lemma ofSet_val {S : Set G} (hS : Subgroup.closure S = ⊤) :
    (Group.Generators.ofSet hS).val = Subtype.val :=
  rfl

/-- The generating family given by a the canonical surjection from `FreeGroup ι`. -/
def ofFreeGroupHom (φ : FreeGroup ι →* G) (hφ : Function.Surjective φ) :
    Group.Generators G ι where
  val := φ ∘ FreeGroup.of
  closure_eq_top := by
    rw [Set.range_comp, ← MonoidHom.map_closure, FreeGroup.closure_range_of,
      Subgroup.map_top_of_surjective φ hφ]

@[simp]
lemma ofFreeGroupHom_val (φ : FreeGroup ι →* G) (hφ : Function.Surjective φ) :
    (Group.Generators.ofFreeGroupHom φ hφ).val = φ ∘ FreeGroup.of :=
  rfl

/-- The canonical surjection attached to `ofFreeGroupHom φ hφ` is `φ`. -/
@[simp]
lemma ofFreeGroupHom_lift (φ : FreeGroup ι →* G) (hφ : Function.Surjective φ) :
    (Group.Generators.ofFreeGroupHom φ hφ).lift = φ :=
  FreeGroup.lift.apply_symm_apply φ

/-- The transport of a generating family along a surjective homomorphism. -/
protected def map (f : G →* H) (hf : Function.Surjective f) : Group.Generators H ι where
  val := f ∘ P.val
  closure_eq_top := by
    rw [Set.range_comp, ← MonoidHom.map_closure, P.closure_eq_top,
      Subgroup.map_top_of_surjective f hf]

@[simp]
lemma map_val (P : Group.Generators G ι) (f : G →* H) (hf : Function.Surjective f) :
    (P.map f hf).val = f ∘ P.val :=
  rfl

/-- The transport of a generating family along a surjection of index types. -/
def reindex (P : Group.Generators G ι) {e : ι' → ι} (he : Function.Surjective e) :
    Group.Generators G ι' where
  val := P.val ∘ e
  closure_eq_top := by rw [Set.range_comp, he.range_eq, Set.image_univ, P.closure_eq_top]

@[simp]
lemma reindex_val (P : Group.Generators G ι) {e : ι' → ι} (he : Function.Surjective e) :
    (P.reindex he).val = P.val ∘ e :=
  rfl

/-- If `G` has a finite generating family, then `G` is finitely generated. -/
theorem fg [Finite ι] (P : Group.Generators G ι) : Group.FG G :=
  Group.fg_of_surjective P.lift_surjective

end Group.Generators

/-- A group is finitely generated if and only if it admits a finite generating family. -/
theorem Group.fg_iff_nonempty_finite_generators :
    Group.FG G ↔ ∃ n : ℕ, Nonempty (Group.Generators G (Fin n)) := by
  constructor
  · rintro ⟨S, hS⟩
    exact ⟨S.card, ⟨(Group.Generators.ofSet hS).reindex S.equivFin.symm.surjective⟩⟩
  · rintro ⟨n, ⟨P⟩⟩
    exact P.fg
