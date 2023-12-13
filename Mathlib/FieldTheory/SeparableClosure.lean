/-
Copyright (c) 2023 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.FieldTheory.IsSepClosed

/-!

# Separable closure

This file contains basics about the (relative) separable closure of a field extension.

## Main definitions

- `separableClosure`: the (relative) separable closure of `E / F`, or called maximal separable
  subextension of `E / F`, is defined to be the intermediate field of `E / F` consisting of all
  separable elements.

- `Field.sepDegree F E`: the (infinite) separable degree $[E:F]_s$ of an algebraic extension
  `E / F` of fields, defined to be the degree of `separableClosure F E / F`. Later we will show
  that (`Field.finSepDegree_eq`, not in this file), if `Field.Emb F E` is finite, then this
  coincides with `Field.finSepDegree F E`.

- `Field.insepDegree F E`: the (infinite) inseparable degree $[E:F]_i$ of an algebraic extension
  `E / F` of fields, defined to be the degree of `E / separableClosure F E`.

- `Field.finInsepDegree F E`: the (finite) inseparable degree $[E:F]_i$ of an algebraic extension
  `E / F` of fields, defined to be the degree of `E / separableClosure F E` as a natural number.
  It is zero if such field extension is not finite.

## Main results

- `le_separableClosure_iff`: an intermediate field of `E / F` is contained in the (relative)
  separable closure of `E / F` if and only if it is separable over `F`.

- `separableClosure.normalClosure_eq_self`: the normal closure of the (relative) separable
  closure of `E / F` is equal to itself.

- `separableClosure.normal`: the (relative) separable closure of a normal extension is normal.

- `separableClosure.isSepClosure`: the (relative) separable closure of a separably closed extension
  is a separable closure of the base field.

- `Field.isSeparable_adjoin_iff_separable`: `F(S) / F` is a separable extension if and only if
  all elements of `S` are separable elements.

- `separableClosure.eq_top_iff`: the (relative) separable closure of `E / F` is equal to `E`
  if and only if `E / F` is separable.

## Tags

separable degree, degree, separable closure

-/

open scoped Classical Polynomial

open FiniteDimensional Polynomial IntermediateField Field

noncomputable section

universe u v w

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]

variable (K : Type w) [Field K] [Algebra F K]

section separableClosure

/-- The (relative) separable closure of `E / F`, or called maximal separable subextension
of `E / F`, is defined to be the intermediate field of `E / F` consisting of all separable
elements. The previous results prove that these elements are closed under field operations. -/
def separableClosure : IntermediateField F E where
  carrier := {x | IsIntegral F x ∧ (minpoly F x).Separable}
  mul_mem' := separable_mul F E
  one_mem' := (map_one (algebraMap F E)) ▸ separable_algebraMap F E 1
  add_mem' := separable_add F E
  zero_mem' := (map_zero (algebraMap F E)) ▸ separable_algebraMap F E 0
  algebraMap_mem' := separable_algebraMap F E
  inv_mem' := separable_inv F E

namespace Field

/-- The (infinite) separable degree for a general field extension `E / F` is defined
to be the degree of `(separableClosure F E) / F`. -/
def sepDegree := Module.rank F (separableClosure F E)

/-- The (infinite) inseparable degree for a general field extension `E / F` is defined
to be the degree of `E / (separableClosure F E)`. -/
def insepDegree := Module.rank (separableClosure F E) E

/-- The (finite) inseparable degree for a general field extension `E / F` is defined
to be the degree of `E / (separableClosure F E)` as a natural number. It is defined to be zero
if such field extension is infinite. -/
def finInsepDegree : ℕ := Cardinal.toNat (insepDegree F E)

/-- The (infinite) separable degree multiply by the (infinite) inseparable degree is equal
to the (infinite) field extension degree. -/
theorem sepDegree_mul_insepDegree : sepDegree F E * insepDegree F E = Module.rank F E :=
  rank_mul_rank F (separableClosure F E) E

end Field

/-- An element is contained in the (relative) separable closure of `E / F` if and only if
it is a separable element. -/
theorem mem_separableClosure_iff {x : E} :
    x ∈ separableClosure F E ↔ IsIntegral F x ∧ (minpoly F x).Separable := by
  simp only [separableClosure]; rfl

/-- The (relative) separable closure of `E / F` is algebraic over `F`. -/
theorem separableClosure.isAlgebraic : Algebra.IsAlgebraic F (separableClosure F E) :=
  fun x ↦ isAlgebraic_iff.2 x.2.1.isAlgebraic

/-- The (relative) separable closure of `E / F` is separable over `F`. -/
instance separableClosure.isSeparable : IsSeparable F (separableClosure F E) :=
  ⟨fun x ↦ by simpa only [minpoly_eq] using x.2.2⟩

/-- An intermediate field of `E / F` is contained in the (relative) separable closure of `E / F`
if all of its elements are separable over `F`. -/
theorem le_separableClosure' {L : IntermediateField F E} (halg : Algebra.IsAlgebraic F L)
    (hsep : ∀ x : L, (minpoly F x).Separable) : L ≤ separableClosure F E := fun x h ↦
  ⟨isIntegral_iff.1 (halg ⟨x, h⟩).isIntegral, by simpa only [minpoly_eq] using hsep ⟨x, h⟩⟩

/-- An intermediate field of `E / F` is contained in the (relative) separable closure of `E / F`
if it is separable over `F`. -/
theorem le_separableClosure (L : IntermediateField F E)
    [IsSeparable F L] : L ≤ separableClosure F E :=
  le_separableClosure' F E (fun x ↦ (IsSeparable.isIntegral F x).isAlgebraic)
    (IsSeparable.separable F)

/-- An intermediate field of `E / F` is contained in the (relative) separable closure of `E / F`
if and only if it is separable over `F`. -/
theorem le_separableClosure_iff (L : IntermediateField F E) :
    L ≤ separableClosure F E ↔ IsSeparable F L :=
  ⟨fun h ↦ isSeparable_iff.2 fun x ↦ by simpa only [isIntegral_iff, minpoly_eq] using h x.2,
    fun _ ↦ le_separableClosure _ _ _⟩

/-- The normal closure of the (relative) separable closure of `E / F` is equal to itself. -/
theorem separableClosure.normalClosure_eq_self :
    normalClosure F (separableClosure F E) E = separableClosure F E := by
  apply le_antisymm ?_ (le_normalClosure _)
  rw [normalClosure_le_iff]
  intro i
  let i' : (separableClosure F E) ≃ₐ[F] i.fieldRange := AlgEquiv.ofInjectiveField i
  haveI := i'.isSeparable
  exact le_separableClosure F E _

/-- If `E` is normal over `F`, then the (relative) separable closure of `E / F` is also normal
over `F`. -/
instance separableClosure.normal [Normal F E] : Normal F (separableClosure F E) := by
  rw [← separableClosure.normalClosure_eq_self]
  exact normalClosure.normal F _ E

/-- If `E` is separably closed, then the (relative) separable closure of `E / F` is a
separable closure of `F`. -/
instance separableClosure.isSepClosure [IsSepClosed E] : IsSepClosure F (separableClosure F E) := by
  refine ⟨IsSepClosed.of_exists_root _ fun p hp hirr hsep ↦ ?_, isSeparable F E⟩
  obtain ⟨x, hx⟩ := IsSepClosed.exists_aeval_eq_zero E p (degree_pos_of_irreducible hirr).ne' hsep
  haveI := (isSeparable_adjoin_simple_iff_separable _ E).2
    ⟨IsAlgebraic.isIntegral ⟨p, hp.ne_zero, hx⟩, hsep.of_dvd <| minpoly.dvd _ x hx⟩
  let L := separableClosure F E
  letI : Algebra L L⟮x⟯ := Subalgebra.algebra L⟮x⟯.toSubalgebra
  letI : Module L L⟮x⟯ := Algebra.toModule
  letI : SMul L L⟮x⟯ := Algebra.toSMul
  haveI : IsScalarTower F L L⟮x⟯ := IntermediateField.isScalarTower L⟮x⟯
  haveI : IsSeparable F (restrictScalars F L⟮x⟯) := IsSeparable.trans F L L⟮x⟯
  have : x ∈ restrictScalars F L⟮x⟯ := mem_adjoin_simple_self _ x
  use ⟨x, le_separableClosure F E (restrictScalars F L⟮x⟯) this⟩
  apply_fun algebraMap L E using (algebraMap L E).injective
  rwa [map_zero, ← aeval_algebraMap_apply_eq_algebraMap_eval]

/-- `F(S) / F` is a separable extension if and only if all elements of `S` are
separable elements. -/
theorem Field.isSeparable_adjoin_iff_separable {S : Set E} :
    IsSeparable F (adjoin F S) ↔ ∀ x ∈ S, IsIntegral F x ∧ (minpoly F x).Separable := by
  simp only [← le_separableClosure_iff, ← mem_separableClosure_iff]
  exact ⟨fun h x hx ↦ (adjoin.mono F _ _ <| Set.singleton_subset_iff.2 hx).trans h <|
    mem_adjoin_simple_self F x, adjoin_le_iff.2⟩

/-- The (relative) separable closure of `E / F` is equal to `E` if and only if `E / F` is
separable. -/
theorem separableClosure.eq_top_iff : separableClosure F E = ⊤ ↔ IsSeparable F E :=
  ⟨fun h ↦ isSeparable_iff.2 fun _ ↦ (mem_separableClosure_iff F E).1 (h ▸ mem_top),
    fun h ↦ top_unique <| fun x _ ↦ (mem_separableClosure_iff F E).2 ((isSeparable_iff.1 h) x)⟩

end separableClosure
