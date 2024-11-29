/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.FieldTheory.Adjoin
import Mathlib.RingTheory.LinearDisjoint

/-!

# Linearly disjoint fields

This file contains basics about the linearly disjoint fields.

## Linear disjoint intermediate fields

We adapt the definitions in <https://en.wikipedia.org/wiki/Linearly_disjoint>.
See the file `Mathlib/LinearAlgebra/LinearDisjoint.lean` for details.

### Main definitions

- `IntermediateField.LinearDisjoint`: an intermediate field `A` of `E / F`
  and an abstract field `L` between `E / F`
  (as a special case, two intermediate fields) are linearly disjoint over `F`,
  if they are linearly disjoint as subalgebras (`Subalgebra.LinearDisjoint`).

### Implementation notes

The `Subalgebra.LinearDisjoint` is stated for two `Subalgebra`s. The original design of
`IntermediateField.LinearDisjoint` is also stated for two `IntermediateField`s
(see `IntermediateField.linearDisjoint_iff'` for the original statement).
But it's probably useful if one of them can be generalized to an abstract field
(see <https://github.com/leanprover-community/mathlib4/pull/9651#discussion_r1464070324>).
This leads to the current design of `IntermediateField.LinearDisjoint`
which is for one `IntermediateField` and one abstract field.
It is not generalized to two abstract fields as this will break the dot notation.

### Main results

Equivalent characterization of linear disjointness:

- `IntermediateField.LinearDisjoint.linearIndependent_left`:
  if `A` and `L` are linearly disjoint, then any `F`-linearly independent family on `A` remains
  linearly independent over `L`.

- `IntermediateField.LinearDisjoint.of_basis_left`:
  conversely, if there exists an `F`-basis of `A` which remains linearly independent over `L`, then
  `A` and `L` are linearly disjoint.

- `IntermediateField.LinearDisjoint.linearIndependent_right`:
  `IntermediateField.LinearDisjoint.linearIndependent_right'`:
  if `A` and `L` are linearly disjoint, then any `F`-linearly independent family on `L` remains
  linearly independent over `A`.

- `IntermediateField.LinearDisjoint.of_basis_right`:
  `IntermediateField.LinearDisjoint.of_basis_right'`:
  conversely, if there exists an `F`-basis of `L` which remains linearly independent over `A`, then
  `A` and `L` are linearly disjoint.

- `IntermediateField.LinearDisjoint.linearIndependent_mul`:
  `IntermediateField.LinearDisjoint.linearIndependent_mul'`:
  if `A` and `L` are linearly disjoint, then for any family of
  `F`-linearly independent elements `{ a_i }` of `A`, and any family of
  `F`-linearly independent elements `{ b_j }` of `L`, the family `{ a_i * b_j }` in `S` is
  also `F`-linearly independent.

- `IntermediateField.LinearDisjoint.of_basis_mul`:
  `IntermediateField.LinearDisjoint.of_basis_mul'`:
  conversely, if `{ a_i }` is an `F`-basis of `A`, if `{ b_j }` is an `F`-basis of `L`,
  such that the family `{ a_i * b_j }` in `E` is `F`-linearly independent,
  then `A` and `L` are linearly disjoint.

Other main results:

- `IntermediateField.LinearDisjoint.symm`, `IntermediateField.linearDisjoint_comm`:
  linear disjointness is symmetric.

- `IntermediateField.LinearDisjoint.rank_sup_of_isAlgebraic`,
  `IntermediateField.LinearDisjoint.finrank_sup`:
  if `A` and `B` are linearly disjoint,
  then the rank of `A ⊔ B` is equal to the product of the rank of `A` and `B`.

  **TODO:** remove the algebraic assumptions (the proof becomes complicated).

- `IntermediateField.LinearDisjoint.of_finrank_sup`:
  conversely, if `A` and `B` are finite extensions,
  such that rank of `A ⊔ B` is equal to the product of the rank of `A` and `B`,
  then `A` and `B` are linearly disjoint.

- `IntermediateField.LinearDisjoint.of_finrank_coprime`:
  if the rank of `A` and `B` are coprime,
  then `A` and `B` are linearly disjoint.

- `IntermediateField.LinearDisjoint.inf_eq_bot`:
  if `A` and `B` are linearly disjoint, then they are disjoint.

## Tags

linearly disjoint, linearly independent, tensor product

-/

open scoped TensorProduct

open Module IntermediateField

noncomputable section

universe u v w

namespace IntermediateField

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]

variable (A B : IntermediateField F E)

variable (L : Type w) [Field L] [Algebra F L] [Algebra L E] [IsScalarTower F L E]

/-- If `A` is an intermediate field of `E / F`, and `E / L / F` is a field extension tower,
then `A` and `L` are linearly disjoint, if they are linearly disjoint as subalgebras of `E`
(`Subalgebra.LinearDisjoint`). -/
protected abbrev LinearDisjoint : Prop :=
  A.toSubalgebra.LinearDisjoint (IsScalarTower.toAlgHom F L E).range

theorem linearDisjoint_iff :
    A.LinearDisjoint L ↔ A.toSubalgebra.LinearDisjoint (IsScalarTower.toAlgHom F L E).range :=
  Iff.rfl

variable {A B L}

/-- Two intermediate fields are linearly disjoint if and only if
they are linearly disjoint as subalgebras. -/
theorem linearDisjoint_iff' :
    A.LinearDisjoint B ↔ A.toSubalgebra.LinearDisjoint B.toSubalgebra := by
  rw [linearDisjoint_iff]
  congr!
  ext; simp

/-- Linear disjointness is symmetric. -/
theorem LinearDisjoint.symm (H : A.LinearDisjoint B) : B.LinearDisjoint A :=
  linearDisjoint_iff'.2 (linearDisjoint_iff'.1 H).symm

/-- Linear disjointness is symmetric. -/
theorem linearDisjoint_comm : A.LinearDisjoint B ↔ B.LinearDisjoint A :=
  ⟨LinearDisjoint.symm, LinearDisjoint.symm⟩

namespace LinearDisjoint

variable (A) in
theorem self_right : A.LinearDisjoint F := Subalgebra.LinearDisjoint.bot_right _

variable (A) in
theorem bot_right : A.LinearDisjoint (⊥ : IntermediateField F E) :=
  linearDisjoint_iff'.2 (Subalgebra.LinearDisjoint.bot_right _)

variable (F E L) in
theorem bot_left : (⊥ : IntermediateField F E).LinearDisjoint L :=
  Subalgebra.LinearDisjoint.bot_left _

/-- If `A` and `L` are linearly disjoint, then any `F`-linearly independent family on `A` remains
linearly independent over `L`. -/
theorem linearIndependent_left (H : A.LinearDisjoint L)
    {ι : Type*} {a : ι → A} (ha : LinearIndependent F a) : LinearIndependent L (A.val ∘ a) :=
  (Subalgebra.LinearDisjoint.linearIndependent_left_of_flat H ha).map_of_injective_injective
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)) (AddMonoidHom.id E)
    (by simp) (by simp) (fun _ _ ↦ by simp_rw [Algebra.smul_def]; rfl)

/-- If there exists an `F`-basis of `A` which remains linearly independent over `L`, then
`A` and `L` are linearly disjoint. -/
theorem of_basis_left {ι : Type*} (a : Basis ι F A)
    (H : LinearIndependent L (A.val ∘ a)) : A.LinearDisjoint L :=
  Subalgebra.LinearDisjoint.of_basis_left _ _ a <| H.map_of_surjective_injective
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)) (AddMonoidHom.id E)
    (AlgEquiv.surjective _) (by simp) (fun _ _ ↦ by simp_rw [Algebra.smul_def]; rfl)

/-- If `A` and `B` are linearly disjoint, then any `F`-linearly independent family on `B` remains
linearly independent over `A`. -/
theorem linearIndependent_right (H : A.LinearDisjoint B)
    {ι : Type*} {b : ι → B} (hb : LinearIndependent F b) : LinearIndependent A (B.val ∘ b) :=
  (linearDisjoint_iff'.1 H).linearIndependent_right_of_flat hb

/-- If there exists an `F`-basis of `B` which remains linearly independent over `A`, then
`A` and `B` are linearly disjoint. -/
theorem of_basis_right {ι : Type*} (b : Basis ι F B)
    (H : LinearIndependent A (B.val ∘ b)) : A.LinearDisjoint B :=
  linearDisjoint_iff'.2 (.of_basis_right _ _ b H)

/-- If `A` and `L` are linearly disjoint, then any `F`-linearly independent family on `L` remains
linearly independent over `A`. -/
theorem linearIndependent_right' (H : A.LinearDisjoint L) {ι : Type*} {b : ι → L}
    (hb : LinearIndependent F b) : LinearIndependent A (algebraMap L E ∘ b) := by
  apply Subalgebra.LinearDisjoint.linearIndependent_right_of_flat H <| hb.map' _
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv.ker

/-- If there exists an `F`-basis of `L` which remains linearly independent over `A`, then
`A` and `L` are linearly disjoint. -/
theorem of_basis_right' {ι : Type*} (b : Basis ι F L)
    (H : LinearIndependent A (algebraMap L E ∘ b)) : A.LinearDisjoint L :=
  Subalgebra.LinearDisjoint.of_basis_right _ _
    (b.map (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv) H

/-- If `A` and `B` are linearly disjoint, then for any `F`-linearly independent families
`{ u_i }`, `{ v_j }` of `A`, `B`, the products `{ u_i * v_j }`
are linearly independent over `F`. -/
theorem linearIndependent_mul (H : A.LinearDisjoint B) {κ ι : Type*} {a : κ → A} {b : ι → B}
    (ha : LinearIndependent F a) (hb : LinearIndependent F b) :
    LinearIndependent F fun (i : κ × ι) ↦ (a i.1).1 * (b i.2).1 :=
  (linearDisjoint_iff'.1 H).linearIndependent_mul_of_flat_left ha hb

/-- If `A` and `L` are linearly disjoint, then for any `F`-linearly independent families
`{ u_i }`, `{ v_j }` of `A`, `L`, the products `{ u_i * v_j }`
are linearly independent over `F`. -/
theorem linearIndependent_mul' (H : A.LinearDisjoint L) {κ ι : Type*} {a : κ → A} {b : ι → L}
    (ha : LinearIndependent F a) (hb : LinearIndependent F b) :
    LinearIndependent F fun (i : κ × ι) ↦ (a i.1).1 * algebraMap L E (b i.2) := by
  apply Subalgebra.LinearDisjoint.linearIndependent_mul_of_flat_left H ha <| hb.map' _
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv.ker

/-- If there are `F`-bases `{ u_i }`, `{ v_j }` of `A`, `B`, such that the products
`{ u_i * v_j }` are linearly independent over `F`, then `A` and `B` are linearly disjoint. -/
theorem of_basis_mul {κ ι : Type*} (a : Basis κ F A) (b : Basis ι F B)
    (H : LinearIndependent F fun (i : κ × ι) ↦ (a i.1).1 * (b i.2).1) : A.LinearDisjoint B :=
  linearDisjoint_iff'.2 (.of_basis_mul _ _ a b H)

/-- If there are `F`-bases `{ u_i }`, `{ v_j }` of `A`, `L`, such that the products
`{ u_i * v_j }` are linearly independent over `F`, then `A` and `L` are linearly disjoint. -/
theorem of_basis_mul' {κ ι : Type*} (a : Basis κ F A) (b : Basis ι F L)
    (H : LinearIndependent F fun (i : κ × ι) ↦ (a i.1).1 * algebraMap L E (b i.2)) :
    A.LinearDisjoint L :=
  Subalgebra.LinearDisjoint.of_basis_mul _ _ a
    (b.map (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv) H

theorem of_le_left {A' : IntermediateField F E} (H : A.LinearDisjoint L)
    (h : A' ≤ A) : A'.LinearDisjoint L :=
  Subalgebra.LinearDisjoint.of_le_left_of_flat H h

theorem of_le_right {B' : IntermediateField F E} (H : A.LinearDisjoint B)
    (h : B' ≤ B) : A.LinearDisjoint B' :=
  linearDisjoint_iff'.2 ((linearDisjoint_iff'.1 H).of_le_right_of_flat h)

/-- Similar to `IntermediateField.LinearDisjoint.of_le_right` but this is for abstract fields. -/
theorem of_le_right' (H : A.LinearDisjoint L) (L' : Type*) [Field L']
    [Algebra F L'] [Algebra L' L] [IsScalarTower F L' L]
    [Algebra L' E] [IsScalarTower F L' E] [IsScalarTower L' L E] : A.LinearDisjoint L' := by
  refine Subalgebra.LinearDisjoint.of_le_right_of_flat H ?_
  convert AlgHom.range_comp_le_range (IsScalarTower.toAlgHom F L' L) (IsScalarTower.toAlgHom F L E)
  ext; exact IsScalarTower.algebraMap_apply L' L E _

/-- If `A` and `B` are linearly disjoint, `A'` and `B'` are contained in `A` and `B`,
respectively, then `A'` and `B'` are also linearly disjoint. -/
theorem of_le {A' B' : IntermediateField F E} (H : A.LinearDisjoint B)
    (hA : A' ≤ A) (hB : B' ≤ B) : A'.LinearDisjoint B' :=
  H.of_le_left hA |>.of_le_right hB

/-- Similar to `IntermediateField.LinearDisjoint.of_le` but this is for abstract fields. -/
theorem of_le' {A' : IntermediateField F E} (H : A.LinearDisjoint L)
    (hA : A' ≤ A) (L' : Type*) [Field L']
    [Algebra F L'] [Algebra L' L] [IsScalarTower F L' L]
    [Algebra L' E] [IsScalarTower F L' E] [IsScalarTower L' L E] : A'.LinearDisjoint L' :=
  H.of_le_left hA |>.of_le_right' L'

/-- If `A` and `B` are linearly disjoint over `F`, then their intersection is equal to `F`. -/
theorem inf_eq_bot (H : A.LinearDisjoint B) :
    A ⊓ B = ⊥ := toSubalgebra_injective (linearDisjoint_iff'.1 H).inf_eq_bot

/-- If `A` and `A` itself are linearly disjoint over `F`, then it is equal to `F`. -/
theorem eq_bot_of_self (H : A.LinearDisjoint A) : A = ⊥ :=
  inf_idem A ▸ H.inf_eq_bot

/-- If `A` and `B` are linearly disjoint over `F`, and at least one them are algebraic, then the
rank of `A ⊔ B` is equal to the product of that of `A` and `B`. Note that this result is
also true without algebraic assumption, but the proof becomes very complicated. -/
theorem rank_sup_of_isAlgebraic (H : A.LinearDisjoint B)
    (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F B) :
    Module.rank F ↥(A ⊔ B) = Module.rank F A * Module.rank F B :=
  have h := le_sup_toSubalgebra A B
  (rank_sup_le_of_isAlgebraic A B halg).antisymm <|
    (linearDisjoint_iff'.1 H).rank_sup_of_free.ge.trans <|
      (Subalgebra.inclusion h).toLinearMap.rank_le_of_injective (Subalgebra.inclusion_injective h)

/-- If `A` and `B` are linearly disjoint over `F`, then the `Module.finrank` of
`A ⊔ B` is equal to the product of that of `A` and `B`. -/
theorem finrank_sup (H : A.LinearDisjoint B) : finrank F ↥(A ⊔ B) = finrank F A * finrank F B := by
  by_cases h : FiniteDimensional F A
  · simpa only [map_mul] using
      congr(Cardinal.toNat $(H.rank_sup_of_isAlgebraic (.inl inferInstance)))
  rw [FiniteDimensional, ← rank_lt_aleph0_iff, not_lt] at h
  have := LinearMap.rank_le_of_injective _ <| Submodule.inclusion_injective <|
    show Subalgebra.toSubmodule A.toSubalgebra ≤ Subalgebra.toSubmodule (A ⊔ B).toSubalgebra by simp
  rw [show finrank F A = 0 from Cardinal.toNat_apply_of_aleph0_le h,
    show finrank F ↥(A ⊔ B) = 0 from Cardinal.toNat_apply_of_aleph0_le (h.trans this), zero_mul]

/-- If `A` and `B` are finite extensions of `F`,
such that rank of `A ⊔ B` is equal to the product of the rank of `A` and `B`,
then `A` and `B` are linearly disjoint. -/
theorem of_finrank_sup [FiniteDimensional F A] [FiniteDimensional F B]
    (H : finrank F ↥(A ⊔ B) = finrank F A * finrank F B) : A.LinearDisjoint B :=
  linearDisjoint_iff'.2 <| .of_finrank_sup_of_free (by rwa [← sup_toSubalgebra_of_left])

/-- If `A` and `L` have coprime degree over `F`, then they are linearly disjoint. -/
theorem of_finrank_coprime (H : (finrank F A).Coprime (finrank F L)) : A.LinearDisjoint L :=
  letI : Field (AlgHom.range (IsScalarTower.toAlgHom F L E)) :=
    inferInstanceAs <| Field (AlgHom.fieldRange (IsScalarTower.toAlgHom F L E))
  letI : Field A.toSubalgebra := inferInstanceAs <| Field A
  Subalgebra.LinearDisjoint.of_finrank_coprime_of_free <| by
    rwa [(AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv.finrank_eq] at H

end LinearDisjoint

end IntermediateField
