/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.FieldTheory.Adjoin
import Mathlib.RingTheory.LinearDisjoint

/-!

# Linearly disjoint of fields

This file contains basics about the linearly disjoint of fields.

## Mathematical background

(<https://en.wikipedia.org/wiki/Linearly_disjoint>) Subalgebras `A`, `B` over a field
`F` inside some field extension `E` of `F` are said to be linearly disjoint over `F` if the
following equivalent conditions are met:

- The map `A ⊗[F] B → A ⊔ B`, `x ⊗ₜ[F] y ↦ x * y` is injective.

- Any `F`-basis of `A` remains linearly independent over `B`.

- If `{ u_i }`, `{ v_j }` are `F`-bases for `A`, `B`, then the products `{ u_i * v_j }` are
  linearly independent over `F`.

Our definition `IntermediateField.LinearDisjoint` is very closed to the second equivalent
definition in the above.

(<https://mathoverflow.net/questions/8324>) For two abstract fields `E` and `K` over `F`, they are
called linearly disjoint over `F` (`LinearDisjoint F E K`), if `E ⊗[F] K` is a field.
In this case, it can be shown that at least one of `E / F` and `K / F` are algebraic, and if this
holds, then it is equivalent to the above `IntermediateField.LinearDisjoint`.

The advantage of `LinearDisjoint` is that it is preserved under algebra isomorphisms, while for
`IntermediateField.LinearDisjoint` this is not so easy to prove, in fact it's wrong if both of the
extensions are not algebraic.

## Main definitions

- ...

## Main results

- ...

## Tags

linearly disjoint, linearly independent, tensor product

## TODO

- ...

-/

open scoped Classical TensorProduct

open FiniteDimensional IntermediateField

noncomputable section

universe u v w

namespace IntermediateField

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]

variable (A B : IntermediateField F E)

variable (L : Type w) [Field L] [Algebra F L] [Algebra L E] [IsScalarTower F L E]

/-- If `A` is an intermediate field of `E / F`, and `E / L / F` is a field extension tower,
then `A` and `L` are linearly disjoint, if they are linearly disjoint as subalgebras of `E`. -/
@[mk_iff]
protected structure LinearDisjoint : Prop where
  subalgebra : A.toSubalgebra.LinearDisjoint (IsScalarTower.toAlgHom F L E).range

variable {A B L}

theorem linearDisjoint_iff' :
    A.LinearDisjoint B ↔ A.toSubalgebra.LinearDisjoint B.toSubalgebra := by
  rw [linearDisjoint_iff]
  congr!
  ext; simp

/-- Linearly disjoint is symmetric. -/
theorem LinearDisjoint.symm (H : A.LinearDisjoint B) : B.LinearDisjoint A :=
  linearDisjoint_iff'.2 (linearDisjoint_iff'.1 H).symm

/-- Linearly disjoint is symmetric. -/
theorem linearDisjoint_symm : A.LinearDisjoint B ↔ B.LinearDisjoint A :=
  ⟨LinearDisjoint.symm, LinearDisjoint.symm⟩

namespace LinearDisjoint

variable (A) in
theorem of_self_right : A.LinearDisjoint F :=
  ⟨.of_bot_right _⟩

variable (A) in
theorem of_bot_right : A.LinearDisjoint (⊥ : IntermediateField F E) :=
  linearDisjoint_iff'.2 (.of_bot_right _)

variable (F E L) in
theorem of_bot_left : (⊥ : IntermediateField F E).LinearDisjoint L :=
  ⟨.of_bot_left _⟩

/-- If `A` and `L` are linearly disjoint, then any `F`-linearly independent family on `A` remains
linearly independent over `L`. -/
theorem map_linearIndependent_left (H : A.LinearDisjoint L)
    {ι : Type*} {a : ι → A} (ha : LinearIndependent F a) :
    LinearIndependent L (A.val ∘ a) :=
  (H.1.map_linearIndependent_left_of_flat ha).map_of_injective_injective
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)) (AddMonoidHom.id E)
    (by simp) (by simp) (fun _ _ ↦ by simp_rw [Algebra.smul_def]; rfl)

/-- If there exists an `F`-basis of `A` which remains linearly independent over `L`, then
`A` and `L` are linearly disjoint. -/
theorem of_map_linearIndependent_left {ι : Type*} (a : Basis ι F A)
    (H : LinearIndependent L (A.val ∘ a)) :
    A.LinearDisjoint L := by
  rw [linearDisjoint_iff]
  refine Subalgebra.LinearDisjoint.of_map_linearIndependent_left _ _ a ?_
  exact H.map_of_surjective_injective
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)) (AddMonoidHom.id E)
    (AlgEquiv.surjective _) (by simp) (fun _ _ ↦ by simp_rw [Algebra.smul_def]; rfl)

/-- If `A` and `B` are linearly disjoint, then any `F`-linearly independent family on `B` remains
linearly independent over `A`. -/
theorem map_linearIndependent_right (H : A.LinearDisjoint B)
    {ι : Type*} {b : ι → B} (hb : LinearIndependent F b) :
    LinearIndependent A (B.val ∘ b) :=
  (linearDisjoint_iff'.1 H).map_linearIndependent_right_of_flat hb

/-- If there exists an `F`-basis of `B` which remains linearly independent over `A`, then
`A` and `B` are linearly disjoint. -/
theorem of_map_linearIndependent_right {ι : Type*} (b : Basis ι F B)
    (H : LinearIndependent A (B.val ∘ b)) :
    A.LinearDisjoint B :=
  linearDisjoint_iff'.2 (.of_map_linearIndependent_right _ _ b H)

/-- If `A` and `L` are linearly disjoint, then any `F`-linearly independent family on `L` remains
linearly independent over `A`. -/
theorem map_linearIndependent_right' (H : A.LinearDisjoint L)
    {ι : Type*} {b : ι → L} (hb : LinearIndependent F b) :
    LinearIndependent A ((algebraMap L E) ∘ b) := by
  have := H.1.map_linearIndependent_right_of_flat <| hb.map' _
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv.ker
  exact this

/-- If there exists an `F`-basis of `L` which remains linearly independent over `A`, then
`A` and `L` are linearly disjoint. -/
theorem of_map_linearIndependent_right' {ι : Type*} (b : Basis ι F L)
    (H : LinearIndependent A ((algebraMap L E) ∘ b)) :
    A.LinearDisjoint L := by
  rw [linearDisjoint_iff]
  exact .of_map_linearIndependent_right _ _
    (b.map (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv) H

/-- If `A` and `B` are linearly disjoint, then for any `F`-linearly independent families
`{ u_i }`, `{ v_j }` of `A`, `B`, the products `{ u_i * v_j }`
are linearly independent over `F`. -/
theorem map_linearIndependent_mul (H : A.LinearDisjoint B)
    {κ ι : Type*} {a : κ → A} {b : ι → B} (ha : LinearIndependent F a)
    (hb : LinearIndependent F b) : LinearIndependent F fun (i : κ × ι) ↦ (a i.1).1 * (b i.2).1 :=
  (linearDisjoint_iff'.1 H).map_linearIndependent_mul_of_flat_left ha hb

/-- If `A` and `L` are linearly disjoint, then for any `F`-linearly independent families
`{ u_i }`, `{ v_j }` of `A`, `L`, the products `{ u_i * v_j }`
are linearly independent over `F`. -/
theorem map_linearIndependent_mul' (H : A.LinearDisjoint L)
    {κ ι : Type*} {a : κ → A} {b : ι → L} (ha : LinearIndependent F a)
    (hb : LinearIndependent F b) :
    LinearIndependent F fun (i : κ × ι) ↦ (a i.1).1 * algebraMap L E (b i.2) := by
  have := H.1.map_linearIndependent_mul_of_flat_left ha <| hb.map' _
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv.ker
  exact this

/-- If there are `F`-bases `{ u_i }`, `{ v_j }` of `A`, `B`, such that the products
`{ u_i * v_j }` are linearly independent over `F`, then `A` and `B` are linearly disjoint. -/
theorem of_map_linearIndependent_mul {κ ι : Type*} (a : Basis κ F A) (b : Basis ι F B)
    (H : LinearIndependent F fun (i : κ × ι) ↦ (a i.1).1 * (b i.2).1) : A.LinearDisjoint B :=
  linearDisjoint_iff'.2 (.of_map_linearIndependent_mul _ _ a b H)

/-- If there are `F`-bases `{ u_i }`, `{ v_j }` of `A`, `L`, such that the products
`{ u_i * v_j }` are linearly independent over `F`, then `A` and `L` are linearly disjoint. -/
theorem of_map_linearIndependent_mul' {κ ι : Type*} (a : Basis κ F A) (b : Basis ι F L)
    (H : LinearIndependent F fun (i : κ × ι) ↦ (a i.1).1 * algebraMap L E (b i.2)) :
    A.LinearDisjoint L := by
  rw [linearDisjoint_iff]
  exact .of_map_linearIndependent_mul _ _ a
    (b.map (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv) H

theorem of_le_left {A' : IntermediateField F E} (H : A.LinearDisjoint L)
    (h : A' ≤ A) : A'.LinearDisjoint L :=
  ⟨H.1.of_le_left_of_flat h⟩

theorem of_le_right {B' : IntermediateField F E} (H : A.LinearDisjoint B)
    (h : B' ≤ B) : A.LinearDisjoint B' :=
  linearDisjoint_iff'.2 ((linearDisjoint_iff'.1 H).of_le_right_of_flat h)

theorem of_le_right' (H : A.LinearDisjoint L) (L' : Type*) [Field L']
    [Algebra F L'] [Algebra L' L] [IsScalarTower F L' L]
    [Algebra L' E] [IsScalarTower F L' E] [IsScalarTower L' L E] : A.LinearDisjoint L' := by
  refine ⟨H.1.of_le_right_of_flat ?_⟩
  convert AlgHom.range_comp_le_range (IsScalarTower.toAlgHom F L' L) (IsScalarTower.toAlgHom F L E)
  ext x
  exact IsScalarTower.algebraMap_apply L' L E x

/-- If `A` and `B` are linearly disjoint, `A'` and `B'` are contained in `A` and `B`,
respectively, then `A'` and `B'` are also linearly disjoint. -/
theorem of_le {A' B' : IntermediateField F E} (H : A.LinearDisjoint B)
    (hA : A' ≤ A) (hB : B' ≤ B) : A'.LinearDisjoint B' :=
  H.of_le_left hA |>.of_le_right hB

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
  inf_of_le_left (le_refl A) ▸ H.inf_eq_bot

/-- If `A` and `L` have coprime degree over `F`, then they are linearly disjoint. -/
theorem of_finrank_coprime (H : (finrank F A).Coprime (finrank F L)) :
    A.LinearDisjoint L := by
  rw [linearDisjoint_iff]
  letI : Field (AlgHom.range (IsScalarTower.toAlgHom F L E)) := by
    change Field (AlgHom.fieldRange (IsScalarTower.toAlgHom F L E))
    infer_instance
  refine .of_finrank_coprime_of_free ?_
  rwa [(AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv.finrank_eq] at H

-- TODO: rank_sup_of_isAlgebraic (?) and finrank_sup (?)

end LinearDisjoint

end IntermediateField

-- section Absolute

-- variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]

-- variable (K : Type w) [Field K] [Algebra F K]

-- /-- Two abstract fields `E` and `K` over `F` are called linearly disjoint, if their
-- tensor product over `F` is a field. -/
-- def LinearDisjoint := IsField (E ⊗[F] K)

-- set_option linter.unusedVariables false in
-- variable {F E K} in
-- /-- If two abstract fields `E` and `K` over `F` are linearly disjoint, then at least one of
-- `E / F` and `K / F` are algebraic. -/
-- proof_wanted LinearDisjoint.isAlgebraic (H : LinearDisjoint F E K) :
--     Algebra.IsAlgebraic F E ∨ Algebra.IsAlgebraic F K

-- end Absolute
