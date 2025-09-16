/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.RingTheory.AlgebraicIndependent.RankAndCardinality
import Mathlib.RingTheory.LinearDisjoint

/-!

# Linearly disjoint fields

This file contains basics about the linearly disjoint fields.
We adapt the definitions in <https://en.wikipedia.org/wiki/Linearly_disjoint>.
See the file `Mathlib/LinearAlgebra/LinearDisjoint.lean`
and `Mathlib/RingTheory/LinearDisjoint.lean` for details.

## Main definitions

- `IntermediateField.LinearDisjoint`: an intermediate field `A` of `E / F`
  and an abstract field `L` between `E / F`
  (as a special case, two intermediate fields) are linearly disjoint over `F`,
  if they are linearly disjoint as subalgebras (`Subalgebra.LinearDisjoint`).

## Implementation notes

The `Subalgebra.LinearDisjoint` is stated for two `Subalgebra`s. The original design of
`IntermediateField.LinearDisjoint` is also stated for two `IntermediateField`s
(see `IntermediateField.linearDisjoint_iff'` for the original statement).
But it's probably useful if one of them can be generalized to an abstract field
(see <https://github.com/leanprover-community/mathlib4/pull/9651#discussion_r1464070324>).
This leads to the current design of `IntermediateField.LinearDisjoint`
which is for one `IntermediateField` and one abstract field.
It is not generalized to two abstract fields as this will break the dot notation.

## Main results

### Equivalent characterization of linear disjointness

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

### Equivalent characterization by `IsDomain` or `IsField` of tensor product

The following results are related to the equivalent characterizations in
<https://mathoverflow.net/questions/8324>.

- `IntermediateField.LinearDisjoint.isDomain'`,
  `IntermediateField.LinearDisjoint.exists_field_of_isDomain`:
  if `A` and `B` are field extensions of `F`, then `A ⊗[F] B`
  is a domain if and only if there exists a field extension of `F` that `A` and `B`
  embed into with linearly disjoint images.

- `IntermediateField.LinearDisjoint.isField_of_forall`,
  `IntermediateField.LinearDisjoint.of_isField'`:
  if `A` and `B` are field extensions of `F`, then `A ⊗[F] B`
  is a field if and only if for any field extension of `F` that `A` and `B` embed into, their
  images are linearly disjoint.

- `Algebra.TensorProduct.isField_of_isAlgebraic`:
  if `E` and `K` are field extensions of `F`, one of them is algebraic, and
  `E ⊗[F] K` is a domain, then `E ⊗[F] K` is also a field.
  See `Algebra.TensorProduct.isAlgebraic_of_isField` for its converse (in an earlier file).

- `IntermediateField.LinearDisjoint.isField_of_isAlgebraic`,
  `IntermediateField.LinearDisjoint.isField_of_isAlgebraic'`:
  if `A` and `B` are field extensions of `F`, one of them is algebraic, such that they are linearly
  disjoint (more generally, if there exists a field extension of `F` that they embed into with
  linearly disjoint images), then `A ⊗[F] B` is a field.

### Other main results

- `IntermediateField.LinearDisjoint.symm`, `IntermediateField.linearDisjoint_comm`:
  linear disjointness is symmetric.

- `IntermediateField.LinearDisjoint.map`:
  linear disjointness is preserved by algebra homomorphism.

- `IntermediateField.LinearDisjoint.rank_sup`,
  `IntermediateField.LinearDisjoint.finrank_sup`:
  if `A` and `B` are linearly disjoint,
  then the rank of `A ⊔ B` is equal to the product of the rank of `A` and `B`.

- `IntermediateField.LinearDisjoint.of_finrank_sup`:
  conversely, if `A` and `B` are finite extensions,
  such that rank of `A ⊔ B` is equal to the product of the rank of `A` and `B`,
  then `A` and `B` are linearly disjoint.

- `IntermediateField.LinearDisjoint.of_finrank_coprime`:
  if the rank of `A` and `B` are coprime,
  then `A` and `B` are linearly disjoint.

- `IntermediateField.LinearDisjoint.inf_eq_bot`:
  if `A` and `B` are linearly disjoint, then they are disjoint.

- `IntermediateField.LinearDisjoint.algEquiv_of_isAlgebraic`:
  linear disjointness is preserved by isomorphisms, provided that one of the field is algebraic.

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

section

variable {L' : Type*} [Field L'] [Algebra F L'] [Algebra L' E] [IsScalarTower F L' E]

/-- Linear disjointness is symmetric. -/
theorem LinearDisjoint.symm' (H : (IsScalarTower.toAlgHom F L E).fieldRange.LinearDisjoint L') :
    (IsScalarTower.toAlgHom F L' E).fieldRange.LinearDisjoint L :=
  Subalgebra.LinearDisjoint.symm H

/-- Linear disjointness is symmetric. -/
theorem linearDisjoint_comm' :
    (IsScalarTower.toAlgHom F L E).fieldRange.LinearDisjoint L' ↔
    (IsScalarTower.toAlgHom F L' E).fieldRange.LinearDisjoint L :=
  ⟨LinearDisjoint.symm', LinearDisjoint.symm'⟩

end

namespace LinearDisjoint

/-- Linear disjointness of intermediate fields is preserved by algebra homomorphisms. -/
theorem map (H : A.LinearDisjoint B) {K : Type*} [Field K] [Algebra F K]
    (f : E →ₐ[F] K) : (A.map f).LinearDisjoint (B.map f) :=
  linearDisjoint_iff'.2 ((linearDisjoint_iff'.1 H).map f f.injective)

/-- Linear disjointness of an intermediate field with a tower of field embeddings is preserved by
algebra homomorphisms. -/
theorem map' (H : A.LinearDisjoint L) (K : Type*) [Field K] [Algebra F K] [Algebra L K]
    [IsScalarTower F L K] [Algebra E K] [IsScalarTower F E K] [IsScalarTower L E K] :
    (A.map (IsScalarTower.toAlgHom F E K)).LinearDisjoint L := by
  rw [linearDisjoint_iff] at H ⊢
  have := H.map (IsScalarTower.toAlgHom F E K) (RingHom.injective _)
  rw [← AlgHom.range_comp] at this
  convert this
  ext; exact IsScalarTower.algebraMap_apply L E K _

/-- Linear disjointness is preserved by algebra homomorphism. -/
theorem map'' {L' : Type*} [Field L'] [Algebra F L'] [Algebra L' E] [IsScalarTower F L' E]
    (H : (IsScalarTower.toAlgHom F L E).fieldRange.LinearDisjoint L')
    (K : Type*) [Field K] [Algebra F K] [Algebra L K] [IsScalarTower F L K]
    [Algebra L' K] [IsScalarTower F L' K] [Algebra E K] [IsScalarTower F E K]
    [IsScalarTower L E K] [IsScalarTower L' E K] :
    (IsScalarTower.toAlgHom F L K).fieldRange.LinearDisjoint L' := by
  rw [linearDisjoint_iff] at H ⊢
  have := H.map (IsScalarTower.toAlgHom F E K) (RingHom.injective _)
  simp_rw [AlgHom.fieldRange_toSubalgebra, ← AlgHom.range_comp] at this
  rw [AlgHom.fieldRange_toSubalgebra]
  convert this <;> (ext; exact IsScalarTower.algebraMap_apply _ E K _)

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

/--
If `A` and `B` are linearly disjoint and such that `A.toSubalgebra ⊔ B.toSubalgebra = ⊤`,
then any `F`-basis of `B` is also an `A`-basis of `E`.
Note that the condition `A.toSubalgebra ⊔ B.toSubalgebra = ⊤` is equivalent to
`A ⊔ B = ⊤` in many cases, see `IntermediateField.sup_toSubalgebra_of_isAlgebraic_right` and similar
results.
-/
noncomputable def basisOfBasisRight (H : A.LinearDisjoint B)
    (H' : A.toSubalgebra ⊔ B.toSubalgebra = ⊤) {ι : Type*} (b : Basis ι F B) :
    Basis ι A E :=
  (linearDisjoint_iff'.mp H).basisOfBasisRight H' b

@[simp]
theorem basisOfBasisRight_apply (H : A.LinearDisjoint B) (H' : A.toSubalgebra ⊔ B.toSubalgebra = ⊤)
    {ι : Type*} (b : Basis ι F B) (i : ι) :
    H.basisOfBasisRight H' b i = algebraMap B E (b i) :=
  (linearDisjoint_iff'.mp H).algebraMap_basisOfBasisRight_apply H' b i

theorem algebraMap_basisOfBasisRight_repr_apply (H : A.LinearDisjoint B)
    (H' : A.toSubalgebra ⊔ B.toSubalgebra = ⊤) {ι : Type*} (b : Basis ι F B) (x : B) (i : ι) :
    algebraMap A E ((H.basisOfBasisRight H' b).repr x i) = algebraMap F E (b.repr x i) :=
  (linearDisjoint_iff'.mp H).algebraMap_basisOfBasisRight_repr_apply H' b x i

/--
If `A` and `B` are linearly disjoint and such that `A.toSubalgebra ⊔ B.toSubalgebra = ⊤`,
then any `F`-basis of `A` is also a `B`-basis of `E`.
Note that the condition `A.toSubalgebra ⊔ B.toSubalgebra = ⊤` is equivalent to
`A ⊔ B = ⊤` in many cases, see `IntermediateField.sup_toSubalgebra_of_isAlgebraic_right` and similar
results.
-/
noncomputable def basisOfBasisLeft (H : A.LinearDisjoint B)
    (H' : A.toSubalgebra ⊔ B.toSubalgebra = ⊤) {ι : Type*} (b : Basis ι F A) :
    Basis ι B E :=
  (linearDisjoint_iff'.mp H).basisOfBasisLeft H' b

@[simp]
theorem basisOfBasisLeft_apply (H : A.LinearDisjoint B) (H' : A.toSubalgebra ⊔ B.toSubalgebra = ⊤)
    {ι : Type*} (b : Basis ι F A) (i : ι) :
    H.basisOfBasisLeft H' b i = algebraMap A E (b i) :=
  (linearDisjoint_iff'.mp H).basisOfBasisLeft_apply H' b i

theorem basisOfBasisLeft_repr_apply (H : A.LinearDisjoint B)
    (H' : A.toSubalgebra ⊔ B.toSubalgebra = ⊤) {ι : Type*} (b : Basis ι F A) (x : A) (i : ι) :
    algebraMap B E ((H.basisOfBasisLeft H' b).repr x i) = algebraMap F E (b.repr x i) :=
  (linearDisjoint_iff'.mp H).basisOfBasisLeft_repr_apply H' b x i

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

/-- If `A` and `B` are linearly disjoint over `F`, then the
rank of `A ⊔ B` is equal to the product of that of `A` and `B`. -/
theorem rank_sup (H : A.LinearDisjoint B) :
    Module.rank F ↥(A ⊔ B) = Module.rank F A * Module.rank F B :=
  have h := le_sup_toSubalgebra A B
  (rank_sup_le A B).antisymm <|
    (linearDisjoint_iff'.1 H).rank_sup_of_free.ge.trans <|
      (Subalgebra.inclusion h).toLinearMap.rank_le_of_injective (Subalgebra.inclusion_injective h)

/-- If `A` and `B` are linearly disjoint over `F`, then the `Module.finrank` of
`A ⊔ B` is equal to the product of that of `A` and `B`. -/
theorem finrank_sup (H : A.LinearDisjoint B) : finrank F ↥(A ⊔ B) = finrank F A * finrank F B := by
  simpa only [map_mul] using congr(Cardinal.toNat $(H.rank_sup))

/-- If `A` and `B` are finite extensions of `F`,
such that rank of `A ⊔ B` is equal to the product of the rank of `A` and `B`,
then `A` and `B` are linearly disjoint. -/
theorem of_finrank_sup [FiniteDimensional F A] [FiniteDimensional F B]
    (H : finrank F ↥(A ⊔ B) = finrank F A * finrank F B) : A.LinearDisjoint B :=
  linearDisjoint_iff'.2 <| .of_finrank_sup_of_free (by rwa [← sup_toSubalgebra_of_left])

/-- If `A` and `B` are linearly disjoint over `F` and `A ⊔ B = E`, then the `Module.finrank` of
`E` over `A` is equal to the `Module.finrank` of `B` over `F`.
-/
theorem finrank_left_eq_finrank [Module.Finite F A] (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤) :
    finrank A E = finrank F B := by
  have := h₁.finrank_sup
  rwa [h₂, finrank_top', ← finrank_mul_finrank F A E, mul_right_inj' finrank_pos.ne'] at this

/-- If `A` and `B` are linearly disjoint over `F` and `A ⊔ B = E`, then the `Module.finrank` of
`E` over `B` is equal to the `Module.finrank` of `A` over `F`.
-/
theorem finrank_right_eq_finrank [Module.Finite F B] (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤) :
    finrank B E = finrank F A :=
  h₁.symm.finrank_left_eq_finrank (by rwa [sup_comm])

/-- If `A` and `L` are linearly disjoint over `F`, one of them is algebraic,
then `[L(A) : L] = [A : F]`. -/
theorem adjoin_rank_eq_rank_left_of_isAlgebraic (H : A.LinearDisjoint L)
    (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) :
    Module.rank L (adjoin L (A : Set E)) = Module.rank F A := by
  refine Eq.trans ?_ (Subalgebra.LinearDisjoint.adjoin_rank_eq_rank_left H)
  set L' := (IsScalarTower.toAlgHom F L E).range
  let i : L ≃ₐ[F] L' := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)
  have heq : (adjoin L (A : Set E)).toSubalgebra.toSubsemiring =
      (Algebra.adjoin L' (A : Set E)).toSubsemiring := by
    rw [adjoin_toSubalgebra_of_isAlgebraic _ _ halg.symm, Algebra.adjoin_toSubsemiring,
      Algebra.adjoin_toSubsemiring]
    congr 2
    ext x
    simp only [Set.mem_range, Subtype.exists]
    exact ⟨fun ⟨y, h⟩ ↦ ⟨x, ⟨y, h⟩, rfl⟩, fun ⟨a, ⟨y, h1⟩, h2⟩ ↦ ⟨y, h1.trans h2⟩⟩
  refine rank_eq_of_equiv_equiv i (RingEquiv.subsemiringCongr heq).toAddEquiv
    i.bijective fun a ⟨x, hx⟩ ↦ ?_
  ext
  simp_rw [Algebra.smul_def]
  rfl

theorem adjoin_rank_eq_rank_left_of_isAlgebraic_left (H : A.LinearDisjoint L)
    [Algebra.IsAlgebraic F A] : Module.rank L (adjoin L (A : Set E)) = Module.rank F A :=
  H.adjoin_rank_eq_rank_left_of_isAlgebraic (.inl ‹_›)

theorem adjoin_rank_eq_rank_left_of_isAlgebraic_right (H : A.LinearDisjoint L)
    [Algebra.IsAlgebraic F L] : Module.rank L (adjoin L (A : Set E)) = Module.rank F A :=
  H.adjoin_rank_eq_rank_left_of_isAlgebraic (.inr ‹_›)

/-- If `A` and `L` are linearly disjoint over `F`, one of them is algebraic,
then `[L(A) : A] = [L : F]`. Note that in Lean `L(A)` is not naturally an `A`-algebra,
so this result is stated in a cumbersome way. -/
theorem lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic (H : A.LinearDisjoint L)
    (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) :
    Cardinal.lift.{w} (Module.rank A (extendScalars
      (show A ≤ (adjoin L (A : Set E)).restrictScalars F from subset_adjoin L (A : Set E)))) =
    Cardinal.lift.{v} (Module.rank F L) := by
  rw [(AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv.lift_rank_eq,
    Cardinal.lift_inj, ← Subalgebra.LinearDisjoint.adjoin_rank_eq_rank_right H]
  set L' := (IsScalarTower.toAlgHom F L E).range
  have heq : (adjoin L (A : Set E)).toSubalgebra.toSubsemiring =
      (Algebra.adjoin A (L' : Set E)).toSubsemiring := by
    rw [adjoin_toSubalgebra_of_isAlgebraic _ _ halg.symm, Algebra.adjoin_toSubsemiring,
      Algebra.adjoin_toSubsemiring, Set.union_comm]
    congr 2
    ext x
    simp
  refine rank_eq_of_equiv_equiv (RingHom.id A) (RingEquiv.subsemiringCongr heq).toAddEquiv
    Function.bijective_id fun ⟨a, ha⟩ ⟨x, hx⟩ ↦ ?_
  ext
  simp_rw [Algebra.smul_def]
  rfl

theorem lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic_left (H : A.LinearDisjoint L)
    [Algebra.IsAlgebraic F A] :
    Cardinal.lift.{w} (Module.rank A (extendScalars
      (show A ≤ (adjoin L (A : Set E)).restrictScalars F from subset_adjoin L (A : Set E)))) =
    Cardinal.lift.{v} (Module.rank F L) :=
  H.lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic (.inl ‹_›)

theorem lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic_right (H : A.LinearDisjoint L)
    [Algebra.IsAlgebraic F L] :
    Cardinal.lift.{w} (Module.rank A (extendScalars
      (show A ≤ (adjoin L (A : Set E)).restrictScalars F from subset_adjoin L (A : Set E)))) =
    Cardinal.lift.{v} (Module.rank F L) :=
  H.lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic (.inr ‹_›)

/-- If `A` is an intermediate field of `E / F`, `L` is an abstract field between `E / F`,
such that they are linearly disjoint over `F`, and one of them is algebraic, then
`[L : F] * [E : L(A)] = [E : A]`. -/
theorem lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic (H : A.LinearDisjoint L)
    (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) :
    Cardinal.lift.{v} (Module.rank F L) * Cardinal.lift.{w} (Module.rank (adjoin L (A : Set E)) E) =
      Cardinal.lift.{w} (Module.rank A E) := by
  rw [← H.lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic halg, ← Cardinal.lift_mul,
    Cardinal.lift_inj]
  exact rank_mul_rank A (extendScalars
    (show A ≤ (adjoin L (A : Set E)).restrictScalars F from subset_adjoin L (A : Set E))) E

theorem lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic_left (H : A.LinearDisjoint L)
    [Algebra.IsAlgebraic F A] :
    Cardinal.lift.{v} (Module.rank F L) * Cardinal.lift.{w} (Module.rank (adjoin L (A : Set E)) E) =
      Cardinal.lift.{w} (Module.rank A E) :=
  H.lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic (.inl ‹_›)

theorem lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic_right (H : A.LinearDisjoint L)
    [Algebra.IsAlgebraic F L] :
    Cardinal.lift.{v} (Module.rank F L) * Cardinal.lift.{w} (Module.rank (adjoin L (A : Set E)) E) =
      Cardinal.lift.{w} (Module.rank A E) :=
  H.lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic (.inr ‹_›)

section

variable {L : Type v} [Field L] [Algebra F L] [Algebra L E] [IsScalarTower F L E]

/-- The same-universe version of
`IntermediateField.LinearDisjoint.lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic`. -/
theorem adjoin_rank_eq_rank_right_of_isAlgebraic (H : A.LinearDisjoint L)
    (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) :
    Module.rank A (extendScalars (show A ≤ (adjoin L (A : Set E)).restrictScalars F from
      subset_adjoin L (A : Set E))) = Module.rank F L := by
  simpa only [Cardinal.lift_id] using H.lift_adjoin_rank_eq_lift_rank_right_of_isAlgebraic halg

theorem adjoin_rank_eq_rank_right_of_isAlgebraic_left (H : A.LinearDisjoint L)
    [Algebra.IsAlgebraic F A] :
    Module.rank A (extendScalars (show A ≤ (adjoin L (A : Set E)).restrictScalars F from
      subset_adjoin L (A : Set E))) = Module.rank F L :=
  H.adjoin_rank_eq_rank_right_of_isAlgebraic (.inl ‹_›)

theorem adjoin_rank_eq_rank_right_of_isAlgebraic_right (H : A.LinearDisjoint L)
    [Algebra.IsAlgebraic F L] :
    Module.rank A (extendScalars (show A ≤ (adjoin L (A : Set E)).restrictScalars F from
      subset_adjoin L (A : Set E))) = Module.rank F L :=
  H.adjoin_rank_eq_rank_right_of_isAlgebraic (.inr ‹_›)

/-- The same-universe version of
`IntermediateField.LinearDisjoint.lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic`. -/
theorem rank_right_mul_adjoin_rank_eq_of_isAlgebraic (H : A.LinearDisjoint L)
    (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) :
    Module.rank F L * Module.rank (adjoin L (A : Set E)) E = Module.rank A E := by
  simpa only [Cardinal.lift_id] using H.lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic halg

theorem rank_right_mul_adjoin_rank_eq_of_isAlgebraic_left (H : A.LinearDisjoint L)
    [Algebra.IsAlgebraic F A] :
    Module.rank F L * Module.rank (adjoin L (A : Set E)) E = Module.rank A E :=
  H.rank_right_mul_adjoin_rank_eq_of_isAlgebraic (.inl ‹_›)

theorem rank_right_mul_adjoin_rank_eq_of_isAlgebraic_right (H : A.LinearDisjoint L)
    [Algebra.IsAlgebraic F L] :
    Module.rank F L * Module.rank (adjoin L (A : Set E)) E = Module.rank A E :=
  H.rank_right_mul_adjoin_rank_eq_of_isAlgebraic (.inr ‹_›)

end

/-- If `A` and `L` have coprime degree over `F`, then they are linearly disjoint. -/
theorem of_finrank_coprime (H : (finrank F A).Coprime (finrank F L)) : A.LinearDisjoint L :=
  letI : Field (AlgHom.range (IsScalarTower.toAlgHom F L E)) :=
    inferInstanceAs <| Field (AlgHom.fieldRange (IsScalarTower.toAlgHom F L E))
  letI : Field A.toSubalgebra := inferInstanceAs <| Field A
  Subalgebra.LinearDisjoint.of_finrank_coprime_of_free <| by
    rwa [(AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv.finrank_eq] at H

/-- If `A` and `L` are linearly disjoint over `F`, then `A ⊗[F] L` is a domain. -/
theorem isDomain (H : A.LinearDisjoint L) : IsDomain (A ⊗[F] L) :=
  have : IsDomain (A ⊗[F] _) := Subalgebra.LinearDisjoint.isDomain H
  (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[F] A)
    (AlgEquiv.ofInjective (IsScalarTower.toAlgHom F L E) (RingHom.injective _))).toMulEquiv.isDomain

/-- If `A` and `B` are field extensions of `F`, there exists a field extension `E` of `F` that
`A` and `B` embed into with linearly disjoint images, then `A ⊗[F] B` is a domain. -/
theorem isDomain' {A B : Type*} [Field A] [Algebra F A] [Field B] [Algebra F B]
    {fa : A →ₐ[F] E} {fb : B →ₐ[F] E} (H : fa.fieldRange.LinearDisjoint fb.fieldRange) :
    IsDomain (A ⊗[F] B) := by
  simp_rw [linearDisjoint_iff', AlgHom.fieldRange_toSubalgebra] at H
  exact H.isDomain_of_injective fa.injective fb.injective

/-- If `A ⊗[F] L` is a field, then `A` and `L` are linearly disjoint over `F`. -/
theorem of_isField (H : IsField (A ⊗[F] L)) : A.LinearDisjoint L := by
  apply Subalgebra.LinearDisjoint.of_isField
  -- need these otherwise the `exact` will stuck at typeclass
  haveI : SMulCommClass F A A := SMulCommClass.of_commMonoid F A A
  haveI : SMulCommClass F A.toSubalgebra A.toSubalgebra := ‹SMulCommClass F A A›
  letI : Mul (A ⊗[F] L) := Algebra.TensorProduct.instMul
  letI : Mul (A.toSubalgebra ⊗[F] (IsScalarTower.toAlgHom F L E).range) :=
    Algebra.TensorProduct.instMul
  exact Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[F] A)
    (AlgEquiv.ofInjective (IsScalarTower.toAlgHom F L E) (RingHom.injective _))
      |>.symm.toMulEquiv.isField H

/-- If `A` and `B` are field extensions of `F`, such that `A ⊗[F] B` is a field, then for any
field extension of `F` that `A` and `B` embed into, their images are linearly disjoint. -/
theorem of_isField' {A : Type v} [Field A] {B : Type w} [Field B]
    [Algebra F A] [Algebra F B] (H : IsField (A ⊗[F] B))
    {K : Type*} [Field K] [Algebra F K] (fa : A →ₐ[F] K) (fb : B →ₐ[F] K) :
    fa.fieldRange.LinearDisjoint fb.fieldRange := by
  rw [linearDisjoint_iff']
  apply Subalgebra.LinearDisjoint.of_isField
  exact Algebra.TensorProduct.congr (AlgEquiv.ofInjective fa fa.injective)
    (AlgEquiv.ofInjective fb fb.injective) |>.symm.toMulEquiv.isField H

variable (F) in
/-- If `A` and `B` are field extensions of `F`, such that `A ⊗[F] B` is a domain, then there exists
a field extension of `F` that `A` and `B` embed into with linearly disjoint images. -/
theorem exists_field_of_isDomain (A : Type v) [Field A] (B : Type w) [Field B]
    [Algebra F A] [Algebra F B] [IsDomain (A ⊗[F] B)] :
    ∃ (K : Type (max v w)) (_ : Field K) (_ : Algebra F K) (fa : A →ₐ[F] K) (fb : B →ₐ[F] K),
    fa.fieldRange.LinearDisjoint fb.fieldRange :=
  have ⟨K, inst1, inst2, fa, fb, _, _, H⟩ :=
    Subalgebra.LinearDisjoint.exists_field_of_isDomain_of_injective F A B
      (RingHom.injective _) (RingHom.injective _)
  ⟨K, inst1, inst2, fa, fb, linearDisjoint_iff'.2 H⟩

variable (F) in
/-- If for any field extension `K` of `F` that `A` and `B` embed into, their images are
linearly disjoint, then `A ⊗[F] B` is a field. (In the proof we choose `K` to be the quotient
of `A ⊗[F] B` by a maximal ideal.) -/
theorem isField_of_forall (A : Type v) [Field A] (B : Type w) [Field B]
    [Algebra F A] [Algebra F B]
    (H : ∀ (K : Type (max v w)) [Field K] [Algebra F K],
      ∀ (fa : A →ₐ[F] K) (fb : B →ₐ[F] K), fa.fieldRange.LinearDisjoint fb.fieldRange) :
    IsField (A ⊗[F] B) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (A ⊗[F] B)
  apply not_imp_not.1 (Ring.ne_bot_of_isMaximal_of_not_isField hM)
  let K : Type (max v w) := A ⊗[F] B ⧸ M
  letI : Field K := Ideal.Quotient.field _
  let i := IsScalarTower.toAlgHom F (A ⊗[F] B) K
  let fa := i.comp (Algebra.TensorProduct.includeLeft : A →ₐ[F] _)
  let fb := i.comp (Algebra.TensorProduct.includeRight : B →ₐ[F] _)
  replace H := H K fa fb
  simp_rw [linearDisjoint_iff', AlgHom.fieldRange_toSubalgebra,
    Subalgebra.linearDisjoint_iff_injective] at H
  have hi : i = (fa.range.mulMap fb.range).comp (Algebra.TensorProduct.congr
      (AlgEquiv.ofInjective fa fa.injective) (AlgEquiv.ofInjective fb fb.injective)) := by
    ext <;> simp [fa, fb]
  replace H : Function.Injective i := by simpa only
    [hi, AlgHom.coe_comp, AlgHom.coe_coe, EquivLike.injective_comp, fa, this, K, fb]
  change Function.Injective (Ideal.Quotient.mk M) at H
  rwa [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker] at H

variable (F E) in
/-- If `E` and `K` are field extensions of `F`, one of them is algebraic, such that
`E ⊗[F] K` is a domain, then `E ⊗[F] K` is also a field. It is a corollary of
`Subalgebra.LinearDisjoint.exists_field_of_isDomain_of_injective` and
`IntermediateField.sup_toSubalgebra_of_isAlgebraic`.
See `Algebra.TensorProduct.isAlgebraic_of_isField` for its converse (in an earlier file). -/
theorem _root_.Algebra.TensorProduct.isField_of_isAlgebraic
    (K : Type*) [Field K] [Algebra F K] [IsDomain (E ⊗[F] K)]
    (halg : Algebra.IsAlgebraic F E ∨ Algebra.IsAlgebraic F K) : IsField (E ⊗[F] K) :=
  have ⟨L, _, _, fa, fb, hfa, hfb, H⟩ :=
    Subalgebra.LinearDisjoint.exists_field_of_isDomain_of_injective F E K
      (RingHom.injective _) (RingHom.injective _)
  let f : E ⊗[F] K ≃ₐ[F] ↥(fa.fieldRange ⊔ fb.fieldRange) :=
    Algebra.TensorProduct.congr (AlgEquiv.ofInjective fa hfa) (AlgEquiv.ofInjective fb hfb)
    |>.trans (Subalgebra.LinearDisjoint.mulMap H)
    |>.trans (Subalgebra.equivOfEq _ _
      (sup_toSubalgebra_of_isAlgebraic fa.fieldRange fb.fieldRange <| by
        rwa [(AlgEquiv.ofInjective fa hfa).isAlgebraic_iff,
          (AlgEquiv.ofInjective fb hfb).isAlgebraic_iff] at halg).symm)
  f.toMulEquiv.isField (Field.toIsField _)

/-- If `A` and `L` are linearly disjoint over `F` and one of them is algebraic,
then `A ⊗[F] L` is a field. -/
theorem isField_of_isAlgebraic (H : A.LinearDisjoint L)
    (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) : IsField (A ⊗[F] L) :=
  have := H.isDomain
  Algebra.TensorProduct.isField_of_isAlgebraic F A L halg

/-- If `A` and `B` are field extensions of `F`, one of them is algebraic, such that there exists a
field `E` that `A` and `B` embeds into with linearly disjoint images, then `A ⊗[F] B`
is a field. -/
theorem isField_of_isAlgebraic' {A B : Type*} [Field A] [Algebra F A] [Field B] [Algebra F B]
    {fa : A →ₐ[F] E} {fb : B →ₐ[F] E} (H : fa.fieldRange.LinearDisjoint fb.fieldRange)
    (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F B) : IsField (A ⊗[F] B) :=
  have := H.isDomain'
  Algebra.TensorProduct.isField_of_isAlgebraic F A B halg

/-- If `A` and `L` are linearly disjoint, one of them is algebraic, then for any `B` and `L'`
isomorphic to `A` and `L` respectively, `B` and `L'` are also linearly disjoint. -/
theorem algEquiv_of_isAlgebraic (H : A.LinearDisjoint L)
    {E' : Type*} [Field E'] [Algebra F E']
    (B : IntermediateField F E')
    (L' : Type*) [Field L'] [Algebra F L'] [Algebra L' E'] [IsScalarTower F L' E']
    (f1 : A ≃ₐ[F] B) (f2 : L ≃ₐ[F] L')
    (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F L) :
    B.LinearDisjoint L' :=
  .of_isField ((Algebra.TensorProduct.congr f1 f2).symm.toMulEquiv.isField
    (H.isField_of_isAlgebraic halg))

/--
If `A` and `B` are linearly disjoint, then `trace` and `algebraMap` commutes.
-/
theorem trace_algebraMap [FiniteDimensional F E] (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤)
    (x : B) :
    Algebra.trace A E (algebraMap B E x) = algebraMap F A (Algebra.trace F B x) := by
  rw [linearDisjoint_iff'] at h₁
  refine h₁.trace_algebraMap ?_ x
  simpa [sup_toSubalgebra_of_isAlgebraic_right] using congr_arg toSubalgebra h₂

/--
If `A` and `B` are linearly disjoint, then `norm` and `algebraMap` commutes.
-/
theorem norm_algebraMap [FiniteDimensional F E] (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤)
    (x : B) :
    Algebra.norm A (algebraMap B E x) = algebraMap F A (Algebra.norm F x) := by
  rw [linearDisjoint_iff'] at h₁
  refine h₁.norm_algebraMap ?_  x
  simpa [sup_toSubalgebra_of_isAlgebraic_right] using congr_arg toSubalgebra h₂

end LinearDisjoint

end IntermediateField
