/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.FieldTheory.Adjoin
import Mathlib.LinearAlgebra.TensorProductBasis

/-!

# Linearly disjoint

This file contains basics about the linearly disjoint of fields.

## Mathematical background

(<https://en.wikipedia.org/wiki/Linearly_disjoint>) In mathematics, algebras `A`, `B` over a field
`F` inside some field extension `E` of `F` are said to be linearly disjoint over `F` if the
following equivalent conditions are met:

- The map `A ⊗[F] B → A ⊔ B`, `x ⊗ₜ[F] y ↦ x * y` is injective.

- Any `F`-basis of `A` remains linearly independent over `B`.

- If `{ u_i }`, `{ v_j }` are `F`-bases for `A`, `B`, then the products `{ u_i * v_j }` are
  linearly independent over `F`.

Our definition `IntermediateField.LinearlyDisjoint` is very closed to the second equivalent
definition in the above.

(<https://mathoverflow.net/questions/8324>) For two abstract fields `E` and `K` over `F`, they are
called linearly disjoint over `F` (`LinearlyDisjoint F E K`), if `E ⊗[F] K` is a field.
In this case, it can be shown that at least one of `E / F` and `K / F` are algebraic, and if this
holds, then it is equivalent to the above `IntermediateField.LinearlyDisjoint`.

The advantage of `LinearlyDisjoint` is that it is preserved under algebra isomorphisms, while for
`IntermediateField.LinearlyDisjoint` this is not so easy to prove, in fact it's wrong if both of the
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

open scoped Classical Polynomial TensorProduct

open FiniteDimensional Polynomial IntermediateField Field

noncomputable section

universe u v w

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]

variable (K : Type w) [Field K] [Algebra F K]

namespace IntermediateField

variable {F E}

variable (A B : IntermediateField F E)

/-- Two intermediate fields `A` and `B` of `E / F` are called linearly disjoint, if any `F`-linearly
independent subset of `A` remains linearly independent over `B`. Marked as `protected` because later
we will define linearly disjoint for two abstract fields over a base field. -/
protected def LinearlyDisjoint := ∀ {a : Set A}, LinearIndependent F (fun x : a ↦ x.1) →
    LinearIndependent B (fun x : a ↦ x.1.1)

variable {A B}

/-- In the definition of linearly disjoint, linearly independent subset of `A` can be replaced
by its embedding into `E`. -/
theorem linearlyDisjoint_def' :
    A.LinearlyDisjoint B ↔ ∀ {a : Set A}, LinearIndependent F (fun x : a ↦ x.1.1) →
      LinearIndependent B (fun x : a ↦ x.1.1) := by
  have h {a : Set A} : LinearIndependent F (fun x : a ↦ x.1) ↔
      LinearIndependent F (fun x : a ↦ x.1.1) :=
    ⟨fun H ↦ H.map' A.val.toLinearMap (LinearMap.ker_eq_bot_of_injective A.val.injective),
      fun H ↦ H.of_comp A.val.toLinearMap⟩
  simp_rw [IntermediateField.LinearlyDisjoint, h]

/-- If `A` and `B` are linearly disjoint, then any `F`-linearly independent family on `A` remains
linearly independent over `B`. -/
theorem LinearlyDisjoint.linearIndependent_map (H : A.LinearlyDisjoint B)
    {ι : Type*} {v : ι → A} (ha : LinearIndependent F v) :
    LinearIndependent B (A.val ∘ v) :=
  (H ha.coe_range).comp (Set.rangeFactorization v)
    (fun _ _ h ↦ ha.injective (congr_arg Subtype.val h))

/-- If `A` and `B` are linearly disjoint, then for a family on `A` which is `F`-linearly independent
when embedded into `E`, it remains linearly independent over `B`. -/
theorem LinearlyDisjoint.linearIndependent_map' (H : A.LinearlyDisjoint B)
    {ι : Type*} {v : ι → A} (ha : LinearIndependent F (A.val ∘ v)) :
    LinearIndependent B (A.val ∘ v) :=
  H.linearIndependent_map (ha.of_comp A.val.toLinearMap)

private lemma test1' {a b : Type*}
    (fa : a → A) (fb : b → B)
    (l : a × b →₀ F) (L : a →₀ B)
    {h0 : Finsupp.total b B F fb 0 = 0}
    (h : L = l.curry.mapRange (Finsupp.total b B F fb) h0) :
    Finsupp.total (a × b) E F (fun x : a × b ↦ (fa x.1).1 * (fb x.2).1) l =
      Finsupp.total a E B (fun x : a ↦ (fa x).1) L := by
  let g (x : a) (y : b) (z : F) := z • ((fa x).1 * (fb y).1)
  rw [Finsupp.total_apply, Finsupp.total_apply, h,
    Finsupp.sum_mapRange_index (by exact fun _ ↦ zero_smul B _),
    ← l.sum_curry_index g (fun _ _ ↦ zero_smul F _) (fun _ _ _ _ ↦ add_smul _ _ _),
    Finsupp.sum]
  congr
  ext x
  simp_rw [Finsupp.total_apply, Finsupp.sum, Finset.sum_smul]
  congr
  ext y
  simp_rw [Algebra.smul_def, map_mul, mul_comm (fa x).1 (fb y).1, ← mul_assoc]
  rfl

private lemma test1 {a : Set A} {b : Set B} (l : a × b →₀ F) (L : a →₀ B)
    {h0 : Finsupp.total b B F (fun y ↦ y.1) 0 = 0}
    (h : L = l.curry.mapRange (Finsupp.total b B F (fun y ↦ y.1)) h0) :
    Finsupp.total (a × b) E F (fun x : a × b ↦ x.1.1.1 * x.2.1.1) l =
      Finsupp.total a E B (fun x : a ↦ x.1.1) L :=
  test1' _ _ l L h

variable (F E) in
private lemma test2 {a b : Type*} {v : a → b →₀ F} (H : LinearIndependent F v) :
    LinearIndependent E fun x : a ↦ (v x).mapRange (algebraMap F E) (map_zero _) := by
  let f := Finsupp.total a _ F v
  obtain ⟨g, hg : g.comp f =  _⟩ := LinearMap.exists_leftInverse_of_injective _ H
  let f' := f.baseChange E
  let g' := g.baseChange E
  have hg' : g'.comp f' = LinearMap.id := by
    convert (LinearMap.baseChange_comp (A := E) f g).symm
    rw [hg]
    refine TensorProduct.AlgebraTensorModule.ext fun x y ↦ ?_
    rw [LinearMap.baseChange_tmul]
    rfl
  let ba := Algebra.TensorProduct.basis E (Basis.ofRepr (LinearEquiv.refl (R := F) (M := a →₀ F)))
  let bb := Algebra.TensorProduct.basis E (Basis.ofRepr (LinearEquiv.refl (R := F) (M := b →₀ F)))
  let f'' := (bb.repr.toLinearMap.comp f').comp ba.repr.symm.toLinearMap
  let g'' := (ba.repr.toLinearMap.comp g').comp bb.repr.symm.toLinearMap
  have hg'' : g''.comp f'' = LinearMap.id := by
    change ba.repr ∘ₗ (g' ∘ₗ (bb.repr.symm.toLinearMap ∘ₗ bb.repr.toLinearMap) ∘ₗ f') ∘ₗ
        ba.repr.symm.toLinearMap = LinearMap.id
    rw [← LinearEquiv.coe_trans, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap,
      LinearMap.id_comp, hg', LinearMap.id_comp, ← LinearEquiv.coe_trans,
      LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap]
  rw [LinearIndependent]
  convert LinearMap.ker_eq_bot_of_inverse hg''
  refine (Basis.ofRepr (LinearEquiv.refl (R := E) (M := a →₀ E))).ext fun x ↦ ?_
  simp only [Basis.coe_ofRepr, LinearEquiv.refl_symm, LinearEquiv.refl_apply, Finsupp.total_single,
    one_smul, Basis.coe_repr_symm, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Algebra.TensorProduct.basis_apply, LinearMap.baseChange_tmul,
    Algebra.TensorProduct.basis_repr_tmul]

/-- If there exists an `F`-basis of `A` which remains linearly independent over `B`, then
`A` and `B` are linearly disjoint. -/
theorem LinearlyDisjoint.of_basis_map {ι : Type*} (basis : Basis ι F A)
    (H : LinearIndependent B (A.val ∘ basis)) : A.LinearlyDisjoint B := fun {a} ha ↦ by
  replace ha := test2 F B <|
    ha.map' basis.repr.toLinearMap (LinearMap.ker_eq_bot_of_injective basis.repr.injective)
  letI : Algebra B B := Algebra.id B
  letI : Module B B := Algebra.toModule
  letI : Module B (ι →₀ B) := Finsupp.module ι B
  rw [linearIndependent_iff] at H ha ⊢
  intro l hl
  let L := Finsupp.total a (ι →₀ B) B
    (fun x ↦ Finsupp.mapRange (algebraMap F B) (map_zero _) (basis.repr x.1)) l
  have key : Finsupp.total a E B (fun x ↦ x.1.1) l = Finsupp.total ι E B (A.val ∘ basis) L := by
    simp_rw [Finsupp.total_apply]
    rw [Finsupp.sum_sum_index (fun _ ↦ by exact zero_smul B _)
      (fun _ _ _ ↦ by exact add_smul _ _ _)]
    congr
    ext x y
    rw [Finsupp.sum_smul_index fun _ ↦ by exact zero_smul _ _,
      Finsupp.sum_mapRange_index fun _ ↦ by rw [mul_zero, zero_smul], Finsupp.sum]
    have (z : ι) : (y * (algebraMap F B) (basis.repr x z)) • (A.val ∘ basis) z =
        y • A.val (basis.repr x z • basis z) := by
      simp_rw [Algebra.smul_def, map_mul (algebraMap B E), map_mul A.val, ← mul_assoc]
      rfl
    simp_rw [this]
    rw [← Finset.smul_sum, ← map_sum]
    congr
    change _ = Finsupp.sum (basis.repr x) fun a b ↦ b • basis a
    rw [← Finsupp.total_apply, basis.total_repr]
  exact ha l (H L (key ▸ hl))

/-- If `A` and `B` are linearly disjoint, then for any `F`-linearly independent subsets
`{ u_i }`, `{ v_j }` of `A`, `B`, the products `{ u_i * v_j }` are linearly independent over `F`. -/
theorem LinearlyDisjoint.linearIndependent_mul_of_set (H : A.LinearlyDisjoint B)
    {a : Set A} {b : Set B}
    (ha : LinearIndependent F (fun x : a ↦ x.1))
    (hb : LinearIndependent F (fun y : b ↦ y.1)) :
    LinearIndependent F (fun x : a × b ↦ x.1.1.1 * x.2.1.1) := by
  replace H := H ha
  rw [linearIndependent_iff] at H hb ⊢
  intro l hl
  let L := l.curry.mapRange (Finsupp.total b B F (fun y ↦ y.1)) (map_zero _)
  ext ⟨x, y⟩
  rw [Finsupp.zero_apply, ← Finsupp.curry_apply, hb (l.curry x) <| by
    simpa only [Finsupp.onFinset_apply, Finsupp.zero_apply] using
      congr($(H _ (test1 l L rfl ▸ hl)) x), Finsupp.zero_apply]

/-- If for any `F`-linearly independent subsets `{ u_i }`, `{ v_j }` of `A`, `B`, the products
`{ u_i * v_j }` are linearly independent over `F`, then `A` and `B` are linearly disjoint. -/
theorem LinearlyDisjoint.of_linearIndependent_mul_of_set
    (H : ∀ {a : Set A} {b : Set B}, LinearIndependent F (fun x : a ↦ x.1) →
      LinearIndependent F (fun y : b ↦ y.1) →
      LinearIndependent F (fun x : a × b ↦ x.1.1.1 * x.2.1.1)) :
    A.LinearlyDisjoint B := fun {a} ha ↦ by
  let b := Basis.ofVectorSpaceIndex F B
  let basis : Basis b F B := Basis.ofVectorSpace F B
  have hb : LinearIndependent F (fun y : b ↦ y.1) := by
    convert basis.linearIndependent
    ext x
    congr
    exact (Basis.extend_apply_self _ _).symm
  replace H := H ha hb
  rw [linearIndependent_iff] at H ⊢
  intro l hl
  let L := Finsupp.finsuppProdEquiv.symm (l.mapRange basis.repr (map_zero _))
  have : l = (Finsupp.finsuppProdEquiv L).mapRange
      (Finsupp.total b B F (fun y ↦ y.1)) (map_zero _) := by
    rw [Finsupp.finsuppProdEquiv.apply_symm_apply,
      ← Finsupp.mapRange_comp _ rfl _ (map_zero _) (by rw [Function.comp_apply, map_zero]; rfl)]
    convert l.mapRange_id.symm
    ext y
    rw [id, Function.comp_apply]
    congr
    convert basis.total_repr y
    ext x
    congr
    exact (Basis.ofVectorSpace_apply_self F B x).symm
  rwa [H L (test1 L l this ▸ hl), show Finsupp.finsuppProdEquiv 0 = 0 from rfl,
    Finsupp.mapRange_zero] at this

/-- `A` and `B` are linearly disjoint if and only if for any `F`-linearly independent subsets
`{ u_i }`, `{ v_j }` of `A`, `B`, the products `{ u_i * v_j }` are linearly independent over `F`. -/
theorem linearlyDisjoint_iff_linearIndependent_mul_of_set :
    A.LinearlyDisjoint B ↔ ∀ {a : Set A} {b : Set B}, LinearIndependent F (fun x : a ↦ x.1) →
      LinearIndependent F (fun y : b ↦ y.1) →
      LinearIndependent F (fun x : a × b ↦ x.1.1.1 * x.2.1.1) :=
  ⟨fun H _ _ ha hb ↦ H.linearIndependent_mul_of_set ha hb,
    LinearlyDisjoint.of_linearIndependent_mul_of_set⟩

theorem LinearlyDisjoint.of_basis_mul {ιA ιB : Type*} (bA : Basis ιA F A) (bB : Basis ιB F B)
    (H : LinearIndependent F (fun x : ιA × ιB ↦ (bA x.1).1 * (bB x.2).1)) :
    A.LinearlyDisjoint B := by
  refine LinearlyDisjoint.of_basis_map bA ?_
  sorry

/-- Linearly disjoint is symmetric. -/
theorem LinearlyDisjoint.symm (H : A.LinearlyDisjoint B) : B.LinearlyDisjoint A := by
  rw [linearlyDisjoint_iff_linearIndependent_mul_of_set] at H ⊢
  intro a b ha hb
  rw [← linearIndependent_equiv (Equiv.prodComm b a)]
  convert H hb ha
  exact mul_comm _ _

theorem linearlyDisjoint_symm : A.LinearlyDisjoint B ↔ B.LinearlyDisjoint A :=
  ⟨LinearlyDisjoint.symm, LinearlyDisjoint.symm⟩

end IntermediateField

/-- Two abstract fields `E` and `K` over `F` are called linearly disjoint, if their tensor product
over `F` is a field. -/
def LinearlyDisjoint := IsField (E ⊗[F] K)

set_option linter.unusedVariables false in
variable {F E K} in
/-- If two abstract fields `E` and `K` over `F` are linearly disjoint, then at least one of `E / F`
and `K / F` are algebraic. -/
proof_wanted LinearlyDisjoint.isAlgebraic (H : LinearlyDisjoint F E K) :
    Algebra.IsAlgebraic F E ∨ Algebra.IsAlgebraic F K
