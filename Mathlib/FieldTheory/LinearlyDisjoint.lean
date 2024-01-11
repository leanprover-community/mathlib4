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
protected def LinearDisjoint := ∀ ⦃a : Set A⦄, LinearIndependent F (fun x : a ↦ x.1) →
    LinearIndependent B (fun x : a ↦ x.1.1)

theorem linearDisjoint_iff :
    A.LinearDisjoint B ↔ ∀ {a : Set A}, LinearIndependent F (fun x : a ↦ x.1) →
      LinearIndependent B (fun x : a ↦ x.1.1) := Iff.rfl

/-- In the definition of linearly disjoint, linearly independent subset of `A` can be replaced
by its embedding into `E`. -/
theorem linearDisjoint_iff' :
    A.LinearDisjoint B ↔ ∀ {a : Set A}, LinearIndependent F (fun x : a ↦ x.1.1) →
      LinearIndependent B (fun x : a ↦ x.1.1) := by
  have h {a : Set A} : LinearIndependent F (fun x : a ↦ x.1) ↔
      LinearIndependent F (fun x : a ↦ x.1.1) :=
    ⟨fun H ↦ H.map' A.val.toLinearMap (LinearMap.ker_eq_bot_of_injective A.val.injective),
      fun H ↦ H.of_comp A.val.toLinearMap⟩
  simp_rw [linearDisjoint_iff, h]

variable {A B}

/-- If `A` and `B` are linearly disjoint, then any `F`-linearly independent family on `A` remains
linearly independent over `B`. -/
theorem LinearDisjoint.linearIndependent_map (H : A.LinearDisjoint B)
    {ιA : Type*} {vA : ιA → A} (hA : LinearIndependent F vA) :
    LinearIndependent B (A.val ∘ vA) :=
  (H hA.coe_range).comp (Set.rangeFactorization vA)
    (fun _ _ h ↦ hA.injective (congr_arg Subtype.val h))

/-- If `A` and `B` are linearly disjoint, then for a family on `A` which is `F`-linearly independent
when embedded into `E`, it remains linearly independent over `B`. -/
theorem LinearDisjoint.linearIndependent_map' (H : A.LinearDisjoint B)
    {ιA : Type*} {vA : ιA → A} (hA : LinearIndependent F (A.val ∘ vA)) :
    LinearIndependent B (A.val ∘ vA) :=
  H.linearIndependent_map (hA.of_comp A.val.toLinearMap)

private lemma test1 {ιA ιB : Type*} (vA : ιA → A) (vB : ιB → B)
    (l : ιA × ιB →₀ F) (L : ιA →₀ B)
    {h0 : Finsupp.total ιB B F vB 0 = 0}
    (h : L = l.curry.mapRange (Finsupp.total ιB B F vB) h0) :
    Finsupp.total (ιA × ιB) E F (fun x : ιA × ιB ↦ (vA x.1).1 * (vB x.2).1) l =
      Finsupp.total ιA E B (fun x : ιA ↦ (vA x).1) L := by
  let g (x : ιA) (y : ιB) (z : F) := z • ((vA x).1 * (vB y).1)
  rw [Finsupp.total_apply, Finsupp.total_apply, h,
    Finsupp.sum_mapRange_index (by exact fun _ ↦ zero_smul B _),
    ← l.sum_curry_index g (fun _ _ ↦ zero_smul F _) (fun _ _ _ _ ↦ add_smul _ _ _),
    Finsupp.sum]
  congr
  ext x
  simp_rw [Finsupp.total_apply, Finsupp.sum, Finset.sum_smul]
  congr
  ext y
  simp_rw [Algebra.smul_def, map_mul, mul_comm (vA x).1 (vB y).1, ← mul_assoc]
  rfl

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
theorem LinearDisjoint.of_basis_map {ιA : Type*} (bA : Basis ιA F A)
    (H : LinearIndependent B (A.val ∘ bA)) : A.LinearDisjoint B := fun a ha ↦ by
  replace ha := test2 F B <|
    ha.map' bA.repr.toLinearMap (LinearMap.ker_eq_bot_of_injective bA.repr.injective)
  letI : Algebra B B := Algebra.id B
  letI : Module B B := Algebra.toModule
  letI : Module B (ιA →₀ B) := Finsupp.module ιA B
  rw [linearIndependent_iff] at H ha ⊢
  intro l hl
  let L := Finsupp.total a (ιA →₀ B) B
    (fun x ↦ Finsupp.mapRange (algebraMap F B) (map_zero _) (bA.repr x.1)) l
  have key : Finsupp.total a E B (fun x ↦ x.1.1) l = Finsupp.total ιA E B (A.val ∘ bA) L := by
    simp_rw [Finsupp.total_apply]
    rw [Finsupp.sum_sum_index (fun _ ↦ by exact zero_smul B _)
      (fun _ _ _ ↦ by exact add_smul _ _ _)]
    congr
    ext x y
    rw [Finsupp.sum_smul_index fun _ ↦ by exact zero_smul _ _,
      Finsupp.sum_mapRange_index fun _ ↦ by rw [mul_zero, zero_smul], Finsupp.sum]
    have (z : ιA) : (y * (algebraMap F B) (bA.repr x z)) • (A.val ∘ bA) z =
        y • A.val (bA.repr x z • bA z) := by
      simp_rw [Algebra.smul_def, map_mul (algebraMap B E), map_mul A.val, ← mul_assoc]
      rfl
    simp_rw [this]
    rw [← Finset.smul_sum, ← map_sum]
    congr
    change _ = Finsupp.sum (bA.repr x) fun a b ↦ b • bA a
    rw [← Finsupp.total_apply, bA.total_repr]
  exact ha l (H L (key ▸ hl))

/-- If `A` and `B` are linearly disjoint, then for any `F`-linearly independent families
`{ u_i }`, `{ v_j }` of `A`, `B`, the products `{ u_i * v_j }` are linearly independent over `F`. -/
theorem LinearDisjoint.linearIndependent_mul (H : A.LinearDisjoint B)
    {ιA ιB : Type*} {vA : ιA → A} {vB : ιB → B}
    (hA : LinearIndependent F vA)
    (hB : LinearIndependent F vB) :
    LinearIndependent F (fun x : ιA × ιB ↦ (vA x.1).1 * (vB x.2).1) := by
  replace H := H.linearIndependent_map hA
  rw [linearIndependent_iff] at H hB ⊢
  intro l hl
  let L := l.curry.mapRange (Finsupp.total ιB B F vB) (map_zero _)
  ext ⟨x, y⟩
  have := hB (l.curry x) <| by simpa only [Finsupp.onFinset_apply,
    Finsupp.zero_apply] using congr($(H _ (test1 vA vB l L rfl ▸ hl)) x)
  rw [Finsupp.zero_apply, ← Finsupp.curry_apply, this, Finsupp.zero_apply]

/-- If there are `F`-bases `{ u_i }`, `{ v_j }` of `A`, `B`, such that the products
`{ u_i * v_j }` are linearly independent over `F`, then `A` and `B` are linearly disjoint. -/
theorem LinearDisjoint.of_basis_mul {ιA ιB : Type*} (bA : Basis ιA F A) (bB : Basis ιB F B)
    (H : LinearIndependent F (fun x : ιA × ιB ↦ (bA x.1).1 * (bB x.2).1)) :
    A.LinearDisjoint B := by
  refine of_basis_map bA ?_
  rw [linearIndependent_iff] at H ⊢
  intro l hl
  let L := Finsupp.finsuppProdEquiv.symm (l.mapRange bB.repr (map_zero _))
  have key : l = (Finsupp.finsuppProdEquiv L).mapRange
      (Finsupp.total ιB B F bB) (map_zero _) := by
    rw [Finsupp.finsuppProdEquiv.apply_symm_apply,
      ← Finsupp.mapRange_comp _ rfl _ (map_zero _) (by rw [Function.comp_apply, map_zero]; rfl)]
    convert l.mapRange_id.symm
    ext y
    exact congr_arg Subtype.val (bB.total_repr y)
  have : _ = Finsupp.total ιA E B (A.val ∘ bA) l := test1 bA bB L l key
  rwa [H L (this.symm ▸ hl), show Finsupp.finsuppProdEquiv 0 = 0 from rfl,
    Finsupp.mapRange_zero] at key

private lemma test3' (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]
    (x : Basis.ofVectorSpaceIndex K V) : (Basis.ofVectorSpace K V) x = x.1 :=
  Basis.extend_apply_self _ _

private lemma test3 (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V] :
    LinearIndependent K (fun x : Basis.ofVectorSpaceIndex K V ↦ x.1) := by
  convert (Basis.ofVectorSpace K V).linearIndependent
  ext _
  exact (test3' K V _).symm

/-- `A` and `B` are linearly disjoint if and only if for any `F`-linearly independent subsets
`{ u_i }`, `{ v_j }` of `A`, `B`, the products `{ u_i * v_j }` are linearly independent over `F`. -/
theorem linearDisjoint_iff_linearIndependent_mul_of_set :
    A.LinearDisjoint B ↔ ∀ {a : Set A} {b : Set B}, LinearIndependent F (fun x : a ↦ x.1) →
      LinearIndependent F (fun y : b ↦ y.1) →
      LinearIndependent F (fun x : a × b ↦ x.1.1.1 * x.2.1.1) := by
  refine ⟨fun H _ _ hA hB ↦ H.linearIndependent_mul hA hB,
    fun H ↦ LinearDisjoint.of_basis_mul (Basis.ofVectorSpace F A) (Basis.ofVectorSpace F B) ?_⟩
  simpa only [test3'] using H (test3 F A) (test3 F B)

/-- Linearly disjoint is symmetric. -/
theorem LinearDisjoint.symm (H : A.LinearDisjoint B) : B.LinearDisjoint A := by
  rw [linearDisjoint_iff_linearIndependent_mul_of_set] at H ⊢
  intro a b ha hb
  rw [← linearIndependent_equiv (Equiv.prodComm b a)]
  convert H hb ha
  exact mul_comm _ _

/-- Linearly disjoint is symmetric. -/
theorem linearDisjoint_symm : A.LinearDisjoint B ↔ B.LinearDisjoint A :=
  ⟨LinearDisjoint.symm, LinearDisjoint.symm⟩

variable (A) in
theorem LinearDisjoint.of_bot_right : A.LinearDisjoint ⊥ := fun a ha ↦
  ha.map_of_injective_injective (M' := E) (botEquiv F E) A.val
    (fun _ _ ↦ (botEquiv F E).injective (by rwa [map_zero]))
    (fun _ _ ↦ A.val.injective (by rwa [map_zero]))
    (fun r _ ↦ by obtain ⟨x, h⟩ := r.2; simp_rw [Algebra.smul_def,
      show r = algebraMap F _ x from SetCoe.ext h.symm, botEquiv_def]; rfl)

variable (B) in
theorem LinearDisjoint.of_bot_left : (⊥ : IntermediateField F E).LinearDisjoint B :=
  LinearDisjoint.of_bot_right B |>.symm

theorem LinearDisjoint.of_inclusion_right {B' : IntermediateField F E} (H : A.LinearDisjoint B)
    (h : B' ≤ B) : A.LinearDisjoint B' := fun a ha ↦
  (H ha).map_of_injective_injective (M' := E) (inclusion h)
    (AddMonoidHom.id E) (fun _ _ ↦ (inclusion h).injective (by rwa [map_zero]))
    (fun _ ↦ id) (fun _ _ ↦ rfl)

theorem LinearDisjoint.of_inclusion_left {A' : IntermediateField F E} (H : A.LinearDisjoint B)
    (h : A' ≤ A) : A'.LinearDisjoint B := H.symm.of_inclusion_right h |>.symm

/-- If `A` and `B` are linearly disjoint, `A'` and `B'` are contained in `A` and `B`, respectively,
then `A'` and `B'` are also linearly disjoint. -/
theorem LinearDisjoint.of_inclusion {A' B' : IntermediateField F E} (H : A.LinearDisjoint B)
    (hA : A' ≤ A) (hB : B' ≤ B) : A'.LinearDisjoint B' :=
  H.of_inclusion_left hA |>.of_inclusion_right hB

/-- If `A` and `B` are linearly disjoint over `F`, then their intersection is equal to `F`. -/
theorem LinearDisjoint.inf_eq_bot (H : A.LinearDisjoint B) : A ⊓ B = ⊥ := bot_unique fun x hx ↦ by
  have hxA := inf_le_left (a := A) (b := B) hx
  replace H := not_imp_not.2 (H.linearIndependent_map (vA := ![1, ⟨x, hxA⟩]))
  have : A.val ∘ ![1, ⟨x, hxA⟩] = ![1, x] := by ext i; fin_cases i <;> rfl
  simp_rw [this, LinearIndependent.pair_iff, not_forall] at H
  obtain ⟨s, t, h1, h2⟩ := H ⟨⟨-x, neg_mem <| inf_le_right (a := A) (b := B) hx⟩, 1,
    by rw [one_smul, Algebra.smul_def, mul_one]; exact add_left_neg x, by simp⟩
  apply_fun algebraMap A E at h1
  simp_rw [Algebra.smul_def, mul_one, map_add, map_mul, map_zero] at h1
  change algebraMap F E s + algebraMap F E t * x = 0 at h1
  have : algebraMap F E t ≠ 0 := (_root_.map_ne_zero _).2 fun h ↦ h2
    ⟨(algebraMap F E).injective (by rw [map_zero, ← h1, h, map_zero, zero_mul, add_zero]), h⟩
  use -s / t
  change algebraMap F E (-s / t) = _
  rwa [map_div₀, map_neg, div_eq_iff this, neg_eq_iff_add_eq_zero, mul_comm]

/-- If `A` and itself are linearly disjoint over `F`, then it is equal to `F`. -/
theorem LinearDisjoint.eq_bot_of_self (H : A.LinearDisjoint A) : A = ⊥ :=
  inf_of_le_left (le_refl A) ▸ H.inf_eq_bot

end IntermediateField

/-- Two abstract fields `E` and `K` over `F` are called linearly disjoint, if their tensor product
over `F` is a field. -/
def LinearDisjoint := IsField (E ⊗[F] K)

set_option linter.unusedVariables false in
variable {F E K} in
/-- If two abstract fields `E` and `K` over `F` are linearly disjoint, then at least one of `E / F`
and `K / F` are algebraic. -/
proof_wanted LinearDisjoint.isAlgebraic (H : LinearDisjoint F E K) :
    Algebra.IsAlgebraic F E ∨ Algebra.IsAlgebraic F K
