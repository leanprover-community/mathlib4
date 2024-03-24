/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.FieldTheory.Adjoin
import Mathlib.RingTheory.Flat.Basic

/-!

# Linearly disjoint

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

open scoped Classical Polynomial TensorProduct

open FiniteDimensional Polynomial IntermediateField

noncomputable section

universe u v w

namespace Submodule

variable {R : Type u} {S : Type v}

section Semiring

variable [CommSemiring R] [Semiring S] [Algebra R S]

variable (M N : Submodule R S)

/-- If `M` and `N` are submodules in an algebra `S` over `R`, there is the natural map
`M ⊗[R] N →ₗ[R] S` induced by multiplication in `S`. -/
def mulMap := TensorProduct.lift <| ((LinearMap.domRestrict' N).comp <| .mul R S).domRestrict M

@[simp]
theorem mulMap_tmul (m : M) (n : N) : mulMap M N (m ⊗ₜ[R] n) = m.1 * n.1 := rfl

theorem mulMap_comm_of_commute (hc : ∀ (m : M) (n : N), Commute m.1 n.1) :
    mulMap N M = (mulMap M N).comp (TensorProduct.comm R N M).toLinearMap := by
  refine TensorProduct.ext' fun n m ↦ ?_
  simp_rw [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.comm_tmul, mulMap_tmul]
  exact (hc m n).symm

/-- Two submodules `M` and `N` in an algebra `S` over `R` are linearly disjoint if the natural map
`M ⊗[R] N →ₗ[R] S` induced by multiplication in `S` is injective. -/
protected def LinearDisjoint : Prop := Function.Injective (mulMap M N)

variable {M N}

theorem LinearDisjoint.injective (H : M.LinearDisjoint N) : Function.Injective (mulMap M N) := H

/-- Linearly disjoint is symmetric if elements in the module commute. -/
theorem LinearDisjoint.symm_of_commute (H : M.LinearDisjoint N)
    (hc : ∀ (m : M) (n : N), Commute m.1 n.1) : N.LinearDisjoint M := by
  rw [Submodule.LinearDisjoint, mulMap_comm_of_commute M N hc]
  exact ((TensorProduct.comm R N M).toEquiv.injective_comp _).2 H

/-- Linearly disjoint is symmetric if elements in the module commute. -/
theorem linearDisjoint_symm_of_commute
    (hc : ∀ (m : M) (n : N), Commute m.1 n.1) : M.LinearDisjoint N ↔ N.LinearDisjoint M :=
  ⟨fun H ↦ H.symm_of_commute hc, fun H ↦ H.symm_of_commute fun _ _ ↦ (hc _ _).symm⟩

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring S] [Algebra R S]

variable (M N : Submodule R S)

theorem mulMap_comm : mulMap N M = (mulMap M N).comp (TensorProduct.comm R N M).toLinearMap :=
  mulMap_comm_of_commute M N fun _ _ ↦ mul_comm _ _

variable {M N}

/-- Linearly disjoint is symmetric in a commutative ring. -/
theorem LinearDisjoint.symm (H : M.LinearDisjoint N) : N.LinearDisjoint M :=
  H.symm_of_commute fun _ _ ↦ mul_comm _ _

/-- Linearly disjoint is symmetric in a commutative ring. -/
theorem linearDisjoint_symm : M.LinearDisjoint N ↔ N.LinearDisjoint M :=
  ⟨LinearDisjoint.symm, LinearDisjoint.symm⟩

end CommSemiring

section Ring

namespace LinearDisjoint

variable [CommRing R] [Ring S] [Algebra R S]

variable (M N : Submodule R S)

variable {M} in
/-- If `m : ι → M` is a family of elements, then there is an `R`-linear map from `ι →₀ N` to
`S` which maps `{ n_i }` to the sum of `m_i * n_i`. -/
def mulLeftMap {ι : Type*} (m : ι → M) : (ι →₀ N) →ₗ[R] S :=
  mulMap M N ∘ₗ LinearMap.rTensor N (Finsupp.total ι M R m) ∘ₗ
    TensorProduct.finsuppScalarLeft.symm.toLinearMap

variable {M N} in
@[simp]
theorem mulLeftMap_apply_single {ι : Type*} (m : ι → M) (i : ι) (n : N) :
    mulLeftMap N m (Finsupp.single i n) = (m i).1 * n.1 := by
  simp [mulLeftMap, TensorProduct.finsuppScalarLeft_symm_apply_single]

variable {M} in
theorem mulLeftMap_def' {ι : Type*} (m : ι → M) : mulLeftMap N m =
    Finsupp.lsum ℕ fun (i : ι) ↦ (LinearMap.mulLeft R (m i).1).comp N.subtype := by
  ext; simp

variable {M N} in
theorem mulLeftMap_apply {ι : Type*} (m : ι → M) (n : ι →₀ N) :
    mulLeftMap N m n = Finsupp.sum n fun (i : ι) (n : N) ↦ (m i).1 * n.1 :=
  congr($(mulLeftMap_def' N m) n)

variable {M N} in
theorem map_linearIndependent_left (H : M.LinearDisjoint N) [Module.Flat R N]
    {ι : Type*} {m : ι → M} (hm : LinearIndependent R m) : LinearMap.ker (mulLeftMap N m) = ⊥ := by
  refine LinearMap.ker_eq_bot_of_injective ?_
  let f := mulMap M N ∘ₗ LinearMap.rTensor N (Finsupp.total ι M R m)
  refine (TensorProduct.finsuppScalarLeft.symm.toEquiv.injective_comp f).2 ?_
  rw [LinearIndependent, LinearMap.ker_eq_bot] at hm
  exact H.injective.comp (Module.Flat.preserves_injective_linearMap (M := N) _ hm)

-- TODO: move to suitable file ?
lemma _root_.TensorProduct.coe_congr_right_refl {R : Type*} [CommSemiring R] {M N P : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    [Module R M] [Module R N] [Module R P] (f : M ≃ₗ[R] P) :
    (TensorProduct.congr f (LinearEquiv.refl R N)).toLinearMap = LinearMap.rTensor N f :=
  TensorProduct.ext' fun _ _ ↦ by simp

-- TODO: move to suitable file ?
lemma _root_.TensorProduct.coe_congr_left_refl {R : Type*} [CommSemiring R] {M N Q : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid Q]
    [Module R M] [Module R N] [Module R Q] (g : N ≃ₗ[R] Q) :
    (TensorProduct.congr (LinearEquiv.refl R M) g).toLinearMap = LinearMap.lTensor M g :=
  TensorProduct.ext' fun _ _ ↦ by simp

-- unused
-- TODO: move to suitable file ?
lemma _root_.TensorProduct.congr_symm {R : Type*} [CommSemiring R] {M N P Q : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]
    [Module R M] [Module R N] [Module R P] [Module R Q] (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) :
    (TensorProduct.congr f g).symm = TensorProduct.congr f.symm g.symm :=
  LinearEquiv.toLinearMap_injective <| TensorProduct.ext' fun _ _ ↦ by simp

theorem of_map_linearIndependent_left {ι : Type*} (m : Basis ι R M)
    (H : LinearMap.ker (mulLeftMap N m) = ⊥) : M.LinearDisjoint N := by
  -- need this instance otherwise `LinearMap.ker_eq_bot` does not work
  letI : AddCommGroup (ι →₀ N) := Finsupp.instAddCommGroup
  simp_rw [LinearMap.ker_eq_bot, mulLeftMap, ← Basis.coe_repr_symm,
    ← TensorProduct.coe_congr_right_refl, LinearEquiv.comp_coe, LinearMap.coe_comp,
    LinearEquiv.coe_coe, EquivLike.injective_comp] at H
  exact H

variable {N} in
/-- If `n : ι → N` is a family of elements, then there is an `R`-linear map from `ι →₀ M` to
`S` which maps `{ m_i }` to the sum of `m_i * n_i`. -/
def mulRightMap {ι : Type*} (n : ι → N) : (ι →₀ M) →ₗ[R] S :=
  mulMap M N ∘ₗ LinearMap.lTensor M (Finsupp.total ι N R n) ∘ₗ
    TensorProduct.finsuppScalarRight.symm.toLinearMap

variable {M N} in
@[simp]
theorem mulRightMap_apply_single {ι : Type*} (n : ι → N) (i : ι) (m : M) :
    mulRightMap M n (Finsupp.single i m) = m.1 * (n i).1 := by
  simp [mulRightMap, TensorProduct.finsuppScalarRight_symm_apply_single]

variable {N} in
theorem mulRightMap_def' {ι : Type*} (n : ι → N) : mulRightMap M n =
    Finsupp.lsum ℕ fun (i : ι) ↦ LinearMap.smulRight M.subtype (n i).1 := by
  ext; simp

variable {M N} in
theorem mulRightMap_apply {ι : Type*} (n : ι → N) (m : ι →₀ M) :
    mulRightMap M n m = Finsupp.sum m fun (i : ι) (m : M) ↦ m.1 * (n i).1 :=
  congr($(mulRightMap_def' M n) m)

-- TODO: move to suitable file ?
theorem _root_.Module.Flat.preserves_injective_linearMap'
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N] {M' : Type*} [AddCommGroup M'] [Module R M']
    [Module.Flat R N] (L : M →ₗ[R] M') (hL : Function.Injective L) :
    Function.Injective (LinearMap.lTensor N L) := by
  simp_rw [← LinearMap.comm_comp_rTensor_comp_comm_eq, LinearMap.coe_comp, LinearEquiv.coe_coe,
    EmbeddingLike.comp_injective, EquivLike.injective_comp]
  exact Module.Flat.preserves_injective_linearMap L hL

variable {M N} in
theorem map_linearIndependent_right (H : M.LinearDisjoint N) [Module.Flat R M]
    {ι : Type*} {n : ι → N} (hn : LinearIndependent R n) : LinearMap.ker (mulRightMap M n) = ⊥ := by
  refine LinearMap.ker_eq_bot_of_injective ?_
  let f := mulMap M N ∘ₗ LinearMap.lTensor M (Finsupp.total ι N R n)
  refine (TensorProduct.finsuppScalarRight.symm.toEquiv.injective_comp f).2 ?_
  rw [LinearIndependent, LinearMap.ker_eq_bot] at hn
  exact H.injective.comp (Module.Flat.preserves_injective_linearMap' (N := M) _ hn)

theorem of_map_linearIndependent_right {ι : Type*} (n : Basis ι R N)
    (H : LinearMap.ker (mulRightMap M n) = ⊥) : M.LinearDisjoint N := by
  -- need this instance otherwise `LinearMap.ker_eq_bot` does not work
  letI : AddCommGroup (ι →₀ M) := Finsupp.instAddCommGroup
  simp_rw [LinearMap.ker_eq_bot, mulRightMap, ← Basis.coe_repr_symm,
    ← TensorProduct.coe_congr_left_refl, LinearEquiv.comp_coe, LinearMap.coe_comp,
    LinearEquiv.coe_coe, EquivLike.injective_comp] at H
  exact H

-- TODO: remove once #11598 is merged
theorem _root_.finsuppTensorFinsupp'_symm_single (R ι κ : Type*) [CommSemiring R] (i : ι × κ)
    (r₁ r₂ : R) :
    (finsuppTensorFinsupp' R ι κ).symm (Finsupp.single i (r₁ * r₂)) =
      Finsupp.single i.1 r₁ ⊗ₜ Finsupp.single i.2 r₂ :=
  Prod.casesOn i fun _ _ =>
    (LinearEquiv.symm_apply_eq _).2 (finsuppTensorFinsupp'_single_tmul_single ..).symm

variable {M N} in
theorem map_linearIndependent_mul_of_flat_left (H : M.LinearDisjoint N) [Module.Flat R M]
    {κ ι : Type*} {m : κ → M} {n : ι → N} (hm : LinearIndependent R m)
    (hn : LinearIndependent R n) : LinearIndependent R fun (i : κ × ι) ↦ (m i.1).1 * (n i.2).1 := by
  rw [LinearIndependent, LinearMap.ker_eq_bot] at hm hn ⊢
  let i0 := (finsuppTensorFinsupp' R κ ι).symm
  let i1 := LinearMap.rTensor (ι →₀ R) (Finsupp.total κ M R m)
  let i2 := LinearMap.lTensor M (Finsupp.total ι N R n)
  let i := mulMap M N ∘ₗ i2 ∘ₗ i1 ∘ₗ i0.toLinearMap
  have h1 : Function.Injective i1 := Module.Flat.preserves_injective_linearMap _ hm
  have h2 : Function.Injective i2 := Module.Flat.preserves_injective_linearMap' _ hn
  have h : Function.Injective i := H.injective.comp h2 |>.comp h1 |>.comp i0.injective
  have : i = Finsupp.total (κ × ι) S R fun i ↦ (m i.1).1 * (n i.2).1 := by
    ext x
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Finsupp.lsingle_apply,
      Finsupp.total_single, one_smul, i, i0]
    rw [show (1 : R) = 1 * 1 by simp, finsuppTensorFinsupp'_symm_single]
    simp [i1, i2]
  rwa [this] at h

variable {M N} in
theorem map_linearIndependent_mul_of_flat_right (H : M.LinearDisjoint N) [Module.Flat R N]
    {κ ι : Type*} {m : κ → M} {n : ι → N} (hm : LinearIndependent R m)
    (hn : LinearIndependent R n) : LinearIndependent R fun (i : κ × ι) ↦ (m i.1).1 * (n i.2).1 := by
  rw [LinearIndependent, LinearMap.ker_eq_bot] at hm hn ⊢
  let i0 := (finsuppTensorFinsupp' R κ ι).symm
  let i1 := LinearMap.lTensor (κ →₀ R) (Finsupp.total ι N R n)
  let i2 := LinearMap.rTensor N (Finsupp.total κ M R m)
  let i := mulMap M N ∘ₗ i2 ∘ₗ i1 ∘ₗ i0.toLinearMap
  have h1 : Function.Injective i1 := Module.Flat.preserves_injective_linearMap' _ hn
  have h2 : Function.Injective i2 := Module.Flat.preserves_injective_linearMap _ hm
  have h : Function.Injective i := H.injective.comp h2 |>.comp h1 |>.comp i0.injective
  have : i = Finsupp.total (κ × ι) S R fun i ↦ (m i.1).1 * (n i.2).1 := by
    ext x
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Finsupp.lsingle_apply,
      Finsupp.total_single, one_smul, i, i0]
    rw [show (1 : R) = 1 * 1 by simp, finsuppTensorFinsupp'_symm_single]
    simp [i1, i2]
  rwa [this] at h

variable {M N} in
theorem map_linearIndependent_mul (H : M.LinearDisjoint N) (hf : Module.Flat R M ∨ Module.Flat R N)
    {κ ι : Type*} {m : κ → M} {n : ι → N} (hm : LinearIndependent R m)
    (hn : LinearIndependent R n) : LinearIndependent R fun (i : κ × ι) ↦ (m i.1).1 * (n i.2).1 := by
  rcases hf with _ | _
  · exact H.map_linearIndependent_mul_of_flat_left hm hn
  · exact H.map_linearIndependent_mul_of_flat_right hm hn

theorem of_map_linearIndependent_mul {κ ι : Type*} (m : Basis κ R M) (n : Basis ι R N)
    (H : LinearIndependent R fun (i : κ × ι) ↦ (m i.1).1 * (n i.2).1) : M.LinearDisjoint N := by
  rw [LinearIndependent, LinearMap.ker_eq_bot] at H
  let i0 := (finsuppTensorFinsupp' R κ ι).symm
  let i1 := TensorProduct.congr m.repr n.repr
  let i := mulMap M N ∘ₗ (i0.trans i1.symm).toLinearMap
  have : i = Finsupp.total (κ × ι) S R fun i ↦ (m i.1).1 * (n i.2).1 := by
    ext x
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Finsupp.lsingle_apply,
      LinearEquiv.trans_apply, Finsupp.total_single, one_smul, i, i0]
    rw [show (1 : R) = 1 * 1 by simp, finsuppTensorFinsupp'_symm_single]
    simp [i1]
  simp_rw [← this, i, LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.injective_comp] at H
  exact H

end LinearDisjoint

end Ring

end Submodule

-- We skip `Subalgebra.LinearDisjoint` since it seems less useful (???)

namespace IntermediateField

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]

variable (A B : IntermediateField F E)

/-- Two intermediate fields `A` and `B` of `E / F` are linearly disjoint, if they are
linearly disjoint as submodules of `E`. -/
protected def LinearDisjoint : Prop :=
  (Subalgebra.toSubmodule A.toSubalgebra).LinearDisjoint (Subalgebra.toSubmodule B.toSubalgebra)

-- theorem linearDisjoint_iff :
--     A.LinearDisjoint B ↔ ∀ {a : Set A}, LinearIndependent F (fun x : a ↦ x.1) →
--       LinearIndependent B (fun x : a ↦ x.1.1) := Iff.rfl

-- /-- In the definition of linearly disjoint, linearly independent subset of `A` can be replaced
-- by its embedding into `E`. -/
-- theorem linearDisjoint_iff' :
--     A.LinearDisjoint B ↔ ∀ {a : Set A}, LinearIndependent F (fun x : a ↦ x.1.1) →
--       LinearIndependent B (fun x : a ↦ x.1.1) := by
--   have h {a : Set A} : LinearIndependent F (fun x : a ↦ x.1) ↔
--       LinearIndependent F (fun x : a ↦ x.1.1) :=
--     ⟨fun H ↦ H.map' A.val.toLinearMap (LinearMap.ker_eq_bot_of_injective A.val.injective),
--       fun H ↦ H.of_comp A.val.toLinearMap⟩
--   simp_rw [linearDisjoint_iff, h]

-- variable {A B}

-- /-- If `A` and `B` are linearly disjoint, then any `F`-linearly independent family on `A` remains
-- linearly independent over `B`. -/
-- theorem LinearDisjoint.linearIndependent_map (H : A.LinearDisjoint B)
--     {ιA : Type*} {vA : ιA → A} (hA : LinearIndependent F vA) :
--     LinearIndependent B (A.val ∘ vA) :=
--   (H hA.coe_range).comp (Set.rangeFactorization vA)
--     (fun _ _ h ↦ hA.injective (congr_arg Subtype.val h))

-- /-- If `A` and `B` are linearly disjoint, then for a family on `A` which is
-- `F`-linearly independent when embedded into `E`, it remains linearly independent over `B`. -/
-- theorem LinearDisjoint.linearIndependent_map' (H : A.LinearDisjoint B)
--     {ιA : Type*} {vA : ιA → A} (hA : LinearIndependent F (A.val ∘ vA)) :
--     LinearIndependent B (A.val ∘ vA) :=
--   H.linearIndependent_map (hA.of_comp A.val.toLinearMap)

-- private lemma test1 {ιA ιB : Type*} (vA : ιA → A) (vB : ιB → B)
--     (l : ιA × ιB →₀ F) (L : ιA →₀ B)
--     {h0 : Finsupp.total ιB B F vB 0 = 0}
--     (h : L = l.curry.mapRange (Finsupp.total ιB B F vB) h0) :
--     Finsupp.total (ιA × ιB) E F (fun x : ιA × ιB ↦ (vA x.1).1 * (vB x.2).1) l =
--       Finsupp.total ιA E B (fun x : ιA ↦ (vA x).1) L := by
--   let g (x : ιA) (y : ιB) (z : F) := z • ((vA x).1 * (vB y).1)
--   rw [Finsupp.total_apply, Finsupp.total_apply, h,
--     Finsupp.sum_mapRange_index (by exact fun _ ↦ zero_smul B _),
--     ← l.sum_curry_index g (fun _ _ ↦ zero_smul F _) (fun _ _ _ _ ↦ add_smul _ _ _),
--     Finsupp.sum]
--   congr
--   ext x
--   simp_rw [Finsupp.total_apply, Finsupp.sum, Finset.sum_smul]
--   congr
--   ext y
--   simp_rw [Algebra.smul_def, map_mul, mul_comm (vA x).1 (vB y).1, ← mul_assoc]
--   rfl

-- variable (E) in
-- private lemma _root_.LinearIndependent.mapRange {a b : Type*} {v : a → b →₀ F}
--     (H : LinearIndependent F v) :
--     LinearIndependent E fun x : a ↦ (v x).mapRange (algebraMap F E) (map_zero _) := by
--   let f := Finsupp.total a _ F v
--   obtain ⟨g, hg : g.comp f =  _⟩ := LinearMap.exists_leftInverse_of_injective _ H
--   let f' := f.baseChange E
--   let g' := g.baseChange E
--   have hg' : g'.comp f' = LinearMap.id := by
--     convert (LinearMap.baseChange_comp (A := E) f g).symm
--     rw [hg]
--     refine TensorProduct.AlgebraTensorModule.ext fun x y ↦ ?_
--     rw [LinearMap.baseChange_tmul]
--     rfl
--   let ba := Algebra.TensorProduct.basis E
--     (Basis.ofRepr (LinearEquiv.refl (R := F) (M := a →₀ F)))
--   let bb := Algebra.TensorProduct.basis E
--     (Basis.ofRepr (LinearEquiv.refl (R := F) (M := b →₀ F)))
--   let f'' := (bb.repr.toLinearMap.comp f').comp ba.repr.symm.toLinearMap
--   let g'' := (ba.repr.toLinearMap.comp g').comp bb.repr.symm.toLinearMap
--   have hg'' : g''.comp f'' = LinearMap.id := by
--     change ba.repr ∘ₗ (g' ∘ₗ (bb.repr.symm.toLinearMap ∘ₗ bb.repr.toLinearMap) ∘ₗ f') ∘ₗ
--         ba.repr.symm.toLinearMap = LinearMap.id
--     rw [← LinearEquiv.coe_trans, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap,
--       LinearMap.id_comp, hg', LinearMap.id_comp, ← LinearEquiv.coe_trans,
--       LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap]
--   rw [LinearIndependent]
--   convert LinearMap.ker_eq_bot_of_inverse hg''
--   refine (Basis.ofRepr (LinearEquiv.refl (R := E) (M := a →₀ E))).ext fun x ↦ ?_
--   simp only [Basis.coe_ofRepr, LinearEquiv.refl_symm, LinearEquiv.refl_apply,
--     Finsupp.total_single,
--     one_smul, Basis.coe_repr_symm, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
--     Algebra.TensorProduct.basis_apply, LinearMap.baseChange_tmul,
--     Algebra.TensorProduct.basis_repr_tmul]

-- /-- If there exists an `F`-basis of `A` which remains linearly independent over `B`, then
-- `A` and `B` are linearly disjoint. -/
-- theorem LinearDisjoint.of_basis_map {ιA : Type*} (bA : Basis ιA F A)
--     (H : LinearIndependent B (A.val ∘ bA)) : A.LinearDisjoint B := fun a ha ↦ by
--   replace ha := ha.map' bA.repr.toLinearMap (LinearMap.ker_eq_bot_of_injective bA.repr.injective)
--     |>.mapRange B
--   letI : Algebra B B := Algebra.id B
--   letI : Module B B := Algebra.toModule
--   letI : Module B (ιA →₀ B) := Finsupp.module ιA B
--   rw [linearIndependent_iff] at H ha ⊢
--   intro l hl
--   let L := Finsupp.total a (ιA →₀ B) B
--     (fun x ↦ Finsupp.mapRange (algebraMap F B) (map_zero _) (bA.repr x.1)) l
--   have key : Finsupp.total a E B (fun x ↦ x.1.1) l = Finsupp.total ιA E B (A.val ∘ bA) L := by
--     simp_rw [Finsupp.total_apply]
--     rw [Finsupp.sum_sum_index (fun _ ↦ by exact zero_smul B _)
--       (fun _ _ _ ↦ by exact add_smul _ _ _)]
--     congr
--     ext x y
--     rw [Finsupp.sum_smul_index fun _ ↦ by exact zero_smul _ _,
--       Finsupp.sum_mapRange_index fun _ ↦ by rw [mul_zero, zero_smul], Finsupp.sum]
--     have (z : ιA) : (y * (algebraMap F B) (bA.repr x z)) • (A.val ∘ bA) z =
--         y • A.val (bA.repr x z • bA z) := by
--       simp_rw [Algebra.smul_def, map_mul (algebraMap B E), map_mul A.val, ← mul_assoc]
--       rfl
--     simp_rw [this]
--     rw [← Finset.smul_sum, ← map_sum]
--     congr
--     change _ = Finsupp.sum (bA.repr x) fun a b ↦ b • bA a
--     rw [← Finsupp.total_apply, bA.total_repr]
--   exact ha l (H L (key ▸ hl))

-- /-- If `A` and `B` are linearly disjoint, then for any `F`-linearly independent families
-- `{ u_i }`, `{ v_j }` of `A`, `B`, the products `{ u_i * v_j }`
-- are linearly independent over `F`. -/
-- theorem LinearDisjoint.linearIndependent_mul (H : A.LinearDisjoint B)
--     {ιA ιB : Type*} {vA : ιA → A} {vB : ιB → B}
--     (hA : LinearIndependent F vA)
--     (hB : LinearIndependent F vB) :
--     LinearIndependent F (fun x : ιA × ιB ↦ (vA x.1).1 * (vB x.2).1) := by
--   replace H := H.linearIndependent_map hA
--   rw [linearIndependent_iff] at H hB ⊢
--   intro l hl
--   let L := l.curry.mapRange (Finsupp.total ιB B F vB) (map_zero _)
--   ext ⟨x, y⟩
--   have := hB (l.curry x) <| by simpa only [Finsupp.onFinset_apply,
--     Finsupp.zero_apply] using congr($(H _ (test1 vA vB l L rfl ▸ hl)) x)
--   rw [Finsupp.zero_apply, ← Finsupp.curry_apply, this, Finsupp.zero_apply]

-- /-- If there are `F`-bases `{ u_i }`, `{ v_j }` of `A`, `B`, such that the products
-- `{ u_i * v_j }` are linearly independent over `F`, then `A` and `B` are linearly disjoint. -/
-- theorem LinearDisjoint.of_basis_mul {ιA ιB : Type*} (bA : Basis ιA F A) (bB : Basis ιB F B)
--     (H : LinearIndependent F (fun x : ιA × ιB ↦ (bA x.1).1 * (bB x.2).1)) :
--     A.LinearDisjoint B := by
--   refine of_basis_map bA ?_
--   rw [linearIndependent_iff] at H ⊢
--   intro l hl
--   have h0 := bB.repr.map_zero
--   let L := Finsupp.finsuppProdEquiv.symm (l.mapRange bB.repr h0)
--   have key : l = (Finsupp.finsuppProdEquiv L).mapRange
--       (Finsupp.total ιB B F bB) (map_zero _) := by
--     rw [Finsupp.finsuppProdEquiv.apply_symm_apply,
--       ← Finsupp.mapRange_comp _ rfl _ h0 (by rw [Function.comp_apply, h0]; rfl)]
--     convert l.mapRange_id.symm
--     ext y
--     exact congr_arg Subtype.val (bB.total_repr y)
--   have : _ = Finsupp.total ιA E B (A.val ∘ bA) l := test1 bA bB L l key
--   rwa [H L (this.symm ▸ hl), show Finsupp.finsuppProdEquiv 0 = 0 from rfl,
--     Finsupp.mapRange_zero] at key

-- private lemma test3' (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]
--     (x : Basis.ofVectorSpaceIndex K V) : (Basis.ofVectorSpace K V) x = x.1 :=
--   Basis.extend_apply_self _ _

-- private lemma test3 (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V] :
--     LinearIndependent K (fun x : Basis.ofVectorSpaceIndex K V ↦ x.1) := by
--   convert (Basis.ofVectorSpace K V).linearIndependent
--   ext _
--   exact (test3' K V _).symm

-- /-- `A` and `B` are linearly disjoint if and only if for any `F`-linearly independent subsets
-- `{ u_i }`, `{ v_j }` of `A`, `B`, the products `{ u_i * v_j }`
-- are linearly independent over `F`. -/
-- theorem linearDisjoint_iff_linearIndependent_mul_of_set :
--     A.LinearDisjoint B ↔ ∀ {a : Set A} {b : Set B}, LinearIndependent F (fun x : a ↦ x.1) →
--       LinearIndependent F (fun y : b ↦ y.1) →
--       LinearIndependent F (fun x : a × b ↦ x.1.1.1 * x.2.1.1) := by
--   refine ⟨fun H _ _ hA hB ↦ H.linearIndependent_mul hA hB,
--     fun H ↦ LinearDisjoint.of_basis_mul (Basis.ofVectorSpace F A) (Basis.ofVectorSpace F B) ?_⟩
--   simpa only [test3'] using H (test3 F A) (test3 F B)

-- /-- Linearly disjoint is symmetric. -/
-- theorem LinearDisjoint.symm (H : A.LinearDisjoint B) : B.LinearDisjoint A := by
--   rw [linearDisjoint_iff_linearIndependent_mul_of_set] at H ⊢
--   intro a b ha hb
--   rw [← linearIndependent_equiv (Equiv.prodComm b a)]
--   convert H hb ha
--   exact mul_comm _ _

-- /-- Linearly disjoint is symmetric. -/
-- theorem linearDisjoint_symm : A.LinearDisjoint B ↔ B.LinearDisjoint A :=
--   ⟨LinearDisjoint.symm, LinearDisjoint.symm⟩

-- variable (A) in
-- theorem LinearDisjoint.of_bot_right : A.LinearDisjoint ⊥ := fun a ha ↦
--   ha.map_of_injective_injective (M' := E) (botEquiv F E) A.val
--     (fun _ _ ↦ (botEquiv F E).injective (by rwa [map_zero]))
--     (fun _ _ ↦ A.val.injective (by rwa [map_zero]))
--     (fun r _ ↦ by obtain ⟨x, h⟩ := r.2; simp_rw [Algebra.smul_def,
--       show r = algebraMap F _ x from SetCoe.ext h.symm, botEquiv_def]; rfl)

-- variable (B) in
-- theorem LinearDisjoint.of_bot_left : (⊥ : IntermediateField F E).LinearDisjoint B :=
--   LinearDisjoint.of_bot_right B |>.symm

-- theorem LinearDisjoint.of_inclusion_right {B' : IntermediateField F E} (H : A.LinearDisjoint B)
--     (h : B' ≤ B) : A.LinearDisjoint B' := fun a ha ↦
--   (H ha).map_of_injective_injective (M' := E) (inclusion h)
--     (AddMonoidHom.id E) (fun _ _ ↦ (inclusion h).injective (by rwa [map_zero]))
--     (fun _ ↦ id) (fun _ _ ↦ rfl)

-- theorem LinearDisjoint.of_inclusion_left {A' : IntermediateField F E} (H : A.LinearDisjoint B)
--     (h : A' ≤ A) : A'.LinearDisjoint B := H.symm.of_inclusion_right h |>.symm

-- /-- If `A` and `B` are linearly disjoint, `A'` and `B'` are contained in `A` and `B`,
-- respectively, then `A'` and `B'` are also linearly disjoint. -/
-- theorem LinearDisjoint.of_inclusion {A' B' : IntermediateField F E} (H : A.LinearDisjoint B)
--     (hA : A' ≤ A) (hB : B' ≤ B) : A'.LinearDisjoint B' :=
--   H.of_inclusion_left hA |>.of_inclusion_right hB

-- /-- If `A` and `B` are linearly disjoint over `F`, then their intersection is equal to `F`. -/
-- theorem LinearDisjoint.inf_eq_bot (H : A.LinearDisjoint B) :
--     A ⊓ B = ⊥ := bot_unique fun x hx ↦ by
--   have hxA := inf_le_left (a := A) (b := B) hx
--   replace H := not_imp_not.2 (H.linearIndependent_map (vA := ![1, ⟨x, hxA⟩]))
--   have : A.val ∘ ![1, ⟨x, hxA⟩] = ![1, x] := by ext i; fin_cases i <;> rfl
--   simp_rw [this, LinearIndependent.pair_iff, not_forall] at H
--   obtain ⟨s, t, h1, h2⟩ := H ⟨⟨-x, neg_mem <| inf_le_right (a := A) (b := B) hx⟩, 1,
--     by rw [one_smul, Algebra.smul_def, mul_one]; exact add_left_neg x, by simp⟩
--   apply_fun algebraMap A E at h1
--   simp_rw [Algebra.smul_def, mul_one, map_add, map_mul, map_zero] at h1
--   change algebraMap F E s + algebraMap F E t * x = 0 at h1
--   have : algebraMap F E t ≠ 0 := (_root_.map_ne_zero _).2 fun h ↦ h2
--     ⟨(algebraMap F E).injective (by rw [map_zero, ← h1, h, map_zero, zero_mul, add_zero]), h⟩
--   use -s / t
--   change algebraMap F E (-s / t) = _
--   rwa [map_div₀, map_neg, div_eq_iff this, neg_eq_iff_add_eq_zero, mul_comm]

-- /-- If `A` and `A` itself are linearly disjoint over `F`, then it is equal to `F`. -/
-- theorem LinearDisjoint.eq_bot_of_self (H : A.LinearDisjoint A) : A = ⊥ :=
--   inf_of_le_left (le_refl A) ▸ H.inf_eq_bot

-- -- /-- If `A` and `B` have coprime degree over `F`, then they are linearly disjoint. -/
-- -- theorem LinearDisjoint.of_finrank_coprime (H : (finrank F A).Coprime (finrank F B)) :
-- --     A.LinearDisjoint B := by
-- --   sorry

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
