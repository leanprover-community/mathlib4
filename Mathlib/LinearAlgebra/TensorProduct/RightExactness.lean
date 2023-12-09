/-
Copyright (c) 2023 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambetr-Loir
-/

import Mathlib.Algebra.Exact
import Mathlib.RingTheory.TensorProduct

/-! # Right-exactness properties of tensor product

* `TensorProduct.rTensor.surjective` asserts that one tensors
  a surjective map on the right, one still gets a surjective linear map.

* `TensorProduct.lTensor.surjective` asserts that one tensors
  a surjective map on the left, one still gets a surjective linear map.

* `TensorProduct.rTensor_exact` says that when one tensors a short exact
  sequence on the right, one still gets a short exact sequence
  (right-exactness of `TensorProduct.rTensor`),
  and `rTensor.equiv` gives the LinearEquiv that follows from this
  combined with `TensorProduct.rTensor.surjective`.

* `TensorProduct.lTensor_exact` says that when one tensors a short exact
  sequence on the left, one still gets a short exact sequence
  (right-exactness of `TensorProduct.rTensor`)
  and `lTensor.equiv` gives the LinearEquiv that follows from this
  combined with `TensorProduct.lTensor.surjective`.

* For `N : Submodule R M`, `LinearMap.exact_subtype_mkQ N` says that
  the inclusion of the submodule and the quotient map form an exact pair,
  and `lTensor_mkQ` compute `ker (lTensor Q (N.mkQ))` and similarly for `rTensor_mkQ`

* `TensorProduct.map_ker` computes the kernel of `TensorProduct.map f g'`
  in the presence of two short exact sequences.

The proofs are those of [bourbaki1989] (chap. 2, §3, n°6)

## TODO

* Treat the noncommutative case

* Treat the case of modules over semirings
  (For a possible definition of an exact sequence of commutative semigroups, see
  [Grillet-1969b], Pierre-Antoine Grillet,
  *The tensor product of commutative semigroups*,
  Trans. Amer. Math. Soc. 138 (1969), 281-293, doi:10.1090/S0002-9947-1969-0237688-1 .)

* Treat algebras (further PR)
-/

suppress_compilation

section Modules

open TensorProduct LinearMap

section Semiring

variable {R : Type*} [CommSemiring R] {M N P Q: Type*}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommGroup P] [AddCommMonoid Q]
    [Module R M] [Module R N] [Module R P] [Module R Q]
    {f : M →ₗ[R] N} (g : N →ₗ[R] P)

lemma le_comap_range_lTensor (q : Q) :
    LinearMap.range g ≤ (LinearMap.range (lTensor Q g)).comap (TensorProduct.mk R Q P q) := by
  rintro x ⟨n, rfl⟩
  exact ⟨q ⊗ₜ[R] n, rfl⟩

lemma le_comap_range_rTensor (q : Q) :
    LinearMap.range g ≤ (LinearMap.range (rTensor Q g)).comap
      ((TensorProduct.mk R P Q).flip q) := by
  rintro x ⟨n, rfl⟩
  exact ⟨n ⊗ₜ[R] q, rfl⟩

variable (Q) {g}

/-- If `g` is surjective, then `lTensor Q g` is surjective -/
theorem lTensor.surjective (hg : Function.Surjective g) :
    Function.Surjective (lTensor Q g) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul q p =>
    obtain ⟨n, rfl⟩ := hg p
    exact ⟨q ⊗ₜ[R] n, rfl⟩
  | add x y hx hy =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, map_add _ _ _⟩

/-- If `g` is surjective, then `rTensor Q g` is surjective -/
theorem rTensor.surjective (hg : Function.Surjective g) :
    Function.Surjective (rTensor Q g) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul p q =>
    obtain ⟨n, rfl⟩ := hg p
    exact ⟨n ⊗ₜ[R] q, rfl⟩
  | add x y hx hy =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, map_add _ _ _⟩

end Semiring

variable {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]

open Function LinearMap

lemma LinearMap.exact_subtype_mkQ (Q : Submodule R N) :
    Exact (Submodule.subtype Q) (Submodule.mkQ Q) := by
  rw [exact_iff, Submodule.ker_mkQ, Submodule.range_subtype Q]

lemma LinearMap.exact_map_mkQ_range (f : M →ₗ[R] N) :
    Exact f (Submodule.mkQ (range f)) :=
  exact_iff.mpr <| Submodule.ker_mkQ _

lemma LinearMap.exact_subtype_ker_map (g : N →ₗ[R] P) :
    Exact (Submodule.subtype (ker g)) g :=
  exact_iff.mpr <| (Submodule.range_subtype _).symm

variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (Q : Type*) [AddCommGroup Q] [Module R Q]
    (hfg : Exact f g) (hg : Function.Surjective g)

/-- The direct map in `lTensor.equiv` -/
def lTensor.toFun :
    Q ⊗[R] N ⧸ LinearMap.range (lTensor Q f) →ₗ[R] Q ⊗[R] P :=
  Submodule.liftQ _ (lTensor Q g) <| by
    rw [LinearMap.range_le_iff_comap, ← LinearMap.ker_comp,
      ← lTensor_comp, hfg.linearMap_comp_eq_zero, lTensor_zero, ker_zero]

/-- The inverse map in `lTensor.equiv_of_rightInverse` (computably, given a right inverse)-/
def lTensor.inverse_of_rightInverse {h : P → N} (hgh : Function.RightInverse h g) :
    Q ⊗[R] P →ₗ[R] Q ⊗[R] N ⧸ LinearMap.range (lTensor Q f) :=
  TensorProduct.lift <| LinearMap.flip <| {
    toFun := fun p ↦ Submodule.mkQ _ ∘ₗ ((TensorProduct.mk R _ _).flip (h p))
    map_add' := fun p p' => LinearMap.ext <| fun q => (Submodule.Quotient.eq _).mpr <| by
      change q ⊗ₜ[R] (h (p + p')) - (q ⊗ₜ[R] (h p) + q ⊗ₜ[R] (h p')) ∈ range (lTensor Q f)
      rw [← TensorProduct.tmul_add, ← TensorProduct.tmul_sub]
      apply le_comap_range_lTensor f
      rw [exact_iff] at hfg
      simp only [← hfg, mem_ker, map_sub, map_add, hgh _, sub_self]
    map_smul' := fun r p => LinearMap.ext <| fun q => (Submodule.Quotient.eq _).mpr <| by
      change q ⊗ₜ[R] (h (r • p)) - r • q ⊗ₜ[R] (h p) ∈ range (lTensor Q f)
      rw [← TensorProduct.tmul_smul, ← TensorProduct.tmul_sub]
      apply le_comap_range_lTensor f
      rw [exact_iff] at hfg
      simp only [← hfg, mem_ker, map_sub, map_smul, hgh _, sub_self] }

lemma lTensor.inverse_of_rightInverse_apply
    {h : P → N} (hgh : Function.RightInverse h g) (y : Q ⊗[R] N) :
    (lTensor.inverse_of_rightInverse Q hfg hgh) ((lTensor Q g) y) =
      Submodule.Quotient.mk (p := (LinearMap.range (lTensor Q f))) y := by
  simp only [← LinearMap.comp_apply, ← Submodule.mkQ_apply]
  rw [exact_iff] at hfg
  apply LinearMap.congr_fun
  apply TensorProduct.ext'
  intro n q
  simp? [lTensor.inverse_of_rightInverse] says
    simp only [inverse_of_rightInverse, coe_comp, Function.comp_apply, lTensor_tmul,
      lift.tmul, flip_apply, coe_mk, AddHom.coe_mk, mk_apply, Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq, ← TensorProduct.tmul_sub]
  apply le_comap_range_lTensor f n
  rw [← hfg, mem_ker, map_sub, sub_eq_zero, hgh]

lemma lTensor.inverse_of_rightInverse_comp_lTensor
    {h : P → N} (hgh : Function.RightInverse h g) :
    (lTensor.inverse_of_rightInverse Q hfg hgh).comp (lTensor Q g) =
      Submodule.mkQ (p := LinearMap.range (lTensor Q f)) := by
  rw [LinearMap.ext_iff]
  intro y
  simp only [coe_comp, Function.comp_apply, Submodule.mkQ_apply,
    lTensor.inverse_of_rightInverse_apply]

/-- The inverse map in `lTensor.equiv` -/
noncomputable
def lTensor.inverse :
    Q ⊗[R] P →ₗ[R] Q ⊗[R] N ⧸ LinearMap.range (lTensor Q f) :=
  lTensor.inverse_of_rightInverse Q hfg (Function.rightInverse_surjInv hg)

lemma lTensor.inverse_apply (y : Q ⊗[R] N) :
    (lTensor.inverse Q hfg hg) ((lTensor Q g) y) =
      Submodule.Quotient.mk (p := (LinearMap.range (lTensor Q f))) y := by
  rw [lTensor.inverse, lTensor.inverse_of_rightInverse_apply]

lemma lTensor.inverse_comp_lTensor :
    (lTensor.inverse Q hfg hg).comp (lTensor Q g) =
      Submodule.mkQ (p := LinearMap.range (lTensor Q f)) := by
  rw [lTensor.inverse, lTensor.inverse_of_rightInverse_comp_lTensor]

/-- For a surjective `f : N →ₗ[R] P`,
  the natural equivalence between `Q ⊗ N ⧸ (image of ker f)` to `Q ⊗ P`
  (computably, given a right inverse) -/
def lTensor.linearEquiv_of_rightInverse {h : P → N} (hgh : Function.RightInverse h g) :
    ((Q ⊗[R] N) ⧸ (LinearMap.range (lTensor Q f))) ≃ₗ[R] (Q ⊗[R] P) := {
  toLinearMap := lTensor.toFun Q hfg
  invFun    := lTensor.inverse_of_rightInverse Q hfg hgh
  left_inv  := fun y ↦ by
    simp only [lTensor.toFun, AddHom.toFun_eq_coe, coe_toAddHom]
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
    simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, lTensor.inverse_of_rightInverse_apply]
  right_inv := fun z ↦ by
    simp only [AddHom.toFun_eq_coe, coe_toAddHom]
    obtain ⟨y, rfl⟩ := lTensor.surjective Q (hgh.surjective) z
    rw [lTensor.inverse_of_rightInverse_apply]
    simp only [lTensor.toFun, Submodule.liftQ_apply] }

/-- For a surjective `f : N →ₗ[R] P`,
  the natural equivalence between `Q ⊗ N ⧸ (image of ker f)` to `Q ⊗ P` -/
noncomputable def lTensor.equiv :
    ((Q ⊗[R] N) ⧸ (LinearMap.range (lTensor Q f))) ≃ₗ[R] (Q ⊗[R] P) :=
  lTensor.linearEquiv_of_rightInverse Q hfg (Function.rightInverse_surjInv hg)

/-- Tensoring an exact pair on the left gives an exact pair -/
theorem lTensor_exact : Exact (lTensor Q f) (lTensor Q g) := by
  rw [exact_iff, ← Submodule.ker_mkQ (p := range (lTensor Q f)),
    ← lTensor.inverse_comp_lTensor Q hfg hg]
  apply symm
  apply LinearMap.ker_comp_of_ker_eq_bot
  rw [LinearMap.ker_eq_bot]
  exact (lTensor.equiv Q hfg hg).symm.injective

/-- Right-exactness of tensor product -/
lemma lTensor_mkQ (N : Submodule R M) :
    ker (lTensor Q (N.mkQ)) = range (lTensor Q N.subtype) := by
  rw [← exact_iff]
  exact lTensor_exact Q (LinearMap.exact_subtype_mkQ N) (Submodule.mkQ_surjective N)

/-- The direct map in `rTensor.equiv` -/
def rTensor.toFun :
    N ⊗[R] Q ⧸ range (rTensor Q f) →ₗ[R] P ⊗[R] Q :=
  Submodule.liftQ _ (rTensor Q g) <| by
    rw [range_le_iff_comap, ← ker_comp, ← rTensor_comp,
      hfg.linearMap_comp_eq_zero, rTensor_zero, ker_zero]

/-- The inverse map in `rTensor.equiv_of_rightInverse` (computably, given a right inverse) -/
def rTensor.inverse_of_rightInverse {h : P → N} (hgh : Function.RightInverse h g) :
    P ⊗[R] Q →ₗ[R] N ⊗[R] Q ⧸ LinearMap.range (rTensor Q f) :=
  TensorProduct.lift  {
    toFun := fun p ↦ Submodule.mkQ _ ∘ₗ TensorProduct.mk R _ _ (h p)
    map_add' := fun p p' => LinearMap.ext <| fun q => (Submodule.Quotient.eq _).mpr <| by
      change h (p + p') ⊗ₜ[R] q - (h p ⊗ₜ[R] q + h p' ⊗ₜ[R] q) ∈ range (rTensor Q f)
      rw [← TensorProduct.add_tmul, ← TensorProduct.sub_tmul]
      apply le_comap_range_rTensor f
      rw [exact_iff] at hfg
      simp only [← hfg, mem_ker, map_sub, map_add, hgh _, sub_self]
    map_smul' := fun r p => LinearMap.ext <| fun q => (Submodule.Quotient.eq _).mpr <| by
      change h (r • p) ⊗ₜ[R] q - r • h p ⊗ₜ[R] q ∈ range (rTensor Q f)
      rw [TensorProduct.smul_tmul', ← TensorProduct.sub_tmul]
      apply le_comap_range_rTensor f
      rw [exact_iff] at hfg
      simp only [← hfg, mem_ker, map_sub, map_smul, hgh _, sub_self] }

lemma rTensor.inverse_of_rightInverse_apply
    {h : P → N} (hgh : Function.RightInverse h g) (y : N ⊗[R] Q) :
    (rTensor.inverse_of_rightInverse Q hfg hgh) ((rTensor Q g) y) =
      Submodule.Quotient.mk (p := LinearMap.range (rTensor Q f)) y := by
  simp only [← LinearMap.comp_apply, ← Submodule.mkQ_apply]
  rw [exact_iff] at hfg
  apply LinearMap.congr_fun
  apply TensorProduct.ext'
  intro n q
  simp? [rTensor.inverse_of_rightInverse] says
    simp only [inverse_of_rightInverse, coe_comp, Function.comp_apply, rTensor_tmul,
      lift.tmul, coe_mk, AddHom.coe_mk, mk_apply, Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq, ← TensorProduct.sub_tmul]
  apply le_comap_range_rTensor f
  rw [← hfg, mem_ker, map_sub, sub_eq_zero, hgh]

lemma rTensor.inverse_of_rightInverse_comp_rTensor
    {h : P → N} (hgh : Function.RightInverse h g) :
    (rTensor.inverse_of_rightInverse Q hfg hgh).comp (rTensor Q g) =
      Submodule.mkQ (p := LinearMap.range (rTensor Q f)) := by
  rw [LinearMap.ext_iff]
  intro y
  simp only [coe_comp, Function.comp_apply, Submodule.mkQ_apply,
    rTensor.inverse_of_rightInverse_apply]

/-- The inverse map in `rTensor.equiv` -/
noncomputable
def rTensor.inverse :
    P ⊗[R] Q →ₗ[R] N ⊗[R] Q ⧸ LinearMap.range (rTensor Q f) :=
  rTensor.inverse_of_rightInverse Q hfg (Function.rightInverse_surjInv hg)

lemma rTensor.inverse_apply (y : N ⊗[R] Q) :
    (rTensor.inverse Q hfg hg) ((rTensor Q g) y) =
      Submodule.Quotient.mk (p := LinearMap.range (rTensor Q f)) y := by
  rw [rTensor.inverse, rTensor.inverse_of_rightInverse_apply]

lemma rTensor.inverse_comp_rTensor :
    (rTensor.inverse Q hfg hg).comp (rTensor Q g) =
      Submodule.mkQ (p := LinearMap.range (rTensor Q f)) := by
  rw [rTensor.inverse, rTensor.inverse_of_rightInverse_comp_rTensor]

/-- For a surjective `f : N →ₗ[R] P`,
  the natural equivalence between `N ⊗[R] Q ⧸ (range (rTensor Q f))` and `P ⊗[R] Q`
  (computably, given a right inverse) -/
def rTensor.linearEquiv_of_rightInverse {h : P → N} (hgh : Function.RightInverse h g) :
    ((N ⊗[R] Q) ⧸ (range (rTensor Q f))) ≃ₗ[R] (P ⊗[R] Q) := {
  toLinearMap := rTensor.toFun Q hfg
  invFun      := rTensor.inverse_of_rightInverse Q hfg hgh
  left_inv    := fun y ↦ by
    simp only [rTensor.toFun, AddHom.toFun_eq_coe, coe_toAddHom]
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
    simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, rTensor.inverse_of_rightInverse_apply]
  right_inv   := fun z ↦ by
    simp only [AddHom.toFun_eq_coe, coe_toAddHom]
    obtain ⟨y, rfl⟩ := rTensor.surjective Q hgh.surjective z
    rw [rTensor.inverse_of_rightInverse_apply]
    simp only [rTensor.toFun, Submodule.liftQ_apply] }

/-- For a surjective `f : N →ₗ[R] P`,
  the natural equivalence between `N ⊗[R] Q ⧸ (range (rTensor Q f))` and `P ⊗[R] Q` -/
noncomputable def rTensor.equiv :
    ((N ⊗[R] Q) ⧸ (LinearMap.range (rTensor Q f))) ≃ₗ[R] (P ⊗[R] Q) :=
  rTensor.linearEquiv_of_rightInverse Q hfg (Function.rightInverse_surjInv hg)

/-- Tensoring an exact pair on the right gives an exact pair -/
theorem rTensor_exact : Exact (rTensor Q f) (rTensor Q g) := by
  rw [exact_iff, ← Submodule.ker_mkQ (p := range (rTensor Q f)),
    ← rTensor.inverse_comp_rTensor Q hfg hg]
  apply symm
  apply ker_comp_of_ker_eq_bot
  rw [ker_eq_bot]
  exact (rTensor.equiv Q hfg hg).symm.injective

/-- Right-exactness of tensor product (`rTensor`) -/
lemma rTensor_mkQ (N : Submodule R M) :
    ker (rTensor Q (N.mkQ)) = range (rTensor Q N.subtype) := by
  rw [← exact_iff]
  exact rTensor_exact Q (LinearMap.exact_subtype_mkQ N) (Submodule.mkQ_surjective N)

variable {M' N' P' : Type*}
    [AddCommGroup M'] [AddCommGroup N'] [AddCommGroup P']
    [Module R M'] [Module R N'] [Module R P']
    {f' : M' →ₗ[R] N'} {g' : N' →ₗ[R] P'}
    (hfg' : Exact f' g') (hg' : Function.Surjective g')

theorem TensorProduct.map_surjective : Function.Surjective (TensorProduct.map g g') := by
  rw [← lTensor_comp_rTensor, coe_comp]
  exact Function.Surjective.comp (lTensor.surjective _ hg') (rTensor.surjective _ hg)

/-- Kernel of a product map (right-exactness of tensor product) -/
theorem TensorProduct.map_ker :
    ker (TensorProduct.map g g') = range (lTensor N f') ⊔ range (rTensor N' f) := by
  rw [← lTensor_comp_rTensor]
  rw [ker_comp]
  rw [← Exact.linearMap_ker_eq (rTensor_exact N' hfg hg)]
  rw [← Submodule.comap_map_eq]
  apply congr_arg₂ _ rfl
  rw [range_eq_map, ← Submodule.map_comp, rTensor_comp_lTensor,
    Submodule.map_top]
  rw [← lTensor_comp_rTensor, range_eq_map, Submodule.map_comp,
    Submodule.map_top]
  rw [range_eq_top.mpr (rTensor.surjective M' hg), Submodule.map_top]
  rw [Exact.linearMap_ker_eq (lTensor_exact P hfg' hg')]

end Modules
