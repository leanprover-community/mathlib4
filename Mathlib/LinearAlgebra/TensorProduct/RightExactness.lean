/-
Copyright (c) 2023 Antoine Chambetr-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambetr-Loir
-/

import Mathlib.LinearAlgebra.TensorProduct
import Mathlib.LinearAlgebra.Quotient

/-! # Right exactness properties of tensor product

* For linear maps `f : M →ₗ[R] N`  and `g : N →ₗ[R] P`, `Exact f g` says that `range f = ker g``

* `TensorProduct.rTensor_exact` says that one can tensor a short exact sequence on the right

* `TensorProduct.lTensor_exact` says that one can tensor a short exact sequence on the left

* For `N : Submodule R M`, `LinearMap.exact_subtype_mkQ N` says that
  the inclusion of the submodule and the quotient map form an exact pair,
  and `lTensor_mkQ` compute `ker (lTensor Q (N.mkQ))` and similarly for `rTensor_mkQ`

* `TensorProduct.map_ker` computes the kernel of `TensorProduct.map g g'`
  in the presence of two short exact sequences.

The proofs are those of [bourbaki1989] (chap. 2, §3, n°6)


## TODO

* Analogue for morphisms of algebras

* Treat the noncommutative case

* Treat the case of modules over semirings
  (For a possible definition of an exact sequence of commutative semigroups, see
  [Grillet-1969b], Pierre-Antoine Grillet,
  *The tensor product of commutative semigroups*,
  Trans. Amer. Math. Soc. 138 (1969), 281-293, doi:10.1090/S0002-9947-1969-0237688-1 .)

-/

section Exact

variable {M N P : Type*} (f : M → N) (g : N → P)

def Exact [Zero P] : Prop := ∀ y, g y = 0 ↔ y ∈ Set.range f

lemma Exact.comp_eq_zero [Zero P] (h : Exact f g) : g.comp f = 0 :=
  funext fun _ => (h _).mpr <| Set.mem_range_self _

open LinearMap

variable {R : Type*} [CommSemiring R]
variable {M N P : Type*}
  [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
  [Module R M] [Module R N] [Module R P]

variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}

lemma Exact.linearMap_ker_eq (hfg : Exact f g) : ker g = range f :=
  SetLike.ext hfg

lemma LinearMap.exact_iff : Exact f g ↔ LinearMap.ker g = LinearMap.range f :=
  Iff.symm <| SetLike.ext_iff

lemma Exact.linearMap_comp_eq_zero (h : Exact f g) : g.comp f = 0 :=
  FunLike.coe_injective h.comp_eq_zero

end Exact

section Modules

open TensorProduct LinearMap

section Semiring

variable {R : Type*} [CommSemiring R]
variable {M N P P' : Type*}
  [AddCommMonoid M] [AddCommMonoid N] [AddCommGroup P] [AddCommMonoid P']
  [Module R M] [Module R N] [Module R P] [Module R P']

variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}

variable {Q : Type*} [AddCommMonoid Q] [Module R Q]

variable (g)

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

end Semiring

variable {R : Type*} [CommRing R]
variable {M N P P' : Type*}
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module R N] [Module R P]

lemma LinearMap.exact_subtype_mkQ (N : Submodule R N) :
    Exact (Submodule.subtype N) (Submodule.mkQ N) := by
  rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_subtype N]

lemma LinearMap.exact_map_mkQ_range (f : M →ₗ[R] N) :
    Exact f (Submodule.mkQ (range f)) :=
  LinearMap.exact_iff.mpr <| Submodule.ker_mkQ _

lemma LinearMap.exact_subtype_ker_map (g : N →ₗ[R] P) :
    Exact (Submodule.subtype (ker g)) g :=
  LinearMap.exact_iff.mpr <| (Submodule.range_subtype _).symm

variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}

variable (Q : Type*) [AddCommGroup Q] [Module R Q]

variable (hfg : Exact f g) (hg : Function.Surjective g)

def rTensor.toFun :
  N ⊗[R] Q ⧸ LinearMap.range (rTensor Q f) →ₗ[R] P ⊗[R] Q := by
  apply Submodule.liftQ _ (rTensor Q g)
  rw [LinearMap.range_le_iff_comap, ← LinearMap.ker_comp, ← rTensor_comp,
    hfg.linearMap_comp_eq_zero, rTensor_zero, ker_zero]

-- private
def rTensor.inverse_ofRightInverse {h : P → N} (hgh : Function.RightInverse h g) :
    P ⊗[R] Q →ₗ[R] N ⊗[R] Q ⧸ LinearMap.range (rTensor Q f) := by
  rw [exact_iff] at hfg
  refine
    TensorProduct.lift
      { toFun := fun p ↦ Submodule.mkQ _ ∘ₗ TensorProduct.mk R _ _ (h p)
        map_add' := fun p p' => LinearMap.ext <| fun q => (Submodule.Quotient.eq _).mpr ?_
        map_smul' := fun r p => LinearMap.ext <| fun q => (Submodule.Quotient.eq _).mpr ?_ }
  · change h (p + p') ⊗ₜ[R] q - (h p ⊗ₜ[R] q + h p' ⊗ₜ[R] q) ∈ range (rTensor Q f)
    rw [← TensorProduct.add_tmul, ← TensorProduct.sub_tmul]
    apply le_comap_range_rTensor f
    rw [← hfg, mem_ker, map_sub, map_add]
    simp only [hgh _, sub_self]
  · change h (r • p) ⊗ₜ[R] q - r • h p ⊗ₜ[R] q ∈ range (rTensor Q f)
    rw [TensorProduct.smul_tmul', ← TensorProduct.sub_tmul]
    apply le_comap_range_rTensor f
    rw [← hfg, mem_ker, map_sub, map_smul]
    simp only [hgh _, sub_self]
  /-
  apply TensorProduct.lift
  apply LinearMap.mk₂ R (fun p q ↦ Submodule.Quotient.mk (h p ⊗ₜ[R] q))
  · intro p p' q
    rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
    rw [← TensorProduct.add_tmul, ← TensorProduct.sub_tmul]
    apply le_comap_range_rTensor f
    rw [← hfg, mem_ker, map_sub, map_add]
    simp only [hgh _, sub_self]
  · intro r p q
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    rw [TensorProduct.smul_tmul', ← TensorProduct.sub_tmul]
    apply le_comap_range_rTensor f
    rw [← hfg, mem_ker, map_sub, map_smul]
    simp only [hgh _, sub_self]
  · intro p q q'
    rw [TensorProduct.tmul_add, ← Submodule.Quotient.mk_add]
  · intro r p q
    simp only [TensorProduct.tmul_smul, Submodule.Quotient.mk_smul] -/

-- private
noncomputable
def rTensor.inverse :
    P ⊗[R] Q →ₗ[R] N ⊗[R] Q ⧸ LinearMap.range (rTensor Q f) :=
  rTensor.inverse_ofRightInverse Q hfg (Function.rightInverse_surjInv hg)

-- private
lemma rTensor.inverse_apply (y : N ⊗[R] Q) :
    (rTensor.inverse Q hfg hg) ((rTensor Q g) y) =
      Submodule.Quotient.mk (p := LinearMap.range (rTensor Q f)) y := by
  simp only [← LinearMap.comp_apply, ← Submodule.mkQ_apply]
  rw [exact_iff] at hfg
  apply LinearMap.congr_fun
  apply TensorProduct.ext'
  intro n q
  simp only [coe_comp, Function.comp_apply, rTensor_tmul, Submodule.mkQ_apply]
  simp only [rTensor.inverse, rTensor.inverse_ofRightInverse]
  simp only [TensorProduct.lift.tmul, coe_mk, AddHom.coe_mk, mk₂_apply]
  simp only [coe_comp, Function.comp_apply, mk_apply, Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq]
  rw [← TensorProduct.sub_tmul]
  apply le_comap_range_rTensor f
  rw [← hfg, mem_ker, map_sub, sub_eq_zero]
  rw [Function.surjInv_eq hg]

lemma rTensor.inverse_comp_rTensor :
    (rTensor.inverse Q hfg hg).comp (rTensor Q g) =
      Submodule.mkQ (p := LinearMap.range (rTensor Q f)) := by
  ext y
  simp only [coe_comp, Function.comp_apply, inverse_apply, Submodule.mkQ_apply]

noncomputable def rTensor.equiv :
    ((N ⊗[R] Q) ⧸ (LinearMap.range (rTensor Q f))) ≃ₗ[R] (P ⊗[R] Q) := {
  rTensor.toFun Q hfg with
  invFun    := rTensor.inverse Q hfg hg
  left_inv  := fun y ↦ by
    simp only [rTensor.toFun, AddHom.toFun_eq_coe, coe_toAddHom]
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
    simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, rTensor.inverse_apply]
  right_inv := fun z ↦ by
    simp only [AddHom.toFun_eq_coe, coe_toAddHom]
    obtain ⟨y, rfl⟩ := rTensor.surjective Q hg z
    rw [rTensor.inverse_apply]
    simp only [rTensor.toFun, Submodule.liftQ_apply] }


-- Which proof is better?

/-- Tensoring an exact pair on the right gives an exact pair -/
theorem rTensor_exact : Exact (rTensor Q f) (rTensor Q g) := by
  rw [LinearMap.exact_iff]
  apply le_antisymm
  · intro x hx
    rw [mem_ker] at hx
    rw [← Submodule.Quotient.mk_eq_zero, ← rTensor.inverse_apply Q hfg hg, hx, map_zero]
  · rintro y ⟨x, rfl⟩
    rw [mem_ker, ← rTensor_comp_apply, Exact.linearMap_comp_eq_zero hfg]
    simp only [rTensor_zero, zero_apply]

/-- Tensoring an exact pair on the right gives an exact pair -/
theorem rTensor_exact' : Exact (rTensor Q f) (rTensor Q g) := by
  intro y
  -- rw [mem_ker]
  constructor
  · intro hy
    simp only [Set.mem_range, ← LinearMap.mem_range]
    rw [← Submodule.Quotient.mk_eq_zero, ← rTensor.inverse_apply Q hfg hg, hy, map_zero]
  · rintro ⟨x, rfl⟩
    rw [← rTensor_comp_apply, Exact.linearMap_comp_eq_zero hfg, rTensor_zero, zero_apply]

/-- Tensoring an exact pair on the right gives an exact pair -/
theorem rTensor_exact'' : Exact (rTensor Q f) (rTensor Q g) := by
  rw [LinearMap.exact_iff]
  rw [← Submodule.ker_mkQ (p := range (rTensor Q f))]
  rw [← rTensor.inverse_comp_rTensor Q hfg hg, LinearMap.ker_comp, ← Submodule.comap_bot]
  apply congr_arg₂ _ rfl
  apply symm
  rw [LinearMap.ker_eq_bot]
  exact (rTensor.equiv Q hfg hg).symm.injective

lemma rTensor_mkQ (N : Submodule R M) :
    ker (rTensor Q (N.mkQ)) = range (rTensor Q N.subtype) := by
  rw [← LinearMap.exact_iff]
  exact rTensor_exact Q (LinearMap.exact_subtype_mkQ N) (Submodule.mkQ_surjective N)

-- private
def lTensor.inverse_ofRightInverse {h : P → N} (hgh : Function.RightInverse h g) :
    Q ⊗[R] P →ₗ[R] Q ⊗[R] N ⧸ LinearMap.range (lTensor Q f) := by
  rw [exact_iff] at hfg
  apply TensorProduct.lift
  apply LinearMap.mk₂ R (fun q p ↦ Submodule.Quotient.mk (q ⊗ₜ[R] (h p)))
  · intro q q' p
    rw [add_tmul, ← Submodule.Quotient.mk_add]
  · intro r p q
    rw [← TensorProduct.smul_tmul', ← Submodule.Quotient.mk_smul]
  · intro q p p'
    rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
    rw [← TensorProduct.tmul_add, ← TensorProduct.tmul_sub]
    apply le_comap_range_lTensor f
    rw [← hfg, mem_ker, map_sub, map_add]
    simp only [hgh _, sub_self]
  · intro r q p
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    rw [← TensorProduct.tmul_smul, ← TensorProduct.tmul_sub]
    apply le_comap_range_lTensor f
    rw [← hfg, mem_ker, map_sub, map_smul]
    simp only [hgh _, sub_self]

-- private
noncomputable
def lTensor.inverse :
    Q ⊗[R] P →ₗ[R] Q ⊗[R] N ⧸ LinearMap.range (lTensor Q f) :=
  lTensor.inverse_ofRightInverse Q hfg
    (Function.rightInverse_surjInv hg)

-- private
lemma lTensor.inverse_apply (y : Q ⊗[R] N) :
    (lTensor.inverse Q hfg hg) ((lTensor Q g) y) =
      Submodule.Quotient.mk (p := (LinearMap.range (lTensor Q f))) y := by
  simp only [← LinearMap.comp_apply, ← Submodule.mkQ_apply]
  rw [exact_iff] at hfg
  apply LinearMap.congr_fun
  apply TensorProduct.ext'
  intro n q
  simp only [coe_comp, Function.comp_apply, lTensor_tmul, Submodule.mkQ_apply]
  simp only [lTensor.inverse, lTensor.inverse_ofRightInverse]
  simp only [TensorProduct.lift.tmul, coe_mk, AddHom.coe_mk, mk₂_apply]
  rw [Submodule.Quotient.eq]
  rw [← TensorProduct.tmul_sub]
  apply le_comap_range_lTensor f n
  rw [← hfg, mem_ker, map_sub, sub_eq_zero]
  rw [Function.surjInv_eq hg]

/-- Tensoring an exact pair on the left gives an exact pair -/
theorem lTensor_exact : Exact (lTensor Q f) (lTensor Q g) := by
  rw [LinearMap.exact_iff]
  apply le_antisymm
  · intro x hx
    rw [mem_ker] at hx
    rw [← Submodule.Quotient.mk_eq_zero, ← lTensor.inverse_apply Q hfg hg, hx, map_zero]
  · rintro y ⟨x, rfl⟩
    rw [mem_ker, ← lTensor_comp_apply, Exact.linearMap_comp_eq_zero hfg]
    simp only [lTensor_zero, zero_apply]

lemma lTensor_mkQ (N : Submodule R M) :
    ker (lTensor Q (N.mkQ)) = range (lTensor Q N.subtype) := by
  rw [← LinearMap.exact_iff]
  exact lTensor_exact Q (LinearMap.exact_subtype_mkQ N) (Submodule.mkQ_surjective N)

variable {M' N' P' : Type*} [AddCommGroup M'] [AddCommGroup N'] [AddCommGroup P']
  [Module R M'] [Module R N'] [Module R P']
variable {f' : M' →ₗ[R] N'} {g' : N' →ₗ[R] P'}

variable  (hfg' : Exact f' g') (hg' : Function.Surjective g')

theorem TensorProduct.map_surjective : Function.Surjective (TensorProduct.map g g') := by
  rw [← LinearMap.lTensor_comp_rTensor]
  rw [LinearMap.coe_comp]
  exact Function.Surjective.comp (lTensor.surjective _ hg') (rTensor.surjective _ hg)

theorem TensorProduct.map_ker :
    LinearMap.ker (TensorProduct.map g g') =
      LinearMap.range (lTensor N f') ⊔ LinearMap.range (rTensor N' f) := by
  rw [← LinearMap.lTensor_comp_rTensor]
  rw [LinearMap.ker_comp]
  rw [← Exact.linearMap_ker_eq (rTensor_exact N' hfg hg)]
  rw [← Submodule.comap_map_eq]
  apply congr_arg₂ _ rfl
  rw [LinearMap.range_eq_map, ← Submodule.map_comp, LinearMap.rTensor_comp_lTensor,
    Submodule.map_top]
  rw [← LinearMap.lTensor_comp_rTensor, LinearMap.range_eq_map, Submodule.map_comp,
    Submodule.map_top]
  rw [LinearMap.range_eq_top.mpr (rTensor.surjective M' hg), Submodule.map_top]
  rw [Exact.linearMap_ker_eq (lTensor_exact P hfg' hg')]

end Modules


--  -·⬝.∙.⬝·-·⬝.∙.⬝·-
