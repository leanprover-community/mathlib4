/-
Copyright (c) 2023 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambetr-Loir
-/

import Mathlib.Algebra.Exact
import Mathlib.RingTheory.TensorProduct

/-! # Right exactness properties of tensor product
* `TensorProduct.rTensor_exact` says that one can tensor a short exact sequence on the right,
  and `rTensor.equiv` gives a LinearEquiv.

* `TensorProduct.lTensor_exact` says that one can tensor a short exact sequence on the left,
  and `lTensor.equiv` gives a LinearEquiv.

* For `N : Submodule R M`, `LinearMap.exact_subtype_mkQ N` says that
  the inclusion of the submodule and the quotient map form an exact pair,
  and `lTensor_mkQ` compute `ker (lTensor Q (N.mkQ))` and similarly for `rTensor_mkQ`

* `TensorProduct.map_ker` computes the kernel of `TensorProduct.map f g'`
  in the presence of two short exact sequences.

The proofs are those of [bourbaki1989] (chap. 2, §3, n°6)

* Analogue for morphisms of algebras :
  `Algebra.TensorProduct.ker_map` computes the kernel of `Algebra.TensorProduct.map f g`

* The two more specific lemmas `Algebra.TensorProduct.lTensor_ker`
  and `Algebra.TensorProduct.rTensor_ker` compute the kernels
  of `Algebra.TensorProduct.map f id` and `Algebra.TensorProduct.map id g`

## TODO

* Treat the noncommutative case

* Treat the case of modules over semirings
  (For a possible definition of an exact sequence of commutative semigroups, see
  [Grillet-1969b], Pierre-Antoine Grillet,
  *The tensor product of commutative semigroups*,
  Trans. Amer. Math. Soc. 138 (1969), 281-293, doi:10.1090/S0002-9947-1969-0237688-1 .)

-/


section Modules

open TensorProduct LinearMap

section Semiring

variable {R : Type*} [CommSemiring R]
variable {M N P P' Q: Type*}
  [AddCommMonoid M] [AddCommMonoid N] [AddCommGroup P] [AddCommMonoid P'] [AddCommMonoid Q]
  [Module R M] [Module R N] [Module R P] [Module R P'] [Module R Q]

variable {f : M →ₗ[R] N} (g : N →ₗ[R] P)

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

variable {R : Type*} [CommRing R]
variable {M N P P' : Type*}
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

variable (Q : Type*) [AddCommGroup Q] [Module R Q]

variable (hfg : Exact f g) (hg : Function.Surjective g)


/-- The direct map in `lTensor.equiv` -/
def lTensor.toFun :
  Q ⊗[R] N ⧸ LinearMap.range (lTensor Q f) →ₗ[R] Q ⊗[R] P := by
  apply Submodule.liftQ _ (lTensor Q g)
  rw [LinearMap.range_le_iff_comap, ← LinearMap.ker_comp, ← lTensor_comp,
    hfg.linearMap_comp_eq_zero, lTensor_zero, ker_zero]

/-- The inverse map in `lTensor.equiv_of_rightInverse` (computably, given a right inverse)-/
def lTensor.inverse_of_rightInverse {h : P → N} (hgh : Function.RightInverse h g) :
    Q ⊗[R] P →ₗ[R] Q ⊗[R] N ⧸ LinearMap.range (lTensor Q f) := by
  rw [exact_iff] at hfg
  apply TensorProduct.lift
  apply LinearMap.flip
  refine
      { toFun := fun p ↦ Submodule.mkQ _ ∘ₗ ((TensorProduct.mk R _ _).flip (h p))
        map_add' := fun p p' => LinearMap.ext <| fun q => (Submodule.Quotient.eq _).mpr ?_
        map_smul' := fun r p => LinearMap.ext <| fun q => (Submodule.Quotient.eq _).mpr ?_ }
  · change q ⊗ₜ[R] (h (p + p')) - (q ⊗ₜ[R] (h p) + q ⊗ₜ[R] (h p')) ∈ range (lTensor Q f)
    rw [← TensorProduct.tmul_add, ← TensorProduct.tmul_sub]
    apply le_comap_range_lTensor f
    simp only [← hfg, mem_ker, map_sub, map_add, hgh _, sub_self]
  · change q ⊗ₜ[R] (h (r • p)) - r • q ⊗ₜ[R] (h p) ∈ range (lTensor Q f)
    rw [← TensorProduct.tmul_smul, ← TensorProduct.tmul_sub]
    apply le_comap_range_lTensor f
    simp only [← hfg, mem_ker, map_sub, map_smul, hgh _, sub_self]

lemma lTensor.inverse_of_rightInverse_apply
    {h : P → N} (hgh : Function.RightInverse h g) (y : Q ⊗[R] N) :
    (lTensor.inverse_of_rightInverse Q hfg hgh) ((lTensor Q g) y) =
      Submodule.Quotient.mk (p := (LinearMap.range (lTensor Q f))) y := by
  simp only [← LinearMap.comp_apply, ← Submodule.mkQ_apply]
  rw [exact_iff] at hfg
  apply LinearMap.congr_fun
  apply TensorProduct.ext'
  intro n q
  simp only [coe_comp, Function.comp_apply, lTensor_tmul, Submodule.mkQ_apply]
  simp only [lTensor.inverse_of_rightInverse]
  simp only [TensorProduct.lift.tmul, coe_mk, AddHom.coe_mk, mk₂_apply]
  simp only [flip_apply, coe_mk, AddHom.coe_mk, coe_comp, Function.comp_apply, mk_apply,
    Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq, ← TensorProduct.tmul_sub]
  apply le_comap_range_lTensor f n
  rw [← hfg, mem_ker, map_sub, sub_eq_zero, hgh]

lemma lTensor.inverse_of_rightInverse_comp_rTensor
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
  lTensor.inverse_of_rightInverse Q hfg
    (Function.rightInverse_surjInv hg)

lemma lTensor.inverse_apply (y : Q ⊗[R] N) :
    (lTensor.inverse Q hfg hg) ((lTensor Q g) y) =
      Submodule.Quotient.mk (p := (LinearMap.range (lTensor Q f))) y := by
  simp only [lTensor.inverse, lTensor.inverse_of_rightInverse_apply]

lemma lTensor.inverse_comp_rTensor :
    (lTensor.inverse Q hfg hg).comp (lTensor Q g) =
      Submodule.mkQ (p := LinearMap.range (lTensor Q f)) := by
  rw [lTensor.inverse, lTensor.inverse_of_rightInverse_comp_rTensor]

/-- For a surjective `f : N →ₗ[R] P`,
  the natural equivalence between `Q ⊗ N ⧸ (image of ker f)` to `Q ⊗ P`
  (computably, given a right inverse) -/
def lTensor.linearEquiv_of_rightInverse {h : P → N} (hgh : Function.RightInverse h g) :
    ((Q ⊗[R] N) ⧸ (LinearMap.range (lTensor Q f))) ≃ₗ[R] (Q ⊗[R] P) := {
  lTensor.toFun Q hfg with
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
  lTensor.linearEquiv_of_rightInverse  Q hfg (Function.rightInverse_surjInv hg)

/-- Tensoring an exact pair on the left gives an exact pair -/
theorem lTensor_exact : Exact (lTensor Q f) (lTensor Q g) := by
  rw [exact_iff]
  rw [← Submodule.ker_mkQ (p := range (lTensor Q f))]
  rw [← lTensor.inverse_comp_rTensor Q hfg hg]
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
  N ⊗[R] Q ⧸ range (rTensor Q f) →ₗ[R] P ⊗[R] Q := by
  apply Submodule.liftQ _ (rTensor Q g)
  rw [range_le_iff_comap, ← ker_comp, ← rTensor_comp,
    hfg.linearMap_comp_eq_zero, rTensor_zero, ker_zero]

/-- The inverse map in `rTensor.equiv_of_rightInverse` (computably, given a right inverse) -/
def rTensor.inverse_of_rightInverse {h : P → N} (hgh : Function.RightInverse h g) :
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
    simp only [← hfg, mem_ker, map_sub, map_add, hgh _, sub_self]
  · change h (r • p) ⊗ₜ[R] q - r • h p ⊗ₜ[R] q ∈ range (rTensor Q f)
    rw [TensorProduct.smul_tmul', ← TensorProduct.sub_tmul]
    apply le_comap_range_rTensor f
    simp only [← hfg, mem_ker, map_sub, map_smul, hgh _, sub_self]

lemma rTensor.inverse_of_rightInverse_apply
    {h : P → N} (hgh : Function.RightInverse h g) (y : N ⊗[R] Q) :
    (rTensor.inverse_of_rightInverse Q hfg hgh) ((rTensor Q g) y) =
      Submodule.Quotient.mk (p := LinearMap.range (rTensor Q f)) y := by
  simp only [← LinearMap.comp_apply, ← Submodule.mkQ_apply]
  rw [exact_iff] at hfg
  apply LinearMap.congr_fun
  apply TensorProduct.ext'
  intro n q
  simp only [coe_comp, Function.comp_apply, rTensor_tmul, Submodule.mkQ_apply]
  simp only [rTensor.inverse_of_rightInverse]
  simp only [TensorProduct.lift.tmul, coe_mk, AddHom.coe_mk, mk₂_apply]
  simp only [coe_comp, Function.comp_apply, mk_apply, Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq, ← TensorProduct.sub_tmul]
  apply le_comap_range_rTensor f
  rw [← hfg, mem_ker, map_sub, sub_eq_zero, hgh]

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
  rw [LinearMap.ext_iff]
  intro y
  simp only [coe_comp, Function.comp_apply, Submodule.mkQ_apply, rTensor.inverse_apply]

/-- For a surjective `f : N →ₗ[R] P`,
  the natural equivalence between `N ⊗[R] Q ⧸ (range (rTensor Q f))` and `P ⊗[R] Q`
  (computably, given a right inverse) -/
def rTensor.equiv_of_rightInverse
    {h : P → N} (hgh : Function.RightInverse h g) :
    ((N ⊗[R] Q) ⧸ (range (rTensor Q f))) ≃ₗ[R] (P ⊗[R] Q) := {
  rTensor.toFun Q hfg with
  invFun    := rTensor.inverse_of_rightInverse Q hfg hgh
  left_inv  := fun y ↦ by
    simp only [rTensor.toFun, AddHom.toFun_eq_coe, coe_toAddHom]
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
    simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, rTensor.inverse_of_rightInverse_apply]
  right_inv := fun z ↦ by
    simp only [AddHom.toFun_eq_coe, coe_toAddHom]
    obtain ⟨y, rfl⟩ := rTensor.surjective Q hgh.surjective z
    rw [rTensor.inverse_of_rightInverse_apply]
    simp only [rTensor.toFun, Submodule.liftQ_apply] }

/-- For a surjective `f : N →ₗ[R] P`,
  the natural equivalence between `N ⊗[R] Q ⧸ (range (rTensor Q f))` and `P ⊗[R] Q` -/
noncomputable def rTensor.equiv :
    ((N ⊗[R] Q) ⧸ (LinearMap.range (rTensor Q f))) ≃ₗ[R] (P ⊗[R] Q) :=
  rTensor.equiv_of_rightInverse Q hfg (Function.rightInverse_surjInv hg)

/-- Tensoring an exact pair on the right gives an exact pair -/
theorem rTensor_exact : Exact (rTensor Q f) (rTensor Q g) := by
  rw [exact_iff]
  rw [← Submodule.ker_mkQ (p := range (rTensor Q f))]
  rw [← rTensor.inverse_comp_rTensor Q hfg hg]
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
variable {f' : M' →ₗ[R] N'} {g' : N' →ₗ[R] P'}

variable  (hfg' : Exact f' g') (hg' : Function.Surjective g')

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

section Algebras

open Algebra.TensorProduct

open scoped TensorProduct

variable
    {R : Type*} [CommSemiring R]
    {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/- The following lemmas could be easier if `I ⊗[R] B` was naturally an `A ⊗[R] B` module,
  and the map to `A ⊗[R] B` was known to be linear.
  This depends on the B-module structure on a tensor product
  whose use rapidly conflicts with
  everything… -/

/-- The ideal of `A ⊗[R] B` generated by `I` is the image of `I ⊗[R] B` -/
lemma Ideal.map_includeLeft_eq (I : Ideal A) :
  (I.map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B)).restrictScalars R
    = LinearMap.range (LinearMap.rTensor B (Submodule.subtype (I.restrictScalars R))) := by
  rw [← Submodule.carrier_inj]
  apply le_antisymm
  · intro x
    simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
      Submodule.mem_toAddSubmonoid, Submodule.restrictScalars_mem, LinearMap.mem_range]
    intro hx
    rw [Ideal.map, ← submodule_span_eq] at hx
    refine' Submodule.span_induction hx _ _ _ _
    · intro x
      simp only [includeLeft_apply, Set.mem_image, SetLike.mem_coe]
      rintro ⟨y, hy, rfl⟩
      use ⟨y, hy⟩ ⊗ₜ[R] 1
      rfl
    · use 0
      simp only [map_zero]
    · rintro x y ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      use x + y
      simp only [map_add]
    · rintro a x ⟨x, hx, rfl⟩
      induction a using TensorProduct.induction_on with
      | zero =>
        use 0
        simp only [map_zero, smul_eq_mul, zero_mul]
      | tmul a b =>
        induction x using TensorProduct.induction_on with
        | zero =>
          use 0
          simp only [map_zero, smul_eq_mul, mul_zero]
        | tmul x y =>
          use (a • x) ⊗ₜ[R] (b * y)
          simp only [LinearMap.lTensor_tmul, Submodule.coeSubtype, smul_eq_mul, tmul_mul_tmul]
          rfl
        | add x y hx hy =>
          obtain ⟨x', hx'⟩ := hx
          obtain ⟨y', hy'⟩ := hy
          use x' + y'
          simp only [map_add, hx', smul_add, hy']
      | add a b ha hb =>
        obtain ⟨x', ha'⟩ := ha
        obtain ⟨y', hb'⟩ := hb
        use x' + y'
        simp only [map_add, ha', add_smul, hb']

  · rintro x ⟨y, rfl⟩
    induction y using TensorProduct.induction_on with
    | zero =>
        rw [map_zero]
        apply zero_mem
    | tmul a b =>
        simp only [LinearMap.rTensor_tmul, Submodule.coeSubtype]
        suffices : (a : A) ⊗ₜ[R] b = ((1 : A) ⊗ₜ[R] b) * ((a : A) ⊗ₜ[R] (1 : B))
        simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
          Submodule.mem_toAddSubmonoid, Submodule.restrictScalars_mem]
        rw [this]
        apply Ideal.mul_mem_left
        apply Ideal.mem_map_of_mem
        exact Submodule.coe_mem a
        simp only [Submodule.coe_restrictScalars, Algebra.TensorProduct.tmul_mul_tmul,
          mul_one, one_mul]
    | add x y hx hy =>
        rw [map_add]
        apply Submodule.add_mem _ hx hy

/-- The ideal of `A ⊗[R] B` generated by `I` is the image of `I ⊗[R] B` -/
lemma Algebra.TensorProduct.ideal_map_includeLeft_carrier
    {R : Type*} [CommSemiring R]
    {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    (I : Ideal A) :
  (I.map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B)).carrier =
    LinearMap.range (LinearMap.rTensor B (Submodule.subtype (I.restrictScalars R))) := by
  rw [← Ideal.map_includeLeft_eq]
  rfl

/-- The ideal of `A ⊗[R] B` generated by `I` is the image of `A ⊗[R] I` -/
lemma Ideal.map_includeRight_eq (I : Ideal B) :
  (I.map (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B)).restrictScalars R
    = LinearMap.range (LinearMap.lTensor A (Submodule.subtype (I.restrictScalars R))) := by
  rw [← Submodule.carrier_inj]
  apply le_antisymm
  · intro x
    simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
      Submodule.mem_toAddSubmonoid, Submodule.restrictScalars_mem, LinearMap.mem_range]
    intro hx
    rw [Ideal.map, ← submodule_span_eq] at hx
    refine' Submodule.span_induction hx _ _ _ _
    · intro x
      simp only [includeRight_apply, Set.mem_image, SetLike.mem_coe]
      rintro ⟨y, hy, rfl⟩
      use 1 ⊗ₜ[R] ⟨y, hy⟩
      rfl
    · use 0
      simp only [map_zero]
    · rintro x y ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      use x + y
      simp only [map_add]
    · rintro a x ⟨x, hx, rfl⟩
      induction a using TensorProduct.induction_on with
      | zero =>
        use 0
        simp only [map_zero, smul_eq_mul, zero_mul]
      | tmul a b =>
        induction x using TensorProduct.induction_on with
        | zero =>
          use 0
          simp only [map_zero, smul_eq_mul, mul_zero]
        | tmul x y =>
          use (a * x) ⊗ₜ[R] (b •y)
          simp only [LinearMap.lTensor_tmul, Submodule.coeSubtype, smul_eq_mul, tmul_mul_tmul]
          rfl
        | add x y hx hy =>
          obtain ⟨x', hx'⟩ := hx
          obtain ⟨y', hy'⟩ := hy
          use x' + y'
          simp only [map_add, hx', smul_add, hy']
      | add a b ha hb =>
        obtain ⟨x', ha'⟩ := ha
        obtain ⟨y', hb'⟩ := hb
        use x' + y'
        simp only [map_add, ha', add_smul, hb']

  · rintro x ⟨y, rfl⟩
    induction y using TensorProduct.induction_on with
    | zero =>
        rw [map_zero]
        apply zero_mem
    | tmul a b =>
        simp only [LinearMap.lTensor_tmul, Submodule.coeSubtype]
        suffices : a ⊗ₜ[R] (b : B) = (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] (b : B))
        rw [this]
        simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
          Submodule.mem_toAddSubmonoid, Submodule.restrictScalars_mem]
        apply Ideal.mul_mem_left
        apply Ideal.mem_map_of_mem
        exact Submodule.coe_mem b
        simp only [Submodule.coe_restrictScalars, Algebra.TensorProduct.tmul_mul_tmul,
          mul_one, one_mul]
    | add x y hx hy =>
        rw [map_add]
        apply Submodule.add_mem _ hx hy

/-- The ideal of `A ⊗[R] B` generated by `I` is the image of `A ⊗[R] I` (carrier) -/
lemma Algebra.TensorProduct.ideal_map_includeRight_carrier
    {R : Type*} [CommSemiring R]
    {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    (I : Ideal B) :
  (I.map (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B)).carrier =
    LinearMap.range (LinearMap.lTensor A (Submodule.subtype (I.restrictScalars R))) := by
  rw [← Ideal.map_includeRight_eq]
  rfl

/- Now, we can prove the right exactness properties of tensor product,
 in its versions for algebras -/

variable {R : Type*} [CommRing R]
  {A B C D : Type*} [Ring A] [Ring B] [Ring C] [Ring D]
  [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
  (f : A →ₐ[R] B) (g : C →ₐ[R] D)

/-- If `g` is surjective, then the kernel of `(id A) ⊗ g` is generated by the kernel of `g` -/
lemma Algebra.TensorProduct.lTensor_ker (hg : Function.Surjective g) :
  RingHom.ker (map (AlgHom.id R A) g) =
    (RingHom.ker g).map (Algebra.TensorProduct.includeRight : C →ₐ[R] A ⊗[R] C) := by
  rw [← Submodule.carrier_inj]
  rw [Algebra.TensorProduct.ideal_map_includeRight_carrier]
  have : (RingHom.ker (map (AlgHom.id R A) g)).toAddSubmonoid.toAddSubsemigroup.carrier =
    LinearMap.ker (LinearMap.lTensor A (AlgHom.toLinearMap g)) := rfl
  rw [this]
  rw [(lTensor_exact A g.toLinearMap.exact_subtype_ker_map hg).linearMap_ker_eq]
  rfl

/-- If `f` is surjective, then the kernel of `f ⊗ (id B)` is generated by the kernel of `f` -/
lemma Algebra.TensorProduct.rTensor_ker (hf : Function.Surjective f) :
    RingHom.ker (map f (AlgHom.id R C)) =
    (RingHom.ker f).map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] C) := by
  rw [← Submodule.carrier_inj, Algebra.TensorProduct.ideal_map_includeLeft_carrier]
  have : (RingHom.ker (map f (AlgHom.id R C))).toAddSubmonoid.toAddSubsemigroup.carrier =
    LinearMap.ker (LinearMap.rTensor C (AlgHom.toLinearMap f)) := rfl
  rw [this]
  rw [(rTensor_exact C f.toLinearMap.exact_subtype_ker_map hf).linearMap_ker_eq]
  rfl

lemma AlgHom.coe_ker {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    RingHom.ker f = RingHom.ker (f : A →+* B) := rfl

lemma AlgHom.coe_ideal_map {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (I : Ideal A) :
    Ideal.map f I = Ideal.map (f : A →+* B) I := rfl

/-- If `f` and `g` are surjective morphisms of algebras, then
  the kernel of `Algebra.TensorProduct.map f g` is generated by the kernels of `f` and `g` -/
theorem Algebra.TensorProduct.map_ker (hf : Function.Surjective f) (hg : Function.Surjective g) :
    RingHom.ker (map f g) =
      (RingHom.ker f).map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] C) ⊔
        (RingHom.ker g).map (Algebra.TensorProduct.includeRight : C →ₐ[R] A ⊗[R] C) := by
  -- rewrite map f g as the composition of two maps
  have : map f g = (map f (AlgHom.id R D)).comp (map (AlgHom.id R A) g) := ext rfl rfl
  rw [this]
  -- this needs some rewriting to RingHom
  simp only [AlgHom.coe_ker, AlgHom.comp_toRingHom]
  rw [← RingHom.comap_ker]
  simp only [← AlgHom.coe_ker]
  -- apply one step of exactness
  rw [← Algebra.TensorProduct.lTensor_ker _ hg, RingHom.ker_eq_comap_bot (map (AlgHom.id R A) g)]
  rw [← Ideal.comap_map_of_surjective _ (lTensor.surjective A hg)]
  -- apply the other step of exactness
  rw [Algebra.TensorProduct.rTensor_ker _ hf]
  apply congr_arg₂ _ rfl
  simp only [AlgHom.coe_ideal_map, Ideal.map_map]
  rw [← AlgHom.comp_toRingHom, Algebra.TensorProduct.map_comp_includeLeft]
  rfl

end Algebras



#exit



-- Johan, Kevin : do you prefer this?
example (hg : Function.Surjective g) :
    Function.Surjective (rTensor Q g) := by
  rw [← LinearMap.comm_comp_lTensor_comp_comm_eq]
  simp only [coe_comp, LinearEquiv.coe_coe, EquivLike.comp_bijective,
    EquivLike.surjective_comp, EquivLike.comp_surjective]
  exact lTensor.surjective Q hg



-- Tentative version for `rTensor` using `lTensor` and `TensorProduct.comm``

lemma comm_comp_rTensor_eq_lTensor_comp_comm {g : N →ₗ[R] P} :
    (TensorProduct.comm R P Q) ∘ₗ (rTensor Q g) =
      lTensor Q g ∘ₗ (TensorProduct.comm R N Q) := by
  exact TensorProduct.ext rfl

lemma comm_comp_lTensor_eq_rTensor_comp_comm {g : N →ₗ[R] P} :
    (TensorProduct.comm R Q P) ∘ₗ (lTensor Q g) =
      rTensor Q g ∘ₗ (TensorProduct.comm R Q N) := by
  exact TensorProduct.ext rfl

lemma comm_range_rTensor_eq_range_lTensor :
    Submodule.map (TensorProduct.comm R N Q) (range (rTensor Q f)) =
      range (lTensor Q f) := by
  change Submodule.map (TensorProduct.comm R N Q).toLinearMap _ = _
  rw [← LinearMap.range_comp, comm_comp_rTensor_eq_lTensor_comp_comm,
    LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]

lemma comm_range_lTensor_eq_range_rTensor :
    Submodule.map (TensorProduct.comm R Q N) (range (lTensor Q f)) =
      range (rTensor Q f) := by
  change Submodule.map (TensorProduct.comm R Q N).toLinearMap _ = _
  rw [← LinearMap.range_comp, comm_comp_lTensor_eq_rTensor_comp_comm,
    LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]

lemma rTensor_range_eq :
  (N ⊗[R] Q ⧸ range (rTensor Q f)) ≃ₗ[R]
    (Q ⊗[R] N ⧸ range (lTensor Q f)) := by
    apply Submodule.Quotient.equiv _ _ (TensorProduct.comm R N Q)
    exact comm_range_rTensor_eq_range_lTensor Q

noncomputable def rTensor.equiv' :
    (N ⊗[R] Q ⧸ range (rTensor Q f)) ≃ₗ[R] (P ⊗[R] Q) :=
  ((Submodule.Quotient.equiv _ _ (TensorProduct.comm R N Q)
    (comm_range_rTensor_eq_range_lTensor Q)).trans
    (lTensor.equiv Q hfg hg)).trans (TensorProduct.comm R Q P)

def rTensor.equiv_of_rightInverse' {h : P → N} (hgh : Function.RightInverse h g) :
    (N ⊗[R] Q ⧸ LinearMap.range (rTensor Q f)) ≃ₗ[R] P ⊗[R] Q :=
  ((Submodule.Quotient.equiv _ _ (TensorProduct.comm R N Q)
    (comm_range_rTensor_eq_range_lTensor Q)).trans
      (lTensor.equiv_of_rightInverse Q hfg hgh)).trans (TensorProduct.comm R Q P)

lemma rTensor.equiv'_apply_tmul (n : N) (q : Q) :
    rTensor.equiv' Q hfg hg (Submodule.Quotient.mk (n ⊗ₜ[R] q)) =
      g n ⊗ₜ[R] q := by
  unfold rTensor.equiv'
  simp only [LinearEquiv.trans_apply, Submodule.Quotient.equiv_apply,
    Submodule.mapQ_apply, LinearEquiv.coe_coe, comm_tmul]
  rfl

lemma rTensor.inverse_comp_rTensor'
        {h : P → N} (hgh : Function.RightInverse h g) :
    (rTensor.equiv_of_rightInverse' Q hfg hgh).symm ∘ (rTensor Q g) =
      Submodule.mkQ (p := LinearMap.range (rTensor Q f)) := by
  rw [LinearEquiv.symm_comp_eq, ← LinearEquiv.coe_coe, ← LinearMap.coe_comp]
  apply congr_arg
  apply TensorProduct.ext'
  intro n q
  rfl

lemma rTensor.equiv'_inverse_of_rightInverse_apply
    {h : P → N} (hgh : Function.RightInverse h g) (y : N ⊗[R] Q) :
    (rTensor.equiv_of_rightInverse' Q hfg hgh).symm ((rTensor Q g) y) =
      Submodule.Quotient.mk (p := LinearMap.range (rTensor Q f)) y := by
  rw [← LinearEquiv.coe_coe, ← Submodule.mkQ_apply, ← LinearMap.comp_apply]
  apply congr_fun
  simp only [coe_comp, LinearEquiv.coe_coe]
  apply rTensor.inverse_comp_rTensor'
