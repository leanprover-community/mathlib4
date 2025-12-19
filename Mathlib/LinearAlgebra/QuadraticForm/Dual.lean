/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# Quadratic form structures related to `Module.Dual`

## Main definitions

* `LinearMap.dualProd R M`, the bilinear form on `(f, x) : Module.Dual R M × M` defined as
  `f x`.
* `QuadraticForm.dualProd R M`, the quadratic form on `(f, x) : Module.Dual R M × M` defined as
  `f x`.
* `QuadraticForm.toDualProd : (Q.prod <| -Q) →qᵢ QuadraticForm.dualProd R M` a form-preserving map
  from `(Q.prod <| -Q)` to `QuadraticForm.dualProd R M`.

-/

@[expose] public section


variable (R M N : Type*)

namespace LinearMap

section Semiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The symmetric bilinear form on `Module.Dual R M × M` defined as
`B (f, x) (g, y) = f y + g x`. -/
@[simps!]
def dualProd : LinearMap.BilinForm R (Module.Dual R M × M) :=
    (applyₗ.comp (snd R (Module.Dual R M) M)).compl₂ (fst R (Module.Dual R M) M) +
      ((applyₗ.comp (snd R (Module.Dual R M) M)).compl₂ (fst R (Module.Dual R M) M)).flip

theorem isSymm_dualProd : (dualProd R M).IsSymm := ⟨fun _x _y => add_comm _ _⟩

end Semiring

section Ring

variable [CommRing R] [AddCommGroup M] [Module R M]

theorem separatingLeft_dualProd :
    (dualProd R M).SeparatingLeft ↔ Function.Injective (Module.Dual.eval R M) := by
  classical
  rw [separatingLeft_iff_ker_eq_bot, ker_eq_bot]
  let e := LinearEquiv.prodComm R _ _ ≪≫ₗ Module.dualProdDualEquivDual R (Module.Dual R M) M
  let h_d := e.symm.toLinearMap.comp (dualProd R M)
  refine (Function.Injective.of_comp_iff e.symm.injective
    (dualProd R M)).symm.trans ?_
  rw [← LinearEquiv.coe_toLinearMap, ← coe_comp]
  change Function.Injective h_d ↔ _
  have : h_d = prodMap id (Module.Dual.eval R M) := by
    refine ext fun x => Prod.ext ?_ ?_
    · ext
      dsimp [e, h_d, Module.Dual.eval, LinearEquiv.prodComm]
      simp
    · ext
      dsimp [e, h_d, Module.Dual.eval, LinearEquiv.prodComm]
      simp
  rw [this, coe_prodMap]
  refine Prod.map_injective.trans ?_
  exact and_iff_right Function.injective_id

end Ring

end LinearMap

namespace QuadraticForm

open QuadraticMap

section Semiring

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

/-- The quadratic form on `Module.Dual R M × M` defined as `Q (f, x) = f x`. -/
@[simps]
def dualProd : QuadraticForm R (Module.Dual R M × M) where
  toFun p := p.1 p.2
  toFun_smul a p := by
    rw [Prod.smul_fst, Prod.smul_snd, LinearMap.smul_apply, map_smul, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, mul_assoc]
  exists_companion' :=
    ⟨LinearMap.dualProd R M, fun p q => by
      rw [LinearMap.dualProd_apply_apply, Prod.fst_add, Prod.snd_add, LinearMap.add_apply, map_add,
        map_add, add_right_comm _ (q.1 q.2), add_comm (q.1 p.2) (p.1 q.2), ← add_assoc, ←
        add_assoc]⟩

@[simp]
theorem _root_.LinearMap.dualProd.toQuadraticForm :
    (LinearMap.dualProd R M).toQuadraticMap = 2 • dualProd R M :=
  ext fun _a => (two_nsmul _).symm

variable {R M N}

/-- Any module isomorphism induces a quadratic isomorphism between the corresponding `dual_prod.` -/
@[simps!]
def dualProdIsometry (f : M ≃ₗ[R] N) : (dualProd R M).IsometryEquiv (dualProd R N) where
  toLinearEquiv := f.dualMap.symm.prodCongr f
  map_app' x := DFunLike.congr_arg x.fst <| f.symm_apply_apply _

/-- `QuadraticForm.dualProd` commutes (isometrically) with `QuadraticForm.prod`. -/
@[simps!]
def dualProdProdIsometry :
    (dualProd R (M × N)).IsometryEquiv ((dualProd R M).prod (dualProd R N)) where
  toLinearEquiv :=
    (Module.dualProdDualEquivDual R M N).symm.prodCongr (LinearEquiv.refl R (M × N)) ≪≫ₗ
      LinearEquiv.prodProdProdComm R _ _ M N
  map_app' m :=
    (m.fst.map_add _ _).symm.trans <| DFunLike.congr_arg m.fst <| Prod.ext (add_zero _) (zero_add _)

end Semiring

section Ring

variable [CommRing R] [AddCommGroup M] [Module R M]
variable {R M}

/-- The isometry sending `(Q.prod <| -Q)` to `(QuadraticForm.dualProd R M)`.

This is `σ` from Proposition 4.8, page 84 of
[*Hermitian K-Theory and Geometric Applications*][hyman1973]; though we swap the order of the pairs.
-/
@[simps!]
def toDualProd (Q : QuadraticForm R M) [Invertible (2 : R)] :
    (Q.prod <| -Q) →qᵢ QuadraticForm.dualProd R M where
  toLinearMap := LinearMap.prod
    (Q.associated.comp (LinearMap.fst _ _ _) + Q.associated.comp (LinearMap.snd _ _ _))
    (LinearMap.fst _ _ _ - LinearMap.snd _ _ _)
  map_app' x := by
    dsimp only [associated, associatedHom]
    dsimp only [LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk, AddHom.toFun_eq_coe,
      LinearMap.coe_toAddHom, LinearMap.prod_apply, Pi.prod, LinearMap.add_apply,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply,
      LinearMap.sub_apply, dualProd_apply, polarBilin_apply_apply, prod_apply, neg_apply]
    simp only [polar_sub_right, polar_self, nsmul_eq_mul, Nat.cast_ofNat, polar_comm _ x.1 x.2,
      smul_sub, Module.End.smul_def, sub_add_sub_cancel, ← sub_eq_add_neg (Q x.1) (Q x.2)]
    rw [← map_sub (⅟2 : Module.End R R), ← mul_sub, ← Module.End.smul_def]
    simp only [Module.End.smul_def, half_moduleEnd_apply_eq_half_smul, smul_eq_mul,
      invOf_mul_cancel_left']

/-!
TODO: show that `QuadraticForm.toDualProd` is an `QuadraticForm.IsometryEquiv`
-/

end Ring

end QuadraticForm

/-- Vectors which subtend obtuse angles with each other and all lie in the same half-space are
linearly independent.

This is [serre1965](Ch. V, §9, Lemma 4). -/
lemma LinearMap.BilinForm.linearIndependent_of_pairwise_le_zero {ι R M : Type*}
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup M] [Module R M]
    (B : LinearMap.BilinForm R M) (hB : B.toQuadraticMap.PosDef)
    (f : Module.Dual R M) (v : ι → M)
    (hp : ∀ i, 0 < f (v i))
    (hn : Pairwise fun i j ↦ B (v i) (v j) ≤ 0) :
    LinearIndependent R v := by
  refine linearIndependent_iff'.mpr fun s c hc ↦ ?_
  set x := ∑ i ∈ s with 0 ≤ c i, c i • v i with hx
  set y := ∑ i ∈ s with c i < 0, (-c i) • v i with hy
  replace hc : x = y := by
    simp_rw [hx, hy, neg_smul, Finset.sum_neg_distrib, ← add_eq_zero_iff_eq_neg, ← hc]
    simp [← s.sum_filter_add_sum_filter_not (p := fun i ↦ 0 ≤ c i) (f := fun i ↦ c i • v i)]
  have hx₀ : x = 0 := by
    suffices B x y ≤ 0 by simpa [hc, ← hB.le_zero_iff, B.toQuadraticMap_apply]
    suffices 0 ≤ ∑ x ∈ s with c x < 0, ∑ i ∈ s with 0 ≤ c i, c x * (c i * (B (v i)) (v x)) by
      simpa [hx, hy, map_neg, Finset.mul_sum]
    refine Finset.sum_nonneg fun i hi ↦ Finset.sum_nonneg fun j hj ↦ ?_
    rcases eq_or_ne i j with rfl | hij
    · rw [← mul_assoc]
      exact mul_nonneg (mul_self_nonneg _) (hB.nonneg _)
    · specialize hn hij.symm
      grind [mul_nonneg_iff, mul_nonpos_iff]
  replace hx : ∑ i ∈ s with 0 ≤ c i, c i * f (v i) = 0 := by
    rw [hx₀] at hx
    simpa using (congr(f $hx)).symm
  replace hx (i : ι) (hi : i ∈ s) : c i ≤ 0 := by
    have aux (j : ι) (hj : j ∈ {i ∈ s | 0 ≤ c i}) : 0 ≤ c j * f (v j) := by
      obtain ⟨hjs : j ∈ s, hj₀ : 0 ≤ c j⟩ := by simpa using hj
      nlinarith [hp j]
    rw [Finset.sum_eq_zero_iff_of_nonneg aux] at hx
    by_contra! hi'
    have : 0 < c i * f (v i) := mul_pos hi' (hp i)
    grind
  replace hy : ∑ i ∈ s with c i < 0, c i * f (v i) = 0 := by
    rw [← hc, hx₀] at hy
    simpa using (congr(f $hy)).symm
  replace hy (i : ι) (hi : i ∈ s) : 0 ≤ c i := by
    have aux (j : ι) (hj : j ∈ {i ∈ s | c i < 0}) : c j * f (v j) ≤ 0 := by
      obtain ⟨hjs : j ∈ s, hj₀ : c j < 0⟩ := by simpa using hj
      nlinarith [hp j]
    rw [Finset.sum_eq_zero_iff_of_nonpos aux] at hy
    by_contra! hi'
    have : c i * f (v i) < 0 := mul_neg_of_neg_of_pos hi' (hp i)
    grind
  exact fun i hi ↦ le_antisymm (hx i hi) (hy i hi)
