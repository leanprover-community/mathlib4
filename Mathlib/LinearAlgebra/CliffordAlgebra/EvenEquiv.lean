/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.CliffordAlgebra.Even
public import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# Isomorphisms with the even subalgebra of a Clifford algebra

This file provides some notable isomorphisms regarding the even subalgebra, `CliffordAlgebra.even`.

## Main definitions

* `CliffordAlgebra.equivEven`: Every Clifford algebra is isomorphic as an algebra to the even
  subalgebra of a Clifford algebra with one more dimension.
  * `CliffordAlgebra.EquivEven.Q'`: The quadratic form used by this "one-up" algebra.
  * `CliffordAlgebra.toEven`: The simp-normal form of the forward direction of this isomorphism.
  * `CliffordAlgebra.ofEven`: The simp-normal form of the reverse direction of this isomorphism.

* `CliffordAlgebra.evenEquivEvenNeg`: Every even subalgebra is isomorphic to the even subalgebra
  of the Clifford algebra with negated quadratic form.
  * `CliffordAlgebra.evenToNeg`: The simp-normal form of each direction of this isomorphism.

## Main results

* `CliffordAlgebra.coe_toEven_reverse_involute`: the behavior of `CliffordAlgebra.toEven` on the
  "Clifford conjugate", that is `CliffordAlgebra.reverse` composed with
  `CliffordAlgebra.involute`.
-/

@[expose] public section


namespace CliffordAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

/-! ### Constructions needed for `CliffordAlgebra.equivEven` -/


namespace EquivEven

/-- The quadratic form on the augmented vector space `M × R` sending `v + r•e0` to `Q v - r^2`. -/
abbrev Q' : QuadraticForm R (M × R) :=
  Q.prod <| -QuadraticMap.sq (R := R)

theorem Q'_apply (m : M × R) : Q' Q m = Q m.1 - m.2 * m.2 :=
  (sub_eq_add_neg _ _).symm

/-- The unit vector in the new dimension -/
def e0 : CliffordAlgebra (Q' Q) :=
  ι (Q' Q) (0, 1)

/-- The embedding from the existing vector space -/
def v : M →ₗ[R] CliffordAlgebra (Q' Q) :=
  ι (Q' Q) ∘ₗ LinearMap.inl _ _ _

theorem ι_eq_v_add_smul_e0 (m : M) (r : R) : ι (Q' Q) (m, r) = v Q m + r • e0 Q := by
  rw [e0, v, LinearMap.comp_apply, LinearMap.inl_apply, ← map_smul, Prod.smul_mk,
    smul_zero, smul_eq_mul, mul_one, ← map_add, Prod.mk_add_mk, zero_add, add_zero]

theorem e0_mul_e0 : e0 Q * e0 Q = -1 :=
  (ι_sq_scalar _ _).trans <| by simp

theorem v_sq_scalar (m : M) : v Q m * v Q m = algebraMap _ _ (Q m) :=
  (ι_sq_scalar _ _).trans <| by simp

theorem neg_e0_mul_v (m : M) : -(e0 Q * v Q m) = v Q m * e0 Q := by
  refine neg_eq_of_add_eq_zero_right ((ι_mul_ι_add_swap _ _).trans ?_)
  dsimp [QuadraticMap.polar]
  simp only [add_zero, mul_zero, mul_one, zero_add, neg_zero,
    add_sub_cancel_right, sub_self, map_zero]

theorem neg_v_mul_e0 (m : M) : -(v Q m * e0 Q) = e0 Q * v Q m := by
  rw [neg_eq_iff_eq_neg]
  exact (neg_e0_mul_v _ m).symm

@[simp]
theorem e0_mul_v_mul_e0 (m : M) : e0 Q * v Q m * e0 Q = v Q m := by
  rw [← neg_v_mul_e0, ← neg_mul, mul_assoc, e0_mul_e0, mul_neg_one, neg_neg]

@[simp]
theorem reverse_v (m : M) : reverse (Q := Q' Q) (v Q m) = v Q m :=
  reverse_ι _

@[simp]
theorem involute_v (m : M) : involute (v Q m) = -v Q m :=
  involute_ι _

@[simp]
theorem reverse_e0 : reverse (Q := Q' Q) (e0 Q) = e0 Q :=
  reverse_ι _

@[simp]
theorem involute_e0 : involute (e0 Q) = -e0 Q :=
  involute_ι _

end EquivEven

open EquivEven

/-- The embedding from the smaller algebra into the new larger one. -/
def toEven : CliffordAlgebra Q →ₐ[R] CliffordAlgebra.even (Q' Q) := by
  refine CliffordAlgebra.lift Q ⟨?_, fun m => ?_⟩
  · refine LinearMap.codRestrict _ ?_ fun m => Submodule.mem_iSup_of_mem ⟨2, rfl⟩ ?_
    · exact (LinearMap.mulLeft R <| e0 Q).comp (v Q)
    rw [Subtype.coe_mk, pow_two]
    exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)
  · ext1
    simp only [Subalgebra.coe_mul, ← even_toSubmodule]
    rw [LinearMap.codRestrict_apply]
    simp [← mul_assoc, v_sq_scalar]

theorem toEven_ι (m : M) : (toEven Q (ι Q m) : CliffordAlgebra (Q' Q)) = e0 Q * v Q m := by
  simp only [toEven, CliffordAlgebra.lift_ι_apply, ← even_toSubmodule]
  rw [LinearMap.codRestrict_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply]

/-- The embedding from the even subalgebra with an extra dimension into the original algebra. -/
def ofEven : CliffordAlgebra.even (Q' Q) →ₐ[R] CliffordAlgebra Q := by
  /-
    Recall that we need:
     * `f ⟨0,1⟩ ⟨x,0⟩ = ι x`
     * `f ⟨x,0⟩ ⟨0,1⟩ = -ι x`
     * `f ⟨x,0⟩ ⟨y,0⟩ = ι x * ι y`
     * `f ⟨0,1⟩ ⟨0,1⟩ = -1`
    -/
  let f : M × R →ₗ[R] M × R →ₗ[R] CliffordAlgebra Q :=
    ((Algebra.lmul R (CliffordAlgebra Q)).toLinearMap.comp <|
          (ι Q).comp (LinearMap.fst _ _ _) +
            (Algebra.linearMap R _).comp (LinearMap.snd _ _ _)).compl₂
      ((ι Q).comp (LinearMap.fst _ _ _) - (Algebra.linearMap R _).comp (LinearMap.snd _ _ _))
  haveI f_apply : ∀ x y, f x y = (ι Q x.1 + algebraMap R _ x.2) * (ι Q y.1 - algebraMap R _ y.2) :=
    fun x y => by rfl
  haveI hc : ∀ (r : R) (x : CliffordAlgebra Q), Commute (algebraMap _ _ r) x := Algebra.commutes
  haveI hm :
    ∀ m : M × R,
      ι Q m.1 * ι Q m.1 - algebraMap R _ m.2 * algebraMap R _ m.2 = algebraMap R _ (Q' Q m) := by
    intro m
    rw [ι_sq_scalar, ← map_mul, ← map_sub, sub_eq_add_neg, Q'_apply, sub_eq_add_neg]
  refine even.lift (Q' Q) ⟨f, ?_, ?_⟩ <;> simp_rw [f_apply]
  · intro m
    rw [← (hc _ _).symm.mul_self_sub_mul_self_eq, hm]
  · intro m₁ m₂ m₃
    rw [← mul_smul_comm, ← mul_assoc, mul_assoc (_ + _), ← (hc _ _).symm.mul_self_sub_mul_self_eq',
      Algebra.smul_def, ← mul_assoc, hm]

theorem ofEven_ι (x y : M × R) :
    ofEven Q ((even.ι (Q' Q)).bilin x y) =
      (ι Q x.1 + algebraMap R _ x.2) * (ι Q y.1 - algebraMap R _ y.2) :=
  even.lift_ι (Q' Q) _ x y

theorem toEven_comp_ofEven : (toEven Q).comp (ofEven Q) = AlgHom.id R _ :=
  even.algHom_ext (Q' Q) <|
    EvenHom.ext <|
      LinearMap.ext fun m₁ =>
        LinearMap.ext fun m₂ =>
          Subtype.ext <|
            let ⟨m₁, r₁⟩ := m₁
            let ⟨m₂, r₂⟩ := m₂
            calc
              ↑(toEven Q (ofEven Q ((even.ι (Q' Q)).bilin (m₁, r₁) (m₂, r₂)))) =
                  (e0 Q * v Q m₁ + algebraMap R _ r₁) * (e0 Q * v Q m₂ - algebraMap R _ r₂) := by
                rw [ofEven_ι, map_mul, map_add, map_sub, AlgHom.commutes,
                  AlgHom.commutes, Subalgebra.coe_mul, Subalgebra.coe_add, Subalgebra.coe_sub,
                  toEven_ι, toEven_ι, Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap]
              _ =
                  e0 Q * v Q m₁ * (e0 Q * v Q m₂) + r₁ • e0 Q * v Q m₂ - r₂ • e0 Q * v Q m₁ -
                    algebraMap R _ (r₁ * r₂) := by
                rw [mul_sub, add_mul, add_mul, ← Algebra.commutes, ← Algebra.smul_def, ← map_mul, ←
                  Algebra.smul_def, sub_add_eq_sub_sub, smul_mul_assoc, smul_mul_assoc]
              _ =
                  v Q m₁ * v Q m₂ + r₁ • e0 Q * v Q m₂ + v Q m₁ * r₂ • e0 Q +
                    r₁ • e0 Q * r₂ • e0 Q := by
                have h1 : e0 Q * v Q m₁ * (e0 Q * v Q m₂) = v Q m₁ * v Q m₂ := by
                  rw [← mul_assoc, e0_mul_v_mul_e0]
                have h2 : -(r₂ • e0 Q * v Q m₁) = v Q m₁ * r₂ • e0 Q := by
                  rw [mul_smul_comm, smul_mul_assoc, ← smul_neg, neg_e0_mul_v]
                have h3 : -algebraMap R _ (r₁ * r₂) = r₁ • e0 Q * r₂ • e0 Q := by
                  rw [Algebra.algebraMap_eq_smul_one, smul_mul_smul_comm, e0_mul_e0, smul_neg]
                rw [sub_eq_add_neg, sub_eq_add_neg, h1, h2, h3]
              _ = ι (Q' Q) (m₁, r₁) * ι (Q' Q) (m₂, r₂) := by
                rw [ι_eq_v_add_smul_e0, ι_eq_v_add_smul_e0, mul_add, add_mul, add_mul, add_assoc]

theorem ofEven_comp_toEven : (ofEven Q).comp (toEven Q) = AlgHom.id R _ :=
  CliffordAlgebra.hom_ext <|
    LinearMap.ext fun m =>
      calc
        ofEven Q (toEven Q (ι Q m)) = ofEven Q ⟨_, (toEven Q (ι Q m)).prop⟩ := by
          rw [Subtype.coe_eta]
        _ = (ι Q 0 + algebraMap R _ 1) * (ι Q m - algebraMap R _ 0) := by
          simp_rw [toEven_ι]
          exact ofEven_ι Q _ _
        _ = ι Q m := by rw [map_one, map_zero, map_zero, sub_zero, zero_add, one_mul]

/-- Any clifford algebra is isomorphic to the even subalgebra of a clifford algebra with an extra
dimension (that is, with vector space `M × R`), with a quadratic form evaluating to `-1` on that new
basis vector. -/
def equivEven : CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra.even (Q' Q) :=
  AlgEquiv.ofAlgHom (toEven Q) (ofEven Q) (toEven_comp_ofEven Q) (ofEven_comp_toEven Q)

/-- The representation of the clifford conjugate (i.e. the reverse of the involute) in the even
subalgebra is just the reverse of the representation. -/
theorem coe_toEven_reverse_involute (x : CliffordAlgebra Q) :
    ↑(toEven Q (reverse (involute x))) =
      reverse (Q := Q' Q) (toEven Q x : CliffordAlgebra (Q' Q)) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp only [AlgHom.commutes, Subalgebra.coe_algebraMap, reverse.commutes]
  | ι m =>
    simp only [involute_ι, Subalgebra.coe_neg, toEven_ι, reverse.map_mul, reverse_v, reverse_e0,
      reverse_ι, neg_e0_mul_v, map_neg]
  | mul x y hx hy => simp only [map_mul, Subalgebra.coe_mul, reverse.map_mul, hx, hy]
  | add x y hx hy => simp only [map_add, Subalgebra.coe_add, hx, hy]

/-! ### Constructions needed for `CliffordAlgebra.evenEquivEvenNeg` -/

/-- One direction of `CliffordAlgebra.evenEquivEvenNeg` -/
def evenToNeg (Q' : QuadraticForm R M) (h : Q' = -Q) :
    CliffordAlgebra.even Q →ₐ[R] CliffordAlgebra.even Q' :=
  even.lift Q <|
    { bilin := -(even.ι Q' :).bilin
      contract := fun m => by
        simp_rw [LinearMap.neg_apply, EvenHom.contract, h, QuadraticMap.neg_apply, map_neg, neg_neg]
      contract_mid := fun m₁ m₂ m₃ => by
        simp_rw [LinearMap.neg_apply, neg_mul_neg, EvenHom.contract_mid, h,
          QuadraticMap.neg_apply, smul_neg, neg_smul] }

@[simp]
theorem evenToNeg_ι (Q' : QuadraticForm R M) (h : Q' = -Q) (m₁ m₂ : M) :
    evenToNeg Q Q' h ((even.ι Q).bilin m₁ m₂) = -(even.ι Q').bilin m₁ m₂ :=
  even.lift_ι _ _ m₁ m₂

theorem evenToNeg_comp_evenToNeg (Q' : QuadraticForm R M) (h : Q' = -Q) (h' : Q = -Q') :
    (evenToNeg Q' Q h').comp (evenToNeg Q Q' h) = AlgHom.id R _ := by
  ext m₁ m₂ : 4
  simp [evenToNeg_ι]

/-- The even subalgebras of the algebras with quadratic form `Q` and `-Q` are isomorphic.

Stated another way, `𝒞ℓ⁺(p,q,r)` and `𝒞ℓ⁺(q,p,r)` are isomorphic. -/
@[simps!]
def evenEquivEvenNeg : CliffordAlgebra.even Q ≃ₐ[R] CliffordAlgebra.even (-Q) :=
  AlgEquiv.ofAlgHom (evenToNeg Q _ rfl) (evenToNeg (-Q) _ (neg_neg _).symm)
    (evenToNeg_comp_evenToNeg _ _ _ _) (evenToNeg_comp_evenToNeg _ _ _ _)

end CliffordAlgebra
