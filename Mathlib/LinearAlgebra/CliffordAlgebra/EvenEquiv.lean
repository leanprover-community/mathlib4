/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.CliffordAlgebra.Even
import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.Tactic.LiftLets

#align_import linear_algebra.clifford_algebra.even_equiv from "leanprover-community/mathlib"@"2196ab363eb097c008d4497125e0dde23fb36db2"

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


namespace CliffordAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

/-! ### Constructions needed for `CliffordAlgebra.equivEven` -/


namespace EquivEven

/-- The quadratic form on the augmented vector space `M × R` sending `v + r•e0` to `Q v - r^2`. -/
abbrev Q' : QuadraticForm R (M × R) :=
  Q.prod <| -@QuadraticForm.sq R _
set_option linter.uppercaseLean3 false in
#align clifford_algebra.equiv_even.Q' CliffordAlgebra.EquivEven.Q'

theorem Q'_apply (m : M × R) : Q' Q m = Q m.1 - m.2 * m.2 :=
  (sub_eq_add_neg _ _).symm
set_option linter.uppercaseLean3 false in
#align clifford_algebra.equiv_even.Q'_apply CliffordAlgebra.EquivEven.Q'_apply

/-- The unit vector in the new dimension -/
def e0 : CliffordAlgebra (Q' Q) :=
  ι (Q' Q) (0, 1)
#align clifford_algebra.equiv_even.e0 CliffordAlgebra.EquivEven.e0

/-- The embedding from the existing vector space -/
def v : M →ₗ[R] CliffordAlgebra (Q' Q) :=
  ι (Q' Q) ∘ₗ LinearMap.inl _ _ _
#align clifford_algebra.equiv_even.v CliffordAlgebra.EquivEven.v

theorem ι_eq_v_add_smul_e0 (m : M) (r : R) : ι (Q' Q) (m, r) = v Q m + r • e0 Q := by
  rw [e0, v, LinearMap.comp_apply, LinearMap.inl_apply, ← LinearMap.map_smul, Prod.smul_mk,
    smul_zero, smul_eq_mul, mul_one, ← LinearMap.map_add, Prod.mk_add_mk, zero_add, add_zero]
#align clifford_algebra.equiv_even.ι_eq_v_add_smul_e0 CliffordAlgebra.EquivEven.ι_eq_v_add_smul_e0

theorem e0_mul_e0 : e0 Q * e0 Q = -1 :=
  (ι_sq_scalar _ _).trans <| by simp
#align clifford_algebra.equiv_even.e0_mul_e0 CliffordAlgebra.EquivEven.e0_mul_e0

theorem v_sq_scalar (m : M) : v Q m * v Q m = algebraMap _ _ (Q m) :=
  (ι_sq_scalar _ _).trans <| by simp
#align clifford_algebra.equiv_even.v_sq_scalar CliffordAlgebra.EquivEven.v_sq_scalar

theorem neg_e0_mul_v (m : M) : -(e0 Q * v Q m) = v Q m * e0 Q := by
  refine neg_eq_of_add_eq_zero_right ((ι_mul_ι_add_swap _ _).trans ?_)
  dsimp [QuadraticForm.polar]
  simp only [add_zero, mul_zero, mul_one, zero_add, neg_zero, QuadraticForm.map_zero,
    add_sub_cancel_right, sub_self, map_zero, zero_sub]
#align clifford_algebra.equiv_even.neg_e0_mul_v CliffordAlgebra.EquivEven.neg_e0_mul_v

theorem neg_v_mul_e0 (m : M) : -(v Q m * e0 Q) = e0 Q * v Q m := by
  rw [neg_eq_iff_eq_neg]
  exact (neg_e0_mul_v _ m).symm
#align clifford_algebra.equiv_even.neg_v_mul_e0 CliffordAlgebra.EquivEven.neg_v_mul_e0

@[simp]
theorem e0_mul_v_mul_e0 (m : M) : e0 Q * v Q m * e0 Q = v Q m := by
  rw [← neg_v_mul_e0, ← neg_mul, mul_assoc, e0_mul_e0, mul_neg_one, neg_neg]
#align clifford_algebra.equiv_even.e0_mul_v_mul_e0 CliffordAlgebra.EquivEven.e0_mul_v_mul_e0

@[simp]
theorem reverse_v (m : M) : reverse (Q := Q' Q) (v Q m) = v Q m :=
  reverse_ι _
#align clifford_algebra.equiv_even.reverse_v CliffordAlgebra.EquivEven.reverse_v

@[simp]
theorem involute_v (m : M) : involute (v Q m) = -v Q m :=
  involute_ι _
#align clifford_algebra.equiv_even.involute_v CliffordAlgebra.EquivEven.involute_v

@[simp]
theorem reverse_e0 : reverse (Q := Q' Q) (e0 Q) = e0 Q :=
  reverse_ι _
#align clifford_algebra.equiv_even.reverse_e0 CliffordAlgebra.EquivEven.reverse_e0

@[simp]
theorem involute_e0 : involute (e0 Q) = -e0 Q :=
  involute_ι _
#align clifford_algebra.equiv_even.involute_e0 CliffordAlgebra.EquivEven.involute_e0

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
    rw [Subalgebra.coe_mul]  -- Porting note: was part of the `dsimp only` below
    erw [LinearMap.codRestrict_apply] -- Porting note: was part of the `dsimp only` below
    dsimp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, Subalgebra.coe_algebraMap]
    rw [← mul_assoc, e0_mul_v_mul_e0, v_sq_scalar]
#align clifford_algebra.to_even CliffordAlgebra.toEven

theorem toEven_ι (m : M) : (toEven Q (ι Q m) : CliffordAlgebra (Q' Q)) = e0 Q * v Q m := by
  rw [toEven, CliffordAlgebra.lift_ι_apply]
  -- Porting note (#10691): was `rw`
  erw [LinearMap.codRestrict_apply]
  rw [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply]
#align clifford_algebra.to_even_ι CliffordAlgebra.toEven_ι

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
    rw [ι_sq_scalar, ← RingHom.map_mul, ← RingHom.map_sub, sub_eq_add_neg, Q'_apply, sub_eq_add_neg]
  refine even.lift (Q' Q) ⟨f, ?_, ?_⟩ <;> simp_rw [f_apply]
  · intro m
    rw [← (hc _ _).symm.mul_self_sub_mul_self_eq, hm]
  · intro m₁ m₂ m₃
    rw [← mul_smul_comm, ← mul_assoc, mul_assoc (_ + _), ← (hc _ _).symm.mul_self_sub_mul_self_eq',
      Algebra.smul_def, ← mul_assoc, hm]
#align clifford_algebra.of_even CliffordAlgebra.ofEven

theorem ofEven_ι (x y : M × R) :
    ofEven Q ((even.ι (Q' Q)).bilin x y) =
      (ι Q x.1 + algebraMap R _ x.2) * (ι Q y.1 - algebraMap R _ y.2) := by
  -- Porting note: entire proof was the term-mode `even.lift_ι (Q' Q) _ x y`
  unfold ofEven
  lift_lets
  intro f
  -- TODO: replacing `?_` with `_` takes way longer?
  exact @even.lift_ι R (M × R) _ _ _ (Q' Q) _ _ _ ⟨f, ?_, ?_⟩ x y
#align clifford_algebra.of_even_ι CliffordAlgebra.ofEven_ι

theorem toEven_comp_ofEven : (toEven Q).comp (ofEven Q) = AlgHom.id R _ :=
  even.algHom_ext (Q' Q) <|
    EvenHom.ext _ _ <|
      LinearMap.ext fun m₁ =>
        LinearMap.ext fun m₂ =>
          Subtype.ext <|
            let ⟨m₁, r₁⟩ := m₁
            let ⟨m₂, r₂⟩ := m₂
            calc
              ↑(toEven Q (ofEven Q ((even.ι (Q' Q)).bilin (m₁, r₁) (m₂, r₂)))) =
                  (e0 Q * v Q m₁ + algebraMap R _ r₁) * (e0 Q * v Q m₂ - algebraMap R _ r₂) := by
                rw [ofEven_ι, AlgHom.map_mul, AlgHom.map_add, AlgHom.map_sub, AlgHom.commutes,
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
                  rw [Algebra.algebraMap_eq_smul_one, smul_mul_smul, e0_mul_e0, smul_neg]
                rw [sub_eq_add_neg, sub_eq_add_neg, h1, h2, h3]
              _ = ι (Q' Q) (m₁, r₁) * ι (Q' Q) (m₂, r₂) := by
                rw [ι_eq_v_add_smul_e0, ι_eq_v_add_smul_e0, mul_add, add_mul, add_mul, add_assoc]
#align clifford_algebra.to_even_comp_of_even CliffordAlgebra.toEven_comp_ofEven

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
#align clifford_algebra.of_even_comp_to_even CliffordAlgebra.ofEven_comp_toEven

/-- Any clifford algebra is isomorphic to the even subalgebra of a clifford algebra with an extra
dimension (that is, with vector space `M × R`), with a quadratic form evaluating to `-1` on that new
basis vector. -/
def equivEven : CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra.even (Q' Q) :=
  AlgEquiv.ofAlgHom (toEven Q) (ofEven Q) (toEven_comp_ofEven Q) (ofEven_comp_toEven Q)
#align clifford_algebra.equiv_even CliffordAlgebra.equivEven

/-- The representation of the clifford conjugate (i.e. the reverse of the involute) in the even
subalgebra is just the reverse of the representation. -/
theorem coe_toEven_reverse_involute (x : CliffordAlgebra Q) :
    ↑(toEven Q (reverse (involute x))) =
      reverse (Q := Q' Q) (toEven Q x : CliffordAlgebra (Q' Q)) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp only [AlgHom.commutes, Subalgebra.coe_algebraMap, reverse.commutes]
  | ι m =>
    -- Porting note: added `letI`
    letI : SubtractionMonoid (even (Q' Q)) := AddGroup.toSubtractionMonoid
    simp only [involute_ι, Subalgebra.coe_neg, toEven_ι, reverse.map_mul, reverse_v, reverse_e0,
      reverse_ι, neg_e0_mul_v, map_neg]
  | mul x y hx hy => simp only [map_mul, Subalgebra.coe_mul, reverse.map_mul, hx, hy]
  | add x y hx hy => simp only [map_add, Subalgebra.coe_add, hx, hy]
#align clifford_algebra.coe_to_even_reverse_involute CliffordAlgebra.coe_toEven_reverse_involute

/-! ### Constructions needed for `CliffordAlgebra.evenEquivEvenNeg` -/

/-- One direction of `CliffordAlgebra.evenEquivEvenNeg` -/
def evenToNeg (Q' : QuadraticForm R M) (h : Q' = -Q) :
    CliffordAlgebra.even Q →ₐ[R] CliffordAlgebra.even Q' :=
  even.lift Q <|
    -- Porting note: added `letI`s
    letI : AddCommGroup (even Q') := AddSubgroupClass.toAddCommGroup _;
    letI : HasDistribNeg (even Q') := NonUnitalNonAssocRing.toHasDistribNeg;
    { bilin := -(even.ι Q' : _).bilin
      contract := fun m => by
        simp_rw [LinearMap.neg_apply, EvenHom.contract, h, QuadraticForm.neg_apply, map_neg,
          neg_neg]
      contract_mid := fun m₁ m₂ m₃ => by
        simp_rw [LinearMap.neg_apply, neg_mul_neg, EvenHom.contract_mid, h,
          QuadraticForm.neg_apply, smul_neg, neg_smul] }
#align clifford_algebra.even_to_neg CliffordAlgebra.evenToNeg

-- Porting note: `simpNF` times out, but only in CI where all of `Mathlib` is imported
@[simp, nolint simpNF]
theorem evenToNeg_ι (Q' : QuadraticForm R M) (h : Q' = -Q) (m₁ m₂ : M) :
    evenToNeg Q Q' h ((even.ι Q).bilin m₁ m₂) = -(even.ι Q').bilin m₁ m₂ :=
  even.lift_ι _ _ m₁ m₂
#align clifford_algebra.even_to_neg_ι CliffordAlgebra.evenToNeg_ι

theorem evenToNeg_comp_evenToNeg (Q' : QuadraticForm R M) (h : Q' = -Q) (h' : Q = -Q') :
    (evenToNeg Q' Q h').comp (evenToNeg Q Q' h) = AlgHom.id R _ := by
  ext m₁ m₂ : 4
  dsimp only [EvenHom.compr₂_bilin, LinearMap.compr₂_apply, AlgHom.toLinearMap_apply,
    AlgHom.comp_apply, AlgHom.id_apply]
  rw [evenToNeg_ι]
  -- Needed to use `RingHom.map_neg` to avoid a timeout and now `erw` #8386
  erw [RingHom.map_neg, evenToNeg_ι, neg_neg]
#align clifford_algebra.even_to_neg_comp_even_to_neg CliffordAlgebra.evenToNeg_comp_evenToNeg

/-- The even subalgebras of the algebras with quadratic form `Q` and `-Q` are isomorphic.

Stated another way, `𝒞ℓ⁺(p,q,r)` and `𝒞ℓ⁺(q,p,r)` are isomorphic. -/
@[simps!]
def evenEquivEvenNeg : CliffordAlgebra.even Q ≃ₐ[R] CliffordAlgebra.even (-Q) :=
  AlgEquiv.ofAlgHom (evenToNeg Q _ rfl) (evenToNeg (-Q) _ (neg_neg _).symm)
    (evenToNeg_comp_evenToNeg _ _ _ _) (evenToNeg_comp_evenToNeg _ _ _ _)
#align clifford_algebra.even_equiv_even_neg CliffordAlgebra.evenEquivEvenNeg

-- Note: times out on linting CI
attribute [nolint simpNF] evenEquivEvenNeg_apply evenEquivEvenNeg_symm_apply

end CliffordAlgebra
