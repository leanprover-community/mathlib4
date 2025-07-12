/-
Copyright (c) 2026 Attila Gáspár. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Attila Gáspár
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import Mathlib.RingTheory.Finiteness.Defs

import Mathlib.Algebra.Module.Submodule.EqLocus
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.Tactic.Module

/-!
# Homogenization of an affine space

The homogenization (or vector hull) of an affine space `P` is a vector space together with an
embedding of `P` as a hyperplane not passing through the origin. This construction has the universal
property that every affine map defined on this hyperplane that takes values in a vector space can be
uniquely extended to a linear map defined on the homogenization.

Note that the homogenization is isomorphic to `k × V`, where `k` is the field of scalars and `V` is
the vector space associated to `P`. However, this isomorphism is not canonical unless `P = V`
(see `Homogenization.toProd` in this case).

## Main definitions

* `Homogenization k P`: the homogenization of the affine space `P` over the ring `k`.
* `Homogenization.ofPoint`: the canonical embedding of the affine space.
* `Homogenization.ofVector`: the canonical embedding of the vector space.
* `Homogenization.lift f`: the linear map obtained by extending the affine map `f` taking values in
  a vector space.

## References

* [J. Gallier, *Geometric Methods and Applications for Computer Science and
  Engineering*][Gallier2011GeometricMethods]
* [X. Gràcia, R. Martín, *Vector Hulls of Affine Spaces and Affine Bundles*][Gracia2008]
-/

public section

/-- Given an affine space `P` over `k`, `Homogenization k P` is a vector space containing `P` as a
hyperplane that does not pass through the origin.

Values of type `Homogenization k P` can be constructed as linear combinations of
`Homogenization.ofPoint` and `Homogenization.ofVector`. To define a linear map on
`Homogenization k P`, use `Homogenization.lift`. -/
/- To simplify the implementation, we define the homogenization as `V × k`, with the element
`(v, c)` representing `ofVector v + c • ofPoint (Classical.arbitrary P)`. -/
@[nolint unusedArguments]
def Homogenization
    (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P] :=
  V × k

variable
  {k : Type*} [Ring k]
  {V P : Type*} [AddCommGroup V] [Module k V] [AddTorsor V P]
  {V1 P1 : Type*} [AddCommGroup V1] [Module k V1] [AddTorsor V1 P1]
  {V2 P2 : Type*} [AddCommGroup V2] [Module k V2] [AddTorsor V2 P2]
  {V3 P3 : Type*} [AddCommGroup V3] [Module k V3] [AddTorsor V3 P3]
  {W : Type*} [AddCommGroup W] [Module k W]

namespace Homogenization

section SMul

variable
  {R : Type*} [Semiring R] [Module R k] [Module R V] [IsScalarTower R k V]
  {S : Type*} [Semiring S] [Module S k] [Module S V] [IsScalarTower S k V]
  [SMul R S] [IsScalarTower R S k] [IsScalarTower R S V]

/- The `[IsScalarTower R k V]` assumption implies that this instance does not depend on the
arbitrary choice made in the definition of `Homogenization`. -/
@[nolint unusedArguments]
noncomputable instance instSMul [IsScalarTower R k V] : SMul R (Homogenization k P) :=
  inferInstanceAs (SMul R (V × k))

noncomputable instance : AddCommGroup (Homogenization k P) where
  __ : AddCommGroup (Homogenization k P) := inferInstanceAs (AddCommGroup (V × k))
  nsmul := instSMul.smul
  zsmul := instSMul.smul

noncomputable instance : Module R (Homogenization k P) :=
  inferInstanceAs (Module R (V × k))

noncomputable instance : IsScalarTower R S (Homogenization k P) :=
  inferInstanceAs (IsScalarTower R S (V × k))

end SMul

/-- The embedding of the affine space into the homogenization. -/
noncomputable def ofPoint : P →ᵃ[k] Homogenization k P :=
  .prod (AffineEquiv.vaddConst k (Classical.arbitrary P)).symm (.const k P (1 : k))

/-- The embedding of the vector space into the homogenization. -/
@[expose]
noncomputable def ofVector : V →ₗ[k] Homogenization k P :=
  ofPoint.linear

@[simp]
theorem ofPoint_linear : ofPoint.linear = ofVector (k := k) (P := P) :=
  rfl

@[simp]
theorem ofVector_vsub {p q : P} : ofVector (k := k) (p -ᵥ q) = ofPoint p - ofPoint q :=
  ofPoint.linearMap_vsub p q

@[simp]
theorem ofVector_smul {R : Type*} [Semiring R] [Module R k] [Module R V] [IsScalarTower R k V]
    {r : R} {v : V} : ofVector (r • v) = r • ofVector (k := k) (P := P) v :=
  Prod.ext rfl (smul_zero r).symm

theorem ofVector_injective : Function.Injective (ofVector (k := k) (P := P)) :=
  (injective_iff_map_eq_zero _).mpr fun _ h => congr($h.1)

theorem ofPoint_injective : Function.Injective (ofPoint (k := k) (P := P)) :=
  ofPoint.linear_injective_iff.mp ofVector_injective

/-- Every element of the homogenization can be written in the form `ofVector v + c • ofPoint p`.

See also `induction_of_point` and `ofVector_ofPoint_cases`. -/
@[induction_eliminator, cases_eliminator]
theorem induction_on {C : Homogenization k P → Prop} (x : Homogenization k P)
    (h : ∀ (v : V) (c : k) (p : P), C (ofVector v + c • ofPoint p)) : C x := by
  specialize h x.1 x.2 (Classical.arbitrary P)
  change C (x.1 + x.2 • (Classical.arbitrary P -ᵥ Classical.arbitrary P), 0 + x.2 * 1) at h
  simpa using h

/-- Every element of the homogenization can be written in the form `ofVector v + c • ofPoint p`,
where `p` can be chosen arbitrarily. -/
theorem induction_of_point {C : Homogenization k P → Prop} (p : P) (x : Homogenization k P)
    (h : ∀ (v : V) (c : k), C (ofVector v + c • ofPoint p)) : C x := by
  cases x with | _ v c q =>
  convert h (v - c • (p -ᵥ q)) c using 1
  simp only [map_sub, map_smul, ofVector_vsub]
  match_scalars <;> norm_num

/-- Over a division ring `k`, every element of `Homogenization k P` is either a nonzero multiple of
a point of `P`, or an element of the vector space associated to `P`. -/
theorem ofVector_ofPoint_cases {k V P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
    [AddTorsor V P] (x : Homogenization k P) {C : Homogenization k P → Prop}
    (smul_ofPoint : ∀ (c : k) p, c ≠ 0 → C (c • ofPoint p)) (ofVector : ∀ v, C (ofVector v)) :
    C x := by
  cases x with | _ v c p =>
  rcases eq_or_ne c 0 with rfl | hc
  · simpa using ofVector v
  · convert smul_ofPoint c (c⁻¹ • v +ᵥ p) hc using 1
    rw [AffineMap.map_vadd, ofPoint_linear, vadd_eq_add, smul_add, map_smul, smul_inv_smul₀ hc]

theorem span_range_ofPoint : Submodule.span k (Set.range (ofPoint (k := k) (P := P))) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun x => ?_
  cases x with | _ v c p
  rw [← vadd_vsub v p, ofVector_vsub]
  refine Submodule.add_mem _ (Submodule.sub_mem _ ?_ ?_) (Submodule.smul_mem _ _ ?_) <;>
    exact Submodule.mem_span_of_mem <| Set.mem_range_self _

theorem hom_ext {f g : Homogenization k P1 →ₗ[k] W}
    (h : ∀ x, f (ofPoint x) = g (ofPoint x)) : f = g := by
  rwa [← LinearMap.eqLocus_eq_top, eq_top_iff, ← span_range_ofPoint, Submodule.span_le,
    Set.range_subset_iff]

theorem hom_ext_iff {f g : Homogenization k P1 →ₗ[k] W} :
    f = g ↔ ∀ x, f (ofPoint x) = g (ofPoint x) :=
  ⟨by rintro rfl _; rfl, hom_ext⟩

/-- The linear map that is constantly `1` when restricted to `P`. -/
noncomputable def weight : Homogenization k P →ₗ[k] k :=
  .snd ..

@[simp]
theorem weight_ofVector {v : V} : weight (k := k) (P := P) (ofVector v) = 0 :=
  (rfl)

@[simp]
theorem weight_ofPoint {p : P} : weight (k := k) (ofPoint p) = 1 :=
  (rfl)

theorem weight_eq_zero_iff {x : Homogenization k P} : weight x = 0 ↔ ∃ v, x = ofVector v where
  mp := by cases x; simp_all
  mpr := by rintro ⟨_, rfl⟩; rw [weight_ofVector]

theorem weight_eq_one_iff {x : Homogenization k P} : weight x = 1 ↔ ∃ p, x = ofPoint p where
  mp h := by
    cases x with | _ v c p =>
    exists v +ᵥ p
    simp_all
  mpr := by rintro ⟨_, rfl⟩; rw [weight_ofPoint]

/-- Auxiliary definition used for defining `Homogenization.lift`. -/
noncomputable def lift.aux (f : P →ᵃ[k] W) : Homogenization k P →ₗ[k] W :=
  f.linear.coprod <| LinearMap.id.smulRight (f (Classical.arbitrary P))

@[simp]
private theorem lift.aux_ofPoint {f : P →ᵃ[k] W} {p : P} : aux f (ofPoint p) = f p := by
  change f.linear (p -ᵥ Classical.arbitrary P) + (1 : k) • f (Classical.arbitrary P) = f p
  simp

/-- An affine map on `P` taking values in a vector space extends uniquely to a linear map on
`Homogenization k P`.

See also `Homogenization.liftₗ` for a version that is linear over some ring. -/
@[expose]
noncomputable def lift : (P →ᵃ[k] W) ≃+ (Homogenization k P →ₗ[k] W) where
  toFun := lift.aux
  invFun f := f.toAffineMap.comp ofPoint
  left_inv f := by ext; simp
  right_inv f := hom_ext <| by simp
  map_add' f g := hom_ext <| by simp

@[simp]
theorem lift_apply_ofPoint {f : P →ᵃ[k] W} {p : P} : lift f (ofPoint p) = f p := by
  simp [lift]

@[simp]
theorem lift_apply_ofVector {f : P →ᵃ[k] W} {v : V} : lift f (ofVector v) = f.linear v := by
  obtain ⟨p⟩ : Nonempty P := inferInstance
  nth_rw 1 [← vadd_vsub v p]
  simp_rw [ofVector_vsub, map_sub, lift_apply_ofPoint, AffineMap.map_vadd, vadd_eq_add,
    add_sub_cancel_right]

@[simp]
theorem lift_symm_apply {f : Homogenization k P →ₗ[k] W} {p : P} : lift.symm f p = f (ofPoint p) :=
  rfl

@[simp]
theorem lift_symm_linear_apply {f : Homogenization k P →ₗ[k] W} {v : V} :
    (lift.symm f).linear v = f (ofVector v) :=
  rfl

theorem lift_symm_id : lift.symm LinearMap.id = ofPoint (k := k) (P := P) :=
  rfl

theorem lift_ofPoint : lift (k := k) (P := P) ofPoint = LinearMap.id :=
  hom_ext <| by simp

theorem lift_const_apply {u : W} {x : Homogenization k P} :
    lift (AffineMap.const k P u) x = weight x • u := by
  cases x; simp

section SMul

variable {R : Type*} [Semiring R] [Module R W] [SMulCommClass k R W]

@[simp]
theorem lift_smul {f : P →ᵃ[k] W} {c : R} : lift (c • f) = c • lift f :=
  hom_ext <| by simp

variable (R) in
/-- Linear version of `Homogenization.lift`. -/
@[expose]
noncomputable def liftₗ : (P →ᵃ[k] W) ≃ₗ[R] (Homogenization k P →ₗ[k] W) :=
  lift.toLinearEquiv fun _ _ => lift_smul

@[simp]
theorem coe_liftₗ : ⇑(liftₗ (k := k) (P := P) (W := W) R) = lift :=
  rfl

@[simp]
theorem coe_liftₗ_symm : ⇑(liftₗ (k := k) (P := P) (W := W) R).symm = lift.symm :=
  rfl

@[simp]
theorem lift_symm_smul {f : Homogenization k P →ₗ[k] W} {c : R} :
    lift.symm (c • f) = c • lift.symm f :=
  map_smul (liftₗ R).symm c f

end SMul

/-- An affine map between two affine spaces extends to a linear map between their homogenizations.
-/
@[expose]
noncomputable def map (f : P1 →ᵃ[k] P2) : Homogenization k P1 →ₗ[k] Homogenization k P2 :=
  lift (ofPoint.comp f)

@[simp]
theorem map_apply_ofPoint {f : P1 →ᵃ[k] P2} {p : P1} : map f (ofPoint p) = ofPoint (f p) := by
  simp [map]

@[simp]
theorem map_apply_ofVector {f : P1 →ᵃ[k] P2} {v : V1} :
    map f (ofVector v) = ofVector (f.linear v) := by
  simp [map]

@[simp]
theorem map_id : map (AffineMap.id k P) = LinearMap.id :=
  hom_ext <| by simp

theorem map_comp {f : P1 →ᵃ[k] P2} {g : P2 →ᵃ[k] P3} : map (g.comp f) = map g ∘ₗ map f :=
  hom_ext <| by simp

@[simp]
theorem weight_map {f : P1 →ᵃ[k] P2} {x : Homogenization k P1} : weight (map f x) = weight x := by
  cases x; simp

theorem lift_map {f : P1 →ᵃ[k] P2} {g : P2 →ᵃ[k] V3} {x : Homogenization k P1} :
    lift g (map f x) = lift (g.comp f) x := by
  cases x; simp

theorem map_injective {f : P1 →ᵃ[k] P2} : Function.Injective (map f) ↔ Function.Injective f where
  mp hf := by
    have h := hf.comp ofPoint_injective
    simp_rw [Function.comp_def, map_apply_ofPoint] at h
    exact h.of_comp
  mpr hf := by
    rw [injective_iff_map_eq_zero]
    intro x h
    have := congr(weight $h)
    rw [weight_map, map_zero, weight_eq_zero_iff] at this
    obtain ⟨v, rfl⟩ := this
    rw [map_apply_ofVector, map_eq_zero_iff _ ofVector_injective,
       map_eq_zero_iff _ (f.linear_injective_iff.mpr hf)] at h
    rw [h, map_zero]

theorem map_surjective {f : P1 →ᵃ[k] P2} : Function.Surjective (map f) ↔ Function.Surjective f where
  mp hf p := by
    obtain ⟨x, hx⟩ := hf (ofPoint p)
    have := congr(weight $hx)
    rw [weight_map, weight_ofPoint, weight_eq_one_iff] at this
    obtain ⟨q, rfl⟩ := this
    rw [map_apply_ofPoint] at hx
    exact ⟨q, ofPoint_injective hx⟩
  mpr hf x := by
    cases x with | _ v c p
    obtain ⟨q, rfl⟩ := hf p
    obtain ⟨u, rfl⟩ := f.linear_surjective_iff.mpr hf v
    exists ofVector u + c • ofPoint q
    simp

/-- An affine isomorphism between two affine spaces extends to a linear isomorphism between their
homogenizations. -/
@[expose]
noncomputable def congr (f : P1 ≃ᵃ[k] P2) : Homogenization k P1 ≃ₗ[k] Homogenization k P2 :=
  .ofLinear (map f) (map f.symm) (hom_ext <| by simp) (hom_ext <| by simp)

@[simp]
theorem coe_congr (f : P1 ≃ᵃ[k] P2) : ⇑(congr f) = map f.toAffineMap :=
  rfl

@[simp]
theorem toLinearMap_congr (f : P1 ≃ᵃ[k] P2) : congr f = map f.toAffineMap :=
  rfl

@[simp]
theorem congr_symm (f : P1 ≃ᵃ[k] P2) : (congr f).symm = congr f.symm :=
  rfl

@[simp]
theorem congr_refl : congr (.refl k P) = .refl .. := by
  ext; simp

theorem congr_trans (f : P1 ≃ᵃ[k] P2) (g : P2 ≃ᵃ[k] P3) :
    congr (f.trans g) = congr f ≪≫ₗ congr g := by
  ext; simp [map_comp]

/-- The homogenization of a vector space `V` over `k` is canonically isomorphic to `V × k` -/
@[expose, simps! -isSimp]
noncomputable def toProd : Homogenization k V ≃ₗ[k] V × k where
  __ := (lift (.id ..)).prod weight
  invFun x := ofVector x.1 + x.2 • ofPoint 0
  left_inv x := by
    cases x using induction_of_point (0 : V)
    simp
  right_inv x := by simp

instance [Module.Finite k V] : Module.Finite k (Homogenization k P) :=
  have ⟨x⟩ : Nonempty P := inferInstance
  .equiv (toProd.symm ≪≫ₗ congr (AffineEquiv.vaddConst k x))

end Homogenization
