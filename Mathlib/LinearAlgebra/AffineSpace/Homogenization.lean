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
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing

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

@[expose] public section

variable
  {k : Type*} [Ring k]
  {V P : Type*} [AddCommGroup V] [Module k V] [AddTorsor V P]
  {V1 P1 : Type*} [AddCommGroup V1] [Module k V1] [AddTorsor V1 P1]
  {V2 P2 : Type*} [AddCommGroup V2] [Module k V2] [AddTorsor V2 P2]
  {V3 P3 : Type*} [AddCommGroup V3] [Module k V3] [AddTorsor V3 P3]
  {W : Type*} [AddCommGroup W] [Module k W]

variable (k V P) in
/-- A formal expression representing an element of `Homogenization k P`. -/
inductive HomogenizationExpr where
  /-- The formal expression `v + c • p`. -/
  | mk (v : V) (c : k) (p : P)
  /-- The embedding of the vector space into the homogenization. This constructor is used for
  defining `Homogenization.ofVector` in a computable way. -/
  | ofVector (v : V)

/-- The equivalence relation on `HomogenizationExpr`. -/
inductive HomogenizationExpr.Equiv :
    HomogenizationExpr k V P → HomogenizationExpr k V P → Prop where
  | mk_mk {c v₁ p₁ v₂ p₂} (h : v₁ - v₂ = c • (p₂ -ᵥ p₁)) : Equiv (mk v₁ c p₁) (mk v₂ c p₂)
  | mk_ofVector {v p} : Equiv (mk v 0 p) (ofVector v)
  | ofVector_mk {v p} : Equiv (ofVector v) (mk v 0 p)
  | ofVector_ofVector {v} : Equiv (ofVector v) (ofVector v)

-- TODO: generalize and improve performance
local macro "affine" P:term : tactic => `(tactic|
  have ⟨q⟩ : Nonempty $P := inferInstance <;>
  simp +singlePass only [← vsub_sub_vsub_cancel_right _ _ q] <;>
  match_scalars <;> solve | noncomm_ring -failIfUnchanged | ring)

variable (k P) in
instance HomogenizationExpr.setoid : Setoid (HomogenizationExpr k V P) where
  r := Equiv
  iseqv.refl x := by
    cases x <;> constructor
    simp
  iseqv.symm h := by
    rcases h with h | _ <;> constructor
    rw [← neg_sub, h, ← smul_neg, neg_vsub_eq_vsub_rev]
  iseqv.trans h₁ h₂ := by
    rcases h₁ with h₁ | _ <;> rcases h₂ with h₂ | _ <;>
      simp -failIfUnchanged only [zero_smul, sub_eq_zero] at * <;>
      subst_vars <;> constructor
    · linear_combination (norm := affine P) h₁ + h₂
    · simp

variable (k P) in
/-- Given an affine space `P` over `k`, `Homogenization k P` is a vector space containing `P` as a
hyperplane that does not pass through the origin.

Values of type `Homogenization k P` can be constructed as linear combinations of
`Homogenization.ofPoint` and `Homogenization.ofVector`. To define a linear map on
`Homogenization k P`, use `Homogenization.lift`. -/
def Homogenization := Quotient (HomogenizationExpr.setoid k P)

namespace Homogenization

/-- Creates an element of `Homogenization` from a `HomogenizationExpr`. This is an
implementation detail, use `Homogenization.ofPoint` and `Homogenization.ofVector` instead for
constructing elements of `Homogenization.` -/
def mk : HomogenizationExpr k V P → Homogenization k P :=
  Quotient.mk _

private theorem mk_induction_of_point (p : P) {motive : Homogenization k P → Prop}
    (x : Homogenization k P) (mk_mk : ∀ (v : V) (c : k), motive (.mk (.mk v c p))) :
    motive x := by
  rcases x with ⟨⟨v, c, q⟩ | v⟩
  · convert mk_mk (v + c • (q -ᵥ p)) c using 1
    refine Quot.sound <| .mk_mk ?_
    affine P
  · convert mk_mk v 0 using 1
    exact Quot.sound .ofVector_mk

section Module

variable
  {R : Type*} [Semiring R] [Module R k] [Module R V] [IsScalarTower R k V]
  {S : Type*} [Semiring S] [Module S k] [Module S V] [IsScalarTower S k V]
  [SMul R S] [IsScalarTower R S k] [IsScalarTower R S V]

instance : Zero (Homogenization k P) where
  zero := mk (.ofVector 0)

instance : Add (Homogenization k P) where
  add := Quot.map₂
    (fun
      | .mk v₁ c₁ p₁, .mk v₂ c₂ p₂ => .mk (v₁ + v₂ + c₂ • (p₂ -ᵥ p₁)) (c₁ + c₂) p₁
      | .mk v₁ c p, .ofVector v₂ => .mk (v₁ + v₂) c p
      | .ofVector v₁, .mk v₂ c p => .mk (v₁ + v₂) c p
      | .ofVector v₁, .ofVector v₂ => .ofVector (v₁ + v₂))
    (by
      rintro (_ | _) _ _ (h | _) <;>
        simp only [add_zero] <;>
        constructor <;>
        solve | affine P | linear_combination (norm := affine P) h)
    (by
      rintro _ _ (_ | _) (h | _) <;>
        simp only [zero_add] <;>
        constructor <;>
        solve | affine P | linear_combination (norm := affine P) h)

private theorem mk_add_mk {v₁ v₂ : V} {c₁ c₂ : k} {p : P} :
    mk (.mk v₁ c₁ p) + mk (.mk v₂ c₂ p) = mk (.mk (v₁ + v₂) (c₁ + c₂) p) :=
  Quot.sound <| .mk_mk <| by affine P

instance : SMul R (Homogenization k P) where
  smul r := Quotient.map
    (fun
      | .mk v c p => .mk (r • v) (r • c) p
      | .ofVector v => .ofVector (r • v))
    (fun _ _ h => by
      rcases h with h | _ <;>
        simp only [smul_zero] <;>
        constructor
      rw [← smul_sub, h, smul_assoc])

private theorem smul_mk {r : R} {v : V} {c : k} {p : P} :
    r • mk (.mk v c p) = mk (.mk (r • v) (r • c) p) :=
  rfl

private nonrec theorem zero_smul {x : Homogenization k P} : (0 : R) • x = 0 := by
  obtain ⟨p⟩ : Nonempty P := inferInstance
  cases x using mk_induction_of_point p
  simp_rw [smul_mk, zero_smul]
  exact Quot.sound .mk_ofVector

private nonrec theorem add_smul {r s : R} {x : Homogenization k P} :
    (r + s) • x = r • x + s • x := by
  obtain ⟨p⟩ : Nonempty P := inferInstance
  cases x using mk_induction_of_point p
  simp_rw [smul_mk, mk_add_mk, add_smul]

private nonrec theorem one_smul {x : Homogenization k P} : (1 : R) • x = x := by
  obtain ⟨p⟩ : Nonempty P := inferInstance
  cases x using mk_induction_of_point p
  simp_rw [smul_mk, one_smul]

instance : AddCommGroup (Homogenization k P) where
  zero_add x := by
    obtain ⟨p⟩ : Nonempty P := inferInstance
    cases x using mk_induction_of_point p
    refine Quot.sound <| .mk_mk ?_
    simp
  add_zero x := by
    obtain ⟨p⟩ : Nonempty P := inferInstance
    cases x using mk_induction_of_point p
    refine Quot.sound <| .mk_mk ?_
    simp
  add_comm x y := by
    obtain ⟨p⟩ : Nonempty P := inferInstance
    cases x using mk_induction_of_point p
    cases y using mk_induction_of_point p
    simp_rw [mk_add_mk]
    congr 2 <;> abel
  add_assoc x y z := by
    obtain ⟨p⟩ : Nonempty P := inferInstance
    cases x using mk_induction_of_point p
    cases y using mk_induction_of_point p
    cases z using mk_induction_of_point p
    simp_rw [mk_add_mk, add_assoc]
  neg := Quotient.map
    (fun
      | .mk v c p => .mk (- v) (- c) p
      | .ofVector v => .ofVector (- v))
    (by
      rintro _ _ (h | _) <;>
        simp only [neg_zero] <;>
        constructor
      rw [← neg_sub', h, neg_smul])
  neg_add_cancel x := by
    obtain ⟨p⟩ : Nonempty P := inferInstance
    cases x using mk_induction_of_point p
    change mk (.mk ..) + _ = _
    simp_rw [mk_add_mk, neg_add_cancel]
    exact Quot.sound .mk_ofVector
  nsmul := (· • ·)
  nsmul_zero _ := by exact zero_smul
  nsmul_succ n x := by rw [add_smul, one_smul]
  zsmul := (· • ·)
  zsmul_zero' x := by exact zero_smul
  zsmul_succ' n x := by rw [Nat.cast_succ, add_smul, one_smul]
  zsmul_neg' n x := by
    obtain ⟨p⟩ : Nonempty P := inferInstance
    cases x using mk_induction_of_point p
    change mk (.mk ..) = mk (.mk ..)
    simp_rw [Int.negSucc_eq, Nat.cast_succ, ← neg_smul]

instance : Module R (Homogenization k P) where
  zero_smul _ := by exact zero_smul
  one_smul _ := by exact one_smul
  add_smul _ _ _ := by exact add_smul
  mul_smul _ _ x := by
    obtain ⟨p⟩ : Nonempty P := inferInstance
    cases x using mk_induction_of_point p
    simp_rw [smul_mk, mul_smul]
  smul_add _ x y := by
    obtain ⟨p⟩ : Nonempty P := inferInstance
    cases x using mk_induction_of_point p
    cases y using mk_induction_of_point p
    simp only [mk_add_mk, smul_mk, smul_add]
  smul_zero r := by
    change mk (.ofVector (r • 0)) = mk (.ofVector 0)
    simp

instance : IsScalarTower R S (Homogenization k P) where
  smul_assoc r s x := by
    obtain ⟨p⟩ : Nonempty P := inferInstance
    cases x using mk_induction_of_point p
    simp_rw [smul_mk, smul_assoc]

end Module

/-- The embedding of the vector space into the homogenization. -/
def ofVector : V →ₗ[k] Homogenization k P where
  toFun v := mk (.ofVector v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The embedding of the affine space into the homogenization. -/
def ofPoint : P →ᵃ[k] Homogenization k P where
  toFun p := mk (.mk 0 1 p)
  linear := ofVector
  map_vadd' p v := .symm <| Quot.sound <| .mk_mk <| by simp

@[simp]
theorem ofPoint_linear : ofPoint.linear = ofVector (k := k) (P := P) :=
  rfl

@[simp]
theorem ofVector_vsub {p q : P} : ofVector (k := k) (p -ᵥ q) = ofPoint p - ofPoint q :=
  ofPoint.linearMap_vsub p q

@[simp]
theorem ofVector_smul {R : Type*} [Semiring R] [Module R k] [Module R V] [IsScalarTower R k V]
    {r : R} {v : V} : ofVector (r • v) = r • ofVector (k := k) (P := P) v :=
  rfl

theorem ofVector_injective : Function.Injective (ofVector (k := k) (P := P)) := by
  intro v u h
  cases Quotient.eq.mp h
  rfl

theorem ofPoint_injective : Function.Injective (ofPoint (k := k) (P := P)) :=
  ofPoint.linear_injective_iff.mp ofVector_injective

/-- Every element of the homogenization can be written in the form `ofVector v + c • ofPoint p`.

See also `induction_of_point` and `ofVector_ofPoint_cases`. -/
@[induction_eliminator, cases_eliminator]
theorem induction_on {motive : Homogenization k P → Prop} (x : Homogenization k P)
    (h : ∀ (v : V) (c : k) (p : P), motive (ofVector v + c • ofPoint p)) : motive x := by
  obtain ⟨p⟩ : Nonempty P := inferInstance
  cases x using mk_induction_of_point p with | mk_mk v c
  convert h v c p
  change mk (.mk ..) = mk (.mk ..)
  simp

/-- Every element of the homogenization can be written in the form `ofVector v + c • ofPoint p`,
where `p` can be chosen arbitrarily. -/
theorem induction_of_point {motive : Homogenization k P → Prop} (p : P) (x : Homogenization k P)
    (h : ∀ (v : V) (c : k), motive (ofVector v + c • ofPoint p)) : motive x := by
  cases x with | _ v c q =>
  convert h (v - c • (p -ᵥ q)) c using 1
  simp only [map_sub, map_smul, ofVector_vsub]
  match_scalars <;> norm_num

/-- Over a division ring `k`, every element of `Homogenization k P` is either a nonzero multiple of
a point of `P`, or an element of the vector space associated to `P`. -/
theorem ofVector_ofPoint_cases {k V P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
    [AddTorsor V P] (x : Homogenization k P) {motive : Homogenization k P → Prop}
    (smul_ofPoint : ∀ (c : k) p, c ≠ 0 → motive (c • ofPoint p))
    (ofVector : ∀ v, motive (ofVector v)) : motive x := by
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

/-- Auxiliary definition used for defining `Homogenization.lift`. -/
def lift.aux (f : P →ᵃ[k] W) : Homogenization k P → W :=
  Quotient.lift
    (fun
      | .mk v c p => f.linear v + c • f p
      | .ofVector v => f.linear v)
    (by
      rintro _ _ (h | _) <;>
        simp only [_root_.zero_smul, add_zero]
      replace h := congr(f.linear $h)
      rw [map_sub, map_smul, f.linearMap_vsub, vsub_eq_sub, smul_sub] at h
      linear_combination (norm := abel) h)

@[simp]
private theorem lift.aux_mk {f : P →ᵃ[k] W} {v : V} {c : k} {p : P} :
    aux f (mk (.mk v c p)) = f.linear v + c • f p :=
  rfl

@[simp]
private theorem lift.aux_ofPoint {f : P →ᵃ[k] W} {p : P} : aux f (ofPoint p) = f p := by
  simp [ofPoint]

/-- An affine map on `P` taking values in a vector space extends uniquely to a linear map on
`Homogenization k P`.

See also `Homogenization.liftₗ` for a version that is linear over some ring. -/
@[expose]
def lift : (P →ᵃ[k] W) ≃+ (Homogenization k P →ₗ[k] W) where
  toFun f :=
    { toFun := lift.aux f
      map_add' x y := by
        obtain ⟨p⟩ : Nonempty P := inferInstance
        cases x using mk_induction_of_point p
        cases y using mk_induction_of_point p
        simp [mk_add_mk, _root_.add_smul]; abel
      map_smul' _ x := by
        obtain ⟨p⟩ : Nonempty P := inferInstance
        cases x using mk_induction_of_point p
        simp [smul_mk, mul_smul] }
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

section SMul

variable {R : Type*} [Semiring R] [Module R W] [SMulCommClass k R W]

@[simp]
theorem lift_smul {f : P →ᵃ[k] W} {c : R} : lift (c • f) = c • lift f :=
  hom_ext <| by simp

@[simp]
theorem lift_symm_smul {f : Homogenization k P →ₗ[k] W} {c : R} :
    lift.symm (c • f) = c • lift.symm f :=
  rfl

variable (R) in
/-- Linear version of `Homogenization.lift`. -/
@[expose]
def liftₗ : (P →ᵃ[k] W) ≃ₗ[R] (Homogenization k P →ₗ[k] W) :=
  lift.toLinearEquiv fun _ _ => lift_smul

@[simp]
theorem coe_liftₗ : ⇑(liftₗ (k := k) (P := P) (W := W) R) = lift :=
  rfl

@[simp]
theorem coe_liftₗ_symm : ⇑(liftₗ (k := k) (P := P) (W := W) R).symm = lift.symm :=
  rfl

end SMul

/-- The linear map that is constantly `1` when restricted to `P`. -/
def weight : Homogenization k P →ₗ[k] k :=
  lift (AffineMap.const k P 1)

@[simp]
theorem weight_ofVector {v : V} : weight (k := k) (P := P) (ofVector v) = 0 := by
  simp [weight]

@[simp]
theorem weight_ofPoint {p : P} : weight (k := k) (ofPoint p) = 1 := by
  simp [weight]

theorem weight_eq_zero_iff {x : Homogenization k P} : weight x = 0 ↔ ∃ v, x = ofVector v where
  mp := by cases x; simp_all
  mpr := by rintro ⟨_, rfl⟩; rw [weight_ofVector]

theorem weight_eq_one_iff {x : Homogenization k P} : weight x = 1 ↔ ∃ p, x = ofPoint p where
  mp h := by
    cases x with | _ v c p =>
    exists v +ᵥ p
    simp_all
  mpr := by rintro ⟨_, rfl⟩; rw [weight_ofPoint]

theorem lift_const_apply {u : W} {x : Homogenization k P} :
    lift (AffineMap.const k P u) x = weight x • u := by
  cases x; simp

/-- An affine map between two affine spaces extends to a linear map between their homogenizations.
-/
@[expose]
def map (f : P1 →ᵃ[k] P2) : Homogenization k P1 →ₗ[k] Homogenization k P2 :=
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
def congr (f : P1 ≃ᵃ[k] P2) : Homogenization k P1 ≃ₗ[k] Homogenization k P2 :=
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
def toProd : Homogenization k V ≃ₗ[k] V × k where
  __ := (lift (.id ..)).prod weight
  invFun x := ofVector x.1 + x.2 • ofPoint 0
  left_inv x := by
    cases x using induction_of_point (0 : V)
    simp
  right_inv x := by simp

@[simp]
theorem toProd_ofPoint {v : V} : toProd (ofPoint (k := k) v) = (v, 1) := by
  simp [toProd_apply]

@[simp]
theorem toProd_ofVector {v : V} : toProd (ofVector (k := k) v) = (v, 0) := by
  simp [toProd_apply]

instance [Module.Finite k V] : Module.Finite k (Homogenization k P) :=
  have ⟨x⟩ : Nonempty P := inferInstance
  .equiv (toProd.symm ≪≫ₗ congr (AffineEquiv.vaddConst k x))

end Homogenization
