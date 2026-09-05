/-
Copyright (c) 2026 Attila Gáspár. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Attila Gáspár
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import Mathlib.LinearAlgebra.AffineSpace.Restrict
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

Note that the homogenization is isomorphic to `V × R`, where `V` is the vector space associated to
`P` and `R` is the ring of scalars. However, this isomorphism is not canonical unless `P = V`
(see `Homogenization.toProd` in this case).

## Main definitions

* `Homogenization R P`: the homogenization of the affine space `P` over the ring `R`.
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
  {R : Type*} [Ring R]
  {V P : Type*} [AddCommGroup V] [Module R V] [AddTorsor V P]
  {V₁ P₁ : Type*} [AddCommGroup V₁] [Module R V₁] [AddTorsor V₁ P₁]
  {V₂ P₂ : Type*} [AddCommGroup V₂] [Module R V₂] [AddTorsor V₂ P₂]
  {V₃ P₃ : Type*} [AddCommGroup V₃] [Module R V₃] [AddTorsor V₃ P₃]
  {W : Type*} [AddCommGroup W] [Module R W]

variable (R V P) in
/-- A formal expression representing an element of `Homogenization R P`. This is an implementation
detail, use the API of `Homogenization` instead. -/
inductive Homogenization.Pre where
  /-- The formal expression `v + c • p`. -/
  | mk (v : V) (c : R) (p : P)
  /-- The embedding of the vector space into the homogenization. This constructor is used for
  defining `Homogenization.ofVector` in a computable way. -/
  | ofVector (v : V)

-- TODO: generalize and improve performance
local macro "affine" P:term : tactic => `(tactic|
  have ⟨q⟩ : Nonempty $P := inferInstance <;>
  simp +singlePass only [← vsub_sub_vsub_cancel_right _ _ q] <;>
  match_scalars <;> solve | noncomm_ring -failIfUnchanged | ring)

namespace Homogenization.Pre

/-- The equivalence relation on `Homogenization.Pre`. -/
inductive Equiv : Pre R V P → Pre R V P → Prop where
  | mk_mk {c v₁ p₁ v₂ p₂} (h : v₁ - v₂ = c • (p₂ -ᵥ p₁)) : Equiv (mk v₁ c p₁) (mk v₂ c p₂)
  | mk_ofVector {v p} : Equiv (mk v 0 p) (ofVector v)
  | ofVector_mk {v p} : Equiv (ofVector v) (mk v 0 p)
  | ofVector_ofVector {v} : Equiv (ofVector v) (ofVector v)

variable (R P) in
instance setoid : Setoid (Pre R V P) where
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

instance decidableEquiv [DecidableEq R] [DecidableEq V] :
    ∀ {x y : Pre R V P}, Decidable (x ≈ y)
  | .mk v₁ c₁ p₁, .mk v₂ c₂ p₂ =>
    decidable_of_iff (c₁ = c₂ ∧ v₁ - v₂ = c₁ • (p₂ -ᵥ p₁))
      ⟨fun ⟨rfl, h⟩ => .mk_mk h, fun | .mk_mk h => ⟨rfl, h⟩⟩
  | .mk v₁ c _, .ofVector v₂ =>
    decidable_of_iff (0 = c ∧ v₁ = v₂)
      ⟨fun ⟨rfl, rfl⟩ => .mk_ofVector, fun | .mk_ofVector => ⟨rfl, rfl⟩⟩
  | .ofVector v₁, .mk v₂ c _ =>
    decidable_of_iff (0 = c ∧ v₁ = v₂)
      ⟨fun ⟨rfl, rfl⟩ => .ofVector_mk, fun | .ofVector_mk => ⟨rfl, rfl⟩⟩
  | .ofVector v₁, .ofVector v₂ =>
    decidable_of_iff (v₁ = v₂)
      ⟨fun | rfl => .ofVector_ofVector, fun | .ofVector_ofVector => rfl⟩

@[simps -isSimp]
instance : Add (Pre R V P) where
  add
    | .mk v₁ c₁ p₁, .mk v₂ c₂ p₂ => .mk (v₁ + v₂ + c₂ • (p₂ -ᵥ p₁)) (c₁ + c₂) p₁
    | .mk v₁ c p, .ofVector v₂ => .mk (v₁ + v₂) c p
    | .ofVector v₁, .mk v₂ c p => .mk (v₁ + v₂) c p
    | .ofVector v₁, .ofVector v₂ => .ofVector (v₁ + v₂)

theorem add_congr {x x' y y' : Pre R V P} (hx : x ≈ x') (hy : y ≈ y') : x + y ≈ x' + y' := by
  -- We add dummy equations so that we can use `linear_combination` uniformly across all subgoals
  have h₁ : (0 : V) = 0 := rfl
  have h₂ := h₁
  rcases hx with h₁ | _ <;> rcases hy with h₂ | _ <;>
    simp only [add_def, zero_smul, add_zero, zero_add] <;>
    constructor <;>
    linear_combination (norm := affine P) h₁ + h₂

section SMul

variable {S : Type*} [Semiring S] [Module S R] [Module S V] [IsScalarTower S R V]

@[simps -isSimp]
instance : SMul S (Pre R V P) where
  smul r
    | .mk v c p => .mk (r • v) (r • c) p
    | .ofVector v => .ofVector (r • v)

theorem smul_congr (r : S) {x x' : Pre R V P} (hx : x ≈ x') : r • x ≈ r • x' := by
  rcases hx with h | _ <;>
    simp only [smul_def, smul_zero] <;>
    constructor
  rw [← smul_sub, h, smul_assoc]

end SMul

end Homogenization.Pre

variable (R P) in
/-- Given an affine space `P` over `R`, `Homogenization R P` is a vector space containing `P` as a
hyperplane that does not pass through the origin.

Values of type `Homogenization R P` can be constructed as linear combinations of
`Homogenization.ofPoint` and `Homogenization.ofVector`. To define a linear map on
`Homogenization R P`, use `Homogenization.lift`. -/
def Homogenization := Quotient (Homogenization.Pre.setoid R P)

namespace Homogenization

/-- Creates an element of `Homogenization` from a `Homogenization.Pre`. This is an
implementation detail, use `Homogenization.ofPoint` and `Homogenization.ofVector` instead for
constructing elements of `Homogenization.` -/
def mk : Pre R V P → Homogenization R P :=
  Quotient.mk _

private theorem mk_induction_of_point (p : P) {motive : Homogenization R P → Prop}
    (x : Homogenization R P) (mk_mk : ∀ (v : V) (c : R), motive (.mk (.mk v c p))) :
    motive x := by
  rcases x with ⟨⟨v, c, q⟩ | v⟩
  · convert (transparency := .default) mk_mk (v + c • (q -ᵥ p)) c using 1
    refine Quot.sound <| .mk_mk ?_
    affine P
  · convert (transparency := .default) mk_mk v 0 using 1
    exact Quot.sound .ofVector_mk

set_option allowUnsafeReducibility true in
set_option warn.classDefReducibility false in
@[semireducible]
instance [DecidableEq R] [DecidableEq V] : DecidableEq (Homogenization R P) :=
  Quotient.decidableEq

section Module

variable
  {S : Type*} [Semiring S] [Module S R] [Module S V] [IsScalarTower S R V]
  {T : Type*} [Semiring T] [Module T R] [Module T V] [IsScalarTower T R V]
  [SMul S T] [IsScalarTower S T R] [IsScalarTower S T V]

instance : Zero (Homogenization R P) where
  zero := mk (.ofVector 0)

-- We mark this `@[semireducible]` because it is ill-typed at implicit transparency
set_option allowUnsafeReducibility true in
set_option warn.classDefReducibility false in
@[semireducible]
instance : Add (Homogenization R P) where
  add := Quotient.map₂ (· + ·) (fun _ _ h₁ _ _ h₂ => Pre.add_congr h₁ h₂)

private theorem mk_add_mk {v₁ v₂ : V} {c₁ c₂ : R} {p : P} :
    mk (.mk v₁ c₁ p) + mk (.mk v₂ c₂ p) = mk (.mk (v₁ + v₂) (c₁ + c₂) p) :=
  Quot.sound <| .mk_mk <| by affine P

set_option allowUnsafeReducibility true in
set_option warn.classDefReducibility false in
@[semireducible]
instance : SMul S (Homogenization R P) where
  smul r := Quotient.map (r • ·) (fun _ _ => Pre.smul_congr r)

private theorem smul_mk {r : S} {v : V} {c : R} {p : P} :
    r • mk (.mk v c p) = mk (.mk (r • v) (r • c) p) :=
  rfl

private nonrec theorem zero_smul {x : Homogenization R P} : (0 : S) • x = 0 := by
  obtain ⟨p⟩ : Nonempty P := inferInstance
  cases x using mk_induction_of_point p
  simp_rw [smul_mk, zero_smul]
  exact Quot.sound .mk_ofVector

private nonrec theorem add_smul {r s : S} {x : Homogenization R P} :
    (r + s) • x = r • x + s • x := by
  obtain ⟨p⟩ : Nonempty P := inferInstance
  cases x using mk_induction_of_point p
  simp_rw [smul_mk, mk_add_mk, add_smul]

private nonrec theorem one_smul {x : Homogenization R P} : (1 : S) • x = x := by
  obtain ⟨p⟩ : Nonempty P := inferInstance
  cases x using mk_induction_of_point p
  simp_rw [smul_mk, one_smul]

instance : AddCommGroup (Homogenization R P) where
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
  neg x := (-1 : R) • x
  neg_add_cancel x := by
    obtain ⟨p⟩ : Nonempty P := inferInstance
    cases x using mk_induction_of_point p
    change mk (.mk ..) + _ = _
    simp_rw [mk_add_mk, neg_one_smul, neg_add_cancel]
    exact Quot.sound .mk_ofVector
  nsmul_zero _ := by exact zero_smul
  nsmul_succ n x := by rw [add_smul, one_smul]
  zsmul_zero' x := by exact zero_smul
  zsmul_succ' n x := by rw [Nat.cast_succ, add_smul, one_smul]
  zsmul_neg' n x := by
    obtain ⟨p⟩ : Nonempty P := inferInstance
    cases x using mk_induction_of_point p
    change mk (.mk ..) = mk (.mk ..)
    simp_rw [Int.negSucc_eq, Nat.cast_succ, neg_one_smul, neg_smul]

instance : Module S (Homogenization R P) where
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

instance : IsScalarTower S T (Homogenization R P) where
  smul_assoc r s x := by
    obtain ⟨p⟩ : Nonempty P := inferInstance
    cases x using mk_induction_of_point p
    simp_rw [smul_mk, smul_assoc]

end Module

/-- The embedding of the vector space into the homogenization. -/
def ofVector : V →ₗ[R] Homogenization R P where
  toFun v := mk (.ofVector v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The embedding of the affine space into the homogenization. -/
def ofPoint : P →ᵃ[R] Homogenization R P where
  toFun p := mk (.mk 0 1 p)
  linear := ofVector
  map_vadd' p v := .symm <| Quot.sound <| .mk_mk <| by simp

@[simp]
theorem ofPoint_linear : ofPoint.linear = ofVector (R := R) (P := P) :=
  rfl

@[simp]
theorem ofVector_vsub (p q : P) : ofVector (R := R) (p -ᵥ q) = ofPoint p - ofPoint q :=
  ofPoint.linearMap_vsub p q

@[simp]
theorem ofVector_smul {S : Type*} [Semiring S] [Module S R] [Module S V] [IsScalarTower S R V]
    (c : S) (v : V) : ofVector (c • v) = c • ofVector (R := R) (P := P) v :=
  rfl

theorem ofVector_injective : Function.Injective (ofVector (R := R) (P := P)) := by
  intro v u h
  cases Quotient.eq.mp h
  rfl

theorem ofPoint_injective : Function.Injective (ofPoint (R := R) (P := P)) :=
  ofPoint.linear_injective_iff.mp ofVector_injective

/-- Every element of the homogenization can be written in the form `ofVector v + c • ofPoint p`,
where `p` can be chosen arbitrarily. -/
theorem induction_of_point {motive : Homogenization R P → Prop} (p : P) (x : Homogenization R P)
    (h : ∀ (v : V) (c : R), motive (ofVector v + c • ofPoint p)) : motive x := by
  cases x using mk_induction_of_point p with | mk_mk v c
  convert h v c
  change mk (.mk ..) = mk (.mk ..)
  simp

/-- Every element of the homogenization can be written in the form `ofVector v + c • ofPoint p`.

See also `induction_of_point` and `ofVector_ofPoint_cases`. -/
@[induction_eliminator, cases_eliminator]
theorem induction_on {motive : Homogenization R P → Prop} (x : Homogenization R P)
    (h : ∀ (v : V) (c : R) (p : P), motive (ofVector v + c • ofPoint p)) : motive x :=
  have ⟨p⟩ : Nonempty P := inferInstance
  x.induction_of_point p (h (p := p))

/-- Over a division ring `R`, every element of `Homogenization R P` is either a nonzero multiple of
a point of `P`, or an element of the vector space associated to `P`. -/
theorem ofVector_ofPoint_cases {R V P : Type*} [DivisionRing R] [AddCommGroup V] [Module R V]
    [AddTorsor V P] (x : Homogenization R P) {motive : Homogenization R P → Prop}
    (smul_ofPoint : ∀ (c : R) p, c ≠ 0 → motive (c • ofPoint p))
    (ofVector : ∀ v, motive (ofVector v)) : motive x := by
  cases x with | _ v c p =>
  rcases eq_or_ne c 0 with rfl | hc
  · simpa using ofVector v
  · convert smul_ofPoint c (c⁻¹ • v +ᵥ p) hc using 1
    rw [AffineMap.map_vadd, ofPoint_linear, vadd_eq_add, smul_add, map_smul, smul_inv_smul₀ hc]

theorem span_range_ofPoint : Submodule.span R (Set.range (ofPoint (R := R) (P := P))) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun x => ?_
  cases x with | _ v c p
  rw [← vadd_vsub v p, ofVector_vsub]
  refine Submodule.add_mem _ (Submodule.sub_mem _ ?_ ?_) (Submodule.smul_mem _ _ ?_) <;>
    exact Submodule.mem_span_of_mem <| Set.mem_range_self _

theorem hom_ext {f g : Homogenization R P →ₗ[R] W}
    (h : ∀ x, f (ofPoint x) = g (ofPoint x)) : f = g := by
  rwa [← LinearMap.eqLocus_eq_top, eq_top_iff, ← span_range_ofPoint, Submodule.span_le,
    Set.range_subset_iff]

theorem hom_ext_iff {f g : Homogenization R P →ₗ[R] W} :
    f = g ↔ ∀ x, f (ofPoint x) = g (ofPoint x) :=
  ⟨by rintro rfl _; rfl, hom_ext⟩

/-- Auxiliary definition used for defining `Homogenization.lift`. -/
def liftAux (f : P →ᵃ[R] W) : Homogenization R P → W :=
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
private theorem lift.aux_mk {f : P →ᵃ[R] W} {v : V} {c : R} {p : P} :
    liftAux f (mk (.mk v c p)) = f.linear v + c • f p :=
  rfl

@[simp]
private theorem liftAux_ofPoint (f : P →ᵃ[R] W) (p : P) : liftAux f (ofPoint p) = f p := by
  simp [ofPoint]

/-- An affine map on `P` taking values in a vector space extends uniquely to a linear map on
`Homogenization R P`.

See also `Homogenization.liftₗ` for a version that is linear over some semiring. -/
def lift : (P →ᵃ[R] W) ≃+ (Homogenization R P →ₗ[R] W) where
  toFun f :=
    { toFun := liftAux f
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
theorem lift_apply_ofPoint (f : P →ᵃ[R] W) (p : P) : lift f (ofPoint p) = f p :=
  liftAux_ofPoint ..

@[simp]
theorem lift_apply_ofVector (f : P →ᵃ[R] W) (v : V) : lift f (ofVector v) = f.linear v := by
  obtain ⟨p⟩ : Nonempty P := inferInstance
  nth_rw 1 [← vadd_vsub v p]
  simp_rw [ofVector_vsub, map_sub, lift_apply_ofPoint, AffineMap.map_vadd, vadd_eq_add,
    add_sub_cancel_right]

@[simp]
theorem lift_symm_apply (f : Homogenization R P →ₗ[R] W) (p : P) : lift.symm f p = f (ofPoint p) :=
  rfl

@[simp]
theorem lift_symm_linear_apply (f : Homogenization R P →ₗ[R] W) (v : V) :
    (lift.symm f).linear v = f (ofVector v) :=
  rfl

theorem lift_symm_id : lift.symm .id = ofPoint (R := R) (P := P) :=
  rfl

theorem lift_ofPoint : lift (R := R) (P := P) ofPoint = .id :=
  hom_ext <| by simp

section SMul

variable {S : Type*} [Semiring S] [Module S W] [SMulCommClass R S W]

@[simp]
theorem lift_smul (c : S) (f : P →ᵃ[R] W) : lift (c • f) = c • lift f :=
  hom_ext <| by simp

@[simp]
theorem lift_symm_smul (c : S) (f : Homogenization R P →ₗ[R] W) :
    lift.symm (c • f) = c • lift.symm f :=
  rfl

variable (S) in
/-- Linear version of `Homogenization.lift`. -/
def liftₗ : (P →ᵃ[R] W) ≃ₗ[S] (Homogenization R P →ₗ[R] W) :=
  lift.toLinearEquiv fun _ _ => lift_smul ..

@[simp]
theorem coe_liftₗ : ⇑(liftₗ (R := R) (P := P) (W := W) S) = lift :=
  rfl

@[simp]
theorem coe_liftₗ_symm : ⇑(liftₗ (R := R) (P := P) (W := W) S).symm = lift.symm :=
  rfl

end SMul

/-- The linear map that is constantly `1` when restricted to `P`. -/
def weight : Homogenization R P →ₗ[R] R :=
  lift (.const R P 1)

@[simp]
theorem weight_ofVector (v : V) : weight (R := R) (P := P) (ofVector v) = 0 := by
  simp [weight]

@[simp]
theorem weight_ofPoint (p : P) : weight (R := R) (ofPoint p) = 1 := by
  simp [weight]

theorem weight_eq_zero_iff {x : Homogenization R P} : weight x = 0 ↔ ∃ v, x = ofVector v where
  mp := by cases x; simp_all
  mpr := by rintro ⟨_, rfl⟩; rw [weight_ofVector]

theorem weight_eq_one_iff {x : Homogenization R P} : weight x = 1 ↔ ∃ p, x = ofPoint p where
  mp h := by
    cases x with | _ v c p =>
    exists v +ᵥ p
    simp_all
  mpr := by rintro ⟨_, rfl⟩; rw [weight_ofPoint]

theorem lift_const_apply (u : W) (x : Homogenization R P) :
    lift (.const R P u) x = weight x • u := by
  cases x; simp

theorem weight_surjective : Function.Surjective (weight (R := R) (P := P)) :=
  have ⟨p⟩ : Nonempty P := inferInstance
  fun c => ⟨c • ofPoint p, by simp⟩

/-- `Homogenization.ofVector` as a linear equivalence onto the kernel of `Homogenization.weight`. -/
def ofVectorEquiv : V ≃ₗ[R] (weight : Homogenization R P →ₗ[R] R).ker where
  toLinearMap := ofVector.codRestrict _ (by simp)
  invFun x := Quotient.hrecOn x.1
    (fun
      | .mk v _ _, _ => v
      | .ofVector v, _ => v)
    (by
      refine fun _ _ h => Function.hfunext (by rw [Quotient.sound h]) fun _ h' _ => ?_
      cases h with
      | @mk_mk c v p v' p' h =>
        simp only
        change (0 : R) + c • 1 = 0 at h'
        rw [smul_eq_mul, mul_one, zero_add] at h'
        rw [h', _root_.zero_smul, sub_eq_zero] at h
        exact heq_of_eq h
      | _ => rfl)
    x.2
  left_inv _ := rfl
  right_inv := by
    intro ⟨x, hx⟩
    obtain ⟨v, rfl⟩ := weight_eq_zero_iff.mp hx
    rfl

@[simp]
theorem coe_ofVectorEquiv_apply {v : V} : (ofVectorEquiv (R := R) (P := P) v).val = ofVector v :=
  rfl

/-- `Homogenization.ofPoint` as an affine equivalence onto its range. -/
def ofPointEquiv [Nontrivial R] :
    P ≃ᵃ[R] AffineSubspace.map (ofPoint : P →ᵃ[R] Homogenization R P) ⊤ where
  toFun x := ⟨ofPoint x, Set.mem_image_of_mem _ trivial⟩
  invFun x := Quotient.hrecOn x.1
    (fun
      | .mk v _ p, _ => v +ᵥ p
      | .ofVector v, h => False.elim <| by
        change ofVector v ∈ _ at h
        obtain ⟨p, -, h⟩ := h
        apply_fun weight at h
        simp at h)
    (by
      refine fun _ _ h => Function.hfunext (by rw [Quotient.sound h]) ?_
      rintro _ h' -
      cases h with
      | @mk_mk c v p v' p' h =>
        simp only
        obtain ⟨q, _, h'⟩ := h'
        replace h' := congr(weight $h')
        change _ = (0 : R) + c • 1 at h'
        rw [smul_eq_mul, mul_one, zero_add, weight_ofPoint] at h'
        rw [← h', _root_.one_smul, ← vadd_eq_vadd_iff_sub_eq_vsub] at h
        exact heq_of_eq h.symm
      | _ => simp only; contradiction)
    x.2
  left_inv p := by
    change (0 : V) +ᵥ p = p
    simp
  right_inv := by
    rintro ⟨-, p, -, rfl⟩
    ext
    change ofPoint ((0 : V) +ᵥ p) = ofPoint p
    simp
  linear := ofVectorEquiv.trans <| .ofEq _ _ <| by
    ext x
    rw [LinearMap.mem_ker, weight_eq_zero_iff]
    conv => enter [1, 1, _]; rw [eq_comm]
    simp
  map_vadd' _ _ := Subtype.ext <| ofPoint.map_vadd _ _

@[simp]
theorem coe_ofPointEquiv_apply [Nontrivial R] {p : P} : (ofPointEquiv (R := R) p).val = ofPoint p :=
  rfl

/-- An affine map between two affine spaces extends to a linear map between their homogenizations.
-/
def map (f : P₁ →ᵃ[R] P₂) : Homogenization R P₁ →ₗ[R] Homogenization R P₂ :=
  lift (ofPoint.comp f)

@[simp]
theorem map_apply_ofPoint (f : P₁ →ᵃ[R] P) (p : P₁) : map f (ofPoint p) = ofPoint (f p) := by
  simp [map]

@[simp]
theorem map_apply_ofVector (f : P₁ →ᵃ[R] P₂) (v : V₁) :
    map f (ofVector v) = ofVector (f.linear v) := by
  simp [map]

@[simp]
theorem map_id : map (.id R P) = .id :=
  hom_ext <| by simp

theorem map_injective' : Function.Injective (map (R := R) (P₁ := P₁) (P₂ := P₂)) := by
  intro f g h
  ext p
  simpa [ofPoint_injective.eq_iff] using congr($h (ofPoint p))

@[simp]
theorem map_eq_id_iff {f : P →ᵃ[R] P} : map f = .id ↔ f = .id .. := by
  rw [← map_id, map_injective'.eq_iff]

theorem map_comp (f : P₂ →ᵃ[R] P₃) (g : P₁ →ᵃ[R] P₂) : map (f.comp g) = map f ∘ₗ map g :=
  hom_ext <| by simp

@[simp]
theorem weight_map (f : P₁ →ᵃ[R] P₂) (x : Homogenization R P₁) : weight (map f x) = weight x := by
  cases x; simp

theorem lift_map (f : P₂ →ᵃ[R] V₃) (g : P₁ →ᵃ[R] P₂) (x : Homogenization R P₁) :
    lift f (map g x) = lift (f.comp g) x := by
  cases x; simp

@[simp]
theorem map_injective {f : P₁ →ᵃ[R] P₂} : Function.Injective (map f) ↔ Function.Injective f where
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

@[simp]
theorem map_surjective {f : P₁ →ᵃ[R] P₂} : Function.Surjective (map f) ↔ Function.Surjective f where
  mp hf p := by
    obtain ⟨x, hx⟩ := hf (ofPoint p)
    have := congr(weight $hx)
    rw [weight_map, weight_ofPoint, weight_eq_one_iff] at this
    obtain ⟨q, rfl⟩ := this
    rw [map_apply_ofPoint] at hx
    exact ⟨q, ofPoint_injective hx⟩
  mpr hf := by
    rw [← LinearMap.range_eq_top, ← top_le_iff, ← span_range_ofPoint, Submodule.span_le,
      Set.range_subset_iff, hf.forall]
    exact fun p => ⟨ofPoint p, map_apply_ofPoint ..⟩

/-- An affine isomorphism between two affine spaces extends to a linear isomorphism between their
homogenizations. -/
def congr (f : P₁ ≃ᵃ[R] P₂) : Homogenization R P₁ ≃ₗ[R] Homogenization R P₂ :=
  .ofLinearMap (map f) (map f.symm) (hom_ext <| by simp) (hom_ext <| by simp)

@[simp]
theorem coe_congr (f : P₁ ≃ᵃ[R] P₂) : ⇑(congr f) = map f.toAffineMap :=
  rfl

@[simp]
theorem toLinearMap_congr (f : P₁ ≃ᵃ[R] P₂) : congr f = map f.toAffineMap :=
  rfl

@[simp]
theorem congr_symm (f : P₁ ≃ᵃ[R] P₂) : (congr f).symm = congr f.symm :=
  rfl

@[simp]
theorem congr_refl : congr (.refl R P) = .refl .. := by
  ext; simp

@[simp]
theorem congr_eq_refl_iff {f : P ≃ᵃ[R] P} : congr f = .refl .. ↔ f = .refl .. := by
  simp [← LinearEquiv.toLinearMap_inj, ← AffineEquiv.toAffineMap_inj]

theorem congr_trans (f : P₁ ≃ᵃ[R] P₂) (g : P₂ ≃ᵃ[R] P₃) :
    congr (f.trans g) = congr f ≪≫ₗ congr g := by
  ext; simp [map_comp]

/-- The homogenization of a vector space `V` over `R` is canonically isomorphic to `V × R` -/
@[simps! -isSimp]
def toProd : Homogenization R V ≃ₗ[R] V × R where
  __ := (lift (.id ..)).prod weight
  invFun x := ofVector x.1 + x.2 • ofPoint 0
  left_inv x := by
    cases x using induction_of_point (0 : V)
    simp
  right_inv x := by simp

@[simp]
theorem toProd_ofPoint (v : V) : toProd (ofPoint (R := R) v) = (v, 1) := by
  simp [toProd_apply]

@[simp]
theorem toProd_ofVector (v : V) : toProd (ofVector (R := R) v) = (v, 0) := by
  simp [toProd_apply]

instance [Module.Finite R V] : Module.Finite R (Homogenization R P) :=
  have ⟨x⟩ : Nonempty P := inferInstance
  .equiv (toProd.symm ≪≫ₗ congr (.vaddConst R x))

end Homogenization
