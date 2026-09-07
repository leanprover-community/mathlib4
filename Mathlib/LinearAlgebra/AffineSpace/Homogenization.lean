/-
Copyright (c) 2026 Attila Gáspár. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Attila Gáspár
-/
module

public import Mathlib.Algebra.Module.TransferInstance
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

public noncomputable section

/-- Given an affine space `P` over `R`, `Homogenization R P` is a vector space containing `P` as a
hyperplane that does not pass through the origin.

Values of type `Homogenization R P` can be constructed as linear combinations of
`Homogenization.ofPoint` and `Homogenization.ofVector`. To define a linear map on
`Homogenization R P`, use `Homogenization.lift`. -/
/- To simplify the implementation, we define the homogenization as `V × R`, with the element
`(v, c)` representing `ofVector v + c • ofPoint (Classical.arbitrary P)`. -/
@[nolint unusedArguments]
def Homogenization
    (R : Type*) {V : Type*} (P : Type*) [Ring R] [AddCommGroup V] [Module R V] [AddTorsor V P] :=
  V × R

variable
  {R : Type*} [Ring R]
  {V P : Type*} [AddCommGroup V] [Module R V] [AddTorsor V P]
  {V₁ P₁ : Type*} [AddCommGroup V₁] [Module R V₁] [AddTorsor V₁ P₁]
  {V₂ P₂ : Type*} [AddCommGroup V₂] [Module R V₂] [AddTorsor V₂ P₂]
  {V₃ P₃ : Type*} [AddCommGroup V₃] [Module R V₃] [AddTorsor V₃ P₃]
  {W : Type*} [AddCommGroup W] [Module R W]

namespace Homogenization

/- TODO: define the `AddCommGroup` and `Module` instances using `inferInstanceAs` once
https://github.com/leanprover/lean4/issues/14470 is fixed -/

/-- Auxiliary definition used for defining the module structure on `Homogenization`. -/
def equivProdAux : Homogenization R P ≃ V × R :=
  .refl _

-- This instance must be exposed to avoid publicly non-defeq instances for `NSMul`.
instance : AddCommGroup (Homogenization R P) :=
  equivProdAux.addCommGroup

section SMul

/- The `[IsScalarTower S R V]` assumption implies that this instance does not depend on the
arbitrary choice made in the definition of `Homogenization`. -/
@[nolint unusedArguments]
instance instModule {S : Type*} [Semiring S] [Module S R] [Module S V] [IsScalarTower S R V] :
    Module S (Homogenization R P) :=
  equivProdAux.addEquiv.module S

variable
  {S : Type*} [Semiring S] [Module S R] [Module S V] [IsScalarTower S R V]
  {T : Type*} [Semiring T] [Module T R] [Module T V] [IsScalarTower T R V]
  [SMul S T] [IsScalarTower S T R] [IsScalarTower S T V]

instance : IsScalarTower S T (Homogenization R P) :=
  inferInstanceAs (IsScalarTower S T (V × R))

end SMul

/-- The embedding of the affine space into the homogenization. -/
def ofPoint : P →ᵃ[R] Homogenization R P :=
  .prod (AffineEquiv.vaddConst R (Classical.arbitrary P)).symm (.const R P (1 : R))

/-- The embedding of the vector space into the homogenization. -/
@[expose]
def ofVector : V →ₗ[R] Homogenization R P :=
  ofPoint.linear

@[simp]
theorem ofPoint_linear : ofPoint.linear = ofVector (R := R) (P := P) :=
  rfl

@[simp]
theorem ofVector_vsub (p q : P) : ofVector (R := R) (p -ᵥ q) = ofPoint p - ofPoint q :=
  ofPoint.linearMap_vsub p q

@[simp]
theorem ofVector_smul {S : Type*} [Semiring S] [Module S R] [Module S V] [IsScalarTower S R V]
    (c : S) (v : V) : ofVector (c • v) = c • ofVector (R := R) (P := P) v :=
  Prod.ext rfl (smul_zero c).symm

theorem ofVector_injective : Function.Injective (ofVector (R := R) (P := P)) :=
  (injective_iff_map_eq_zero _).mpr fun _ h => congr($h.1)

theorem ofPoint_injective : Function.Injective (ofPoint (R := R) (P := P)) :=
  ofPoint.linear_injective_iff.mp ofVector_injective

/-- Every element of the homogenization can be written in the form `ofVector v + c • ofPoint p`.

See also `induction_of_point` and `ofVector_ofPoint_cases`. -/
@[induction_eliminator, cases_eliminator]
theorem induction_on {motive : Homogenization R P → Prop} (x : Homogenization R P)
    (h : ∀ (v : V) (c : R) (p : P), motive (ofVector v + c • ofPoint p)) : motive x := by
  specialize h x.1 x.2 (Classical.arbitrary P)
  change motive (x.1 + x.2 • (Classical.arbitrary P -ᵥ Classical.arbitrary P), 0 + x.2 * 1) at h
  simpa using! h

/-- Every element of the homogenization can be written in the form `ofVector v + c • ofPoint p`,
where `p` can be chosen arbitrarily. -/
theorem induction_of_point {motive : Homogenization R P → Prop} (p : P) (x : Homogenization R P)
    (h : ∀ (v : V) (c : R), motive (ofVector v + c • ofPoint p)) : motive x := by
  cases x with | _ v c q =>
  convert h (v - c • (p -ᵥ q)) c using 1
  simp only [map_sub, map_smul, ofVector_vsub]
  match_scalars <;> norm_num

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
private def liftAux (f : P →ᵃ[R] W) : Homogenization R P →ₗ[R] W :=
  f.linear.coprod <| LinearMap.id.smulRight (f (Classical.arbitrary P))

@[simp]
private theorem liftAux_ofPoint (f : P →ᵃ[R] W) (p : P) : liftAux f (ofPoint p) = f p := by
  change f.linear (p -ᵥ Classical.arbitrary P) + (1 : R) • f (Classical.arbitrary P) = f p
  simp

/-- An affine map on `P` taking values in a vector space extends uniquely to a linear map on
`Homogenization R P`.

See also `Homogenization.liftₗ` for a version that is linear over some semiring. -/
@[expose]
def lift : (P →ᵃ[R] W) ≃+ (Homogenization R P →ₗ[R] W) where
  toFun := private liftAux
  invFun f := f.toAffineMap.comp ofPoint
  left_inv f := by
    change (liftAux f).toAffineMap.comp ofPoint = f
    ext; simp
  right_inv f := by
    change liftAux (f.toAffineMap.comp ofPoint) = f
    apply hom_ext; simp
  map_add' f g := by
    change liftAux (f + g) = liftAux f + liftAux g
    apply hom_ext; simp

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
@[expose]
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
@[expose]
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

/-- An affine map between two affine spaces extends to a linear map between their homogenizations.
-/
@[expose]
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
@[expose]
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
@[expose, simps! -isSimp]
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
