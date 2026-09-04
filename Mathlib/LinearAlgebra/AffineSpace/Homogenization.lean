/-
Copyright (c) 2026 Attila Gáspár. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Attila Gáspár
-/
module

public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
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
* `AffineSubspace.homogenize`: the homogenization of an affine subspace of `P`, as a linear subspace
  of `Homogenization R P`.
* `Submodule.dehomogenize`: the intersection of a linear subspace with the canonical embedding of
  `P`, as an affine subspace of `P`.

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

theorem ofPoint_ne_ofVector [Nontrivial R] (p : P) (v : V) : ofPoint (R := R) p ≠ ofVector v :=
  ne_of_apply_ne weight <| by simp

theorem ofPoint_ne_zero [Nontrivial R] (p : P) : ofPoint (R := R) p ≠ 0 := by
  simpa using ofPoint_ne_ofVector p 0

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

open Homogenization

/-- The homogenization of an affine subspace, as a linear subspace of the homogenization. -/
@[expose]
def AffineSubspace.homogenize (s : AffineSubspace R P) : Submodule R (Homogenization R P) :=
  .span R (ofPoint '' s)

/-- The dehomogenization of a linear subspace of `Homogenization k P` is its intersection
with the canonical embedding of `P`, as an affine subspace of `P`. -/
@[expose]
def Submodule.dehomogenize (s : Submodule R (Homogenization R P)) : AffineSubspace R P :=
  s.toAffineSubspace.comap ofPoint

theorem AffineSubspace.homogenize_le_iff {s : AffineSubspace R P}
    {t : Submodule R (Homogenization R P)} : s.homogenize ≤ t ↔ s ≤ t.dehomogenize := by
  rw [homogenize, Submodule.span_le, Set.image_subset_iff, ← Submodule.coe_toAffineSubspace,
    ← AffineSubspace.coe_comap, Submodule.dehomogenize, SetLike.coe_subset_coe]

theorem AffineSubspace.gc_homogenize :
    GaloisConnection (α := AffineSubspace R P) AffineSubspace.homogenize Submodule.dehomogenize :=
  fun _ _ => homogenize_le_iff

namespace Submodule

open AffineSubspace (gc_homogenize)

@[simp]
theorem mem_dehomogenize {p : P} {s : Submodule R (Homogenization R P)} :
    p ∈ s.dehomogenize ↔ ofPoint p ∈ s :=
  .rfl

@[gcongr]
theorem monotone_dehomogenize : Monotone (dehomogenize (R := R) (P := P)) :=
  gc_homogenize.monotone_u

@[simp]
theorem dehomogenize_top : (⊤ : Submodule R (Homogenization R P)).dehomogenize = ⊤ :=
  AffineSubspace.gc_homogenize.u_top

@[simp]
theorem dehomogenize_ker_weight [Nontrivial R] :
    (weight (R := R) (P := P)).ker.dehomogenize = ⊥ := by
  ext; simp [AffineSubspace.notMem_bot]

@[simp]
theorem dehomogenize_bot [Nontrivial R] :
    (⊥ : Submodule R (Homogenization R P)).dehomogenize = ⊥ := by
  grw [eq_bot_iff, show ⊥ ≤ weight.ker from bot_le, dehomogenize_ker_weight]

theorem dehomogenize_eq_bot_iff {R V P : Type*} [DivisionRing R] [AddCommGroup V] [Module R V]
    [AddTorsor V P] {s : Submodule R (Homogenization R P)} :
    s.dehomogenize = ⊥ ↔ s ≤ weight.ker where
  mp h := by
    rcases Ideal.eq_bot_or_top (s.map weight) with h' | h'
    · rw [LinearMap.ker, ← map_le_iff_le_comap, h']
    · rw [Ideal.eq_top_iff_one] at h'
      obtain ⟨p, hp, hp'⟩ := h'
      obtain ⟨p, rfl⟩ := weight_eq_one_iff.mp hp'
      rw [SetLike.mem_coe, ← mem_dehomogenize, h] at hp
      contradiction
  mpr h := by grw [eq_bot_iff, h, dehomogenize_ker_weight]

theorem dehomogenize_inf (s t : Submodule R (Homogenization R P)) :
    (s ⊓ t).dehomogenize = s.dehomogenize ⊓ t.dehomogenize :=
  gc_homogenize.u_inf

theorem dehomogenize_sInf (s : Set (Submodule R (Homogenization R P))) :
    (sInf s).dehomogenize = ⨅ t ∈ s, t.dehomogenize :=
  gc_homogenize.u_sInf

theorem dehomogenize_iInf {ι : Type*} (s : ι → Submodule R (Homogenization R P)) :
    (⨅ i, s i).dehomogenize = ⨅ i, (s i).dehomogenize :=
  gc_homogenize.u_iInf

theorem map_dehomogenize (f : P₁ →ᵃ[R] P₂) (s : Submodule R (Homogenization R P₁)) :
    s.dehomogenize.map f = (s.map (Homogenization.map f)).dehomogenize := by
  apply le_antisymm
  · rw [AffineSubspace.map_le_iff_le_comap]
    exact fun p hp => ⟨ofPoint p, hp, map_apply_ofPoint ..⟩
  · intro p ⟨x, hx, h⟩
    obtain ⟨q, rfl⟩ := weight_eq_one_iff.mp <| show weight x = 1 by simpa using congr(weight $h)
    rw [map_apply_ofPoint, ofPoint_injective.eq_iff] at h
    exact ⟨q, hx, h⟩

theorem comap_dehomogenize (f : P₁ →ᵃ[R] P₂) (s : Submodule R (Homogenization R P₂)) :
    s.dehomogenize.comap f = (s.comap (Homogenization.map f)).dehomogenize := by
  ext; simp

theorem homogenize_dehomogenize_le (s : Submodule R (Homogenization R P)) :
    s.dehomogenize.homogenize ≤ s :=
  gc_homogenize.l_u_le s

theorem direction_dehomogenize_le (s : Submodule R (Homogenization R P)) :
    s.dehomogenize.direction ≤ s.comap ofVector := by
  grw [dehomogenize, AffineSubspace.direction_comap_le, toAffineSubspace_direction,
    ofPoint_linear]

theorem direction_dehomogenize {s : Submodule R (Homogenization R P)} (h : s.dehomogenize ≠ ⊥) :
    s.dehomogenize.direction = s.comap ofVector := by
  refine le_antisymm s.direction_dehomogenize_le (fun v hv => ?_)
  obtain ⟨p, hp⟩ := s.dehomogenize.nonempty_iff_ne_bot.mpr h
  rw [← vadd_vsub v p]
  refine AffineSubspace.vsub_mem_direction ?_ hp
  rw [mem_dehomogenize, AffineMap.map_vadd, ofPoint_linear]
  exact add_mem hv hp

@[simp]
theorem mem_direction_dehomogenize {v : V} {s : Submodule R (Homogenization R P)}
    (h : s.dehomogenize ≠ ⊥) : v ∈ s.dehomogenize.direction ↔ ofVector v ∈ s := by
  simp [direction_dehomogenize h]

end Submodule

namespace AffineSubspace

@[gcongr]
theorem monotone_homogenize : Monotone (homogenize (R := R) (P := P)) :=
  gc_homogenize.monotone_l

@[simp]
theorem homogenize_top : (⊤ : AffineSubspace R P).homogenize = ⊤ := by
  rw [homogenize, top_coe, Set.image_univ, span_range_ofPoint]

@[simp]
theorem homogenize_bot : (⊥ : AffineSubspace R P).homogenize = ⊥ :=
  gc_homogenize.l_bot

theorem homogenize_sup (s t : AffineSubspace R P) :
    (s ⊔ t).homogenize = s.homogenize ⊔ t.homogenize :=
  gc_homogenize.l_sup

theorem homogenize_sSup (s : Set (AffineSubspace R P)) :
    (sSup s).homogenize = ⨆ t ∈ s, t.homogenize :=
  gc_homogenize.l_sSup

theorem homogenize_iSup {ι : Type*} (s : ι → AffineSubspace R P) :
    (⨆ i, s i).homogenize = ⨆ i, (s i).homogenize :=
  gc_homogenize.l_iSup

theorem homogenize_map (f : P₁ →ᵃ[R] P₂) (s : AffineSubspace R P₁) :
    (s.map f).homogenize = s.homogenize.map (Homogenization.map f) := by
  apply le_antisymm
  · grw [homogenize_le_iff, ← Submodule.map_dehomogenize, ← gc_homogenize.le_u_l]
  · grw [Submodule.map_le_iff_le_comap, homogenize_le_iff, ← Submodule.comap_dehomogenize,
      ← gc_homogenize.le_u_l, ← le_comap_map]

theorem homogenize_comap_le (f : P₁ →ᵃ[R] P₂) (s : AffineSubspace R P₂) :
    (s.comap f).homogenize ≤ s.homogenize.comap (Homogenization.map f) := by
  grw [homogenize_le_iff, ← Submodule.comap_dehomogenize, ← gc_homogenize.le_u_l]

theorem ofPoint_mem_homogenize_of_mem {p : P} {s : AffineSubspace R P} (h : p ∈ s) :
    ofPoint p ∈ s.homogenize :=
  Submodule.mem_span_of_mem <| Set.mem_image_of_mem _ h

theorem homogenize_eq_of_mem {s : AffineSubspace R P} {p : P} (hp : p ∈ s) :
    s.homogenize = s.direction.map ofVector ⊔ R ∙ ofPoint p := by
  apply le_antisymm
  · rw [homogenize_le_iff]
    intro q hq
    rw [Submodule.mem_dehomogenize, ← vsub_vadd q p, AffineMap.map_vadd, ofPoint_linear,
      vadd_eq_add]
    exact Submodule.add_mem_sup
      (Submodule.mem_map_of_mem <| s.vsub_mem_direction hq hp)
      (Submodule.mem_span_singleton_self _)
  · simp_rw [sup_le_iff, Submodule.span_singleton_le_iff_mem, Submodule.map_le_iff_le_comap,
      direction, vectorSpan, Submodule.span_le, Set.vsub_subset_iff, SetLike.mem_coe,
      Submodule.mem_comap, ofVector_vsub]
    grind [sub_mem, ofPoint_mem_homogenize_of_mem]

theorem comap_ofVector_homogenize (s : AffineSubspace R P) :
    s.homogenize.comap ofVector = s.direction := by
  rcases s.eq_bot_or_nonempty with rfl | ⟨p, hp⟩
  · simp [LinearMap.ker_eq_bot_of_injective ofVector_injective]
  rw [homogenize_eq_of_mem hp, Submodule.comap_map_sup_of_comap_le ?_]
  intro v h
  obtain ⟨c, h⟩ := Submodule.mem_span_singleton.mp h
  rw [show c = 0 by simpa using congr(weight $h), zero_smul, eq_comm,
    map_eq_zero_iff _ ofVector_injective] at h
  rw [h]
  exact zero_mem _

@[simp]
theorem ofVector_mem_homogenize {v : V} {s : AffineSubspace R P} :
    ofVector v ∈ s.homogenize ↔ v ∈ s.direction := by
  simp [← comap_ofVector_homogenize]

theorem homogenize_sInf {s : Set (AffineSubspace R P)} (h : sInf s ≠ ⊥) :
    (sInf s).homogenize = ⨅ t ∈ s, t.homogenize := by
  refine le_antisymm monotone_homogenize.map_sInf_le (fun x hx => ?_)
  obtain ⟨p, hp⟩ := (nonempty_iff_ne_bot _).mpr h
  cases x using induction_of_point p with | _ v c =>
  refine add_mem ?_ <| Submodule.smul_mem _ _ <| ofPoint_mem_homogenize_of_mem hp
  rw [SetLike.mem_coe, mem_sInf_iff] at hp
  rw [add_mem_cancel_right <| Submodule.smul_mem _ _ <| by
    grind [Submodule.mem_iInf, ofPoint_mem_homogenize_of_mem]] at hx
  simpa [direction_sInf_of_mem _ p hp] using hx

theorem homogenize_iInf {ι : Type*} {s : ι → AffineSubspace R P} (h : ⨅ i, s i ≠ ⊥) :
    (⨅ i, s i).homogenize = ⨅ i, (s i).homogenize := by
  rw [← sInf_range] at h ⊢
  rw [homogenize_sInf h, iInf_range]

theorem homogenize_inf {s t : AffineSubspace R P} (h : s ⊓ t ≠ ⊥) :
    (s ⊓ t).homogenize = s.homogenize ⊓ t.homogenize := by
  simp_rw [inf_eq_iInf] at h ⊢
  simp_rw [homogenize_iInf h, Bool.apply_cond]

theorem homogenize_comap {f : P₁ →ᵃ[R] P₂} {s : AffineSubspace R P₂}
    (h : s.comap f ≠ ⊥) : (s.comap f).homogenize = s.homogenize.comap (Homogenization.map f) := by
  refine le_antisymm (homogenize_comap_le f s) (fun x hx => ?_)
  obtain ⟨p, hp⟩ := (nonempty_iff_ne_bot _).mpr h
  cases x using induction_of_point p with | _ v c =>
  refine add_mem (ofVector_mem_homogenize.mpr ?_)
    (Submodule.smul_mem _ _ <| ofPoint_mem_homogenize_of_mem hp)
  rw [Submodule.mem_comap, map_add, map_apply_ofVector, map_smul, map_apply_ofPoint,
    add_mem_cancel_right <| s.homogenize.smul_mem c <| ofPoint_mem_homogenize_of_mem hp,
    ofVector_mem_homogenize] at hx
  simpa [direction_comap h] using hx

variable [Nontrivial R]

/-- `AffineSubspace.homogenize` and `Submodule.dehomogenize` form a Galois coinsertion. -/
@[expose]
def gciHomogenize :
    GaloisCoinsertion (α := AffineSubspace R P) AffineSubspace.homogenize Submodule.dehomogenize :=
  gc_homogenize.toGaloisCoinsertion fun s => by
    rcases s.eq_bot_or_nonempty with rfl | h
    · simp
    apply le_of_direction_le
    · grw [Submodule.direction_dehomogenize_le, s.comap_ofVector_homogenize]
    · rwa [Set.inter_eq_right.mpr <| gc_homogenize.le_u_l s]

@[simp]
theorem dehomogenize_homogenize (s : AffineSubspace R P) : s.homogenize.dehomogenize = s :=
  gciHomogenize.u_l_eq s

@[simp]
theorem ofPoint_mem_homogenize {p : P} {s : AffineSubspace R P} :
    ofPoint p ∈ s.homogenize ↔ p ∈ s := by
  rw [← Submodule.mem_dehomogenize, s.dehomogenize_homogenize]

@[simp]
theorem homogenize_le_homogenize {s t : AffineSubspace R P} : s.homogenize ≤ t.homogenize ↔ s ≤ t :=
  gciHomogenize.l_le_l_iff

theorem homogenize_injective : Function.Injective (homogenize (R := R) (P := P)) :=
  gciHomogenize.l_injective

end AffineSubspace

namespace Submodule

@[simp]
theorem homogenize_dehomogenize {s : Submodule R (Homogenization R P)} (hs : s.dehomogenize ≠ ⊥) :
    s.dehomogenize.homogenize = s := by
  obtain ⟨p, hp⟩ := s.dehomogenize.nonempty_iff_ne_bot.mpr hs
  refine le_antisymm s.homogenize_dehomogenize_le (fun x hx => ?_)
  cases x using induction_of_point p with | _ v c =>
  rw [add_mem_cancel_right <| smul_mem s c hp] at hx
  refine add_mem ?_ <| smul_mem _ _ <| AffineSubspace.ofPoint_mem_homogenize_of_mem ?_
  · rwa [AffineSubspace.ofVector_mem_homogenize, mem_direction_dehomogenize hs]
  · rwa [mem_dehomogenize]

theorem dehomogenize_iSup [Nontrivial R] {ι : Type*} {s : ι → Submodule R (Homogenization R P)}
    (h : ∀ i, dehomogenize (s i) ≠ ⊥) : (⨆ i, s i).dehomogenize = ⨆ i, (s i).dehomogenize := by
  cases isEmpty_or_nonempty ι
  · simp
  inhabit ι
  have : (⨆ i, s i).dehomogenize ≠ ⊥ :=
    ne_bot_of_le_ne_bot (h default) <| monotone_dehomogenize <| le_iSup _ default
  simp_rw [← AffineSubspace.homogenize_injective.eq_iff, homogenize_dehomogenize this,
    AffineSubspace.homogenize_iSup, homogenize_dehomogenize (h _)]

theorem dehomogenize_sSup [Nontrivial R] {s : Set (Submodule R (Homogenization R P))}
    (h : ∀ t ∈ s, t.dehomogenize ≠ ⊥) : (sSup s).dehomogenize = ⨆ t ∈ s, t.dehomogenize := by
  rw [Subtype.forall'] at h
  rw [sSup_eq_iSup', dehomogenize_iSup h, iSup_subtype]

theorem dehomogenize_sup {s t : Submodule R (Homogenization R P)} (hs : s.dehomogenize ≠ ⊥)
    (ht : t.dehomogenize ≠ ⊥) : (s ⊔ t).dehomogenize = s.dehomogenize ⊔ t.dehomogenize := by
  nontriviality R using Subsingleton.elim _ ⊤
  simp_rw [sup_eq_iSup, ← Bool.apply_cond]
  exact dehomogenize_iSup <| Bool.rec ht hs

end Submodule
