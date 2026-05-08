/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Algebra.Order.Group.Pointwise.Interval
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.AddTorsor.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Defs
/-!
# Affine maps

This file defines affine maps.

## Main definitions

* `AffineMap` is the type of affine maps between two affine spaces with the same ring `k`.  Various
  basic examples of affine maps are defined, including `const`, `id`, `lineMap` and `homothety`.

## Notation

* `P1 →ᵃ[k] P2` is a notation for `AffineMap k P1 P2`;
* `AffineSpace V P`: a localized notation for `AddTorsor V P` defined in
  `LinearAlgebra.AffineSpace.Basic`.

## Implementation notes

`outParam` is used in the definition of `[AddTorsor V P]` to make `V` an implicit argument
(deduced from `P`) in most cases. As for modules, `k` is an explicit argument rather than implied by
`P` or `V`.

This file only provides purely algebraic definitions and results. Those depending on analysis or
topology are defined elsewhere; see `Analysis.Normed.Affine.AddTorsor` and
`Topology.Algebra.Affine`.

## References

* https://en.wikipedia.org/wiki/Affine_space
* https://en.wikipedia.org/wiki/Principal_homogeneous_space
-/

@[expose] public section

open Affine Module

/-- An `AffineMap k P1 P2` (notation: `P1 →ᵃ[k] P2`) is a map from `P1` to `P2` that
induces a corresponding linear map from `V1` to `V2`. -/
structure AffineMap (k : Type*) {V1 : Type*} (P1 : Type*) {V2 : Type*} (P2 : Type*) [Ring k]
  [AddCommGroup V1] [Module k V1] [AffineSpace V1 P1] [AddCommGroup V2] [Module k V2]
  [AffineSpace V2 P2] where
  /-- The underlying function between the affine spaces `P1` and `P2`. -/
  toFun : P1 → P2
  /-- The linear map between the corresponding vector spaces `V1` and `V2`.
  This represents how the affine map acts on differences of points. -/
  linear : V1 →ₗ[k] V2
  map_vadd' : ∀ (p : P1) (v : V1), toFun (v +ᵥ p) = linear v +ᵥ toFun p

/-- An `AffineMap k P1 P2` (notation: `P1 →ᵃ[k] P2`) is a map from `P1` to `P2` that
induces a corresponding linear map from `V1` to `V2`. -/
notation:25 P1 " →ᵃ[" k:25 "] " P2:0 => AffineMap k P1 P2

instance AffineMap.instFunLike (k : Type*) {V1 : Type*} (P1 : Type*) {V2 : Type*} (P2 : Type*)
    [Ring k] [AddCommGroup V1] [Module k V1] [AffineSpace V1 P1] [AddCommGroup V2] [Module k V2]
    [AffineSpace V2 P2] : FunLike (P1 →ᵃ[k] P2) P1 P2 where
  coe := AffineMap.toFun
  coe_injective' := fun ⟨f, f_linear, f_add⟩ ⟨g, g_linear, g_add⟩ => fun (h : f = g) => by
    obtain ⟨p⟩ := (AddTorsor.nonempty : Nonempty P1)
    congr with v
    apply vadd_right_cancel (f p)
    rw [← f_add, h, ← g_add]

namespace LinearMap

variable {k : Type*} {V₁ : Type*} {V₂ : Type*} [Ring k] [AddCommGroup V₁] [Module k V₁]
  [AddCommGroup V₂] [Module k V₂] (f : V₁ →ₗ[k] V₂)

/-- Reinterpret a linear map as an affine map. -/
def toAffineMap : V₁ →ᵃ[k] V₂ where
  toFun := f
  linear := f
  map_vadd' p v := f.map_add v p

@[simp]
theorem coe_toAffineMap : ⇑f.toAffineMap = f :=
  rfl

@[simp]
theorem toAffineMap_linear : f.toAffineMap.linear = f :=
  rfl

end LinearMap

namespace AffineMap

variable {k : Type*} {V1 : Type*} {P1 : Type*} {V2 : Type*} {P2 : Type*} {V3 : Type*}
  {P3 : Type*} {V4 : Type*} {P4 : Type*} [Ring k] [AddCommGroup V1] [Module k V1]
  [AffineSpace V1 P1] [AddCommGroup V2] [Module k V2] [AffineSpace V2 P2] [AddCommGroup V3]
  [Module k V3] [AffineSpace V3 P3] [AddCommGroup V4] [Module k V4] [AffineSpace V4 P4]

/-- Constructing an affine map and coercing back to a function
produces the same map. -/
@[simp]
theorem coe_mk (f : P1 → P2) (linear add) : ((mk f linear add : P1 →ᵃ[k] P2) : P1 → P2) = f :=
  rfl

/-- `toFun` is the same as the result of coercing to a function. -/
@[simp]
theorem toFun_eq_coe (f : P1 →ᵃ[k] P2) : f.toFun = ⇑f :=
  rfl

/-- An affine map on the result of adding a vector to a point produces
the same result as the linear map applied to that vector, added to the
affine map applied to that point. -/
@[simp]
theorem map_vadd (f : P1 →ᵃ[k] P2) (p : P1) (v : V1) : f (v +ᵥ p) = f.linear v +ᵥ f p :=
  f.map_vadd' p v

/-- The linear map on the result of subtracting two points is the
result of subtracting the result of the affine map on those two
points. -/
@[simp]
theorem linearMap_vsub (f : P1 →ᵃ[k] P2) (p1 p2 : P1) : f.linear (p1 -ᵥ p2) = f p1 -ᵥ f p2 := by
  conv_rhs => rw [← vsub_vadd p1 p2, map_vadd, vadd_vsub]

/-- Two affine maps are equal if they coerce to the same function. -/
@[ext]
theorem ext {f g : P1 →ᵃ[k] P2} (h : ∀ p, f p = g p) : f = g :=
  DFunLike.ext _ _ h

theorem coeFn_injective : @Function.Injective (P1 →ᵃ[k] P2) (P1 → P2) (⇑) :=
  DFunLike.coe_injective

protected theorem congr_arg (f : P1 →ᵃ[k] P2) {x y : P1} (h : x = y) : f x = f y :=
  congr_arg _ h

protected theorem congr_fun {f g : P1 →ᵃ[k] P2} (h : f = g) (x : P1) : f x = g x :=
  h ▸ rfl

/-- Two affine maps are equal if they have equal linear maps and are equal at some point. -/
theorem ext_linear {f g : P1 →ᵃ[k] P2} (h₁ : f.linear = g.linear) {p : P1} (h₂ : f p = g p) :
    f = g := by
  ext q
  have hgl : g.linear (q -ᵥ p) = toFun g ((q -ᵥ p) +ᵥ q) -ᵥ toFun g q := by simp
  have := f.map_vadd' q (q -ᵥ p)
  rw [h₁, hgl, toFun_eq_coe, map_vadd, linearMap_vsub, h₂] at this
  simpa

/-- Two affine maps are equal if they have equal linear maps and are equal at some point. -/
theorem ext_linear_iff {f g : P1 →ᵃ[k] P2} : f = g ↔ (f.linear = g.linear) ∧ (∃ p, f p = g p) :=
  ⟨fun h ↦ ⟨congrArg _ h, by inhabit P1; exact default, by rw [h]⟩,
  fun h ↦ Exists.casesOn h.2 fun _ hp ↦ ext_linear h.1 hp⟩

variable (k P1)

/-- The constant function as an `AffineMap`. -/
def const (p : P2) : P1 →ᵃ[k] P2 where
  toFun := Function.const P1 p
  linear := 0
  map_vadd' _ _ :=
    letI : AddAction V2 P2 := inferInstance
    by simp

@[simp]
theorem coe_const (p : P2) : ⇑(const k P1 p) = Function.const P1 p :=
  rfl

@[simp]
theorem const_apply (p : P2) (q : P1) : (const k P1 p) q = p := rfl

@[simp]
theorem const_linear (p : P2) : (const k P1 p).linear = 0 :=
  rfl

variable {k P1}

theorem linear_eq_zero_iff_exists_const (f : P1 →ᵃ[k] P2) :
    f.linear = 0 ↔ ∃ q, f = const k P1 q := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · use f (Classical.arbitrary P1)
    ext
    rw [coe_const, Function.const_apply, ← @vsub_eq_zero_iff_eq V2, ← f.linearMap_vsub, h,
      LinearMap.zero_apply]
  · rcases h with ⟨q, rfl⟩
    exact const_linear k P1 q

instance nonempty : Nonempty (P1 →ᵃ[k] P2) :=
  (AddTorsor.nonempty : Nonempty P2).map <| const k P1

/-- Construct an affine map by verifying the relation between the map and its linear part at one
base point. Namely, this function takes a map `f : P₁ → P₂`, a linear map `f' : V₁ →ₗ[k] V₂`, and
a point `p` such that for any other point `p'` we have `f p' = f' (p' -ᵥ p) +ᵥ f p`. -/
def mk' (f : P1 → P2) (f' : V1 →ₗ[k] V2) (p : P1) (h : ∀ p' : P1, f p' = f' (p' -ᵥ p) +ᵥ f p) :
    P1 →ᵃ[k] P2 where
  toFun := f
  linear := f'
  map_vadd' p' v := by rw [h, h p', vadd_vsub_assoc, f'.map_add, vadd_vadd]

@[simp]
theorem coe_mk' (f : P1 → P2) (f' : V1 →ₗ[k] V2) (p h) : ⇑(mk' f f' p h) = f :=
  rfl

@[simp]
theorem mk'_linear (f : P1 → P2) (f' : V1 →ₗ[k] V2) (p h) : (mk' f f' p h).linear = f' :=
  rfl

section SMul

variable {R : Type*} [Monoid R] [DistribMulAction R V2] [SMulCommClass k R V2]
/-- The space of affine maps to a module inherits an `R`-action from the action on its codomain. -/
instance mulAction : MulAction R (P1 →ᵃ[k] V2) where
  smul c f := ⟨c • ⇑f, c • f.linear, fun p v => by simp [smul_add]⟩
  one_smul _ := ext fun _ => one_smul _ _
  mul_smul _ _ _ := ext fun _ => mul_smul _ _ _

@[simp, norm_cast]
theorem coe_smul (c : R) (f : P1 →ᵃ[k] V2) : ⇑(c • f) = c • ⇑f :=
  rfl

@[simp]
theorem smul_linear (t : R) (f : P1 →ᵃ[k] V2) : (t • f).linear = t • f.linear :=
  rfl

instance isCentralScalar [DistribMulAction Rᵐᵒᵖ V2] [IsCentralScalar R V2] :
    IsCentralScalar R (P1 →ᵃ[k] V2) where
  op_smul_eq_smul _r _x := ext fun _ => op_smul_eq_smul _ _

end SMul

instance : Zero (P1 →ᵃ[k] V2) where zero := ⟨0, 0, fun _ _ => (zero_vadd _ _).symm⟩

instance : Add (P1 →ᵃ[k] V2) where
  add f g := ⟨f + g, f.linear + g.linear, fun p v => by simp [add_add_add_comm]⟩

instance : Sub (P1 →ᵃ[k] V2) where
  sub f g := ⟨f - g, f.linear - g.linear, fun p v => by simp [sub_add_sub_comm]⟩

instance : Neg (P1 →ᵃ[k] V2) where
  neg f := ⟨-f, -f.linear, fun p v => by simp [add_comm, map_vadd f]⟩

@[simp, norm_cast]
theorem coe_zero : ⇑(0 : P1 →ᵃ[k] V2) = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_add (f g : P1 →ᵃ[k] V2) : ⇑(f + g) = f + g :=
  rfl

@[simp, norm_cast]
theorem coe_neg (f : P1 →ᵃ[k] V2) : ⇑(-f) = -f :=
  rfl

@[simp, norm_cast]
theorem coe_sub (f g : P1 →ᵃ[k] V2) : ⇑(f - g) = f - g :=
  rfl

@[simp]
theorem zero_linear : (0 : P1 →ᵃ[k] V2).linear = 0 :=
  rfl

@[simp]
theorem add_linear (f g : P1 →ᵃ[k] V2) : (f + g).linear = f.linear + g.linear :=
  rfl

@[simp]
theorem sub_linear (f g : P1 →ᵃ[k] V2) : (f - g).linear = f.linear - g.linear :=
  rfl

@[simp]
theorem neg_linear (f : P1 →ᵃ[k] V2) : (-f).linear = -f.linear :=
  rfl

/-- The set of affine maps to a vector space is an additive commutative group. -/
instance : AddCommGroup (P1 →ᵃ[k] V2) :=
  coeFn_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_smul _ _)
    fun _ _ => coe_smul _ _

/-- The space of affine maps from `P1` to `P2` is an affine space over the space of affine maps
from `P1` to the vector space `V2` corresponding to `P2`. -/
instance : AffineSpace (P1 →ᵃ[k] V2) (P1 →ᵃ[k] P2) where
  vadd f g :=
    ⟨fun p => f p +ᵥ g p, f.linear + g.linear,
      fun p v => by simp [vadd_vadd, add_right_comm]⟩
  zero_vadd f := ext fun p => zero_vadd _ (f p)
  add_vadd f₁ f₂ f₃ := ext fun p => add_vadd (f₁ p) (f₂ p) (f₃ p)
  vsub f g :=
    ⟨fun p => f p -ᵥ g p, f.linear - g.linear, fun p v => by
      simp [vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, sub_add_eq_add_sub]⟩
  vsub_vadd' f g := ext fun p => vsub_vadd (f p) (g p)
  vadd_vsub' f g := ext fun p => vadd_vsub (f p) (g p)

@[simp]
theorem vadd_apply (f : P1 →ᵃ[k] V2) (g : P1 →ᵃ[k] P2) (p : P1) : (f +ᵥ g) p = f p +ᵥ g p :=
  rfl

@[simp]
theorem vadd_linear (f : P1 →ᵃ[k] V2) (g : P1 →ᵃ[k] P2) : (f +ᵥ g).linear = f.linear + g.linear :=
  rfl

@[simp]
theorem vsub_apply (f g : P1 →ᵃ[k] P2) (p : P1) : (f -ᵥ g : P1 →ᵃ[k] V2) p = f p -ᵥ g p :=
  rfl

@[simp]
theorem vsub_linear (f g : P1 →ᵃ[k] P2) : (f -ᵥ g).linear = f.linear - g.linear :=
  rfl

/-- `Prod.fst` as an `AffineMap`. -/
def fst : P1 × P2 →ᵃ[k] P1 where
  toFun := Prod.fst
  linear := LinearMap.fst k V1 V2
  map_vadd' _ _ := rfl

@[simp]
theorem coe_fst : ⇑(fst : P1 × P2 →ᵃ[k] P1) = Prod.fst :=
  rfl

@[simp]
theorem fst_linear : (fst : P1 × P2 →ᵃ[k] P1).linear = LinearMap.fst k V1 V2 :=
  rfl

/-- `Prod.snd` as an `AffineMap`. -/
def snd : P1 × P2 →ᵃ[k] P2 where
  toFun := Prod.snd
  linear := LinearMap.snd k V1 V2
  map_vadd' _ _ := rfl

@[simp]
theorem coe_snd : ⇑(snd : P1 × P2 →ᵃ[k] P2) = Prod.snd :=
  rfl

@[simp]
theorem snd_linear : (snd : P1 × P2 →ᵃ[k] P2).linear = LinearMap.snd k V1 V2 :=
  rfl

variable (k P1)
/-- Identity map as an affine map. -/
nonrec def id : P1 →ᵃ[k] P1 where
  toFun := id
  linear := LinearMap.id
  map_vadd' _ _ := rfl

/-- The identity affine map acts as the identity. -/
@[simp, norm_cast]
theorem coe_id : ⇑(id k P1) = _root_.id :=
  rfl

@[simp]
theorem id_linear : (id k P1).linear = LinearMap.id :=
  rfl

variable {P1}

/-- The identity affine map acts as the identity. -/
theorem id_apply (p : P1) : id k P1 p = p :=
  rfl

variable {k}

instance : Inhabited (P1 →ᵃ[k] P1) :=
  ⟨id k P1⟩

/-- Composition of affine maps. -/
@[simps linear]
def comp (f : P2 →ᵃ[k] P3) (g : P1 →ᵃ[k] P2) : P1 →ᵃ[k] P3 where
  toFun := f ∘ g
  linear := f.linear.comp g.linear
  map_vadd' := by
    intro p v
    rw [Function.comp_apply, g.map_vadd, f.map_vadd]
    rfl

/-- Composition of affine maps acts as applying the two functions. -/
@[simp]
theorem coe_comp (f : P2 →ᵃ[k] P3) (g : P1 →ᵃ[k] P2) : ⇑(f.comp g) = f ∘ g :=
  rfl

/-- Composition of affine maps acts as applying the two functions. -/
theorem comp_apply (f : P2 →ᵃ[k] P3) (g : P1 →ᵃ[k] P2) (p : P1) : f.comp g p = f (g p) :=
  rfl

@[simp]
theorem comp_id (f : P1 →ᵃ[k] P2) : f.comp (id k P1) = f :=
  ext fun _ => rfl

@[simp]
theorem id_comp (f : P1 →ᵃ[k] P2) : (id k P2).comp f = f :=
  ext fun _ => rfl

theorem comp_assoc (f₃₄ : P3 →ᵃ[k] P4) (f₂₃ : P2 →ᵃ[k] P3) (f₁₂ : P1 →ᵃ[k] P2) :
    (f₃₄.comp f₂₃).comp f₁₂ = f₃₄.comp (f₂₃.comp f₁₂) :=
  rfl

instance : Monoid (P1 →ᵃ[k] P1) where
  one := id k P1
  mul := comp
  one_mul := id_comp
  mul_one := comp_id
  mul_assoc := comp_assoc

@[simp]
theorem coe_mul (f g : P1 →ᵃ[k] P1) : ⇑(f * g) = f ∘ g :=
  rfl

@[simp]
theorem coe_one : ⇑(1 : P1 →ᵃ[k] P1) = _root_.id :=
  rfl

/-- `AffineMap.linear` on endomorphisms is a `MonoidHom`. -/
@[simps]
def linearHom : (P1 →ᵃ[k] P1) →* V1 →ₗ[k] V1 where
  toFun := linear
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem linear_injective_iff (f : P1 →ᵃ[k] P2) :
    Function.Injective f.linear ↔ Function.Injective f := by
  obtain ⟨p⟩ := (inferInstance : Nonempty P1)
  have h : ⇑f.linear = (Equiv.vaddConst (f p)).symm ∘ f ∘ Equiv.vaddConst p := by
    ext v
    simp [f.map_vadd]
  rw [h, Equiv.comp_injective, Equiv.injective_comp]

@[simp]
theorem linear_surjective_iff (f : P1 →ᵃ[k] P2) :
    Function.Surjective f.linear ↔ Function.Surjective f := by
  obtain ⟨p⟩ := (inferInstance : Nonempty P1)
  have h : ⇑f.linear = (Equiv.vaddConst (f p)).symm ∘ f ∘ Equiv.vaddConst p := by
    ext v
    simp [f.map_vadd]
  rw [h, Equiv.comp_surjective, Equiv.surjective_comp]

@[simp]
theorem linear_bijective_iff (f : P1 →ᵃ[k] P2) :
    Function.Bijective f.linear ↔ Function.Bijective f :=
  and_congr f.linear_injective_iff f.linear_surjective_iff

theorem image_vsub_image {s t : Set P1} (f : P1 →ᵃ[k] P2) :
    f '' s -ᵥ f '' t = f.linear '' (s -ᵥ t) := by
  ext v
  simp only [Set.mem_vsub, Set.mem_image,
    exists_exists_and_eq_and, ← f.linearMap_vsub]
  grind

/-- The product of two affine maps is an affine map. -/
@[simps linear]
def prod (f : P1 →ᵃ[k] P2) (g : P1 →ᵃ[k] P3) : P1 →ᵃ[k] P2 × P3 where
  toFun := Pi.prod f g
  linear := f.linear.prod g.linear
  map_vadd' := by simp

theorem coe_prod (f : P1 →ᵃ[k] P2) (g : P1 →ᵃ[k] P3) : prod f g = Pi.prod f g :=
  rfl

@[simp]
theorem prod_apply (f : P1 →ᵃ[k] P2) (g : P1 →ᵃ[k] P3) (p : P1) : prod f g p = (f p, g p) :=
  rfl

/-- `Prod.map` of two affine maps. -/
@[simps linear]
def prodMap (f : P1 →ᵃ[k] P2) (g : P3 →ᵃ[k] P4) : P1 × P3 →ᵃ[k] P2 × P4 where
  toFun := Prod.map f g
  linear := f.linear.prodMap g.linear
  map_vadd' := by simp

theorem coe_prodMap (f : P1 →ᵃ[k] P2) (g : P3 →ᵃ[k] P4) : ⇑(f.prodMap g) = Prod.map f g :=
  rfl

@[simp]
theorem prodMap_apply (f : P1 →ᵃ[k] P2) (g : P3 →ᵃ[k] P4) (x) : f.prodMap g x = (f x.1, g x.2) :=
  rfl

/-! ### Definition of `AffineMap.lineMap` and lemmas about it -/

/-- The affine map from `k` to `P1` sending `0` to `p₀` and `1` to `p₁`. -/
def lineMap (p₀ p₁ : P1) : k →ᵃ[k] P1 :=
  ((LinearMap.id : k →ₗ[k] k).smulRight (p₁ -ᵥ p₀)).toAffineMap +ᵥ const k k p₀

theorem coe_lineMap (p₀ p₁ : P1) : (lineMap p₀ p₁ : k → P1) = fun c => c • (p₁ -ᵥ p₀) +ᵥ p₀ :=
  rfl

theorem lineMap_apply (p₀ p₁ : P1) (c : k) : lineMap p₀ p₁ c = c • (p₁ -ᵥ p₀) +ᵥ p₀ :=
  rfl

theorem lineMap_apply_module' (p₀ p₁ : V1) (c : k) : lineMap p₀ p₁ c = c • (p₁ - p₀) + p₀ :=
  rfl

theorem lineMap_apply_module (p₀ p₁ : V1) (c : k) : lineMap p₀ p₁ c = (1 - c) • p₀ + c • p₁ := by
  simp [lineMap_apply_module', smul_sub, sub_smul]; abel

theorem lineMap_apply_ring' (a b c : k) : lineMap a b c = c * (b - a) + a :=
  rfl

theorem lineMap_apply_ring (a b c : k) : lineMap a b c = (1 - c) * a + c * b :=
  lineMap_apply_module a b c

theorem lineMap_vadd_apply (p : P1) (v : V1) (c : k) : lineMap p (v +ᵥ p) c = c • v +ᵥ p := by
  rw [lineMap_apply, vadd_vsub]

@[simp]
theorem lineMap_linear (p₀ p₁ : P1) :
    (lineMap p₀ p₁ : k →ᵃ[k] P1).linear = LinearMap.id.smulRight (p₁ -ᵥ p₀) :=
  add_zero _

theorem lineMap_same_apply (p : P1) (c : k) : lineMap p p c = p := by
  simp [lineMap_apply]

@[simp]
theorem lineMap_same (p : P1) : lineMap p p = const k k p :=
  ext <| lineMap_same_apply p

@[simp]
theorem lineMap_apply_zero (p₀ p₁ : P1) : lineMap p₀ p₁ (0 : k) = p₀ := by
  simp [lineMap_apply]

@[simp]
theorem lineMap_apply_one (p₀ p₁ : P1) : lineMap p₀ p₁ (1 : k) = p₁ := by
  simp [lineMap_apply]

@[simp]
theorem lineMap_eq_lineMap_iff [IsDomain k] [IsTorsionFree k V1] {p₀ p₁ : P1} {c₁ c₂ : k} :
    lineMap p₀ p₁ c₁ = lineMap p₀ p₁ c₂ ↔ p₀ = p₁ ∨ c₁ = c₂ := by
  rw [lineMap_apply, lineMap_apply, ← @vsub_eq_zero_iff_eq V1, vadd_vsub_vadd_cancel_right, ←
    sub_smul, smul_eq_zero, sub_eq_zero, vsub_eq_zero_iff_eq, or_comm, eq_comm]

@[simp]
theorem lineMap_eq_left_iff [IsDomain k] [IsTorsionFree k V1] {p₀ p₁ : P1} {c : k} :
    lineMap p₀ p₁ c = p₀ ↔ p₀ = p₁ ∨ c = 0 := by
  rw [← @lineMap_eq_lineMap_iff k V1, lineMap_apply_zero]

@[simp]
theorem lineMap_eq_right_iff [IsDomain k] [IsTorsionFree k V1] {p₀ p₁ : P1} {c : k} :
    lineMap p₀ p₁ c = p₁ ↔ p₀ = p₁ ∨ c = 1 := by
  rw [← @lineMap_eq_lineMap_iff k V1, lineMap_apply_one]

variable (k) in
theorem lineMap_injective [IsDomain k] [IsTorsionFree k V1] {p₀ p₁ : P1} (h : p₀ ≠ p₁) :
    Function.Injective (lineMap p₀ p₁ : k → P1) := fun _c₁ _c₂ hc =>
  (lineMap_eq_lineMap_iff.mp hc).resolve_left h

@[simp]
theorem apply_lineMap (f : P1 →ᵃ[k] P2) (p₀ p₁ : P1) (c : k) :
    f (lineMap p₀ p₁ c) = lineMap (f p₀) (f p₁) c := by
  simp [lineMap_apply]

@[simp]
theorem comp_lineMap (f : P1 →ᵃ[k] P2) (p₀ p₁ : P1) :
    f.comp (lineMap p₀ p₁) = lineMap (f p₀) (f p₁) :=
  ext <| f.apply_lineMap p₀ p₁

@[simp]
theorem fst_lineMap (p₀ p₁ : P1 × P2) (c : k) : (lineMap p₀ p₁ c).1 = lineMap p₀.1 p₁.1 c :=
  fst.apply_lineMap p₀ p₁ c

@[simp]
theorem snd_lineMap (p₀ p₁ : P1 × P2) (c : k) : (lineMap p₀ p₁ c).2 = lineMap p₀.2 p₁.2 c :=
  snd.apply_lineMap p₀ p₁ c

theorem lineMap_symm (p₀ p₁ : P1) :
    lineMap p₀ p₁ = (lineMap p₁ p₀).comp (lineMap (1 : k) (0 : k)) := by
  simp

@[simp]
theorem lineMap_apply_one_sub (p₀ p₁ : P1) (c : k) : lineMap p₀ p₁ (1 - c) = lineMap p₁ p₀ c := by
  rw [lineMap_symm p₀, comp_apply]
  congr
  simp [lineMap_apply]

@[simp]
theorem lineMap_vsub_left (p₀ p₁ : P1) (c : k) : lineMap p₀ p₁ c -ᵥ p₀ = c • (p₁ -ᵥ p₀) :=
  vadd_vsub _ _

@[simp]
theorem left_vsub_lineMap (p₀ p₁ : P1) (c : k) : p₀ -ᵥ lineMap p₀ p₁ c = c • (p₀ -ᵥ p₁) := by
  rw [← neg_vsub_eq_vsub_rev, lineMap_vsub_left, ← smul_neg, neg_vsub_eq_vsub_rev]

@[simp]
theorem lineMap_vsub_right (p₀ p₁ : P1) (c : k) : lineMap p₀ p₁ c -ᵥ p₁ = (1 - c) • (p₀ -ᵥ p₁) := by
  rw [← lineMap_apply_one_sub, lineMap_vsub_left]

@[simp]
theorem right_vsub_lineMap (p₀ p₁ : P1) (c : k) : p₁ -ᵥ lineMap p₀ p₁ c = (1 - c) • (p₁ -ᵥ p₀) := by
  rw [← lineMap_apply_one_sub, left_vsub_lineMap]

theorem lineMap_vadd_lineMap (v₁ v₂ : V1) (p₁ p₂ : P1) (c : k) :
    lineMap v₁ v₂ c +ᵥ lineMap p₁ p₂ c = lineMap (v₁ +ᵥ p₁) (v₂ +ᵥ p₂) c :=
  ((fst : V1 × P1 →ᵃ[k] V1) +ᵥ (snd : V1 × P1 →ᵃ[k] P1)).apply_lineMap (v₁, p₁) (v₂, p₂) c

theorem lineMap_vsub_lineMap (p₁ p₂ p₃ p₄ : P1) (c : k) :
    lineMap p₁ p₂ c -ᵥ lineMap p₃ p₄ c = lineMap (p₁ -ᵥ p₃) (p₂ -ᵥ p₄) c :=
  ((fst : P1 × P1 →ᵃ[k] P1) -ᵥ (snd : P1 × P1 →ᵃ[k] P1)).apply_lineMap (_, _) (_, _) c

@[simp] lemma lineMap_lineMap_right (p₀ p₁ : P1) (c d : k) :
    lineMap p₀ (lineMap p₀ p₁ c) d = lineMap p₀ p₁ (d * c) := by simp [lineMap_apply, mul_smul]

@[simp] lemma lineMap_lineMap_left (p₀ p₁ : P1) (c d : k) :
    lineMap (lineMap p₀ p₁ c) p₁ d = lineMap p₀ p₁ (1 - (1 - d) * (1 - c)) := by
  simp_rw [lineMap_apply_one_sub, ← lineMap_apply_one_sub p₁, lineMap_lineMap_right]

lemma lineMap_mono [LinearOrder k] [Preorder V1] [AddRightMono V1] [SMulPosMono k V1]
    {p₀ p₁ : V1} (h : p₀ ≤ p₁) :
    Monotone (lineMap (k := k) p₀ p₁) := by
  intro x y hxy
  suffices x • (p₁ - p₀) ≤ y • (p₁ - p₀) by simpa [lineMap]
  gcongr
  simpa

lemma lineMap_anti [LinearOrder k] [Preorder V1] [AddLeftMono V1] [SMulPosMono k V1]
    {p₀ p₁ : V1} (h : p₁ ≤ p₀) :
    Antitone (lineMap (k := k) p₀ p₁) := by
  intro x y hxy
  suffices y • (p₁ - p₀) ≤ x • (p₁ - p₀) by simpa [lineMap]
  rw [← neg_le_neg_iff, ← smul_neg, ← smul_neg]
  gcongr
  simpa

/-- Decomposition of an affine map in the special case when the point space and vector space
are the same. -/
theorem decomp (f : V1 →ᵃ[k] V2) : (f : V1 → V2) = ⇑f.linear + fun _ => f 0 := by
  ext x
  calc
    f x = f.linear x +ᵥ f 0 := by rw [← f.map_vadd, vadd_eq_add, add_zero]
    _ = (f.linear + fun _ : V1 => f 0) x := rfl

/-- Decomposition of an affine map in the special case when the point space and vector space
are the same. -/
theorem decomp' (f : V1 →ᵃ[k] V2) : (f.linear : V1 → V2) = ⇑f - fun _ => f 0 := by
  rw [decomp]
  simp only [map_zero, Pi.add_apply, add_sub_cancel_right, zero_add]

theorem image_uIcc {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k]
    (f : k →ᵃ[k] k) (a b : k) :
    f '' Set.uIcc a b = Set.uIcc (f a) (f b) := by
  have : ⇑f = (fun x => x + f 0) ∘ fun x => x * (f 1 - f 0) := by
    ext x
    change f x = x • (f 1 -ᵥ f 0) +ᵥ f 0
    rw [← f.linearMap_vsub, ← f.linear.map_smul, ← f.map_vadd]
    simp only [vsub_eq_sub, add_zero, mul_one, vadd_eq_add, sub_zero, smul_eq_mul]
  rw [this, Set.image_comp]
  simp only [Set.image_add_const_uIcc, Set.image_mul_const_uIcc, Function.comp_apply]

section

variable {ι : Type*} {V : ι → Type*} {P : ι → Type*} [∀ i, AddCommGroup (V i)]
  [∀ i, Module k (V i)] [∀ i, AddTorsor (V i) (P i)]

/-- Evaluation at a point as an affine map. -/
def proj (i : ι) : (∀ i : ι, P i) →ᵃ[k] P i where
  toFun f := f i
  linear := @LinearMap.proj k ι _ V _ _ i
  map_vadd' _ _ := rfl

@[simp]
theorem proj_apply (i : ι) (f : ∀ i, P i) : @proj k _ ι V P _ _ _ i f = f i :=
  rfl

@[simp]
theorem proj_linear (i : ι) : (@proj k _ ι V P _ _ _ i).linear = @LinearMap.proj k ι _ V _ _ i :=
  rfl

theorem pi_lineMap_apply (f g : ∀ i, P i) (c : k) (i : ι) :
    lineMap f g c i = lineMap (f i) (g i) c :=
  (proj i : (∀ i, P i) →ᵃ[k] P i).apply_lineMap f g c

end

end AffineMap

namespace AffineMap

variable {R k V1 P1 V2 P2 V3 P3 : Type*}

section Ring

variable [Ring k] [AddCommGroup V1] [AffineSpace V1 P1] [AddCommGroup V2] [AffineSpace V2 P2]
variable [AddCommGroup V3] [AffineSpace V3 P3] [Module k V1] [Module k V2] [Module k V3]

section DistribMulAction

variable [Monoid R] [DistribMulAction R V2] [SMulCommClass k R V2]

/-- The space of affine maps to a module inherits an `R`-action from the action on its codomain. -/
instance distribMulAction : DistribMulAction R (P1 →ᵃ[k] V2) where
  smul_add _ _ _ := ext fun _ => smul_add _ _ _
  smul_zero _ := ext fun _ => smul_zero _

end DistribMulAction

section Module

variable [Semiring R] [Module R V2] [SMulCommClass k R V2]

/-- The space of affine maps taking values in an `R`-module is an `R`-module. -/
instance : Module R (P1 →ᵃ[k] V2) :=
  { AffineMap.distribMulAction with
    add_smul := fun _ _ _ => ext fun _ => add_smul _ _ _
    zero_smul := fun _ => ext fun _ => zero_smul _ _ }

variable (R)

/-- The space of affine maps between two modules is linearly equivalent to the product of the
domain with the space of linear maps, by taking the value of the affine map at `(0 : V1)` and the
linear part.

See note [bundled maps over different rings] -/
@[simps]
def toConstProdLinearMap : (V1 →ᵃ[k] V2) ≃ₗ[R] V2 × (V1 →ₗ[k] V2) where
  toFun f := ⟨f 0, f.linear⟩
  invFun p := p.2.toAffineMap + const k V1 p.1
  left_inv f := by
    ext
    rw [f.decomp]
    simp
  right_inv := by
    rintro ⟨v, f⟩
    ext <;> simp [const_linear]
  map_add' := by simp
  map_smul' := by simp

end Module

/-- Interpolating between affine maps with `lineMap` commutes with evaluation. -/
@[simp]
lemma lineMap_apply' [SMulCommClass k k V2] (f g : P1 →ᵃ[k] P2) (c : k)
    (p : P1) : lineMap f g c p = lineMap (f p) (g p) c := by
  simp [AffineMap.lineMap_apply]

section Pi

variable {ι : Type*} {φv φp : ι → Type*} [(i : ι) → AddCommGroup (φv i)]
  [(i : ι) → Module k (φv i)] [(i : ι) → AffineSpace (φv i) (φp i)]
/-- `pi` construction for affine maps. From a family of affine maps it produces an affine
map into a family of affine spaces.

This is the affine version of `LinearMap.pi`.
-/
@[simps linear]
def pi (f : (i : ι) → (P1 →ᵃ[k] φp i)) : P1 →ᵃ[k] ((i : ι) → φp i) where
  toFun m a := f a m
  linear := LinearMap.pi (fun a ↦ (f a).linear)
  map_vadd' _ _ := funext fun _ ↦ map_vadd _ _ _

--fp for when the image is a dependent AffineSpace φp i, fv for when the
--image is a Module φv i, f' for when the image isn't dependent.
variable (fp : (i : ι) → (P1 →ᵃ[k] φp i)) (fv : (i : ι) → (P1 →ᵃ[k] φv i))
  (f' : ι → P1 →ᵃ[k] P2)

@[simp]
theorem pi_apply (c : P1) (i : ι) : pi fp c i = fp i c :=
  rfl

theorem pi_comp (g : P3 →ᵃ[k] P1) : (pi fp).comp g = pi (fun i => (fp i).comp g) :=
  rfl

theorem pi_eq_zero : pi fv = 0 ↔ ∀ i, fv i = 0 := by
  simp only [AffineMap.ext_iff, funext_iff, pi_apply]
  exact forall_comm

theorem pi_zero : pi (fun _ ↦ 0 : (i : ι) → P1 →ᵃ[k] φv i) = 0 := by
  ext; rfl

theorem proj_pi (i : ι) : (proj i).comp (pi fp) = fp i :=
  ext fun _ => rfl
section Ext

variable [Finite ι] [DecidableEq ι] {f g : ((i : ι) → φv i) →ᵃ[k] P2}

/-- Two affine maps from a Pi-type of modules `(i : ι) → φv i` are equal if they are equal in their
  operation on `Pi.single` and at zero. Analogous to `LinearMap.pi_ext`. See also `pi_ext_nonempty`,
  which instead of agreement at zero requires `Nonempty ι`. -/
theorem pi_ext_zero (h : ∀ i x, f (Pi.single i x) = g (Pi.single i x)) (h₂ : f 0 = g 0) :
    f = g := by
  apply ext_linear
  · apply LinearMap.pi_ext
    intro i x
    have s₁ := h i x
    have s₂ := f.map_vadd 0 (Pi.single i x)
    have s₃ := g.map_vadd 0 (Pi.single i x)
    rw [vadd_eq_add, add_zero] at s₂ s₃
    replace h₂ := h i 0
    simp only [Pi.single_zero] at h₂
    rwa [s₂, s₃, h₂, vadd_right_cancel_iff] at s₁
  · exact h₂

/-- Two affine maps from a Pi-type of modules `(i : ι) → φv i` are equal if they are equal in their
  operation on `Pi.single` and `ι` is nonempty.  Analogous to `LinearMap.pi_ext`. See also
  `pi_ext_zero`, which instead of `Nonempty ι` requires agreement at 0. -/
theorem pi_ext_nonempty [Nonempty ι] (h : ∀ i x, f (Pi.single i x) = g (Pi.single i x)) :
    f = g := by
  apply pi_ext_zero h
  inhabit ι
  rw [← Pi.single_zero default]
  apply h

/-- This is used as the ext lemma instead of `AffineMap.pi_ext_nonempty` for reasons explained in
note [partially-applied ext lemmas]. Analogous to `LinearMap.pi_ext'` -/
@[ext (iff := false)]
theorem pi_ext_nonempty' [Nonempty ι] (h : ∀ i, f.comp (LinearMap.single _ _ i).toAffineMap =
    g.comp (LinearMap.single _ _ i).toAffineMap) : f = g := by
  refine pi_ext_nonempty fun i x => ?_
  convert AffineMap.congr_fun (h i) x

end Ext

end Pi

end Ring

section CommRing

variable [CommRing k] [AddCommGroup V1] [AffineSpace V1 P1] [AddCommGroup V2]
variable [Module k V1] [Module k V2]

/-- `homothety c r` is the homothety (also known as dilation) about `c` with scale factor `r`. -/
def homothety (c : P1) (r : k) : P1 →ᵃ[k] P1 :=
  r • (id k P1 -ᵥ const k P1 c) +ᵥ const k P1 c

theorem homothety_def (c : P1) (r : k) :
    homothety c r = r • (id k P1 -ᵥ const k P1 c) +ᵥ const k P1 c :=
  rfl

theorem coe_homothety (c : P1) (r : k) : homothety c r = fun p => r • (p -ᵥ c) +ᵥ c :=
  rfl

theorem homothety_apply (c : P1) (r : k) (p : P1) : homothety c r p = r • (p -ᵥ c : V1) +ᵥ c :=
  rfl

@[simp]
theorem homothety_linear (c : P1) (r : k) : (homothety c r).linear = r • LinearMap.id := by
  simp [homothety]

theorem homothety_eq_lineMap (c : P1) (r : k) (p : P1) : homothety c r p = lineMap c p r :=
  rfl

@[simp]
theorem homothety_one (c : P1) : homothety c (1 : k) = id k P1 := by
  ext p
  simp [homothety_apply]

@[simp]
theorem homothety_apply_same (c : P1) (r : k) : homothety c r c = c :=
  lineMap_same_apply c r

theorem homothety_mul_apply (c : P1) (r₁ r₂ : k) (p : P1) :
    homothety c (r₁ * r₂) p = homothety c r₁ (homothety c r₂ p) := by
  simp only [homothety_apply, mul_smul, vadd_vsub]

theorem homothety_mul (c : P1) (r₁ r₂ : k) :
    homothety c (r₁ * r₂) = (homothety c r₁).comp (homothety c r₂) :=
  ext <| homothety_mul_apply c r₁ r₂

@[simp]
theorem homothety_zero (c : P1) : homothety c (0 : k) = const k P1 c := by
  ext p
  simp [homothety_apply]

@[simp]
theorem homothety_add (c : P1) (r₁ r₂ : k) :
    homothety c (r₁ + r₂) = r₁ • (id k P1 -ᵥ const k P1 c) +ᵥ homothety c r₂ := by
  simp only [homothety_def, add_smul, vadd_vadd]

theorem homothety_eq_iff_of_mul_eq_one {c p q : P1} {r₁ r₂ : k} (h : r₁ * r₂ = 1) :
    homothety c r₁ p = q ↔ homothety c r₂ q = p := by
  obtain h' : r₂ * r₁ = 1 := mul_eq_one_comm.mp h
  refine ⟨fun h1 ↦ ?_, fun h1 ↦ ?_⟩
  all_goals
    rw [← h1, ← homothety_mul_apply]
    simp [h, h']

theorem homothety_injective [Module.IsTorsionFree k V1] [IsCancelMulZero k] (c : P1) {r : k}
    (hr : r ≠ 0) :
    Function.Injective (homothety c r) :=
  fun _ _ h ↦ by simpa [homothety_def, hr] using h

@[simp]
theorem homothety_inj [Module.IsTorsionFree k V1] [IsCancelMulZero k] (c : P1) {r : k} (hr : r ≠ 0)
    {p q : P1} :
    homothety c r p = homothety c r q ↔ p = q :=
  (homothety_injective c hr).eq_iff

/-- `homothety` as a multiplicative monoid homomorphism. -/
def homothetyHom (c : P1) : k →* P1 →ᵃ[k] P1 where
  toFun := homothety c
  map_one' := homothety_one c
  map_mul' := homothety_mul c

@[simp]
theorem coe_homothetyHom (c : P1) : ⇑(homothetyHom c : k →* _) = homothety c :=
  rfl

/-- `homothety` as an affine map. -/
def homothetyAffine (c : P1) : k →ᵃ[k] P1 →ᵃ[k] P1 :=
  ⟨homothety c, (LinearMap.lsmul k _).flip (id k P1 -ᵥ const k P1 c),
    Function.swap (homothety_add c)⟩

@[simp]
theorem coe_homothetyAffine (c : P1) : ⇑(homothetyAffine c : k →ᵃ[k] _) = homothety c :=
  rfl

end CommRing

end AffineMap

section

variable {𝕜 E F : Type*} [Ring 𝕜] [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F]

/-- Applying an affine map to an affine combination of two points yields an affine combination of
the images. -/
theorem Convex.combo_affine_apply {x y : E} {a b : 𝕜} {f : E →ᵃ[𝕜] F} (h : a + b = 1) :
    f (a • x + b • y) = a • f x + b • f y := by
  simp only [Convex.combo_eq_smul_sub_add h, ← vsub_eq_sub]
  exact f.apply_lineMap _ _ _

end
