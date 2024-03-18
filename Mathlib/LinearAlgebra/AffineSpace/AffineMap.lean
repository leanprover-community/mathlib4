/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Data.Set.Pointwise.Interval
import Mathlib.LinearAlgebra.AffineSpace.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod

#align_import linear_algebra.affine_space.affine_map from "leanprover-community/mathlib"@"bd1fc183335ea95a9519a1630bcf901fe9326d83"

/-!
# Affine maps

This file defines affine maps.

## Main definitions

* `AffineMap` is the type of affine maps between two affine spaces with the same ring `k`.  Various
  basic examples of affine maps are defined, including `const`, `id`, `lineMap` and `homothety`.

## Notations

* `P1 →ᵃ[k] P2` is a notation for `AffineMap k P1 P2`;
* `AffineSpace V P`: a localized notation for `AddTorsor V P` defined in
  `LinearAlgebra.AffineSpace.Basic`.

## Implementation notes

`outParam` is used in the definition of `[AddTorsor V P]` to make `V` an implicit argument
(deduced from `P`) in most cases. As for modules, `k` is an explicit argument rather than implied by
`P` or `V`.

This file only provides purely algebraic definitions and results. Those depending on analysis or
topology are defined elsewhere; see `Analysis.NormedSpace.AddTorsor` and
`Topology.Algebra.Affine`.

## References

* https://en.wikipedia.org/wiki/Affine_space
* https://en.wikipedia.org/wiki/Principal_homogeneous_space
-/

open Affine

/-- An `AffineMap k P1 P2` (notation: `P1 →ᵃ[k] P2`) is a map from `P1` to `P2` that
induces a corresponding linear map from `V1` to `V2`. -/
structure AffineMap (k : Type*) {V1 : Type*} (P1 : Type*) {V2 : Type*} (P2 : Type*) [Ring k]
  [AddCommGroup V1] [Module k V1] [AffineSpace V1 P1] [AddCommGroup V2] [Module k V2]
  [AffineSpace V2 P2] where
  toFun : P1 → P2
  linear : V1 →ₗ[k] V2
  map_vadd' : ∀ (p : P1) (v : V1), toFun (v +ᵥ p) = linear v +ᵥ toFun p
#align affine_map AffineMap

/-- An `AffineMap k P1 P2` (notation: `P1 →ᵃ[k] P2`) is a map from `P1` to `P2` that
induces a corresponding linear map from `V1` to `V2`. -/
notation:25 P1 " →ᵃ[" k:25 "] " P2:0 => AffineMap k P1 P2

instance AffineMap.instFunLike (k : Type*) {V1 : Type*} (P1 : Type*) {V2 : Type*} (P2 : Type*)
    [Ring k] [AddCommGroup V1] [Module k V1] [AffineSpace V1 P1] [AddCommGroup V2] [Module k V2]
    [AffineSpace V2 P2] : FunLike (P1 →ᵃ[k] P2) P1 P2
    where
  coe := AffineMap.toFun
  coe_injective' := fun ⟨f, f_linear, f_add⟩ ⟨g, g_linear, g_add⟩ => fun (h : f = g) => by
    cases' (AddTorsor.nonempty : Nonempty P1) with p
    congr with v
    apply vadd_right_cancel (f p)
    erw [← f_add, h, ← g_add]
#align affine_map.fun_like AffineMap.instFunLike

instance AffineMap.hasCoeToFun (k : Type*) {V1 : Type*} (P1 : Type*) {V2 : Type*} (P2 : Type*)
    [Ring k] [AddCommGroup V1] [Module k V1] [AffineSpace V1 P1] [AddCommGroup V2] [Module k V2]
    [AffineSpace V2 P2] : CoeFun (P1 →ᵃ[k] P2) fun _ => P1 → P2 :=
  DFunLike.hasCoeToFun
#align affine_map.has_coe_to_fun AffineMap.hasCoeToFun

namespace LinearMap

variable {k : Type*} {V₁ : Type*} {V₂ : Type*} [Ring k] [AddCommGroup V₁] [Module k V₁]
  [AddCommGroup V₂] [Module k V₂] (f : V₁ →ₗ[k] V₂)

/-- Reinterpret a linear map as an affine map. -/
def toAffineMap : V₁ →ᵃ[k] V₂ where
  toFun := f
  linear := f
  map_vadd' p v := f.map_add v p
#align linear_map.to_affine_map LinearMap.toAffineMap

@[simp]
theorem coe_toAffineMap : ⇑f.toAffineMap = f :=
  rfl
#align linear_map.coe_to_affine_map LinearMap.coe_toAffineMap

@[simp]
theorem toAffineMap_linear : f.toAffineMap.linear = f :=
  rfl
#align linear_map.to_affine_map_linear LinearMap.toAffineMap_linear

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
#align affine_map.coe_mk AffineMap.coe_mk

/-- `toFun` is the same as the result of coercing to a function. -/
@[simp]
theorem toFun_eq_coe (f : P1 →ᵃ[k] P2) : f.toFun = ⇑f :=
  rfl
#align affine_map.to_fun_eq_coe AffineMap.toFun_eq_coe

/-- An affine map on the result of adding a vector to a point produces
the same result as the linear map applied to that vector, added to the
affine map applied to that point. -/
@[simp]
theorem map_vadd (f : P1 →ᵃ[k] P2) (p : P1) (v : V1) : f (v +ᵥ p) = f.linear v +ᵥ f p :=
  f.map_vadd' p v
#align affine_map.map_vadd AffineMap.map_vadd

/-- The linear map on the result of subtracting two points is the
result of subtracting the result of the affine map on those two
points. -/
@[simp]
theorem linearMap_vsub (f : P1 →ᵃ[k] P2) (p1 p2 : P1) : f.linear (p1 -ᵥ p2) = f p1 -ᵥ f p2 := by
  conv_rhs => rw [← vsub_vadd p1 p2, map_vadd, vadd_vsub]
#align affine_map.linear_map_vsub AffineMap.linearMap_vsub

/-- Two affine maps are equal if they coerce to the same function. -/
@[ext]
theorem ext {f g : P1 →ᵃ[k] P2} (h : ∀ p, f p = g p) : f = g :=
  DFunLike.ext _ _ h
#align affine_map.ext AffineMap.ext

theorem ext_iff {f g : P1 →ᵃ[k] P2} : f = g ↔ ∀ p, f p = g p :=
  ⟨fun h _ => h ▸ rfl, ext⟩
#align affine_map.ext_iff AffineMap.ext_iff

theorem coeFn_injective : @Function.Injective (P1 →ᵃ[k] P2) (P1 → P2) (⇑) :=
  DFunLike.coe_injective
#align affine_map.coe_fn_injective AffineMap.coeFn_injective

protected theorem congr_arg (f : P1 →ᵃ[k] P2) {x y : P1} (h : x = y) : f x = f y :=
  congr_arg _ h
#align affine_map.congr_arg AffineMap.congr_arg

protected theorem congr_fun {f g : P1 →ᵃ[k] P2} (h : f = g) (x : P1) : f x = g x :=
  h ▸ rfl
#align affine_map.congr_fun AffineMap.congr_fun

/-- Two affine maps are equal if they have equal linear maps and are equal at some point. -/
theorem ext_linear {f g : P1 →ᵃ[k] P2} (h₁ : f.linear = g.linear) {p : P1} (h₂ : f p = g p) :
    f = g := by
  ext q
  have hgl : g.linear (q -ᵥ p) = toFun g ((q -ᵥ p) +ᵥ q) -ᵥ toFun g q := by simp
  have := f.map_vadd' q (q -ᵥ p)
  rw [h₁, hgl, toFun_eq_coe, map_vadd, linearMap_vsub, h₂] at this
  simp at this
  exact this

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
#align affine_map.const AffineMap.const

@[simp]
theorem coe_const (p : P2) : ⇑(const k P1 p) = Function.const P1 p :=
  rfl
#align affine_map.coe_const AffineMap.coe_const

-- Porting note (#10756): new theorem
@[simp]
theorem const_apply (p : P2) (q : P1) : (const k P1 p) q = p := rfl

@[simp]
theorem const_linear (p : P2) : (const k P1 p).linear = 0 :=
  rfl
#align affine_map.const_linear AffineMap.const_linear

variable {k P1}

theorem linear_eq_zero_iff_exists_const (f : P1 →ᵃ[k] P2) :
    f.linear = 0 ↔ ∃ q, f = const k P1 q := by
  refine' ⟨fun h => _, fun h => _⟩
  · use f (Classical.arbitrary P1)
    ext
    rw [coe_const, Function.const_apply, ← @vsub_eq_zero_iff_eq V2, ← f.linearMap_vsub, h,
      LinearMap.zero_apply]
  · rcases h with ⟨q, rfl⟩
    exact const_linear k P1 q
#align affine_map.linear_eq_zero_iff_exists_const AffineMap.linear_eq_zero_iff_exists_const

instance nonempty : Nonempty (P1 →ᵃ[k] P2) :=
  (AddTorsor.nonempty : Nonempty P2).map <| const k P1
#align affine_map.nonempty AffineMap.nonempty

/-- Construct an affine map by verifying the relation between the map and its linear part at one
base point. Namely, this function takes a map `f : P₁ → P₂`, a linear map `f' : V₁ →ₗ[k] V₂`, and
a point `p` such that for any other point `p'` we have `f p' = f' (p' -ᵥ p) +ᵥ f p`. -/
def mk' (f : P1 → P2) (f' : V1 →ₗ[k] V2) (p : P1) (h : ∀ p' : P1, f p' = f' (p' -ᵥ p) +ᵥ f p) :
    P1 →ᵃ[k] P2 where
  toFun := f
  linear := f'
  map_vadd' p' v := by rw [h, h p', vadd_vsub_assoc, f'.map_add, vadd_vadd]
#align affine_map.mk' AffineMap.mk'

@[simp]
theorem coe_mk' (f : P1 → P2) (f' : V1 →ₗ[k] V2) (p h) : ⇑(mk' f f' p h) = f :=
  rfl
#align affine_map.coe_mk' AffineMap.coe_mk'

@[simp]
theorem mk'_linear (f : P1 → P2) (f' : V1 →ₗ[k] V2) (p h) : (mk' f f' p h).linear = f' :=
  rfl
#align affine_map.mk'_linear AffineMap.mk'_linear

section SMul

variable {R : Type*} [Monoid R] [DistribMulAction R V2] [SMulCommClass k R V2]
/-- The space of affine maps to a module inherits an `R`-action from the action on its codomain. -/
instance mulAction : MulAction R (P1 →ᵃ[k] V2) where
  -- Porting note: `map_vadd` is `simp`, but we still have to pass it explicitly
  smul c f := ⟨c • ⇑f, c • f.linear, fun p v => by simp [smul_add, map_vadd f]⟩
  one_smul f := ext fun p => one_smul _ _
  mul_smul c₁ c₂ f := ext fun p => mul_smul _ _ _

@[simp, norm_cast]
theorem coe_smul (c : R) (f : P1 →ᵃ[k] V2) : ⇑(c • f) = c • ⇑f :=
  rfl
#align affine_map.coe_smul AffineMap.coe_smul

@[simp]
theorem smul_linear (t : R) (f : P1 →ᵃ[k] V2) : (t • f).linear = t • f.linear :=
  rfl
#align affine_map.smul_linear AffineMap.smul_linear

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
#align affine_map.coe_zero AffineMap.coe_zero

@[simp, norm_cast]
theorem coe_add (f g : P1 →ᵃ[k] V2) : ⇑(f + g) = f + g :=
  rfl
#align affine_map.coe_add AffineMap.coe_add

@[simp, norm_cast]
theorem coe_neg (f : P1 →ᵃ[k] V2) : ⇑(-f) = -f :=
  rfl
#align affine_map.coe_neg AffineMap.coe_neg

@[simp, norm_cast]
theorem coe_sub (f g : P1 →ᵃ[k] V2) : ⇑(f - g) = f - g :=
  rfl
#align affine_map.coe_sub AffineMap.coe_sub

@[simp]
theorem zero_linear : (0 : P1 →ᵃ[k] V2).linear = 0 :=
  rfl
#align affine_map.zero_linear AffineMap.zero_linear

@[simp]
theorem add_linear (f g : P1 →ᵃ[k] V2) : (f + g).linear = f.linear + g.linear :=
  rfl
#align affine_map.add_linear AffineMap.add_linear

@[simp]
theorem sub_linear (f g : P1 →ᵃ[k] V2) : (f - g).linear = f.linear - g.linear :=
  rfl
#align affine_map.sub_linear AffineMap.sub_linear

@[simp]
theorem neg_linear (f : P1 →ᵃ[k] V2) : (-f).linear = -f.linear :=
  rfl
#align affine_map.neg_linear AffineMap.neg_linear

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
      simp [vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, add_sub, sub_add_eq_add_sub]⟩
  vsub_vadd' f g := ext fun p => vsub_vadd (f p) (g p)
  vadd_vsub' f g := ext fun p => vadd_vsub (f p) (g p)

@[simp]
theorem vadd_apply (f : P1 →ᵃ[k] V2) (g : P1 →ᵃ[k] P2) (p : P1) : (f +ᵥ g) p = f p +ᵥ g p :=
  rfl
#align affine_map.vadd_apply AffineMap.vadd_apply

@[simp]
theorem vsub_apply (f g : P1 →ᵃ[k] P2) (p : P1) : (f -ᵥ g : P1 →ᵃ[k] V2) p = f p -ᵥ g p :=
  rfl
#align affine_map.vsub_apply AffineMap.vsub_apply

/-- `Prod.fst` as an `AffineMap`. -/
def fst : P1 × P2 →ᵃ[k] P1 where
  toFun := Prod.fst
  linear := LinearMap.fst k V1 V2
  map_vadd' _ _ := rfl
#align affine_map.fst AffineMap.fst

@[simp]
theorem coe_fst : ⇑(fst : P1 × P2 →ᵃ[k] P1) = Prod.fst :=
  rfl
#align affine_map.coe_fst AffineMap.coe_fst

@[simp]
theorem fst_linear : (fst : P1 × P2 →ᵃ[k] P1).linear = LinearMap.fst k V1 V2 :=
  rfl
#align affine_map.fst_linear AffineMap.fst_linear

/-- `Prod.snd` as an `AffineMap`. -/
def snd : P1 × P2 →ᵃ[k] P2 where
  toFun := Prod.snd
  linear := LinearMap.snd k V1 V2
  map_vadd' _ _ := rfl
#align affine_map.snd AffineMap.snd

@[simp]
theorem coe_snd : ⇑(snd : P1 × P2 →ᵃ[k] P2) = Prod.snd :=
  rfl
#align affine_map.coe_snd AffineMap.coe_snd

@[simp]
theorem snd_linear : (snd : P1 × P2 →ᵃ[k] P2).linear = LinearMap.snd k V1 V2 :=
  rfl
#align affine_map.snd_linear AffineMap.snd_linear

variable (k P1)
/-- Identity map as an affine map. -/
nonrec def id : P1 →ᵃ[k] P1 where
  toFun := id
  linear := LinearMap.id
  map_vadd' _ _ := rfl
#align affine_map.id AffineMap.id

/-- The identity affine map acts as the identity. -/
@[simp]
theorem coe_id : ⇑(id k P1) = _root_.id :=
  rfl
#align affine_map.coe_id AffineMap.coe_id

@[simp]
theorem id_linear : (id k P1).linear = LinearMap.id :=
  rfl
#align affine_map.id_linear AffineMap.id_linear

variable {P1}

/-- The identity affine map acts as the identity. -/
theorem id_apply (p : P1) : id k P1 p = p :=
  rfl
#align affine_map.id_apply AffineMap.id_apply

variable {k}

instance : Inhabited (P1 →ᵃ[k] P1) :=
  ⟨id k P1⟩

/-- Composition of affine maps. -/
def comp (f : P2 →ᵃ[k] P3) (g : P1 →ᵃ[k] P2) : P1 →ᵃ[k] P3 where
  toFun := f ∘ g
  linear := f.linear.comp g.linear
  map_vadd' := by
    intro p v
    rw [Function.comp_apply, g.map_vadd, f.map_vadd]
    rfl
#align affine_map.comp AffineMap.comp

/-- Composition of affine maps acts as applying the two functions. -/
@[simp]
theorem coe_comp (f : P2 →ᵃ[k] P3) (g : P1 →ᵃ[k] P2) : ⇑(f.comp g) = f ∘ g :=
  rfl
#align affine_map.coe_comp AffineMap.coe_comp

/-- Composition of affine maps acts as applying the two functions. -/
theorem comp_apply (f : P2 →ᵃ[k] P3) (g : P1 →ᵃ[k] P2) (p : P1) : f.comp g p = f (g p) :=
  rfl
#align affine_map.comp_apply AffineMap.comp_apply

@[simp]
theorem comp_id (f : P1 →ᵃ[k] P2) : f.comp (id k P1) = f :=
  ext fun _ => rfl
#align affine_map.comp_id AffineMap.comp_id

@[simp]
theorem id_comp (f : P1 →ᵃ[k] P2) : (id k P2).comp f = f :=
  ext fun _ => rfl
#align affine_map.id_comp AffineMap.id_comp

theorem comp_assoc (f₃₄ : P3 →ᵃ[k] P4) (f₂₃ : P2 →ᵃ[k] P3) (f₁₂ : P1 →ᵃ[k] P2) :
    (f₃₄.comp f₂₃).comp f₁₂ = f₃₄.comp (f₂₃.comp f₁₂) :=
  rfl
#align affine_map.comp_assoc AffineMap.comp_assoc

instance : Monoid (P1 →ᵃ[k] P1) where
  one := id k P1
  mul := comp
  one_mul := id_comp
  mul_one := comp_id
  mul_assoc := comp_assoc

@[simp]
theorem coe_mul (f g : P1 →ᵃ[k] P1) : ⇑(f * g) = f ∘ g :=
  rfl
#align affine_map.coe_mul AffineMap.coe_mul

@[simp]
theorem coe_one : ⇑(1 : P1 →ᵃ[k] P1) = _root_.id :=
  rfl
#align affine_map.coe_one AffineMap.coe_one

/-- `AffineMap.linear` on endomorphisms is a `MonoidHom`. -/
@[simps]
def linearHom : (P1 →ᵃ[k] P1) →* V1 →ₗ[k] V1 where
  toFun := linear
  map_one' := rfl
  map_mul' _ _ := rfl
#align affine_map.linear_hom AffineMap.linearHom

@[simp]
theorem linear_injective_iff (f : P1 →ᵃ[k] P2) :
    Function.Injective f.linear ↔ Function.Injective f := by
  obtain ⟨p⟩ := (inferInstance : Nonempty P1)
  have h : ⇑f.linear = (Equiv.vaddConst (f p)).symm ∘ f ∘ Equiv.vaddConst p := by
    ext v
    simp [f.map_vadd, vadd_vsub_assoc]
  rw [h, Equiv.comp_injective, Equiv.injective_comp]
#align affine_map.linear_injective_iff AffineMap.linear_injective_iff

@[simp]
theorem linear_surjective_iff (f : P1 →ᵃ[k] P2) :
    Function.Surjective f.linear ↔ Function.Surjective f := by
  obtain ⟨p⟩ := (inferInstance : Nonempty P1)
  have h : ⇑f.linear = (Equiv.vaddConst (f p)).symm ∘ f ∘ Equiv.vaddConst p := by
    ext v
    simp [f.map_vadd, vadd_vsub_assoc]
  rw [h, Equiv.comp_surjective, Equiv.surjective_comp]
#align affine_map.linear_surjective_iff AffineMap.linear_surjective_iff

@[simp]
theorem linear_bijective_iff (f : P1 →ᵃ[k] P2) :
    Function.Bijective f.linear ↔ Function.Bijective f :=
  and_congr f.linear_injective_iff f.linear_surjective_iff
#align affine_map.linear_bijective_iff AffineMap.linear_bijective_iff

theorem image_vsub_image {s t : Set P1} (f : P1 →ᵃ[k] P2) :
    f '' s -ᵥ f '' t = f.linear '' (s -ᵥ t) := by
  ext v
  -- Porting note: `simp` needs `Set.mem_vsub` to be an expression
  simp only [(Set.mem_vsub), Set.mem_image,
    exists_exists_and_eq_and, exists_and_left, ← f.linearMap_vsub]
  constructor
  · rintro ⟨x, hx, y, hy, hv⟩
    exact ⟨x -ᵥ y, ⟨x, hx, y, hy, rfl⟩, hv⟩
  · rintro ⟨-, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    exact ⟨x, hx, y, hy, rfl⟩
#align affine_map.image_vsub_image AffineMap.image_vsub_image

/-! ### Definition of `AffineMap.lineMap` and lemmas about it -/

/-- The affine map from `k` to `P1` sending `0` to `p₀` and `1` to `p₁`. -/
def lineMap (p₀ p₁ : P1) : k →ᵃ[k] P1 :=
  ((LinearMap.id : k →ₗ[k] k).smulRight (p₁ -ᵥ p₀)).toAffineMap +ᵥ const k k p₀
#align affine_map.line_map AffineMap.lineMap

theorem coe_lineMap (p₀ p₁ : P1) : (lineMap p₀ p₁ : k → P1) = fun c => c • (p₁ -ᵥ p₀) +ᵥ p₀ :=
  rfl
#align affine_map.coe_line_map AffineMap.coe_lineMap

theorem lineMap_apply (p₀ p₁ : P1) (c : k) : lineMap p₀ p₁ c = c • (p₁ -ᵥ p₀) +ᵥ p₀ :=
  rfl
#align affine_map.line_map_apply AffineMap.lineMap_apply

theorem lineMap_apply_module' (p₀ p₁ : V1) (c : k) : lineMap p₀ p₁ c = c • (p₁ - p₀) + p₀ :=
  rfl
#align affine_map.line_map_apply_module' AffineMap.lineMap_apply_module'

theorem lineMap_apply_module (p₀ p₁ : V1) (c : k) : lineMap p₀ p₁ c = (1 - c) • p₀ + c • p₁ := by
  simp [lineMap_apply_module', smul_sub, sub_smul]; abel
#align affine_map.line_map_apply_module AffineMap.lineMap_apply_module

theorem lineMap_apply_ring' (a b c : k) : lineMap a b c = c * (b - a) + a :=
  rfl
#align affine_map.line_map_apply_ring' AffineMap.lineMap_apply_ring'

theorem lineMap_apply_ring (a b c : k) : lineMap a b c = (1 - c) * a + c * b :=
  lineMap_apply_module a b c
#align affine_map.line_map_apply_ring AffineMap.lineMap_apply_ring

theorem lineMap_vadd_apply (p : P1) (v : V1) (c : k) : lineMap p (v +ᵥ p) c = c • v +ᵥ p := by
  rw [lineMap_apply, vadd_vsub]
#align affine_map.line_map_vadd_apply AffineMap.lineMap_vadd_apply

@[simp]
theorem lineMap_linear (p₀ p₁ : P1) :
    (lineMap p₀ p₁ : k →ᵃ[k] P1).linear = LinearMap.id.smulRight (p₁ -ᵥ p₀) :=
  add_zero _
#align affine_map.line_map_linear AffineMap.lineMap_linear

theorem lineMap_same_apply (p : P1) (c : k) : lineMap p p c = p := by
  simp [lineMap_apply]
#align affine_map.line_map_same_apply AffineMap.lineMap_same_apply

@[simp]
theorem lineMap_same (p : P1) : lineMap p p = const k k p :=
  ext <| lineMap_same_apply p
#align affine_map.line_map_same AffineMap.lineMap_same

@[simp]
theorem lineMap_apply_zero (p₀ p₁ : P1) : lineMap p₀ p₁ (0 : k) = p₀ := by
  simp [lineMap_apply]
#align affine_map.line_map_apply_zero AffineMap.lineMap_apply_zero

@[simp]
theorem lineMap_apply_one (p₀ p₁ : P1) : lineMap p₀ p₁ (1 : k) = p₁ := by
  simp [lineMap_apply]
#align affine_map.line_map_apply_one AffineMap.lineMap_apply_one

@[simp]
theorem lineMap_eq_lineMap_iff [NoZeroSMulDivisors k V1] {p₀ p₁ : P1} {c₁ c₂ : k} :
    lineMap p₀ p₁ c₁ = lineMap p₀ p₁ c₂ ↔ p₀ = p₁ ∨ c₁ = c₂ := by
  rw [lineMap_apply, lineMap_apply, ← @vsub_eq_zero_iff_eq V1, vadd_vsub_vadd_cancel_right, ←
    sub_smul, smul_eq_zero, sub_eq_zero, vsub_eq_zero_iff_eq, or_comm, eq_comm]
#align affine_map.line_map_eq_line_map_iff AffineMap.lineMap_eq_lineMap_iff

@[simp]
theorem lineMap_eq_left_iff [NoZeroSMulDivisors k V1] {p₀ p₁ : P1} {c : k} :
    lineMap p₀ p₁ c = p₀ ↔ p₀ = p₁ ∨ c = 0 := by
  rw [← @lineMap_eq_lineMap_iff k V1, lineMap_apply_zero]
#align affine_map.line_map_eq_left_iff AffineMap.lineMap_eq_left_iff

@[simp]
theorem lineMap_eq_right_iff [NoZeroSMulDivisors k V1] {p₀ p₁ : P1} {c : k} :
    lineMap p₀ p₁ c = p₁ ↔ p₀ = p₁ ∨ c = 1 := by
  rw [← @lineMap_eq_lineMap_iff k V1, lineMap_apply_one]
#align affine_map.line_map_eq_right_iff AffineMap.lineMap_eq_right_iff

variable (k)

theorem lineMap_injective [NoZeroSMulDivisors k V1] {p₀ p₁ : P1} (h : p₀ ≠ p₁) :
    Function.Injective (lineMap p₀ p₁ : k → P1) := fun _c₁ _c₂ hc =>
  (lineMap_eq_lineMap_iff.mp hc).resolve_left h
#align affine_map.line_map_injective AffineMap.lineMap_injective

variable {k}

@[simp]
theorem apply_lineMap (f : P1 →ᵃ[k] P2) (p₀ p₁ : P1) (c : k) :
    f (lineMap p₀ p₁ c) = lineMap (f p₀) (f p₁) c := by
  simp [lineMap_apply]
#align affine_map.apply_line_map AffineMap.apply_lineMap

@[simp]
theorem comp_lineMap (f : P1 →ᵃ[k] P2) (p₀ p₁ : P1) :
    f.comp (lineMap p₀ p₁) = lineMap (f p₀) (f p₁) :=
  ext <| f.apply_lineMap p₀ p₁
#align affine_map.comp_line_map AffineMap.comp_lineMap

@[simp]
theorem fst_lineMap (p₀ p₁ : P1 × P2) (c : k) : (lineMap p₀ p₁ c).1 = lineMap p₀.1 p₁.1 c :=
  fst.apply_lineMap p₀ p₁ c
#align affine_map.fst_line_map AffineMap.fst_lineMap

@[simp]
theorem snd_lineMap (p₀ p₁ : P1 × P2) (c : k) : (lineMap p₀ p₁ c).2 = lineMap p₀.2 p₁.2 c :=
  snd.apply_lineMap p₀ p₁ c
#align affine_map.snd_line_map AffineMap.snd_lineMap

theorem lineMap_symm (p₀ p₁ : P1) :
    lineMap p₀ p₁ = (lineMap p₁ p₀).comp (lineMap (1 : k) (0 : k)) := by
  rw [comp_lineMap]
  simp
#align affine_map.line_map_symm AffineMap.lineMap_symm

theorem lineMap_apply_one_sub (p₀ p₁ : P1) (c : k) : lineMap p₀ p₁ (1 - c) = lineMap p₁ p₀ c := by
  rw [lineMap_symm p₀, comp_apply]
  congr
  simp [lineMap_apply]
#align affine_map.line_map_apply_one_sub AffineMap.lineMap_apply_one_sub

@[simp]
theorem lineMap_vsub_left (p₀ p₁ : P1) (c : k) : lineMap p₀ p₁ c -ᵥ p₀ = c • (p₁ -ᵥ p₀) :=
  vadd_vsub _ _
#align affine_map.line_map_vsub_left AffineMap.lineMap_vsub_left

@[simp]
theorem left_vsub_lineMap (p₀ p₁ : P1) (c : k) : p₀ -ᵥ lineMap p₀ p₁ c = c • (p₀ -ᵥ p₁) := by
  rw [← neg_vsub_eq_vsub_rev, lineMap_vsub_left, ← smul_neg, neg_vsub_eq_vsub_rev]
#align affine_map.left_vsub_line_map AffineMap.left_vsub_lineMap

@[simp]
theorem lineMap_vsub_right (p₀ p₁ : P1) (c : k) : lineMap p₀ p₁ c -ᵥ p₁ = (1 - c) • (p₀ -ᵥ p₁) := by
  rw [← lineMap_apply_one_sub, lineMap_vsub_left]
#align affine_map.line_map_vsub_right AffineMap.lineMap_vsub_right

@[simp]
theorem right_vsub_lineMap (p₀ p₁ : P1) (c : k) : p₁ -ᵥ lineMap p₀ p₁ c = (1 - c) • (p₁ -ᵥ p₀) := by
  rw [← lineMap_apply_one_sub, left_vsub_lineMap]
#align affine_map.right_vsub_line_map AffineMap.right_vsub_lineMap

theorem lineMap_vadd_lineMap (v₁ v₂ : V1) (p₁ p₂ : P1) (c : k) :
    lineMap v₁ v₂ c +ᵥ lineMap p₁ p₂ c = lineMap (v₁ +ᵥ p₁) (v₂ +ᵥ p₂) c :=
  ((fst : V1 × P1 →ᵃ[k] V1) +ᵥ (snd : V1 × P1 →ᵃ[k] P1)).apply_lineMap (v₁, p₁) (v₂, p₂) c
#align affine_map.line_map_vadd_line_map AffineMap.lineMap_vadd_lineMap

theorem lineMap_vsub_lineMap (p₁ p₂ p₃ p₄ : P1) (c : k) :
    lineMap p₁ p₂ c -ᵥ lineMap p₃ p₄ c = lineMap (p₁ -ᵥ p₃) (p₂ -ᵥ p₄) c :=
  ((fst : P1 × P1 →ᵃ[k] P1) -ᵥ (snd : P1 × P1 →ᵃ[k] P1)).apply_lineMap (_, _) (_, _) c
#align affine_map.line_map_vsub_line_map AffineMap.lineMap_vsub_lineMap

/-- Decomposition of an affine map in the special case when the point space and vector space
are the same. -/
theorem decomp (f : V1 →ᵃ[k] V2) : (f : V1 → V2) = ⇑f.linear + fun _ => f 0 := by
  ext x
  calc
    f x = f.linear x +ᵥ f 0 := by rw [← f.map_vadd, vadd_eq_add, add_zero]
    _ = (f.linear + fun _ : V1 => f 0) x := rfl
#align affine_map.decomp AffineMap.decomp

/-- Decomposition of an affine map in the special case when the point space and vector space
are the same. -/
theorem decomp' (f : V1 →ᵃ[k] V2) : (f.linear : V1 → V2) = ⇑f - fun _ => f 0 := by
  rw [decomp]
  simp only [LinearMap.map_zero, Pi.add_apply, add_sub_cancel, zero_add]
#align affine_map.decomp' AffineMap.decomp'

theorem image_uIcc {k : Type*} [LinearOrderedField k] (f : k →ᵃ[k] k) (a b : k) :
    f '' Set.uIcc a b = Set.uIcc (f a) (f b) := by
  have : ⇑f = (fun x => x + f 0) ∘ fun x => x * (f 1 - f 0) := by
    ext x
    change f x = x • (f 1 -ᵥ f 0) +ᵥ f 0
    rw [← f.linearMap_vsub, ← f.linear.map_smul, ← f.map_vadd]
    simp only [vsub_eq_sub, add_zero, mul_one, vadd_eq_add, sub_zero, smul_eq_mul]
  rw [this, Set.image_comp]
  simp only [Set.image_add_const_uIcc, Set.image_mul_const_uIcc, Function.comp_apply]
#align affine_map.image_uIcc AffineMap.image_uIcc

section

variable {ι : Type*} {V : ι → Type*} {P : ι → Type*} [∀ i, AddCommGroup (V i)]
  [∀ i, Module k (V i)] [∀ i, AddTorsor (V i) (P i)]

/-- Evaluation at a point as an affine map. -/
def proj (i : ι) : (∀ i : ι, P i) →ᵃ[k] P i where
  toFun f := f i
  linear := @LinearMap.proj k ι _ V _ _ i
  map_vadd' _ _ := rfl
#align affine_map.proj AffineMap.proj

@[simp]
theorem proj_apply (i : ι) (f : ∀ i, P i) : @proj k _ ι V P _ _ _ i f = f i :=
  rfl
#align affine_map.proj_apply AffineMap.proj_apply

@[simp]
theorem proj_linear (i : ι) : (@proj k _ ι V P _ _ _ i).linear = @LinearMap.proj k ι _ V _ _ i :=
  rfl
#align affine_map.proj_linear AffineMap.proj_linear

theorem pi_lineMap_apply (f g : ∀ i, P i) (c : k) (i : ι) :
    lineMap f g c i = lineMap (f i) (g i) c :=
  (proj i : (∀ i, P i) →ᵃ[k] P i).apply_lineMap f g c
#align affine_map.pi_line_map_apply AffineMap.pi_lineMap_apply

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
  smul_add _c _f _g := ext fun _p => smul_add _ _ _
  smul_zero _c := ext fun _p => smul_zero _

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

See note [bundled maps over different rings]-/
@[simps]
def toConstProdLinearMap : (V1 →ᵃ[k] V2) ≃ₗ[R] V2 × (V1 →ₗ[k] V2) where
  toFun f := ⟨f 0, f.linear⟩
  invFun p := p.2.toAffineMap + const k V1 p.1
  left_inv f := by
    ext
    rw [f.decomp]
    simp [const_apply _ _]  -- Porting note: `simp` needs `_`s to use this lemma
  right_inv := by
    rintro ⟨v, f⟩
    ext <;> simp [const_apply _ _, const_linear _ _]  -- Porting note: `simp` needs `_`s
  map_add' := by simp
  map_smul' := by simp
#align affine_map.to_const_prod_linear_map AffineMap.toConstProdLinearMap

end Module

section Pi

-- The pi construction for AffineMaps. This accepts dependent types in both the module V
-- and the AffineSpace P. This leads to pretty unreadable / un-loogle-able type signatures,
-- so a non-dependent pi construction pi' is also given with corresponding theorems.

variable {ι : Type*} {φv φp : ι → Type*} [(i : ι) → AddCommGroup (φv i)]
  [(i : ι) → Module k (φv i)] [(i : ι) → AffineSpace (φv i) (φp i)]

/-- The dependently-typed version of `AffineMap.pi`, where the module `V1 := φv i` and the
 AffineSpace `P2 := φp i` can depend on the index `i : ι`.
-/
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
  simp only [AffineMap.ext_iff, Function.funext_iff, pi_apply]
  exact forall_comm

theorem pi_zero : pi (fun _ ↦ 0 : (i : ι) → P1 →ᵃ[k] φv i) = 0 := by
  ext; rfl

theorem proj_pi (i : ι) : (proj i).comp (pi fp) = fp i :=
  ext fun _ => rfl

/-- An ι-indexed collection of AffineMaps `P1 →ᵃ P2` lifts to an AffineMap from P1 to the
  Module of functions, `ι → P2`. This module is `Pi.module`. This is the AffineMap analog
  of `LinearMap.pi`. Actually defeq to `AffineMap.pi'` but the type signature is
  much easier to read.
-/
abbrev pi' : (ι → (P1 →ᵃ[k] P2)) → P1 →ᵃ[k] (ι → P2) := pi

@[simp]
theorem pi'_apply (c : P1) (i : ι) : pi' f' c i = f' i c :=
  rfl

theorem pi'_comp {V3 P3 : Type*} [AddCommGroup V3] [Module k V3] [AffineSpace V3 P3]
    (g : P3 →ᵃ[k] P1) : (pi' f').comp g = pi' (fun i => (f' i).comp g) :=
  rfl

theorem pi'_eq_zero (f : (i : ι) → P1 →ᵃ[k] V2) : pi' f = 0 ↔ ∀ i, f i = 0 :=
  pi_eq_zero f

theorem pi'_zero : pi' (fun _ ↦ 0 : (i : ι) → P1 →ᵃ[k] V2) = 0 := by ext; rfl

theorem proj_pi' (i : ι) : (proj i).comp (pi' f') = f' i :=
  ext fun _ => rfl

section Ext

variable [Finite ι] [DecidableEq ι] {f g : ((i : ι) → φv i) →ᵃ[k] P2}

/-- Two affine maps from a Pi-tyoe of modules `(i : ι) → φv i` are equal if they are equal in their
  operation on `Pi.single` and at zero. Analogous to `LinearMap.pi_ext`. See also `pi_ext_nonempty`,
  which instead of agrement at zero requires `Nonempty ι`. -/
theorem pi_ext_zero (h : ∀ i x, f (Pi.single i x) = g (Pi.single i x)) (h₂ : f 0 = g 0) :
    f = g := by
  apply ext_linear
  next =>
    apply LinearMap.pi_ext
    intro i x
    have s₁ := h i x
    have s₂ := f.map_vadd 0 (Pi.single i x)
    have s₃ := g.map_vadd 0 (Pi.single i x)
    rw [vadd_eq_add, add_zero] at s₂ s₃
    replace h₂ := h i 0
    simp at h₂
    rwa [s₂, s₃, h₂, vadd_right_cancel_iff] at s₁
  next =>
    exact h₂

/-- Two affine maps from a Pi-tyoe of modules `(i : ι) → φv i` are equal if they are equal in their
  operation on `Pi.single` and `ι` is nonempty.  Analogous to `LinearMap.pi_ext`. See also
  `pi_ext_zero`, which instead `Nonempty ι` requires agreement at 0.-/
theorem pi_ext_nonempty [Nonempty ι] (h : ∀ i x, f (Pi.single i x) = g (Pi.single i x)) :
    f = g := by
  apply pi_ext_zero h
  rw [← Pi.single_zero]
  apply h
  inhabit ι
  exact default

/-- This is used as the ext lemma instead of `AffineMap.pi_ext_nonempty` for reasons explained in
note [partially-applied ext lemmas]. Analogous to `LinearMap.pi_ext'`-/
@[ext]
theorem pi_ext_nonempty' [Nonempty ι] (h : ∀ i, f.comp (LinearMap.single i).toAffineMap =
    g.comp (LinearMap.single i).toAffineMap) : f = g := by
  refine' pi_ext_nonempty fun i x => _
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
#align affine_map.homothety AffineMap.homothety

theorem homothety_def (c : P1) (r : k) :
    homothety c r = r • (id k P1 -ᵥ const k P1 c) +ᵥ const k P1 c :=
  rfl
#align affine_map.homothety_def AffineMap.homothety_def

theorem homothety_apply (c : P1) (r : k) (p : P1) : homothety c r p = r • (p -ᵥ c : V1) +ᵥ c :=
  rfl
#align affine_map.homothety_apply AffineMap.homothety_apply

theorem homothety_eq_lineMap (c : P1) (r : k) (p : P1) : homothety c r p = lineMap c p r :=
  rfl
#align affine_map.homothety_eq_line_map AffineMap.homothety_eq_lineMap

@[simp]
theorem homothety_one (c : P1) : homothety c (1 : k) = id k P1 := by
  ext p
  simp [homothety_apply]
#align affine_map.homothety_one AffineMap.homothety_one

@[simp]
theorem homothety_apply_same (c : P1) (r : k) : homothety c r c = c :=
  lineMap_same_apply c r
#align affine_map.homothety_apply_same AffineMap.homothety_apply_same

theorem homothety_mul_apply (c : P1) (r₁ r₂ : k) (p : P1) :
    homothety c (r₁ * r₂) p = homothety c r₁ (homothety c r₂ p) := by
  simp only [homothety_apply, mul_smul, vadd_vsub]
#align affine_map.homothety_mul_apply AffineMap.homothety_mul_apply

theorem homothety_mul (c : P1) (r₁ r₂ : k) :
    homothety c (r₁ * r₂) = (homothety c r₁).comp (homothety c r₂) :=
  ext <| homothety_mul_apply c r₁ r₂
#align affine_map.homothety_mul AffineMap.homothety_mul

@[simp]
theorem homothety_zero (c : P1) : homothety c (0 : k) = const k P1 c := by
  ext p
  simp [homothety_apply]
#align affine_map.homothety_zero AffineMap.homothety_zero

@[simp]
theorem homothety_add (c : P1) (r₁ r₂ : k) :
    homothety c (r₁ + r₂) = r₁ • (id k P1 -ᵥ const k P1 c) +ᵥ homothety c r₂ := by
  simp only [homothety_def, add_smul, vadd_vadd]
#align affine_map.homothety_add AffineMap.homothety_add

/-- `homothety` as a multiplicative monoid homomorphism. -/
def homothetyHom (c : P1) : k →* P1 →ᵃ[k] P1 where
  toFun := homothety c
  map_one' := homothety_one c
  map_mul' := homothety_mul c
#align affine_map.homothety_hom AffineMap.homothetyHom

@[simp]
theorem coe_homothetyHom (c : P1) : ⇑(homothetyHom c : k →* _) = homothety c :=
  rfl
#align affine_map.coe_homothety_hom AffineMap.coe_homothetyHom

/-- `homothety` as an affine map. -/
def homothetyAffine (c : P1) : k →ᵃ[k] P1 →ᵃ[k] P1 :=
  ⟨homothety c, (LinearMap.lsmul k _).flip (id k P1 -ᵥ const k P1 c),
    Function.swap (homothety_add c)⟩
#align affine_map.homothety_affine AffineMap.homothetyAffine

@[simp]
theorem coe_homothetyAffine (c : P1) : ⇑(homothetyAffine c : k →ᵃ[k] _) = homothety c :=
  rfl
#align affine_map.coe_homothety_affine AffineMap.coe_homothetyAffine

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
#align convex.combo_affine_apply Convex.combo_affine_apply

end
