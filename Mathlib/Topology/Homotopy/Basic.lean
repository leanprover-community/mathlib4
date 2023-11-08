/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
import Mathlib.Topology.Algebra.Order.ProjIcc
import Mathlib.Topology.ContinuousFunction.Ordered
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.UnitInterval

#align_import topology.homotopy.basic from "leanprover-community/mathlib"@"11c53f174270aa43140c0b26dabce5fc4a253e80"

/-!
# Homotopy between functions

In this file, we define a homotopy between two functions `f₀` and `f₁`. First we define
`ContinuousMap.Homotopy` between the two functions, with no restrictions on the intermediate
maps. Then, as in the formalisation in HOL-Analysis, we define
`ContinuousMap.HomotopyWith f₀ f₁ P`, for homotopies between `f₀` and `f₁`, where the
intermediate maps satisfy the predicate `P`. Finally, we define
`ContinuousMap.HomotopyRel f₀ f₁ S`, for homotopies between `f₀` and `f₁` which are fixed
on `S`.

## Definitions

* `ContinuousMap.Homotopy f₀ f₁` is the type of homotopies between `f₀` and `f₁`.
* `ContinuousMap.HomotopyWith f₀ f₁ P` is the type of homotopies between `f₀` and `f₁`, where
  the intermediate maps satisfy the predicate `P`.
* `ContinuousMap.HomotopyRel f₀ f₁ S` is the type of homotopies between `f₀` and `f₁` which
  are fixed on `S`.

For each of the above, we have

* `refl f`, which is the constant homotopy from `f` to `f`.
* `symm F`, which reverses the homotopy `F`. For example, if `F : ContinuousMap.Homotopy f₀ f₁`,
  then `F.symm : ContinuousMap.Homotopy f₁ f₀`.
* `trans F G`, which concatenates the homotopies `F` and `G`. For example, if
  `F : ContinuousMap.Homotopy f₀ f₁` and `G : ContinuousMap.Homotopy f₁ f₂`, then
  `F.trans G : ContinuousMap.Homotopy f₀ f₂`.

We also define the relations

* `ContinuousMap.Homotopic f₀ f₁` is defined to be `Nonempty (ContinuousMap.Homotopy f₀ f₁)`
* `ContinuousMap.HomotopicWith f₀ f₁ P` is defined to be
  `Nonempty (ContinuousMap.HomotopyWith f₀ f₁ P)`
* `ContinuousMap.HomotopicRel f₀ f₁ P` is defined to be
  `Nonempty (ContinuousMap.HomotopyRel f₀ f₁ P)`

and for `ContinuousMap.homotopic` and `ContinuousMap.homotopic_rel`, we also define the
`setoid` and `quotient` in `C(X, Y)` by these relations.

## References

- [HOL-Analysis formalisation](https://isabelle.in.tum.de/library/HOL/HOL-Analysis/Homotopy.html)
-/

set_option autoImplicit true


noncomputable section

universe u v w x

variable {F : Type*} {X : Type u} {Y : Type v} {Z : Type w} {Z' : Type x}

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace Z']

open unitInterval

namespace Function

/-- `ContinuousMap.Homotopy f₀ f₁` is the type of homotopies from `f₀` to `f₁`.

When possible, instead of parametrizing results over `(f : Homotopy f₀ f₁)`,
you should parametrize over `{F : Type*} [HomotopyLike F f₀ f₁] (f : F)`.

When you extend this structure, make sure to extend `ContinuousMap.HomotopyLike`. -/
structure Homotopy (f₀ f₁ : X → Y) extends C(I × X, Y) where
  /-- value of the homotopy at 0 -/
  map_zero_left : ∀ x, toFun (0, x) = f₀ x
  /-- value of the homotopy at 1 -/
  map_one_left : ∀ x, toFun (1, x) = f₁ x
#align continuous_map.homotopy Function.Homotopy

section

/-- `ContinuousMap.HomotopyLike F f₀ f₁` states that `F` is a type of homotopies between `f₀` and
`f₁`.

You should extend this class when you extend `ContinuousMap.Homotopy`. -/
class HomotopyLike {X Y : outParam (Type*)} [TopologicalSpace X] [TopologicalSpace Y]
    (F : Type*) (f₀ f₁ : outParam <| X → Y) extends ContinuousMapClass F (I × X) Y where
  /-- value of the homotopy at 0 -/
  map_zero_left (f : F) : ∀ x, f (0, x) = f₀ x
  /-- value of the homotopy at 1 -/
  map_one_left (f : F) : ∀ x, f (1, x) = f₁ x
#align continuous_map.homotopy_like Function.HomotopyLike

end

namespace Homotopy

section

variable {f₀ f₁ : X → Y}

instance : HomotopyLike (Homotopy f₀ f₁) f₀ f₁ where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr
  map_continuous f := f.continuous_toFun
  map_zero_left f := f.map_zero_left
  map_one_left f := f.map_one_left

/- porting note: probably not needed anymore
/-- Helper instance for when there's too many metavariables to apply `FunLike.hasCoeToFun`
directly. -/
instance : CoeFun (Homotopy f₀ f₁) fun _ => I × X → Y :=
  FunLike.hasCoeToFun -/

@[ext]
theorem ext {F G : Homotopy f₀ f₁} (h : ∀ x, F x = G x) : F = G :=
  FunLike.ext _ _ h
#align continuous_map.homotopy.ext Function.Homotopy.ext

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def Simps.apply (F : Homotopy f₀ f₁) : I × X → Y :=
  F
#align continuous_map.homotopy.simps.apply Function.Homotopy.Simps.apply

initialize_simps_projections Homotopy (toFun → apply, -toContinuousMap)

/-- Deprecated. Use `map_continuous` instead. -/
protected theorem continuous (F : Homotopy f₀ f₁) : Continuous F :=
  F.continuous_toFun
#align continuous_map.homotopy.continuous Function.Homotopy.continuous

@[simp]
theorem apply_zero (F : Homotopy f₀ f₁) (x : X) : F (0, x) = f₀ x :=
  F.map_zero_left x
#align continuous_map.homotopy.apply_zero Function.Homotopy.apply_zero

@[simp]
theorem apply_one (F : Homotopy f₀ f₁) (x : X) : F (1, x) = f₁ x :=
  F.map_one_left x
#align continuous_map.homotopy.apply_one Function.Homotopy.apply_one

@[simp]
theorem coe_toContinuousMap (F : Homotopy f₀ f₁) : ⇑F.toContinuousMap = F :=
  rfl
#align continuous_map.homotopy.coe_to_continuous_map Function.Homotopy.coe_toContinuousMap

/-- Currying a homotopy to a continuous function from `I` to `C(X, Y)`.
-/
def curry (F : Homotopy f₀ f₁) : C(I, C(X, Y)) :=
  F.toContinuousMap.curry
#align continuous_map.homotopy.curry Function.Homotopy.curry

@[simp]
theorem curry_apply (F : Homotopy f₀ f₁) (t : I) (x : X) : F.curry t x = F (t, x) :=
  rfl
#align continuous_map.homotopy.curry_apply Function.Homotopy.curry_apply

/-- Continuously extending a curried homotopy to a function from `ℝ` to `C(X, Y)`.
-/
def extend (F : Homotopy f₀ f₁) : C(ℝ, C(X, Y)) :=
  F.curry.IccExtend zero_le_one
#align continuous_map.homotopy.extend Function.Homotopy.extend

theorem extend_apply_of_le_zero (F : Homotopy f₀ f₁) {t : ℝ} (ht : t ≤ 0) (x : X) :
    F.extend t x = f₀ x := by
  rw [← F.apply_zero]
  exact ContinuousMap.congr_fun (Set.IccExtend_of_le_left (zero_le_one' ℝ) F.curry ht) x
#align continuous_map.homotopy.extend_apply_of_le_zero Function.Homotopy.extend_apply_of_le_zero

theorem extend_apply_of_one_le (F : Homotopy f₀ f₁) {t : ℝ} (ht : 1 ≤ t) (x : X) :
    F.extend t x = f₁ x := by
  rw [← F.apply_one]
  exact ContinuousMap.congr_fun (Set.IccExtend_of_right_le (zero_le_one' ℝ) F.curry ht) x
#align continuous_map.homotopy.extend_apply_of_one_le Function.Homotopy.extend_apply_of_one_le

@[simp]
theorem extend_apply_coe (F : Homotopy f₀ f₁) (t : I) (x : X) : F.extend t x = F (t, x) :=
  ContinuousMap.congr_fun (Set.IccExtend_val (zero_le_one' ℝ) F.curry t) x
#align continuous_map.homotopy.extend_apply_coe Function.Homotopy.extend_apply_coe

@[simp]
theorem extend_apply_of_mem_I (F : Homotopy f₀ f₁) {t : ℝ} (ht : t ∈ I) (x : X) :
    F.extend t x = F (⟨t, ht⟩, x) :=
  ContinuousMap.congr_fun (Set.IccExtend_of_mem (zero_le_one' ℝ) F.curry ht) x
set_option linter.uppercaseLean3 false in
#align continuous_map.homotopy.extend_apply_of_mem_I Function.Homotopy.extend_apply_of_mem_I

theorem congr_fun {F G : Homotopy f₀ f₁} (h : F = G) (x : I × X) : F x = G x :=
  ContinuousMap.congr_fun (congr_arg _ h) x
#align continuous_map.homotopy.congr_fun Function.Homotopy.congr_fun

theorem congr_arg (F : Homotopy f₀ f₁) {x y : I × X} (h : x = y) : F x = F y :=
  F.toContinuousMap.congr_arg h
#align continuous_map.homotopy.congr_arg Function.Homotopy.congr_arg

end

/-- Given a continuous function `f`, we can define a `Homotopy f f` by `F (t, x) = f x`
-/
@[simps]
def refl (f : C(X, Y)) : Homotopy f f where
  toFun x := f x.2
  map_zero_left _ := rfl
  map_one_left _ := rfl
#align continuous_map.homotopy.refl Function.Homotopy.refl

instance : Inhabited (Homotopy (ContinuousMap.id X) (ContinuousMap.id X)) :=
  ⟨Homotopy.refl _⟩

/-- Given a `Homotopy f₀ f₁`, we can define a `Homotopy f₁ f₀` by reversing the homotopy.
-/
@[simps]
def symm {f₀ f₁ : X → Y} (F : Homotopy f₀ f₁) : Homotopy f₁ f₀ where
  toFun x := F (σ x.1, x.2)
  map_zero_left := by norm_num
  map_one_left := by norm_num
#align continuous_map.homotopy.symm Function.Homotopy.symm

@[simp]
theorem symm_symm {f₀ f₁ : X → Y} (F : Homotopy f₀ f₁) : F.symm.symm = F := by
  ext
  simp
#align continuous_map.homotopy.symm_symm Function.Homotopy.symm_symm

/--
Given `Homotopy f₀ f₁` and `Homotopy f₁ f₂`, we can define a `Homotopy f₀ f₂` by putting the first
homotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans {f₀ f₁ f₂ : X → Y} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) : Homotopy f₀ f₂ where
  toFun x := if (x.1 : ℝ) ≤ 1 / 2 then F.extend (2 * x.1) x.2 else G.extend (2 * x.1 - 1) x.2
  continuous_toFun := by
    refine'
      continuous_if_le (continuous_induced_dom.comp continuous_fst) continuous_const
        (F.continuous.comp (by continuity)).continuousOn
        (G.continuous.comp (by continuity)).continuousOn _
    rintro x hx
    norm_num [hx]
  map_zero_left x := by norm_num
  map_one_left x := by norm_num
#align continuous_map.homotopy.trans Function.Homotopy.trans

theorem trans_apply {f₀ f₁ f₂ : X → Y} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) (x : I × X) :
    (F.trans G) x =
      if h : (x.1 : ℝ) ≤ 1 / 2 then
        F (⟨2 * x.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
      else
        G (⟨2 * x.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
  show ite _ _ _ = _ by
    split_ifs <;>
      · rw [extend, ContinuousMap.coe_IccExtend, Set.IccExtend_of_mem]
        rfl
#align continuous_map.homotopy.trans_apply Function.Homotopy.trans_apply

theorem symm_trans {f₀ f₁ f₂ : X → Y} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) :
    (F.trans G).symm = G.symm.trans F.symm := by
  ext ⟨t, _⟩
  rw [trans_apply, symm_apply, trans_apply]
  simp only [coe_symm_eq, symm_apply]
  split_ifs with h₁ h₂ h₂
  · have ht : (t : ℝ) = 1 / 2 := by linarith
    norm_num [ht]
  · congr 2
    apply Subtype.ext
    simp only [coe_symm_eq]
    linarith
  · congr 2
    apply Subtype.ext
    simp only [coe_symm_eq]
    linarith
  · exfalso
    linarith
#align continuous_map.homotopy.symm_trans Function.Homotopy.symm_trans

/-- Casting a `Homotopy f₀ f₁` to a `Homotopy g₀ g₁` where `f₀ = g₀` and `f₁ = g₁`.
-/
@[simps]
def cast {f₀ f₁ g₀ g₁ : X → Y} (F : Homotopy f₀ f₁) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) :
    Homotopy g₀ g₁ where
  toFun := F
  map_zero_left := by simp [← h₀]
  map_one_left := by simp [← h₁]
#align continuous_map.homotopy.cast Function.Homotopy.cast

/-- Composition of a `Homotopy g₀ g₁` and `f : C(X, Y)` as a homotopy between `g₀.comp f` and
`g₁.comp f`. -/
@[simps!]
def compContinuousMap {g₀ g₁ : Y → Z} (G : Homotopy g₀ g₁) (f : C(X, Y)) :
    Homotopy (g₀.comp f) (g₁.comp f) where
  toContinuousMap := G.comp (.prodMap (.id _) f)
  map_zero_left _ := G.map_zero_left _
  map_one_left _ := G.map_one_left _

/-- If we have a `Homotopy f₀ f₁` and a `Homotopy g₀ g₁`, then we can compose them and get a
`Homotopy (g₀.comp f₀) (g₁.comp f₁)`.
-/
@[simps]
def hcomp {f₀ f₁ : X → Y} {g₀ g₁ : Y → Z} (F : Homotopy f₀ f₁) (G : Homotopy g₀ g₁) :
    Homotopy (g₀.comp f₀) (g₁.comp f₁) where
  toFun x := G (x.1, F x)
  map_zero_left := by simp
  map_one_left := by simp
#align continuous_map.homotopy.hcomp Function.Homotopy.hcomp

/-- Let `F` be a homotopy between `f₀ : C(X, Y)` and `f₁ : C(X, Y)`. Let `G` be a homotopy between
`g₀ : C(X, Z)` and `g₁ : C(X, Z)`. Then `F.prodMk G` is the homotopy between `f₀.prodMk g₀` and
`f₁.prodMk g₁` that sends `p` to `(F p, G p)`. -/
nonrec def prodMk {f₀ f₁ : X → Y} {g₀ g₁ : X → Z} (F : Homotopy f₀ f₁) (G : Homotopy g₀ g₁) :
    Homotopy (fun x ↦ (f₀ x, g₀ x)) (fun x ↦ (f₁ x, g₁ x)) where
  toContinuousMap := F.prodMk G
  map_zero_left _ := Prod.ext (F.map_zero_left _) (G.map_zero_left _)
  map_one_left _ := Prod.ext (F.map_one_left _) (G.map_one_left _)

/-- Let `F` be a homotopy between `f₀ : C(X, Y)` and `f₁ : C(X, Y)`. Let `G` be a homotopy between
`g₀ : C(Z, Z')` and `g₁ : C(Z, Z')`. Then `F.prodMap G` is the homotopy between `f₀.prodMap g₀` and
`f₁.prodMap g₁` that sends `(t, x, z)` to `(F (t, x), G (t, z))`. -/
def prodMap {f₀ f₁ : X → Y} {g₀ g₁ : Z → Z'} (F : Homotopy f₀ f₁) (G : Homotopy g₀ g₁) :
    Homotopy (Prod.map f₀ g₀) (Prod.map f₁ g₁) :=
  .prodMk (.hcomp (.refl .fst) F) (.hcomp (.refl .snd) G)

/-- Given a family of homotopies `F i` between `f₀ i : C(X, Y i)` and `f₁ i : C(X, Y i)`, returns a
homotopy between `ContinuousMap.pi f₀` and `ContinuousMap.pi f₁`. -/
protected def pi {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] {f₀ f₁ : ∀ i, X → Y i}
    (F : ∀ i, Homotopy (f₀ i) (f₁ i)) :
    Homotopy (fun x i ↦ f₀ i x) (fun x i ↦ f₁ i x) where
  toContinuousMap := .pi fun i ↦ F i
  map_zero_left x := funext fun i ↦ (F i).map_zero_left x
  map_one_left x := funext fun i ↦ (F i).map_one_left x

/-- Given a family of homotopies `F i` between `f₀ i : C(X i, Y i)` and `f₁ i : C(X i, Y i)`,
returns a homotopy between `ContinuousMap.piMap f₀` and `ContinuousMap.piMap f₁`. -/
protected def piMap {X Y : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    {f₀ f₁ : ∀ i, X i → Y i} (F : ∀ i, Homotopy (f₀ i) (f₁ i)) :
    Homotopy (X := ∀ i, X i) (fun x i ↦ f₀ i (x i)) (fun x i ↦ f₁ i (x i)) :=
  .pi fun i ↦ .hcomp (.refl <| .eval i) (F i)

end Homotopy

/-- Given continuous maps `f₀` and `f₁`, we say `f₀` and `f₁` are homotopic if there exists a
`Homotopy f₀ f₁`.
-/
def Homotopic (f₀ f₁ : X → Y) : Prop :=
  Nonempty (Homotopy f₀ f₁)
#align continuous_map.homotopic Function.Homotopic

namespace Homotopic

@[refl]
theorem refl (f : C(X, Y)) : Homotopic f f :=
  ⟨Homotopy.refl f⟩
#align continuous_map.homotopic.refl Function.Homotopic.refl

@[symm]
theorem symm ⦃f g : X → Y⦄ (h : Homotopic f g) : Homotopic g f :=
  h.map Homotopy.symm
#align continuous_map.homotopic.symm Function.Homotopic.symm

@[trans]
theorem trans ⦃f g h :X → Y⦄ (h₀ : Homotopic f g) (h₁ : Homotopic g h) : Homotopic f h :=
  h₀.map2 Homotopy.trans h₁
#align continuous_map.homotopic.trans Function.Homotopic.trans

theorem hcomp {f₀ f₁ : X → Y} {g₀ g₁ : Y → Z} (h₀ : Homotopic f₀ f₁) (h₁ : Homotopic g₀ g₁) :
    Homotopic (g₀.comp f₀) (g₁.comp f₁) :=
  h₀.map2 Homotopy.hcomp h₁
#align continuous_map.homotopic.hcomp Function.Homotopic.hcomp

theorem equivalence : Equivalence fun f₀ f₁ : C(X, Y) ↦ Homotopic f₀ f₁ :=
  ⟨refl, fun h ↦ symm h, fun h ↦ trans h⟩
#align continuous_map.homotopic.equivalence Function.Homotopic.equivalence

nonrec theorem prodMk {f₀ f₁ : X → Y} {g₀ g₁ : X → Z} :
    Homotopic f₀ f₁ → Homotopic g₀ g₁ → Homotopic (fun x ↦ (f₀ x, g₀ x)) (fun x ↦ (f₁ x, g₁ x))
  | ⟨F⟩, ⟨G⟩ => ⟨F.prodMk G⟩

nonrec theorem prodMap {f₀ f₁ : X → Y} {g₀ g₁ : Z → Z'} :
    Homotopic f₀ f₁ → Homotopic g₀ g₁ → Homotopic (Prod.map f₀ g₀) (Prod.map f₁ g₁)
  | ⟨F⟩, ⟨G⟩ => ⟨F.prodMap G⟩

/-- If each `f₀ i : C(X, Y i)` is homotopic to `f₁ i : C(X, Y i)`, then `ContinuousMap.pi f₀` is
homotopic to `ContinuousMap.pi f₁`. -/
protected theorem pi {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] {f₀ f₁ : ∀ i, X → Y i}
    (F : ∀ i, Homotopic (f₀ i) (f₁ i)) :
    Homotopic (fun x i ↦ f₀ i x) (fun x i ↦ f₁ i x) :=
  ⟨.pi fun i ↦ (F i).some⟩

/-- If each `f₀ i : C(X, Y i)` is homotopic to `f₁ i : C(X, Y i)`, then `ContinuousMap.pi f₀` is
homotopic to `ContinuousMap.pi f₁`. -/
protected theorem piMap {X Y : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] {f₀ f₁ : ∀ i, C(X i, Y i)} (F : ∀ i, Homotopic (f₀ i) (f₁ i)) :
   Homotopic (X := ∀ i, X i) (fun x i ↦ f₀ i (x i)) (fun x i ↦ f₁ i (x i)) :=
  .pi fun i ↦ .hcomp (.refl <| .eval i) (F i)

end Homotopic

/--
The type of homotopies between `f₀ f₁ : C(X, Y)`, where the intermediate maps satisfy the predicate
`P : C(X, Y) → Prop`
-/
structure HomotopyWith (f₀ f₁ : X → Y) (P : (X → Y) → Prop) extends Homotopy f₀ f₁ where
  -- porting note: todo: use `toHomotopy.curry t`
  /-- the intermediate maps of the homotopy satisfy the property -/
  prop' : ∀ t, P fun x ↦ toFun (t, x)
#align continuous_map.homotopy_with Function.HomotopyWith

namespace HomotopyWith

section

variable {f₀ f₁ : X → Y} {P : (X → Y) → Prop}

instance : HomotopyLike (HomotopyWith f₀ f₁ P) f₀ f₁ where
  coe F := ⇑F.toHomotopy
  coe_injective'
  | ⟨⟨⟨_, _⟩, _, _⟩, _⟩, ⟨⟨⟨_, _⟩, _, _⟩, _⟩, rfl => rfl
  map_continuous F := F.continuous_toFun
  map_zero_left F := F.map_zero_left
  map_one_left F := F.map_one_left

theorem coeFn_injective : @Function.Injective (HomotopyWith f₀ f₁ P) (I × X → Y) (⇑) :=
  FunLike.coe_injective'
#align continuous_map.homotopy_with.coe_fn_injective Function.HomotopyWith.coeFn_injective

@[ext]
theorem ext {F G : HomotopyWith f₀ f₁ P} (h : ∀ x, F x = G x) : F = G := FunLike.ext F G h
#align continuous_map.homotopy_with.ext Function.HomotopyWith.ext

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def Simps.apply (F : HomotopyWith f₀ f₁ P) : I × X → Y := F
#align continuous_map.homotopy_with.simps.apply Function.HomotopyWith.Simps.apply

initialize_simps_projections HomotopyWith (toHomotopy_toContinuousMap_toFun → apply,
  -toHomotopy_toContinuousMap)

@[continuity]
protected theorem continuous (F : HomotopyWith f₀ f₁ P) : Continuous F :=
  F.continuous_toFun
#align continuous_map.homotopy_with.continuous Function.HomotopyWith.continuous

@[simp]
theorem apply_zero (F : HomotopyWith f₀ f₁ P) (x : X) : F (0, x) = f₀ x :=
  F.map_zero_left x
#align continuous_map.homotopy_with.apply_zero Function.HomotopyWith.apply_zero

@[simp]
theorem apply_one (F : HomotopyWith f₀ f₁ P) (x : X) : F (1, x) = f₁ x :=
  F.map_one_left x
#align continuous_map.homotopy_with.apply_one Function.HomotopyWith.apply_one

-- porting note: removed `simp`
theorem coe_toContinuousMap (F : HomotopyWith f₀ f₁ P) : ⇑F.toContinuousMap = F :=
  rfl
#align continuous_map.homotopy_with.coe_to_continuous_map Function.HomotopyWith.coe_toContinuousMap

@[simp]
theorem coe_toHomotopy (F : HomotopyWith f₀ f₁ P) : ⇑F.toHomotopy = F :=
  rfl
#align continuous_map.homotopy_with.coe_to_homotopy Function.HomotopyWith.coe_toHomotopy

theorem prop (F : HomotopyWith f₀ f₁ P) (t : I) : P (F.toHomotopy.curry t) := F.prop' t
#align continuous_map.homotopy_with.prop Function.HomotopyWith.prop

theorem extendProp (F : HomotopyWith f₀ f₁ P) (t : ℝ) : P (F.toHomotopy.extend t) := F.prop _
#align continuous_map.homotopy_with.extend_prop Function.HomotopyWith.extendProp

end

variable {P : (X → Y) → Prop}

/-- Given a continuous function `f`, and a proof `h : P f`, we can define a `HomotopyWith f f P` by
`F (t, x) = f x`
-/
@[simps!]
def refl (f : C(X, Y)) (hf : P f) : HomotopyWith f f P where
  toHomotopy := Homotopy.refl f
  prop' := fun _ => hf
#align continuous_map.homotopy_with.refl Function.HomotopyWith.refl

instance : Inhabited (HomotopyWith (ContinuousMap.id X) (ContinuousMap.id X) fun _ => True) :=
  ⟨HomotopyWith.refl _ trivial⟩

/--
Given a `HomotopyWith f₀ f₁ P`, we can define a `HomotopyWith f₁ f₀ P` by reversing the homotopy.
-/
@[simps!]
def symm {f₀ f₁ : X → Y} (F : HomotopyWith f₀ f₁ P) : HomotopyWith f₁ f₀ P where
  toHomotopy := F.toHomotopy.symm
  prop' := fun t => F.prop (σ t)
#align continuous_map.homotopy_with.symm Function.HomotopyWith.symm

@[simp]
theorem symm_symm {f₀ f₁ : X → Y} (F : HomotopyWith f₀ f₁ P) : F.symm.symm = F :=
  ext <| Homotopy.congr_fun <| Homotopy.symm_symm _
#align continuous_map.homotopy_with.symm_symm Function.HomotopyWith.symm_symm

/--
Given `HomotopyWith f₀ f₁ P` and `HomotopyWith f₁ f₂ P`, we can define a `HomotopyWith f₀ f₂ P`
by putting the first homotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans {f₀ f₁ f₂ : X → Y} (F : HomotopyWith f₀ f₁ P) (G : HomotopyWith f₁ f₂ P) :
    HomotopyWith f₀ f₂ P :=
  { F.toHomotopy.trans G.toHomotopy with
    prop' := fun t => by
      simp only [Homotopy.trans]
      change P fun _ => ite ((t : ℝ) ≤ _) _ _
      split_ifs
      · exact F.extendProp _
      · exact G.extendProp _ }
#align continuous_map.homotopy_with.trans Function.HomotopyWith.trans

theorem trans_apply {f₀ f₁ f₂ : X → Y} (F : HomotopyWith f₀ f₁ P) (G : HomotopyWith f₁ f₂ P)
    (x : I × X) :
    (F.trans G) x =
      if h : (x.1 : ℝ) ≤ 1 / 2 then
        F (⟨2 * x.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
      else
        G (⟨2 * x.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
  Homotopy.trans_apply _ _ _
#align continuous_map.homotopy_with.trans_apply Function.HomotopyWith.trans_apply

theorem symm_trans {f₀ f₁ f₂ : X → Y} (F : HomotopyWith f₀ f₁ P) (G : HomotopyWith f₁ f₂ P) :
    (F.trans G).symm = G.symm.trans F.symm :=
  ext <| Homotopy.congr_fun <| Homotopy.symm_trans _ _
#align continuous_map.homotopy_with.symm_trans Function.HomotopyWith.symm_trans

/-- Casting a `HomotopyWith f₀ f₁ P` to a `HomotopyWith g₀ g₁ P` where `f₀ = g₀` and `f₁ = g₁`.
-/
@[simps!]
def cast {f₀ f₁ g₀ g₁ : X → Y} (F : HomotopyWith f₀ f₁ P) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) :
    HomotopyWith g₀ g₁ P where
  toHomotopy := F.toHomotopy.cast h₀ h₁
  prop' := F.prop
#align continuous_map.homotopy_with.cast Function.HomotopyWith.cast

end HomotopyWith

/-- Given continuous maps `f₀` and `f₁`, we say `f₀` and `f₁` are homotopic with respect to the
predicate `P` if there exists a `HomotopyWith f₀ f₁ P`.
-/
def HomotopicWith (f₀ f₁ : X → Y) (P : (X → Y) → Prop) : Prop :=
  Nonempty (HomotopyWith f₀ f₁ P)
#align continuous_map.homotopic_with Function.HomotopicWith

namespace HomotopicWith

variable {P : (X → Y) → Prop}

-- porting note: removed @[refl]
theorem refl (f : C(X, Y)) (hf : P f) : HomotopicWith f f P :=
  ⟨HomotopyWith.refl f hf⟩
#align continuous_map.homotopic_with.refl Function.HomotopicWith.refl

@[symm]
theorem symm ⦃f g : X → Y⦄ (h : HomotopicWith f g P) : HomotopicWith g f P :=
  ⟨h.some.symm⟩
#align continuous_map.homotopic_with.symm Function.HomotopicWith.symm

-- Note: this was formerly tagged with `@[trans]`, and although the `trans` attribute accepted it
-- the `trans` tactic could not use it.
-- An update to the trans tactic coming in mathlib4#7014 will reject this attribute.
-- It could be restored by changing the argument order to `HomotopicWith P f g`.
@[trans]
theorem trans ⦃f g h : X → Y⦄ (h₀ : HomotopicWith f g P) (h₁ : HomotopicWith g h P) :
    HomotopicWith f h P :=
  ⟨h₀.some.trans h₁.some⟩
#align continuous_map.homotopic_with.trans Function.HomotopicWith.trans

end HomotopicWith

/--
A `HomotopyRel f₀ f₁ S` is a homotopy between `f₀` and `f₁` which is fixed on the points in `S`.
-/
abbrev HomotopyRel (f₀ f₁ : X → Y) (S : Set X) :=
  HomotopyWith f₀ f₁ fun f ↦ ∀ x ∈ S, f x = f₀ x
#align continuous_map.homotopy_rel Function.HomotopyRel

namespace HomotopyRel

section

variable {f₀ f₁ : X → Y} {S : Set X}

theorem eq_fst (F : HomotopyRel f₀ f₁ S) (t : I) {x : X} (hx : x ∈ S) : F (t, x) = f₀ x :=
  F.prop t x hx
#align continuous_map.homotopy_rel.eq_fst Function.HomotopyRel.eq_fst

theorem eq_snd (F : HomotopyRel f₀ f₁ S) (t : I) {x : X} (hx : x ∈ S) : F (t, x) = f₁ x := by
  rw [F.eq_fst t hx, ← F.eq_fst 1 hx, F.apply_one]
#align continuous_map.homotopy_rel.eq_snd Function.HomotopyRel.eq_snd

theorem fst_eq_snd (F : HomotopyRel f₀ f₁ S) {x : X} (hx : x ∈ S) : f₀ x = f₁ x :=
  F.eq_fst 0 hx ▸ F.eq_snd 0 hx
#align continuous_map.homotopy_rel.fst_eq_snd Function.HomotopyRel.fst_eq_snd

end

variable {f₀ f₁ f₂ : X → Y} {S : Set X}

/-- Given a map `f : C(X, Y)` and a set `S`, we can define a `HomotopyRel f f S` by setting
`F (t, x) = f x` for all `t`. This is defined using `HomotopyWith.refl`, but with the proof
filled in.
-/
@[simps!]
def refl (f : C(X, Y)) (S : Set X) : HomotopyRel f f S :=
  HomotopyWith.refl f fun _ _ ↦ rfl
#align continuous_map.homotopy_rel.refl Function.HomotopyRel.refl

/--
Given a `HomotopyRel f₀ f₁ S`, we can define a `HomotopyRel f₁ f₀ S` by reversing the homotopy.
-/
@[simps!]
def symm (F : HomotopyRel f₀ f₁ S) : HomotopyRel f₁ f₀ S where
  toHomotopy := F.toHomotopy.symm
  prop' := fun _ _ hx ↦ F.eq_snd _ hx
#align continuous_map.homotopy_rel.symm Function.HomotopyRel.symm

@[simp]
theorem symm_symm (F : HomotopyRel f₀ f₁ S) : F.symm.symm = F :=
  HomotopyWith.symm_symm F
#align continuous_map.homotopy_rel.symm_symm Function.HomotopyRel.symm_symm

/-- Given `HomotopyRel f₀ f₁ S` and `HomotopyRel f₁ f₂ S`, we can define a `HomotopyRel f₀ f₂ S`
by putting the first homotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans (F : HomotopyRel f₀ f₁ S) (G : HomotopyRel f₁ f₂ S) : HomotopyRel f₀ f₂ S where
  toHomotopy := F.toHomotopy.trans G.toHomotopy
  prop' t x hx := by
    simp only [Homotopy.trans]
    split_ifs
    · simp [HomotopyWith.extendProp F (2 * t) x hx, F.fst_eq_snd hx, G.fst_eq_snd hx]
    · simp [HomotopyWith.extendProp G (2 * t - 1) x hx, F.fst_eq_snd hx, G.fst_eq_snd hx]
#align continuous_map.homotopy_rel.trans Function.HomotopyRel.trans

theorem trans_apply (F : HomotopyRel f₀ f₁ S) (G : HomotopyRel f₁ f₂ S) (x : I × X) :
    (F.trans G) x =
      if h : (x.1 : ℝ) ≤ 1 / 2 then
        F (⟨2 * x.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
      else
        G (⟨2 * x.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
  Homotopy.trans_apply _ _ _
#align continuous_map.homotopy_rel.trans_apply Function.HomotopyRel.trans_apply

theorem symm_trans (F : HomotopyRel f₀ f₁ S) (G : HomotopyRel f₁ f₂ S) :
    (F.trans G).symm = G.symm.trans F.symm :=
  HomotopyWith.ext <| Homotopy.congr_fun <| Homotopy.symm_trans _ _
#align continuous_map.homotopy_rel.symm_trans Function.HomotopyRel.symm_trans

/-- Casting a `HomotopyRel f₀ f₁ S` to a `HomotopyRel g₀ g₁ S` where `f₀ = g₀` and `f₁ = g₁`.
-/
@[simps!]
def cast {f₀ f₁ g₀ g₁ : X → Y} (F : HomotopyRel f₀ f₁ S) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) :
    HomotopyRel g₀ g₁ S where
  toHomotopy := Homotopy.cast F.toHomotopy h₀ h₁
  prop' t x hx := by simpa only [← h₀, ← h₁] using F.prop t x hx
#align continuous_map.homotopy_rel.cast Function.HomotopyRel.cast

/-- Post-compose a homotopy relative to a set by a continuous function. -/
@[simps!] def compContinuousMap {f₀ f₁ : X → Y} (F : f₀.HomotopyRel f₁ S) (g : C(Y, Z)) :
    (comp g f₀).HomotopyRel (comp g f₁) S where
  toHomotopy := F.hcomp (Homotopy.refl g)
  prop' t x hx := congr_arg g (F.prop t x hx)

end HomotopyRel

/-- Given continuous maps `f₀` and `f₁`, we say `f₀` and `f₁` are homotopic relative to a set `S` if
there exists a `HomotopyRel f₀ f₁ S`.
-/
def HomotopicRel (f₀ f₁ : X → Y) (S : Set X) : Prop :=
  Nonempty (HomotopyRel f₀ f₁ S)
#align continuous_map.homotopic_rel Function.HomotopicRel

namespace HomotopicRel

variable {S : Set X}

/-- If two maps are homotopic relative to a set, then they are homotopic. -/
protected theorem homotopic {f₀ f₁ : X → Y} (h : HomotopicRel f₀ f₁ S) : Homotopic f₀ f₁ :=
  h.map fun F ↦ F.1

-- porting note: removed @[refl]
theorem refl (f : C(X, Y)) : HomotopicRel f f S :=
  ⟨HomotopyRel.refl f S⟩
#align continuous_map.homotopic_rel.refl Function.HomotopicRel.refl

@[symm]
theorem symm ⦃f g : X → Y⦄ (h : HomotopicRel f g S) : HomotopicRel g f S :=
  h.map HomotopyRel.symm
#align continuous_map.homotopic_rel.symm Function.HomotopicRel.symm

@[trans]
theorem trans ⦃f g h : X → Y⦄ (h₀ : HomotopicRel f g S) (h₁ : HomotopicRel g h S) :
    HomotopicRel f h S :=
  h₀.map2 HomotopyRel.trans h₁
#align continuous_map.homotopic_rel.trans Function.HomotopicRel.trans

theorem equivalence : Equivalence fun f g : C(X, Y) ↦ HomotopicRel f g S :=
  ⟨refl, fun h ↦ symm h, fun h ↦ trans h⟩
#align continuous_map.homotopic_rel.equivalence Function.HomotopicRel.equivalence

end HomotopicRel

@[simp] theorem homotopicRel_empty {f₀ f₁ : X → Y} : HomotopicRel f₀ f₁ ∅ ↔ Homotopic f₀ f₁ :=
  ⟨fun h ↦ h.homotopic, fun ⟨F⟩ ↦ ⟨⟨F, fun _ _ ↦ False.elim⟩⟩⟩

end Function
