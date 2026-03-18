/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
module

public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Topology.ContinuousMap.Ordered
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.UnitInterval

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

@[expose] public section

noncomputable section

universe u v w x

variable {F : Type*} {X : Type u} {Y : Type v} {Z : Type w} {Z' : Type x} {ι : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace Z']

open unitInterval

namespace ContinuousMap

/-- `ContinuousMap.Homotopy f₀ f₁` is the type of homotopies from `f₀` to `f₁`.

When possible, instead of parametrizing results over `(f : Homotopy f₀ f₁)`,
you should parametrize over `{F : Type*} [HomotopyLike F f₀ f₁] (f : F)`.

When you extend this structure, make sure to extend `ContinuousMap.HomotopyLike`. -/
structure Homotopy (f₀ f₁ : C(X, Y)) extends C(I × X, Y) where
  /-- value of the homotopy at 0 -/
  map_zero_left : ∀ x, toFun (0, x) = f₀ x
  /-- value of the homotopy at 1 -/
  map_one_left : ∀ x, toFun (1, x) = f₁ x

section

/-- `ContinuousMap.HomotopyLike F f₀ f₁` states that `F` is a type of homotopies between `f₀` and
`f₁`.

You should extend this class when you extend `ContinuousMap.Homotopy`. -/
class HomotopyLike {X Y : outParam Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (F : Type*) (f₀ f₁ : outParam <| C(X, Y)) [FunLike F (I × X) Y] : Prop
    extends ContinuousMapClass F (I × X) Y where
  /-- value of the homotopy at 0 -/
  map_zero_left (f : F) : ∀ x, f (0, x) = f₀ x
  /-- value of the homotopy at 1 -/
  map_one_left (f : F) : ∀ x, f (1, x) = f₁ x

end

namespace Homotopy

section

variable {f₀ f₁ : C(X, Y)}

instance instFunLike : FunLike (Homotopy f₀ f₁) (I × X) Y where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

instance : HomotopyLike (Homotopy f₀ f₁) f₀ f₁ where
  map_continuous f := f.continuous_toFun
  map_zero_left f := f.map_zero_left
  map_one_left f := f.map_one_left

@[ext]
theorem ext {F G : Homotopy f₀ f₁} (h : ∀ x, F x = G x) : F = G :=
  DFunLike.ext _ _ h

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def Simps.apply (F : Homotopy f₀ f₁) : I × X → Y :=
  F

initialize_simps_projections Homotopy (toFun → apply, -toContinuousMap)

/-- Deprecated. Use `map_continuous` instead. -/
protected theorem continuous (F : Homotopy f₀ f₁) : Continuous F :=
  F.continuous_toFun

@[simp]
theorem apply_zero (F : Homotopy f₀ f₁) (x : X) : F (0, x) = f₀ x :=
  F.map_zero_left x

@[simp]
theorem apply_one (F : Homotopy f₀ f₁) (x : X) : F (1, x) = f₁ x :=
  F.map_one_left x

@[simp]
theorem coe_toContinuousMap (F : Homotopy f₀ f₁) : ⇑F.toContinuousMap = F :=
  rfl

/-- Currying a homotopy to a continuous function from `I` to `C(X, Y)`.
-/
def curry (F : Homotopy f₀ f₁) : C(I, C(X, Y)) :=
  F.toContinuousMap.curry

@[simp]
theorem curry_apply (F : Homotopy f₀ f₁) (t : I) (x : X) : F.curry t x = F (t, x) :=
  rfl

@[simp] theorem curry_zero (F : Homotopy f₀ f₁) : F.curry 0 = f₀ := by ext; simp
@[simp] theorem curry_one (F : Homotopy f₀ f₁) : F.curry 1 = f₁ := by ext; simp

/-- Continuously extending a curried homotopy to a function from `ℝ` to `C(X, Y)`.
-/
def extend (F : Homotopy f₀ f₁) : C(ℝ, C(X, Y)) :=
  F.curry.IccExtend zero_le_one

theorem extend_apply_of_le_zero (F : Homotopy f₀ f₁) {t : ℝ} (ht : t ≤ 0) (x : X) :
    F.extend t x = f₀ x := by
  rw [← F.apply_zero]
  exact ContinuousMap.congr_fun (Set.IccExtend_of_le_left (zero_le_one' ℝ) F.curry ht) x

theorem extend_apply_of_one_le (F : Homotopy f₀ f₁) {t : ℝ} (ht : 1 ≤ t) (x : X) :
    F.extend t x = f₁ x := by
  rw [← F.apply_one]
  exact ContinuousMap.congr_fun (Set.IccExtend_of_right_le (zero_le_one' ℝ) F.curry ht) x

theorem extend_apply_coe (F : Homotopy f₀ f₁) (t : I) (x : X) : F.extend t x = F (t, x) :=
  ContinuousMap.congr_fun (Set.IccExtend_val (zero_le_one' ℝ) F.curry t) x

@[simp]
theorem extend_of_mem_I (F : Homotopy f₀ f₁) {t : ℝ} (ht : t ∈ I) :
    F.extend t = F.curry ⟨t, ht⟩ :=
  Set.IccExtend_of_mem (zero_le_one' ℝ) F.curry ht

theorem extend_zero (F : Homotopy f₀ f₁) : F.extend 0 = f₀ := by simp
theorem extend_one (F : Homotopy f₀ f₁) : F.extend 1 = f₁ := by simp

theorem extend_apply_of_mem_I (F : Homotopy f₀ f₁) {t : ℝ} (ht : t ∈ I) (x : X) :
    F.extend t x = F (⟨t, ht⟩, x) := by
  simp [ht]

protected theorem congr_fun {F G : Homotopy f₀ f₁} (h : F = G) (x : I × X) : F x = G x :=
  ContinuousMap.congr_fun (congr_arg _ h) x

protected theorem congr_arg (F : Homotopy f₀ f₁) {x y : I × X} (h : x = y) : F x = F y :=
  F.toContinuousMap.congr_arg h

end

/-- Given a continuous function `f`, we can define a `Homotopy f f` by `F (t, x) = f x`
-/
@[simps]
def refl (f : C(X, Y)) : Homotopy f f where
  toFun x := f x.2
  map_zero_left _ := rfl
  map_one_left _ := rfl

instance : Inhabited (Homotopy (ContinuousMap.id X) (ContinuousMap.id X)) :=
  ⟨Homotopy.refl _⟩

/-- Given a `Homotopy f₀ f₁`, we can define a `Homotopy f₁ f₀` by reversing the homotopy.
-/
@[simps]
def symm {f₀ f₁ : C(X, Y)} (F : Homotopy f₀ f₁) : Homotopy f₁ f₀ where
  toFun x := F (σ x.1, x.2)
  map_zero_left := by simp
  map_one_left := by norm_num

@[simp]
theorem symm_symm {f₀ f₁ : C(X, Y)} (F : Homotopy f₀ f₁) : F.symm.symm = F := by
  ext
  simp

theorem symm_bijective {f₀ f₁ : C(X, Y)} :
    Function.Bijective (Homotopy.symm : Homotopy f₀ f₁ → Homotopy f₁ f₀) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/--
Given `Homotopy f₀ f₁` and `Homotopy f₁ f₂`, we can define a `Homotopy f₀ f₂` by putting the first
homotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans {f₀ f₁ f₂ : C(X, Y)} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) : Homotopy f₀ f₂ where
  toFun x := if (x.1 : ℝ) ≤ 1 / 2 then F.extend (2 * x.1) x.2 else G.extend (2 * x.1 - 1) x.2
  continuous_toFun :=
    continuous_if_le (by fun_prop) .const
      (F.continuous.comp (by fun_prop)).continuousOn
      (G.continuous.comp (by fun_prop)).continuousOn (fun x hx ↦ by norm_num [hx])
  map_zero_left x := by norm_num
  map_one_left x := by norm_num

theorem trans_apply {f₀ f₁ f₂ : C(X, Y)} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) (x : I × X) :
    (F.trans G) x =
      if h : (x.1 : ℝ) ≤ 1 / 2 then
        F (⟨2 * x.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
      else
        G (⟨2 * x.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
  show ite _ _ _ = _ by
    split_ifs <;>
      · rw [extend, ContinuousMap.coe_IccExtend, Set.IccExtend_of_mem]
        rfl

theorem symm_trans {f₀ f₁ f₂ : C(X, Y)} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) :
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

/-- Casting a `Homotopy f₀ f₁` to a `Homotopy g₀ g₁` where `f₀ = g₀` and `f₁ = g₁`.
-/
@[simps]
def cast {f₀ f₁ g₀ g₁ : C(X, Y)} (F : Homotopy f₀ f₁) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) :
    Homotopy g₀ g₁ where
  toFun := F
  map_zero_left := by simp [← h₀]
  map_one_left := by simp [← h₁]

/-- If we have a `Homotopy g₀ g₁` and a `Homotopy f₀ f₁`, then we can compose them and get a
`Homotopy (g₀.comp f₀) (g₁.comp f₁)`.
-/
@[simps]
def comp {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(Y, Z)} (G : Homotopy g₀ g₁) (F : Homotopy f₀ f₁) :
    Homotopy (g₀.comp f₀) (g₁.comp f₁) where
  toFun x := G (x.1, F x)
  map_zero_left := by simp
  map_one_left := by simp

/-- Composition of a `Homotopy g₀ g₁` and `f : C(X, Y)` as a homotopy between `g₀.comp f` and
`g₁.comp f`. -/
@[simps!]
def compContinuousMap {g₀ g₁ : C(Y, Z)} (G : Homotopy g₀ g₁) (f : C(X, Y)) :
    Homotopy (g₀.comp f) (g₁.comp f) :=
  G.comp (.refl f)

/-- Let `F` be a homotopy between `f₀ : C(X, Y)` and `f₁ : C(X, Y)`. Let `G` be a homotopy between
`g₀ : C(X, Z)` and `g₁ : C(X, Z)`. Then `F.prodMk G` is the homotopy between `f₀.prodMk g₀` and
`f₁.prodMk g₁` that sends `p` to `(F p, G p)`. -/
nonrec def prodMk {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(X, Z)} (F : Homotopy f₀ f₁) (G : Homotopy g₀ g₁) :
    Homotopy (f₀.prodMk g₀) (f₁.prodMk g₁) where
  toContinuousMap := F.prodMk G
  map_zero_left _ := Prod.ext (F.map_zero_left _) (G.map_zero_left _)
  map_one_left _ := Prod.ext (F.map_one_left _) (G.map_one_left _)

/-- Let `F` be a homotopy between `f₀ : C(X, Y)` and `f₁ : C(X, Y)`. Let `G` be a homotopy between
`g₀ : C(Z, Z')` and `g₁ : C(Z, Z')`. Then `F.prodMap G` is the homotopy between `f₀.prodMap g₀` and
`f₁.prodMap g₁` that sends `(t, x, z)` to `(F (t, x), G (t, z))`. -/
def prodMap {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(Z, Z')} (F : Homotopy f₀ f₁) (G : Homotopy g₀ g₁) :
    Homotopy (f₀.prodMap g₀) (f₁.prodMap g₁) :=
  .prodMk (F.compContinuousMap .fst) (G.compContinuousMap .snd)

/-- Given a family of homotopies `F i` between `f₀ i : C(X, Y i)` and `f₁ i : C(X, Y i)`, returns a
homotopy between `ContinuousMap.pi f₀` and `ContinuousMap.pi f₁`. -/
protected def pi {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] {f₀ f₁ : ∀ i, C(X, Y i)}
    (F : ∀ i, Homotopy (f₀ i) (f₁ i)) :
    Homotopy (.pi f₀) (.pi f₁) where
  toContinuousMap := .pi fun i ↦ F i
  map_zero_left x := funext fun i ↦ (F i).map_zero_left x
  map_one_left x := funext fun i ↦ (F i).map_one_left x

/-- Given a family of homotopies `F i` between `f₀ i : C(X i, Y i)` and `f₁ i : C(X i, Y i)`,
returns a homotopy between `ContinuousMap.piMap f₀` and `ContinuousMap.piMap f₁`. -/
protected def piMap {X Y : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    {f₀ f₁ : ∀ i, C(X i, Y i)} (F : ∀ i, Homotopy (f₀ i) (f₁ i)) :
    Homotopy (.piMap f₀) (.piMap f₁) :=
  .pi fun i ↦ (F i).compContinuousMap <| .eval i

end Homotopy

/-- Given continuous maps `f₀` and `f₁`, we say `f₀` and `f₁` are homotopic if there exists a
`Homotopy f₀ f₁`.
-/
def Homotopic (f₀ f₁ : C(X, Y)) : Prop :=
  Nonempty (Homotopy f₀ f₁)

namespace Homotopic

@[refl]
theorem refl (f : C(X, Y)) : Homotopic f f :=
  ⟨Homotopy.refl f⟩

@[symm]
theorem symm ⦃f g : C(X, Y)⦄ (h : Homotopic f g) : Homotopic g f :=
  h.map Homotopy.symm

@[trans]
theorem trans ⦃f g h : C(X, Y)⦄ (h₀ : Homotopic f g) (h₁ : Homotopic g h) : Homotopic f h :=
  h₀.map2 Homotopy.trans h₁

theorem comp {g₀ g₁ : C(Y, Z)} {f₀ f₁ : C(X, Y)} (hg : Homotopic g₀ g₁) (hf : Homotopic f₀ f₁) :
    Homotopic (g₀.comp f₀) (g₁.comp f₁) :=
  hg.map2 Homotopy.comp hf

theorem equivalence : Equivalence (@Homotopic X Y _ _) :=
  ⟨refl, by apply symm, by apply trans⟩

nonrec theorem prodMk {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(X, Z)} :
    Homotopic f₀ f₁ → Homotopic g₀ g₁ → Homotopic (f₀.prodMk g₀) (f₁.prodMk g₁)
  | ⟨F⟩, ⟨G⟩ => ⟨F.prodMk G⟩

nonrec theorem prodMap {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(Z, Z')} :
    Homotopic f₀ f₁ → Homotopic g₀ g₁ → Homotopic (f₀.prodMap g₀) (f₁.prodMap g₁)
  | ⟨F⟩, ⟨G⟩ => ⟨F.prodMap G⟩

/-- If each `f₀ i : C(X, Y i)` is homotopic to `f₁ i : C(X, Y i)`, then `ContinuousMap.pi f₀` is
homotopic to `ContinuousMap.pi f₁`. -/
protected theorem pi {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] {f₀ f₁ : ∀ i, C(X, Y i)}
    (F : ∀ i, Homotopic (f₀ i) (f₁ i)) :
    Homotopic (.pi f₀) (.pi f₁) :=
  ⟨.pi fun i ↦ (F i).some⟩

/-- If each `f₀ i : C(X, Y i)` is homotopic to `f₁ i : C(X, Y i)`, then `ContinuousMap.pi f₀` is
homotopic to `ContinuousMap.pi f₁`. -/
protected theorem piMap {X Y : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] {f₀ f₁ : ∀ i, C(X i, Y i)} (F : ∀ i, Homotopic (f₀ i) (f₁ i)) :
    Homotopic (.piMap f₀) (.piMap f₁) :=
  .pi fun i ↦ .comp (F i) (.refl <| .eval i)

end Homotopic

/--
The type of homotopies between `f₀ f₁ : C(X, Y)`, where the intermediate maps satisfy the predicate
`P : C(X, Y) → Prop`
-/
structure HomotopyWith (f₀ f₁ : C(X, Y)) (P : C(X, Y) → Prop) extends Homotopy f₀ f₁ where
  -- TODO: use `toHomotopy.curry t`
  /-- the intermediate maps of the homotopy satisfy the property -/
  prop' : ∀ t, P ⟨fun x ↦ toFun (t, x), continuous_toFun.comp (by fun_prop)⟩

namespace HomotopyWith

section

variable {f₀ f₁ : C(X, Y)} {P : C(X, Y) → Prop}

instance instFunLike : FunLike (HomotopyWith f₀ f₁ P) (I × X) Y where
  coe F := ⇑F.toHomotopy
  coe_injective'
  | ⟨⟨⟨_, _⟩, _, _⟩, _⟩, ⟨⟨⟨_, _⟩, _, _⟩, _⟩, rfl => rfl

instance : HomotopyLike (HomotopyWith f₀ f₁ P) f₀ f₁ where
  map_continuous F := F.continuous_toFun
  map_zero_left F := F.map_zero_left
  map_one_left F := F.map_one_left

theorem coeFn_injective : @Function.Injective (HomotopyWith f₀ f₁ P) (I × X → Y) (⇑) :=
  DFunLike.coe_injective'

@[ext]
theorem ext {F G : HomotopyWith f₀ f₁ P} (h : ∀ x, F x = G x) : F = G := DFunLike.ext F G h

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def Simps.apply (F : HomotopyWith f₀ f₁ P) : I × X → Y := F

initialize_simps_projections HomotopyWith (toFun → apply, -toHomotopy_toContinuousMap)

@[continuity]
protected theorem continuous (F : HomotopyWith f₀ f₁ P) : Continuous F :=
  F.continuous_toFun

@[simp]
theorem apply_zero (F : HomotopyWith f₀ f₁ P) (x : X) : F (0, x) = f₀ x :=
  F.map_zero_left x

@[simp]
theorem apply_one (F : HomotopyWith f₀ f₁ P) (x : X) : F (1, x) = f₁ x :=
  F.map_one_left x

theorem coe_toContinuousMap (F : HomotopyWith f₀ f₁ P) : ⇑F.toContinuousMap = F :=
  rfl

@[simp]
theorem coe_toHomotopy (F : HomotopyWith f₀ f₁ P) : ⇑F.toHomotopy = F :=
  rfl

theorem prop (F : HomotopyWith f₀ f₁ P) (t : I) : P (F.toHomotopy.curry t) := F.prop' t

theorem extendProp (F : HomotopyWith f₀ f₁ P) (t : ℝ) : P (F.toHomotopy.extend t) := F.prop _

end

variable {P : C(X, Y) → Prop}

/-- Given a continuous function `f`, and a proof `h : P f`, we can define a `HomotopyWith f f P` by
`F (t, x) = f x`
-/
@[simps!]
def refl (f : C(X, Y)) (hf : P f) : HomotopyWith f f P where
  toHomotopy := Homotopy.refl f
  prop' := fun _ => hf

instance : Inhabited (HomotopyWith (ContinuousMap.id X) (ContinuousMap.id X) fun _ => True) :=
  ⟨HomotopyWith.refl _ trivial⟩

/--
Given a `HomotopyWith f₀ f₁ P`, we can define a `HomotopyWith f₁ f₀ P` by reversing the homotopy.
-/
@[simps!]
def symm {f₀ f₁ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) : HomotopyWith f₁ f₀ P where
  toHomotopy := F.toHomotopy.symm
  prop' := fun t => F.prop (σ t)

@[simp]
theorem symm_symm {f₀ f₁ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) : F.symm.symm = F :=
  ext <| Homotopy.congr_fun <| Homotopy.symm_symm _

theorem symm_bijective {f₀ f₁ : C(X, Y)} :
    Function.Bijective (HomotopyWith.symm : HomotopyWith f₀ f₁ P → HomotopyWith f₁ f₀ P) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/--
Given `HomotopyWith f₀ f₁ P` and `HomotopyWith f₁ f₂ P`, we can define a `HomotopyWith f₀ f₂ P`
by putting the first homotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans {f₀ f₁ f₂ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) (G : HomotopyWith f₁ f₂ P) :
    HomotopyWith f₀ f₂ P :=
  { F.toHomotopy.trans G.toHomotopy with
    prop' := fun t => by
      simp only [Homotopy.trans]
      change P ⟨fun _ => ite ((t : ℝ) ≤ _) _ _, _⟩
      split_ifs
      · exact F.extendProp _
      · exact G.extendProp _ }

theorem trans_apply {f₀ f₁ f₂ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) (G : HomotopyWith f₁ f₂ P)
    (x : I × X) :
    (F.trans G) x =
      if h : (x.1 : ℝ) ≤ 1 / 2 then
        F (⟨2 * x.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
      else
        G (⟨2 * x.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
  Homotopy.trans_apply _ _ _

theorem symm_trans {f₀ f₁ f₂ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) (G : HomotopyWith f₁ f₂ P) :
    (F.trans G).symm = G.symm.trans F.symm :=
  ext <| Homotopy.congr_fun <| Homotopy.symm_trans _ _

/-- Casting a `HomotopyWith f₀ f₁ P` to a `HomotopyWith g₀ g₁ P` where `f₀ = g₀` and `f₁ = g₁`.
-/
@[simps!]
def cast {f₀ f₁ g₀ g₁ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) :
    HomotopyWith g₀ g₁ P where
  toHomotopy := F.toHomotopy.cast h₀ h₁
  prop' := F.prop

end HomotopyWith

/-- Given continuous maps `f₀` and `f₁`, we say `f₀` and `f₁` are homotopic with respect to the
predicate `P` if there exists a `HomotopyWith f₀ f₁ P`.
-/
def HomotopicWith (f₀ f₁ : C(X, Y)) (P : C(X, Y) → Prop) : Prop :=
  Nonempty (HomotopyWith f₀ f₁ P)

namespace HomotopicWith

variable {P : C(X, Y) → Prop}

theorem refl (f : C(X, Y)) (hf : P f) : HomotopicWith f f P :=
  ⟨HomotopyWith.refl f hf⟩

@[symm]
theorem symm ⦃f g : C(X, Y)⦄ (h : HomotopicWith f g P) : HomotopicWith g f P :=
  ⟨h.some.symm⟩

-- Note: this was formerly tagged with `@[trans]`, and although the `trans` attribute accepted it
-- the `trans` tactic could not use it.
-- An update to the trans tactic coming in https://github.com/leanprover-community/mathlib4/pull/7014 will reject this attribute.
-- It could be restored by changing the argument order to `HomotopicWith P f g`.
@[trans]
theorem trans ⦃f g h : C(X, Y)⦄ (h₀ : HomotopicWith f g P) (h₁ : HomotopicWith g h P) :
    HomotopicWith f h P :=
  ⟨h₀.some.trans h₁.some⟩

end HomotopicWith

/--
A `HomotopyRel f₀ f₁ S` is a homotopy between `f₀` and `f₁` which is fixed on the points in `S`.
-/
abbrev HomotopyRel (f₀ f₁ : C(X, Y)) (S : Set X) :=
  HomotopyWith f₀ f₁ fun f ↦ ∀ x ∈ S, f x = f₀ x

namespace HomotopyRel

section

variable {f₀ f₁ : C(X, Y)} {S : Set X}

theorem eq_fst (F : HomotopyRel f₀ f₁ S) (t : I) {x : X} (hx : x ∈ S) : F (t, x) = f₀ x :=
  F.prop t x hx

theorem eq_snd (F : HomotopyRel f₀ f₁ S) (t : I) {x : X} (hx : x ∈ S) : F (t, x) = f₁ x := by
  rw [F.eq_fst t hx, ← F.eq_fst 1 hx, F.apply_one]

theorem fst_eq_snd (F : HomotopyRel f₀ f₁ S) {x : X} (hx : x ∈ S) : f₀ x = f₁ x :=
  F.eq_fst 0 hx ▸ F.eq_snd 0 hx

end

variable {f₀ f₁ f₂ : C(X, Y)} {S : Set X}

/-- Given a map `f : C(X, Y)` and a set `S`, we can define a `HomotopyRel f f S` by setting
`F (t, x) = f x` for all `t`. This is defined using `HomotopyWith.refl`, but with the proof
filled in.
-/
@[simps!]
def refl (f : C(X, Y)) (S : Set X) : HomotopyRel f f S :=
  HomotopyWith.refl f fun _ _ ↦ rfl

/--
Given a `HomotopyRel f₀ f₁ S`, we can define a `HomotopyRel f₁ f₀ S` by reversing the homotopy.
-/
@[simps!]
def symm (F : HomotopyRel f₀ f₁ S) : HomotopyRel f₁ f₀ S where
  toHomotopy := F.toHomotopy.symm
  prop' := fun _ _ hx ↦ F.eq_snd _ hx

@[simp]
theorem symm_symm (F : HomotopyRel f₀ f₁ S) : F.symm.symm = F :=
  HomotopyWith.symm_symm F

theorem symm_bijective :
    Function.Bijective (HomotopyRel.symm : HomotopyRel f₀ f₁ S → HomotopyRel f₁ f₀ S) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

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

theorem trans_apply (F : HomotopyRel f₀ f₁ S) (G : HomotopyRel f₁ f₂ S) (x : I × X) :
    (F.trans G) x =
      if h : (x.1 : ℝ) ≤ 1 / 2 then
        F (⟨2 * x.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
      else
        G (⟨2 * x.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
  Homotopy.trans_apply _ _ _

theorem symm_trans (F : HomotopyRel f₀ f₁ S) (G : HomotopyRel f₁ f₂ S) :
    (F.trans G).symm = G.symm.trans F.symm :=
  HomotopyWith.ext <| Homotopy.congr_fun <| Homotopy.symm_trans _ _

/-- Casting a `HomotopyRel f₀ f₁ S` to a `HomotopyRel g₀ g₁ S` where `f₀ = g₀` and `f₁ = g₁`.
-/
@[simps!]
def cast {f₀ f₁ g₀ g₁ : C(X, Y)} (F : HomotopyRel f₀ f₁ S) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) :
    HomotopyRel g₀ g₁ S where
  toHomotopy := Homotopy.cast F.toHomotopy h₀ h₁
  prop' t x hx := by simpa only [← h₀, ← h₁] using F.prop t x hx

/-- Post-compose a homotopy relative to a set by a continuous function. -/
@[simps!] def compContinuousMap {f₀ f₁ : C(X, Y)} (F : f₀.HomotopyRel f₁ S) (g : C(Y, Z)) :
    (g.comp f₀).HomotopyRel (g.comp f₁) S where
  toHomotopy := .comp (.refl g) F.toHomotopy
  prop' t x hx := congr_arg g (F.prop t x hx)

end HomotopyRel

/-- Given continuous maps `f₀` and `f₁`, we say `f₀` and `f₁` are homotopic relative to a set `S` if
there exists a `HomotopyRel f₀ f₁ S`.
-/
def HomotopicRel (f₀ f₁ : C(X, Y)) (S : Set X) : Prop :=
  Nonempty (HomotopyRel f₀ f₁ S)

namespace HomotopicRel

variable {S : Set X}

/-- If two maps are homotopic relative to a set, then they are homotopic. -/
protected theorem homotopic {f₀ f₁ : C(X, Y)} (h : HomotopicRel f₀ f₁ S) : Homotopic f₀ f₁ :=
  h.map fun F ↦ F.1

/-- If two maps are homotopic relative to a set, then they agree on it. -/
theorem fst_eq_snd ⦃f₀ f₁ : C(X, Y)⦄ (h : HomotopicRel f₀ f₁ S) {x : X} (hx : x ∈ S) :
    f₀ x = f₁ x :=
  Nonempty.elim h (HomotopyRel.fst_eq_snd · hx)

theorem refl (f : C(X, Y)) : HomotopicRel f f S :=
  ⟨HomotopyRel.refl f S⟩

@[symm]
theorem symm ⦃f g : C(X, Y)⦄ (h : HomotopicRel f g S) : HomotopicRel g f S :=
  h.map HomotopyRel.symm

@[trans]
theorem trans ⦃f g h : C(X, Y)⦄ (h₀ : HomotopicRel f g S) (h₁ : HomotopicRel g h S) :
    HomotopicRel f h S :=
  h₀.map2 HomotopyRel.trans h₁

theorem equivalence : Equivalence fun f g : C(X, Y) => HomotopicRel f g S :=
  ⟨refl, by apply symm, by apply trans⟩

theorem comp_continuousMap ⦃f₀ f₁ : C(X, Y)⦄ (h : f₀.HomotopicRel f₁ S) (g : C(Y, Z)) :
    (g.comp f₀).HomotopicRel (g.comp f₁) S := h.map (·.compContinuousMap g)

end HomotopicRel

@[simp] theorem homotopicRel_empty {f₀ f₁ : C(X, Y)} : HomotopicRel f₀ f₁ ∅ ↔ Homotopic f₀ f₁ :=
  ⟨fun h ↦ h.homotopic, fun ⟨F⟩ ↦ ⟨⟨F, fun _ _ ↦ False.elim⟩⟩⟩

end ContinuousMap
