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
#align continuous_map.homotopy ContinuousMap.Homotopy

section

/-- `ContinuousMap.HomotopyLike F f₀ f₁` states that `F` is a type of homotopies between `f₀` and
`f₁`.

You should extend this class when you extend `ContinuousMap.Homotopy`. -/
class HomotopyLike {X Y : outParam (Type*)} [TopologicalSpace X] [TopologicalSpace Y]
    (F : Type*) (f₀ f₁ : outParam <| C(X, Y)) extends ContinuousMapClass F (I × X) Y where
  /-- value of the homotopy at 0 -/
  map_zero_left (f : F) : ∀ x, f (0, x) = f₀ x
  /-- value of the homotopy at 1 -/
  map_one_left (f : F) : ∀ x, f (1, x) = f₁ x
#align continuous_map.homotopy_like ContinuousMap.HomotopyLike

end

namespace Homotopy

section

variable {f₀ f₁ : C(X, Y)}

instance : HomotopyLike (Homotopy f₀ f₁) f₀ f₁ where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    -- ⊢ { toContinuousMap := ContinuousMap.mk toFun✝, map_zero_left := map_zero_left …
    obtain ⟨⟨_, _⟩, _⟩ := g
    -- ⊢ { toContinuousMap := ContinuousMap.mk toFun✝¹, map_zero_left := map_zero_lef …
    congr
    -- 🎉 no goals
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
#align continuous_map.homotopy.ext ContinuousMap.Homotopy.ext

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def Simps.apply (F : Homotopy f₀ f₁) : I × X → Y :=
  F
#align continuous_map.homotopy.simps.apply ContinuousMap.Homotopy.Simps.apply

initialize_simps_projections Homotopy (toFun → apply, -toContinuousMap)

/-- Deprecated. Use `map_continuous` instead. -/
protected theorem continuous (F : Homotopy f₀ f₁) : Continuous F :=
  F.continuous_toFun
#align continuous_map.homotopy.continuous ContinuousMap.Homotopy.continuous

@[simp]
theorem apply_zero (F : Homotopy f₀ f₁) (x : X) : F (0, x) = f₀ x :=
  F.map_zero_left x
#align continuous_map.homotopy.apply_zero ContinuousMap.Homotopy.apply_zero

@[simp]
theorem apply_one (F : Homotopy f₀ f₁) (x : X) : F (1, x) = f₁ x :=
  F.map_one_left x
#align continuous_map.homotopy.apply_one ContinuousMap.Homotopy.apply_one

@[simp]
theorem coe_toContinuousMap (F : Homotopy f₀ f₁) : ⇑F.toContinuousMap = F :=
  rfl
#align continuous_map.homotopy.coe_to_continuous_map ContinuousMap.Homotopy.coe_toContinuousMap

/-- Currying a homotopy to a continuous function from `I` to `C(X, Y)`.
-/
def curry (F : Homotopy f₀ f₁) : C(I, C(X, Y)) :=
  F.toContinuousMap.curry
#align continuous_map.homotopy.curry ContinuousMap.Homotopy.curry

@[simp]
theorem curry_apply (F : Homotopy f₀ f₁) (t : I) (x : X) : F.curry t x = F (t, x) :=
  rfl
#align continuous_map.homotopy.curry_apply ContinuousMap.Homotopy.curry_apply

/-- Continuously extending a curried homotopy to a function from `ℝ` to `C(X, Y)`.
-/
def extend (F : Homotopy f₀ f₁) : C(ℝ, C(X, Y)) :=
  F.curry.IccExtend zero_le_one
#align continuous_map.homotopy.extend ContinuousMap.Homotopy.extend

theorem extend_apply_of_le_zero (F : Homotopy f₀ f₁) {t : ℝ} (ht : t ≤ 0) (x : X) :
    F.extend t x = f₀ x := by
  rw [← F.apply_zero]
  -- ⊢ ↑(↑(extend F) t) x = ↑F (0, x)
  exact ContinuousMap.congr_fun (Set.IccExtend_of_le_left (zero_le_one' ℝ) F.curry ht) x
  -- 🎉 no goals
#align continuous_map.homotopy.extend_apply_of_le_zero ContinuousMap.Homotopy.extend_apply_of_le_zero

theorem extend_apply_of_one_le (F : Homotopy f₀ f₁) {t : ℝ} (ht : 1 ≤ t) (x : X) :
    F.extend t x = f₁ x := by
  rw [← F.apply_one]
  -- ⊢ ↑(↑(extend F) t) x = ↑F (1, x)
  exact ContinuousMap.congr_fun (Set.IccExtend_of_right_le (zero_le_one' ℝ) F.curry ht) x
  -- 🎉 no goals
#align continuous_map.homotopy.extend_apply_of_one_le ContinuousMap.Homotopy.extend_apply_of_one_le

@[simp]
theorem extend_apply_coe (F : Homotopy f₀ f₁) (t : I) (x : X) : F.extend t x = F (t, x) :=
  ContinuousMap.congr_fun (Set.IccExtend_val (zero_le_one' ℝ) F.curry t) x
#align continuous_map.homotopy.extend_apply_coe ContinuousMap.Homotopy.extend_apply_coe

@[simp]
theorem extend_apply_of_mem_I (F : Homotopy f₀ f₁) {t : ℝ} (ht : t ∈ I) (x : X) :
    F.extend t x = F (⟨t, ht⟩, x) :=
  ContinuousMap.congr_fun (Set.IccExtend_of_mem (zero_le_one' ℝ) F.curry ht) x
set_option linter.uppercaseLean3 false in
#align continuous_map.homotopy.extend_apply_of_mem_I ContinuousMap.Homotopy.extend_apply_of_mem_I

theorem congr_fun {F G : Homotopy f₀ f₁} (h : F = G) (x : I × X) : F x = G x :=
  ContinuousMap.congr_fun (congr_arg _ h) x
#align continuous_map.homotopy.congr_fun ContinuousMap.Homotopy.congr_fun

theorem congr_arg (F : Homotopy f₀ f₁) {x y : I × X} (h : x = y) : F x = F y :=
  F.toContinuousMap.congr_arg h
#align continuous_map.homotopy.congr_arg ContinuousMap.Homotopy.congr_arg

end

/-- Given a continuous function `f`, we can define a `Homotopy f f` by `F (t, x) = f x`
-/
@[simps]
def refl (f : C(X, Y)) : Homotopy f f where
  toFun x := f x.2
  map_zero_left _ := rfl
  map_one_left _ := rfl
#align continuous_map.homotopy.refl ContinuousMap.Homotopy.refl

instance : Inhabited (Homotopy (ContinuousMap.id X) (ContinuousMap.id X)) :=
  ⟨Homotopy.refl _⟩

/-- Given a `Homotopy f₀ f₁`, we can define a `Homotopy f₁ f₀` by reversing the homotopy.
-/
@[simps]
def symm {f₀ f₁ : C(X, Y)} (F : Homotopy f₀ f₁) : Homotopy f₁ f₀ where
  toFun x := F (σ x.1, x.2)
  map_zero_left := by norm_num
                      -- 🎉 no goals
  map_one_left := by norm_num
                     -- 🎉 no goals
#align continuous_map.homotopy.symm ContinuousMap.Homotopy.symm

@[simp]
theorem symm_symm {f₀ f₁ : C(X, Y)} (F : Homotopy f₀ f₁) : F.symm.symm = F := by
  ext
  -- ⊢ ↑(symm (symm F)) x✝ = ↑F x✝
  simp
  -- 🎉 no goals
#align continuous_map.homotopy.symm_symm ContinuousMap.Homotopy.symm_symm

/--
Given `Homotopy f₀ f₁` and `Homotopy f₁ f₂`, we can define a `Homotopy f₀ f₂` by putting the first
homotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans {f₀ f₁ f₂ : C(X, Y)} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) : Homotopy f₀ f₂ where
  toFun x := if (x.1 : ℝ) ≤ 1 / 2 then F.extend (2 * x.1) x.2 else G.extend (2 * x.1 - 1) x.2
  continuous_toFun := by
    refine'
      continuous_if_le (continuous_induced_dom.comp continuous_fst) continuous_const
        (F.continuous.comp (by continuity)).continuousOn
        (G.continuous.comp (by continuity)).continuousOn _
    rintro x hx
    -- ⊢ ↑(↑(extend F) (2 * ↑x.fst)) x.snd = ↑(↑(extend G) (2 * ↑x.fst - 1)) x.snd
    norm_num [hx]
    -- 🎉 no goals
  map_zero_left x := by norm_num
                        -- 🎉 no goals
  map_one_left x := by norm_num
                       -- 🎉 no goals
#align continuous_map.homotopy.trans ContinuousMap.Homotopy.trans

theorem trans_apply {f₀ f₁ f₂ : C(X, Y)} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) (x : I × X) :
    (F.trans G) x =
      if h : (x.1 : ℝ) ≤ 1 / 2 then
        F (⟨2 * x.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
      else
        G (⟨2 * x.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
  show ite _ _ _ = _ by
    split_ifs <;>
    -- ⊢ ↑(↑(extend F) (2 * ↑x.fst)) x.snd = ↑F ({ val := 2 * ↑x.fst, property := (_  …
      · rw [extend, ContinuousMap.coe_IccExtend, Set.IccExtend_of_mem]
        -- ⊢ ↑(↑(curry F) { val := 2 * ↑x.fst, property := ?pos.hx✝ }) x.snd = ↑F ({ val  …
        -- ⊢ ↑(↑(curry G) { val := 2 * ↑x.fst - 1, property := ?neg.hx✝ }) x.snd = ↑G ({  …
        -- 🎉 no goals
        rfl
        -- 🎉 no goals
#align continuous_map.homotopy.trans_apply ContinuousMap.Homotopy.trans_apply

theorem symm_trans {f₀ f₁ f₂ : C(X, Y)} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) :
    (F.trans G).symm = G.symm.trans F.symm := by
  ext ⟨t, _⟩
  -- ⊢ ↑(symm (trans F G)) (t, snd✝) = ↑(trans (symm G) (symm F)) (t, snd✝)
  rw [trans_apply, symm_apply, trans_apply]
  -- ⊢ (if h : ↑(σ (t, snd✝).fst, (t, snd✝).snd).fst ≤ 1 / 2 then ↑F ({ val := 2 *  …
  simp only [coe_symm_eq, symm_apply]
  -- ⊢ (if h : 1 - ↑t ≤ 1 / 2 then ↑F ({ val := 2 * (1 - ↑t), property := (_ : (fun …
  split_ifs with h₁ h₂ h₂
  · have ht : (t : ℝ) = 1 / 2 := by linarith
    -- ⊢ ↑F ({ val := 2 * (1 - ↑t), property := (_ : (fun x => x ∈ I) (2 * (1 - ↑t))) …
    norm_num [ht]
    -- 🎉 no goals
  · congr 2
    -- ⊢ { val := 2 * (1 - ↑t), property := (_ : (fun x => x ∈ I) (2 * (1 - ↑t))) } = …
    apply Subtype.ext
    -- ⊢ ↑{ val := 2 * (1 - ↑t), property := (_ : (fun x => x ∈ I) (2 * (1 - ↑t))) }  …
    simp only [coe_symm_eq]
    -- ⊢ 2 * (1 - ↑t) = 1 - (2 * ↑t - 1)
    linarith
    -- 🎉 no goals
  · congr 2
    -- ⊢ { val := 2 * (1 - ↑t) - 1, property := (_ : (fun x => x ∈ I) (2 * (1 - ↑t) - …
    apply Subtype.ext
    -- ⊢ ↑{ val := 2 * (1 - ↑t) - 1, property := (_ : (fun x => x ∈ I) (2 * (1 - ↑t)  …
    simp only [coe_symm_eq]
    -- ⊢ 2 * (1 - ↑t) - 1 = 1 - 2 * ↑t
    linarith
    -- 🎉 no goals
  · exfalso
    -- ⊢ False
    linarith
    -- 🎉 no goals
#align continuous_map.homotopy.symm_trans ContinuousMap.Homotopy.symm_trans

/-- Casting a `Homotopy f₀ f₁` to a `Homotopy g₀ g₁` where `f₀ = g₀` and `f₁ = g₁`.
-/
@[simps]
def cast {f₀ f₁ g₀ g₁ : C(X, Y)} (F : Homotopy f₀ f₁) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) :
    Homotopy g₀ g₁ where
  toFun := F
  map_zero_left := by simp [← h₀]
                      -- 🎉 no goals
  map_one_left := by simp [← h₁]
                     -- 🎉 no goals
#align continuous_map.homotopy.cast ContinuousMap.Homotopy.cast

/-- Composition of a `Homotopy g₀ g₁` and `f : C(X, Y)` as a homotopy between `g₀.comp f` and
`g₁.comp f`. -/
@[simps!]
def compContinuousMap {g₀ g₁ : C(Y, Z)} (G : Homotopy g₀ g₁) (f : C(X, Y)) :
    Homotopy (g₀.comp f) (g₁.comp f) where
  toContinuousMap := G.comp (.prodMap (.id _) f)
  map_zero_left _ := G.map_zero_left _
  map_one_left _ := G.map_one_left _

/-- If we have a `Homotopy f₀ f₁` and a `Homotopy g₀ g₁`, then we can compose them and get a
`Homotopy (g₀.comp f₀) (g₁.comp f₁)`.
-/
@[simps]
def hcomp {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(Y, Z)} (F : Homotopy f₀ f₁) (G : Homotopy g₀ g₁) :
    Homotopy (g₀.comp f₀) (g₁.comp f₁) where
  toFun x := G (x.1, F x)
  map_zero_left := by simp
                      -- 🎉 no goals
  map_one_left := by simp
                     -- 🎉 no goals
#align continuous_map.homotopy.hcomp ContinuousMap.Homotopy.hcomp

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
  .prodMk (.hcomp (.refl .fst) F) (.hcomp (.refl .snd) G)

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
  .pi fun i ↦ .hcomp (.refl <| .eval i) (F i)

end Homotopy

/-- Given continuous maps `f₀` and `f₁`, we say `f₀` and `f₁` are homotopic if there exists a
`Homotopy f₀ f₁`.
-/
def Homotopic (f₀ f₁ : C(X, Y)) : Prop :=
  Nonempty (Homotopy f₀ f₁)
#align continuous_map.homotopic ContinuousMap.Homotopic

namespace Homotopic

@[refl]
theorem refl (f : C(X, Y)) : Homotopic f f :=
  ⟨Homotopy.refl f⟩
#align continuous_map.homotopic.refl ContinuousMap.Homotopic.refl

@[symm]
theorem symm ⦃f g : C(X, Y)⦄ (h : Homotopic f g) : Homotopic g f :=
  h.map Homotopy.symm
#align continuous_map.homotopic.symm ContinuousMap.Homotopic.symm

@[trans]
theorem trans ⦃f g h : C(X, Y)⦄ (h₀ : Homotopic f g) (h₁ : Homotopic g h) : Homotopic f h :=
  h₀.map2 Homotopy.trans h₁
#align continuous_map.homotopic.trans ContinuousMap.Homotopic.trans

theorem hcomp {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(Y, Z)} (h₀ : Homotopic f₀ f₁) (h₁ : Homotopic g₀ g₁) :
    Homotopic (g₀.comp f₀) (g₁.comp f₁) :=
  h₀.map2 Homotopy.hcomp h₁
#align continuous_map.homotopic.hcomp ContinuousMap.Homotopic.hcomp

theorem equivalence : Equivalence (@Homotopic X Y _ _) :=
  ⟨refl, by apply symm, by apply trans⟩
            -- 🎉 no goals
                           -- 🎉 no goals
#align continuous_map.homotopic.equivalence ContinuousMap.Homotopic.equivalence

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
  .pi fun i ↦ .hcomp (.refl <| .eval i) (F i)

end Homotopic

/--
The type of homotopies between `f₀ f₁ : C(X, Y)`, where the intermediate maps satisfy the predicate
`P : C(X, Y) → Prop`
-/
structure HomotopyWith (f₀ f₁ : C(X, Y)) (P : C(X, Y) → Prop) extends Homotopy f₀ f₁ where
  -- porting note: todo: use `toHomotopy.curry t`
  /-- the intermediate maps of the homotopy satisfy the property -/
  prop' : ∀ t, P ⟨fun x => toFun (t, x),
    Continuous.comp continuous_toFun (continuous_const.prod_mk continuous_id')⟩
#align continuous_map.homotopy_with ContinuousMap.HomotopyWith

namespace HomotopyWith

section

variable {f₀ f₁ : C(X, Y)} {P : C(X, Y) → Prop}

instance : HomotopyLike (HomotopyWith f₀ f₁ P) f₀ f₁ where
  coe F := ⇑F.toHomotopy
  coe_injective'
  | ⟨⟨⟨_, _⟩, _, _⟩, _⟩, ⟨⟨⟨_, _⟩, _, _⟩, _⟩, rfl => rfl
  map_continuous F := F.continuous_toFun
  map_zero_left F := F.map_zero_left
  map_one_left F := F.map_one_left

theorem coeFn_injective : @Function.Injective (HomotopyWith f₀ f₁ P) (I × X → Y) (⇑) :=
  FunLike.coe_injective'
#align continuous_map.homotopy_with.coe_fn_injective ContinuousMap.HomotopyWith.coeFn_injective

@[ext]
theorem ext {F G : HomotopyWith f₀ f₁ P} (h : ∀ x, F x = G x) : F = G := FunLike.ext F G h
#align continuous_map.homotopy_with.ext ContinuousMap.HomotopyWith.ext

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def Simps.apply (F : HomotopyWith f₀ f₁ P) : I × X → Y := F
#align continuous_map.homotopy_with.simps.apply ContinuousMap.HomotopyWith.Simps.apply

initialize_simps_projections HomotopyWith (toHomotopy_toContinuousMap_toFun → apply,
  -toHomotopy_toContinuousMap)

@[continuity]
protected theorem continuous (F : HomotopyWith f₀ f₁ P) : Continuous F :=
  F.continuous_toFun
#align continuous_map.homotopy_with.continuous ContinuousMap.HomotopyWith.continuous

@[simp]
theorem apply_zero (F : HomotopyWith f₀ f₁ P) (x : X) : F (0, x) = f₀ x :=
  F.map_zero_left x
#align continuous_map.homotopy_with.apply_zero ContinuousMap.HomotopyWith.apply_zero

@[simp]
theorem apply_one (F : HomotopyWith f₀ f₁ P) (x : X) : F (1, x) = f₁ x :=
  F.map_one_left x
#align continuous_map.homotopy_with.apply_one ContinuousMap.HomotopyWith.apply_one

-- porting note: removed `simp`
theorem coe_toContinuousMap (F : HomotopyWith f₀ f₁ P) : ⇑F.toContinuousMap = F :=
  rfl
#align continuous_map.homotopy_with.coe_to_continuous_map ContinuousMap.HomotopyWith.coe_toContinuousMap

@[simp]
theorem coe_toHomotopy (F : HomotopyWith f₀ f₁ P) : ⇑F.toHomotopy = F :=
  rfl
#align continuous_map.homotopy_with.coe_to_homotopy ContinuousMap.HomotopyWith.coe_toHomotopy

theorem prop (F : HomotopyWith f₀ f₁ P) (t : I) : P (F.toHomotopy.curry t) := F.prop' t
#align continuous_map.homotopy_with.prop ContinuousMap.HomotopyWith.prop

theorem extendProp (F : HomotopyWith f₀ f₁ P) (t : ℝ) : P (F.toHomotopy.extend t) := F.prop _
#align continuous_map.homotopy_with.extend_prop ContinuousMap.HomotopyWith.extendProp

end

variable {P : C(X, Y) → Prop}

/-- Given a continuous function `f`, and a proof `h : P f`, we can define a `HomotopyWith f f P` by
`F (t, x) = f x`
-/
@[simps!]
def refl (f : C(X, Y)) (hf : P f) : HomotopyWith f f P where
  toHomotopy := Homotopy.refl f
  prop' := fun _ => hf
#align continuous_map.homotopy_with.refl ContinuousMap.HomotopyWith.refl

instance : Inhabited (HomotopyWith (ContinuousMap.id X) (ContinuousMap.id X) fun _ => True) :=
  ⟨HomotopyWith.refl _ trivial⟩

/--
Given a `HomotopyWith f₀ f₁ P`, we can define a `HomotopyWith f₁ f₀ P` by reversing the homotopy.
-/
@[simps!]
def symm {f₀ f₁ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) : HomotopyWith f₁ f₀ P where
  toHomotopy := F.toHomotopy.symm
  prop' := fun t => F.prop (σ t)
#align continuous_map.homotopy_with.symm ContinuousMap.HomotopyWith.symm

@[simp]
theorem symm_symm {f₀ f₁ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) : F.symm.symm = F :=
  ext <| Homotopy.congr_fun <| Homotopy.symm_symm _
#align continuous_map.homotopy_with.symm_symm ContinuousMap.HomotopyWith.symm_symm

/--
Given `HomotopyWith f₀ f₁ P` and `HomotopyWith f₁ f₂ P`, we can define a `HomotopyWith f₀ f₂ P`
by putting the first homotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans {f₀ f₁ f₂ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) (G : HomotopyWith f₁ f₂ P) :
    HomotopyWith f₀ f₂ P :=
  { F.toHomotopy.trans G.toHomotopy with
    prop' := fun t => by
      simp only [Homotopy.trans]
      -- ⊢ P (ContinuousMap.mk fun x => if ↑t ≤ 1 / 2 then ↑(↑(Homotopy.extend F.toHomo …
      change P ⟨fun _ => ite ((t : ℝ) ≤ _) _ _, _⟩
      -- ⊢ P (ContinuousMap.mk fun x => if ↑t ≤ 1 / 2 then ↑(↑(Homotopy.extend F.toHomo …
      split_ifs
      -- ⊢ P (ContinuousMap.mk fun x => ↑(↑(Homotopy.extend F.toHomotopy) (2 * ↑t)) x)
      · exact F.extendProp _
        -- 🎉 no goals
      · exact G.extendProp _ }
        -- 🎉 no goals
#align continuous_map.homotopy_with.trans ContinuousMap.HomotopyWith.trans

theorem trans_apply {f₀ f₁ f₂ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) (G : HomotopyWith f₁ f₂ P)
    (x : I × X) :
    (F.trans G) x =
      if h : (x.1 : ℝ) ≤ 1 / 2 then
        F (⟨2 * x.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
      else
        G (⟨2 * x.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
  Homotopy.trans_apply _ _ _
#align continuous_map.homotopy_with.trans_apply ContinuousMap.HomotopyWith.trans_apply

theorem symm_trans {f₀ f₁ f₂ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) (G : HomotopyWith f₁ f₂ P) :
    (F.trans G).symm = G.symm.trans F.symm :=
  ext <| Homotopy.congr_fun <| Homotopy.symm_trans _ _
#align continuous_map.homotopy_with.symm_trans ContinuousMap.HomotopyWith.symm_trans

/-- Casting a `HomotopyWith f₀ f₁ P` to a `HomotopyWith g₀ g₁ P` where `f₀ = g₀` and `f₁ = g₁`.
-/
@[simps!]
def cast {f₀ f₁ g₀ g₁ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) :
    HomotopyWith g₀ g₁ P where
  toHomotopy := F.toHomotopy.cast h₀ h₁
  prop' := F.prop
#align continuous_map.homotopy_with.cast ContinuousMap.HomotopyWith.cast

end HomotopyWith

/-- Given continuous maps `f₀` and `f₁`, we say `f₀` and `f₁` are homotopic with respect to the
predicate `P` if there exists a `HomotopyWith f₀ f₁ P`.
-/
def HomotopicWith (f₀ f₁ : C(X, Y)) (P : C(X, Y) → Prop) : Prop :=
  Nonempty (HomotopyWith f₀ f₁ P)
#align continuous_map.homotopic_with ContinuousMap.HomotopicWith

namespace HomotopicWith

variable {P : C(X, Y) → Prop}

-- porting note: removed @[refl]
theorem refl (f : C(X, Y)) (hf : P f) : HomotopicWith f f P :=
  ⟨HomotopyWith.refl f hf⟩
#align continuous_map.homotopic_with.refl ContinuousMap.HomotopicWith.refl

@[symm]
theorem symm ⦃f g : C(X, Y)⦄ (h : HomotopicWith f g P) : HomotopicWith g f P :=
  ⟨h.some.symm⟩
#align continuous_map.homotopic_with.symm ContinuousMap.HomotopicWith.symm

@[trans]
theorem trans ⦃f g h : C(X, Y)⦄ (h₀ : HomotopicWith f g P) (h₁ : HomotopicWith g h P) :
    HomotopicWith f h P :=
  ⟨h₀.some.trans h₁.some⟩
#align continuous_map.homotopic_with.trans ContinuousMap.HomotopicWith.trans

end HomotopicWith

/--
A `HomotopyRel f₀ f₁ S` is a homotopy between `f₀` and `f₁` which is fixed on the points in `S`.
-/
abbrev HomotopyRel (f₀ f₁ : C(X, Y)) (S : Set X) :=
  HomotopyWith f₀ f₁ fun f => ∀ x ∈ S, f x = f₀ x ∧ f x = f₁ x
#align continuous_map.homotopy_rel ContinuousMap.HomotopyRel

namespace HomotopyRel

section

variable {f₀ f₁ : C(X, Y)} {S : Set X}

theorem eq_fst (F : HomotopyRel f₀ f₁ S) (t : I) {x : X} (hx : x ∈ S) : F (t, x) = f₀ x :=
  (F.prop t x hx).1
#align continuous_map.homotopy_rel.eq_fst ContinuousMap.HomotopyRel.eq_fst

theorem eq_snd (F : HomotopyRel f₀ f₁ S) (t : I) {x : X} (hx : x ∈ S) : F (t, x) = f₁ x :=
  (F.prop t x hx).2
#align continuous_map.homotopy_rel.eq_snd ContinuousMap.HomotopyRel.eq_snd

theorem fst_eq_snd (F : HomotopyRel f₀ f₁ S) {x : X} (hx : x ∈ S) : f₀ x = f₁ x :=
  F.eq_fst 0 hx ▸ F.eq_snd 0 hx
#align continuous_map.homotopy_rel.fst_eq_snd ContinuousMap.HomotopyRel.fst_eq_snd

end

variable {f₀ f₁ f₂ : C(X, Y)} {S : Set X}

/-- Given a map `f : C(X, Y)` and a set `S`, we can define a `HomotopyRel f f S` by setting
`F (t, x) = f x` for all `t`. This is defined using `HomotopyWith.refl`, but with the proof
filled in.
-/
@[simps!]
def refl (f : C(X, Y)) (S : Set X) : HomotopyRel f f S :=
  HomotopyWith.refl f fun _ _ => ⟨rfl, rfl⟩
#align continuous_map.homotopy_rel.refl ContinuousMap.HomotopyRel.refl

/--
Given a `HomotopyRel f₀ f₁ S`, we can define a `HomotopyRel f₁ f₀ S` by reversing the homotopy.
-/
@[simps!]
def symm (F : HomotopyRel f₀ f₁ S) : HomotopyRel f₁ f₀ S where
  toHomotopy := F.toHomotopy.symm
  prop' := fun _ _ hx => ⟨F.eq_snd _ hx, F.eq_fst _ hx⟩
#align continuous_map.homotopy_rel.symm ContinuousMap.HomotopyRel.symm

@[simp]
theorem symm_symm (F : HomotopyRel f₀ f₁ S) : F.symm.symm = F :=
  HomotopyWith.symm_symm F
#align continuous_map.homotopy_rel.symm_symm ContinuousMap.HomotopyRel.symm_symm

/-- Given `HomotopyRel f₀ f₁ S` and `HomotopyRel f₁ f₂ S`, we can define a `HomotopyRel f₀ f₂ S`
by putting the first homotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans (F : HomotopyRel f₀ f₁ S) (G : HomotopyRel f₁ f₂ S) : HomotopyRel f₀ f₂ S :=
  { Homotopy.trans F.toHomotopy G.toHomotopy with
    prop' := fun t x hx => by
      simp only [Homotopy.trans]
      -- ⊢ ↑(mk fun x => if ↑t ≤ 1 / 2 then ↑(↑(Homotopy.extend F.toHomotopy) (2 * ↑t)) …
      change (⟨fun _ => ite ((t : ℝ) ≤ _) _ _, _⟩ : C(X, Y)) _ = _ ∧ _ = _
      -- ⊢ ↑(mk fun x => if ↑t ≤ 1 / 2 then ↑(↑(Homotopy.extend F.toHomotopy) (2 * ↑t)) …
      split_ifs
      -- ⊢ ↑(mk fun x => ↑(↑(Homotopy.extend F.toHomotopy) (2 * ↑t)) x) x = ↑f₀ x ∧ ↑(m …
      · simp [(HomotopyWith.extendProp F (2 * t) x hx).1, F.fst_eq_snd hx, G.fst_eq_snd hx]
        -- 🎉 no goals
      · simp [(HomotopyWith.extendProp G (2 * t - 1) x hx).1, F.fst_eq_snd hx, G.fst_eq_snd hx] }
        -- 🎉 no goals
#align continuous_map.homotopy_rel.trans ContinuousMap.HomotopyRel.trans

theorem trans_apply (F : HomotopyRel f₀ f₁ S) (G : HomotopyRel f₁ f₂ S) (x : I × X) :
    (F.trans G) x =
      if h : (x.1 : ℝ) ≤ 1 / 2 then
        F (⟨2 * x.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
      else
        G (⟨2 * x.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
  Homotopy.trans_apply _ _ _
#align continuous_map.homotopy_rel.trans_apply ContinuousMap.HomotopyRel.trans_apply

theorem symm_trans (F : HomotopyRel f₀ f₁ S) (G : HomotopyRel f₁ f₂ S) :
    (F.trans G).symm = G.symm.trans F.symm :=
  HomotopyWith.ext <| Homotopy.congr_fun <| Homotopy.symm_trans _ _
#align continuous_map.homotopy_rel.symm_trans ContinuousMap.HomotopyRel.symm_trans

/-- Casting a `HomotopyRel f₀ f₁ S` to a `HomotopyRel g₀ g₁ S` where `f₀ = g₀` and `f₁ = g₁`.
-/
@[simps!]
def cast {f₀ f₁ g₀ g₁ : C(X, Y)} (F : HomotopyRel f₀ f₁ S) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) :
    HomotopyRel g₀ g₁ S where
  toHomotopy := Homotopy.cast F.toHomotopy h₀ h₁
  prop' t x hx := by simpa only [← h₀, ← h₁] using F.prop t x hx
                     -- 🎉 no goals
#align continuous_map.homotopy_rel.cast ContinuousMap.HomotopyRel.cast

end HomotopyRel

/-- Given continuous maps `f₀` and `f₁`, we say `f₀` and `f₁` are homotopic relative to a set `S` if
there exists a `HomotopyRel f₀ f₁ S`.
-/
def HomotopicRel (f₀ f₁ : C(X, Y)) (S : Set X) : Prop :=
  Nonempty (HomotopyRel f₀ f₁ S)
#align continuous_map.homotopic_rel ContinuousMap.HomotopicRel

namespace HomotopicRel

variable {S : Set X}

/-- If two maps are homotopic relative to a set, then they are homotopic. -/
protected theorem homotopic {f₀ f₁ : C(X, Y)} (h : HomotopicRel f₀ f₁ S) : Homotopic f₀ f₁ :=
  h.map fun F ↦ F.1

-- porting note: removed @[refl]
theorem refl (f : C(X, Y)) : HomotopicRel f f S :=
  ⟨HomotopyRel.refl f S⟩
#align continuous_map.homotopic_rel.refl ContinuousMap.HomotopicRel.refl

@[symm]
theorem symm ⦃f g : C(X, Y)⦄ (h : HomotopicRel f g S) : HomotopicRel g f S :=
  h.map HomotopyRel.symm
#align continuous_map.homotopic_rel.symm ContinuousMap.HomotopicRel.symm

@[trans]
theorem trans ⦃f g h : C(X, Y)⦄ (h₀ : HomotopicRel f g S) (h₁ : HomotopicRel g h S) :
    HomotopicRel f h S :=
  h₀.map2 HomotopyRel.trans h₁
#align continuous_map.homotopic_rel.trans ContinuousMap.HomotopicRel.trans

theorem equivalence : Equivalence fun f g : C(X, Y) => HomotopicRel f g S :=
  ⟨refl, by apply symm, by apply trans⟩
            -- 🎉 no goals
                           -- 🎉 no goals
#align continuous_map.homotopic_rel.equivalence ContinuousMap.HomotopicRel.equivalence

end HomotopicRel

@[simp] theorem homotopicRel_empty {f₀ f₁ : C(X, Y)} : HomotopicRel f₀ f₁ ∅ ↔ Homotopic f₀ f₁ :=
  ⟨fun h ↦ h.homotopic, fun ⟨F⟩ ↦ ⟨⟨F, fun _ _ ↦ False.elim⟩⟩⟩

end ContinuousMap
