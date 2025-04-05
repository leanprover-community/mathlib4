/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.Data.Nat.Log
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.UnitInterval

/-!
# Paths in topological spaces

This file introduces continuous paths and provides API for them.

## Main definitions

In this file the unit interval `[0, 1]` in `ℝ` is denoted by `I`, and `X` is a topological space.

* `Path x y` is the type of paths from `x` to `y`, i.e., continuous maps from `I` to `X`
  mapping `0` to `x` and `1` to `y`.
* `Path.refl x : Path x x` is the constant path at `x`.
* `Path.symm γ : Path y x` is the reverse of a path `γ : Path x y`.
* `Path.trans γ γ' : Path x z` is the concatenation of two paths `γ : Path x y`, `γ' : Path y z`.
* `Path.map γ hf : Path (f x) (f y)` is the image of `γ : Path x y` under a continuous map `f`.
* `Path.reparam γ f hf hf₀ hf₁ : Path x y` is the reparametrisation of `γ : Path x y` by
  a continuous map `f : I → I` fixing `0` and `1`.
* `Path.truncate γ t₀ t₁ : Path (γ t₀) (γ t₁)` is the path that follows `γ` from `t₀` to `t₁` and
  stays constant otherwise.
* `Path.extend γ : ℝ → X` is the extension `γ` to `ℝ` that is constant before `0` and after `1`.
* `Path.countableConcat γ x hb hγ` is the concatenation of countably many paths `γ n` leading up to
  some point `x`, given an antitone neighbourhood basis `b : ℕ → Set X` at `x` such that `γ n` lies
  in `b n` for all `n`.

`Path x y` is equipped with the topology induced by the compact-open topology on `C(I,X)`, and
several of the above constructions are shown to be continuous.

## Implementation notes

By default, all paths have `I` as their source and `X` as their target, but there is an
operation `Set.IccExtend` that will extend any continuous map `γ : I → X` into a continuous map
`IccExtend zero_le_one γ : ℝ → X` that is constant before `0` and after `1`.

This is used to define `Path.extend` that turns `γ : Path x y` into a continuous map
`γ.extend : ℝ → X` whose restriction to `I` is the original `γ`, and is equal to `x`
on `(-∞, 0]` and to `y` on `[1, +∞)`.
-/

noncomputable section

open Topology Filter unitInterval Set Function

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x y z : X} {ι : Type*}

/-! ### Paths -/

/-- Continuous path connecting two points `x` and `y` in a topological space -/
structure Path (x y : X) extends C(I, X) where
  /-- The start point of a `Path`. -/
  source' : toFun 0 = x
  /-- The end point of a `Path`. -/
  target' : toFun 1 = y

instance Path.funLike : FunLike (Path x y) I X where
  coe γ := ⇑γ.toContinuousMap
  coe_injective' γ₁ γ₂ h := by
    simp only [DFunLike.coe_fn_eq] at h
    cases γ₁; cases γ₂; congr

instance Path.continuousMapClass : ContinuousMapClass (Path x y) I X where
  map_continuous γ := show Continuous γ.toContinuousMap by fun_prop

@[ext]
protected theorem Path.ext : ∀ {γ₁ γ₂ : Path x y}, (γ₁ : I → X) = γ₂ → γ₁ = γ₂ := by
  rintro ⟨⟨x, h11⟩, h12, h13⟩ ⟨⟨x, h21⟩, h22, h23⟩ rfl
  rfl

namespace Path

@[simp]
theorem coe_mk_mk (f : I → X) (h₁) (h₂ : f 0 = x) (h₃ : f 1 = y) :
    ⇑(mk ⟨f, h₁⟩ h₂ h₃ : Path x y) = f :=
  rfl

variable (γ : Path x y)

@[continuity]
protected theorem continuous : Continuous γ :=
  γ.continuous_toFun

@[simp]
protected theorem source : γ 0 = x :=
  γ.source'

@[simp]
protected theorem target : γ 1 = y :=
  γ.target'

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def simps.apply : I → X :=
  γ

initialize_simps_projections Path (toFun → simps.apply, -toContinuousMap)

@[simp]
theorem coe_toContinuousMap : ⇑γ.toContinuousMap = γ :=
  rfl

@[simp]
theorem coe_mk : ⇑(γ : C(I, X)) = γ :=
  rfl

/-- Any function `φ : Π (a : α), Path (x a) (y a)` can be seen as a function `α × I → X`. -/
instance hasUncurryPath {X α : Type*} [TopologicalSpace X] {x y : α → X} :
    HasUncurry (∀ a : α, Path (x a) (y a)) (α × I) X :=
  ⟨fun φ p => φ p.1 p.2⟩

/-- The constant path from a point to itself -/
@[refl, simps]
def refl (x : X) : Path x x where
  toFun _t := x
  continuous_toFun := continuous_const
  source' := rfl
  target' := rfl

@[simp]
theorem refl_range {a : X} : range (Path.refl a) = {a} := by simp [Path.refl, CoeFun.coe]

/-- The reverse of a path from `x` to `y`, as a path from `y` to `x` -/
@[symm, simps]
def symm (γ : Path x y) : Path y x where
  toFun := γ ∘ σ
  continuous_toFun := by continuity
  source' := by simpa [-Path.target] using γ.target
  target' := by simpa [-Path.source] using γ.source

@[simp]
theorem symm_symm (γ : Path x y) : γ.symm.symm = γ := by
  ext t
  show γ (σ (σ t)) = γ t
  rw [unitInterval.symm_symm]

theorem symm_bijective : Function.Bijective (Path.symm : Path x y → Path y x) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
theorem refl_symm {a : X} : (Path.refl a).symm = Path.refl a := by
  ext
  rfl

@[simp]
theorem symm_range {a b : X} (γ : Path a b) : range γ.symm = range γ := by
  ext x
  simp only [mem_range, Path.symm, DFunLike.coe, unitInterval.symm, SetCoe.exists, comp_apply,
    Subtype.coe_mk]
  constructor <;> rintro ⟨y, hy, hxy⟩ <;> refine ⟨1 - y, mem_iff_one_sub_mem.mp hy, ?_⟩ <;>
    convert hxy
  simp

/-! #### Space of paths -/


open ContinuousMap

/-- The following instance defines the topology on the path space to be induced from the
compact-open topology on the space `C(I,X)` of continuous maps from `I` to `X`.
-/
instance topologicalSpace : TopologicalSpace (Path x y) :=
  TopologicalSpace.induced ((↑) : _ → C(I, X)) ContinuousMap.compactOpen

instance : ContinuousEval (Path x y) I X := .of_continuous_forget continuous_induced_dom

@[deprecated (since := "2024-10-04")] protected alias continuous_eval := continuous_eval

@[deprecated Continuous.eval (since := "2024-10-04")]
theorem _root_.Continuous.path_eval {Y} [TopologicalSpace Y] {f : Y → Path x y} {g : Y → I}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun y => f y (g y) := by
  fun_prop

theorem continuous_uncurry_iff {Y} [TopologicalSpace Y] {g : Y → Path x y} :
    Continuous ↿g ↔ Continuous g :=
  Iff.symm <| continuous_induced_rng.trans
    ⟨fun h => continuous_uncurry_of_continuous ⟨_, h⟩,
    continuous_of_continuous_uncurry (fun (y : Y) ↦ ContinuousMap.mk (g y))⟩

/-- A continuous map extending a path to `ℝ`, constant before `0` and after `1`. -/
def extend : ℝ → X :=
  IccExtend zero_le_one γ

/-- See Note [continuity lemma statement]. -/
theorem _root_.Continuous.path_extend {γ : Y → Path x y} {f : Y → ℝ} (hγ : Continuous ↿γ)
    (hf : Continuous f) : Continuous fun t => (γ t).extend (f t) :=
  Continuous.IccExtend hγ hf

/-- A useful special case of `Continuous.path_extend`. -/
@[continuity, fun_prop]
theorem continuous_extend : Continuous γ.extend :=
  γ.continuous.Icc_extend'

theorem _root_.Filter.Tendsto.path_extend
    {l r : Y → X} {y : Y} {l₁ : Filter ℝ} {l₂ : Filter X} {γ : ∀ y, Path (l y) (r y)}
    (hγ : Tendsto (↿γ) (𝓝 y ×ˢ l₁.map (projIcc 0 1 zero_le_one)) l₂) :
    Tendsto (↿fun x => (γ x).extend) (𝓝 y ×ˢ l₁) l₂ :=
  Filter.Tendsto.IccExtend _ hγ

theorem _root_.ContinuousAt.path_extend {g : Y → ℝ} {l r : Y → X} (γ : ∀ y, Path (l y) (r y))
    {y : Y} (hγ : ContinuousAt (↿γ) (y, projIcc 0 1 zero_le_one (g y))) (hg : ContinuousAt g y) :
    ContinuousAt (fun i => (γ i).extend (g i)) y :=
  hγ.IccExtend (fun x => γ x) hg

@[simp]
theorem extend_extends {a b : X} (γ : Path a b) {t : ℝ}
    (ht : t ∈ (Icc 0 1 : Set ℝ)) : γ.extend t = γ ⟨t, ht⟩ :=
  IccExtend_of_mem _ γ ht

theorem extend_zero : γ.extend 0 = x := by simp

theorem extend_one : γ.extend 1 = y := by simp

theorem extend_extends' {a b : X} (γ : Path a b) (t : (Icc 0 1 : Set ℝ)) : γ.extend t = γ t :=
  IccExtend_val _ γ t

@[simp]
theorem extend_range {a b : X} (γ : Path a b) :
    range γ.extend = range γ :=
  IccExtend_range _ γ

theorem extend_of_le_zero {a b : X} (γ : Path a b) {t : ℝ}
    (ht : t ≤ 0) : γ.extend t = a :=
  (IccExtend_of_le_left _ _ ht).trans γ.source

theorem extend_of_one_le {a b : X} (γ : Path a b) {t : ℝ}
    (ht : 1 ≤ t) : γ.extend t = b :=
  (IccExtend_of_right_le _ _ ht).trans γ.target

@[simp]
theorem refl_extend {a : X} : (Path.refl a).extend = fun _ => a :=
  rfl

/-- The path obtained from a map defined on `ℝ` by restriction to the unit interval. -/
def ofLine {f : ℝ → X} (hf : ContinuousOn f I) (h₀ : f 0 = x) (h₁ : f 1 = y) : Path x y where
  toFun := f ∘ ((↑) : unitInterval → ℝ)
  continuous_toFun := hf.comp_continuous continuous_subtype_val Subtype.prop
  source' := h₀
  target' := h₁

theorem ofLine_mem {f : ℝ → X} (hf : ContinuousOn f I) (h₀ : f 0 = x) (h₁ : f 1 = y) :
    ∀ t, ofLine hf h₀ h₁ t ∈ f '' I := fun ⟨t, t_in⟩ => ⟨t, t_in, rfl⟩

attribute [local simp] Iic_def

/-- Concatenation of two paths from `x` to `y` and from `y` to `z`, putting the first
path on `[0, 1/2]` and the second one on `[1/2, 1]`. -/
@[trans]
def trans (γ : Path x y) (γ' : Path y z) : Path x z where
  toFun := (fun t : ℝ => if t ≤ 1 / 2 then γ.extend (2 * t) else γ'.extend (2 * t - 1)) ∘ (↑)
  continuous_toFun := by
    refine
      (Continuous.if_le ?_ ?_ continuous_id continuous_const (by norm_num)).comp
        continuous_subtype_val <;>
    fun_prop
  source' := by norm_num
  target' := by norm_num

theorem trans_apply (γ : Path x y) (γ' : Path y z) (t : I) :
    (γ.trans γ') t =
      if h : (t : ℝ) ≤ 1 / 2 then γ ⟨2 * t, (mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩⟩
      else γ' ⟨2 * t - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t.2.2⟩⟩ :=
  show ite _ _ _ = _ by split_ifs <;> rw [extend_extends]

@[simp]
theorem trans_symm (γ : Path x y) (γ' : Path y z) : (γ.trans γ').symm = γ'.symm.trans γ.symm := by
  ext t
  simp only [trans_apply, ← one_div, symm_apply, not_le, Function.comp_apply]
  split_ifs with h h₁ h₂ <;> rw [coe_symm_eq] at h
  · have ht : (t : ℝ) = 1 / 2 := by linarith
    norm_num [ht]
  · refine congr_arg _ (Subtype.ext ?_)
    norm_num [sub_sub_eq_add_sub, mul_sub]
  · refine congr_arg _ (Subtype.ext ?_)
    norm_num [mul_sub, h]
    ring -- TODO norm_num should really do this
  · exfalso
    linarith

@[simp]
theorem refl_trans_refl {a : X} :
    (Path.refl a).trans (Path.refl a) = Path.refl a := by
  ext
  simp only [Path.trans, ite_self, one_div, Path.refl_extend]
  rfl

theorem trans_range {a b c : X} (γ₁ : Path a b) (γ₂ : Path b c) :
    range (γ₁.trans γ₂) = range γ₁ ∪ range γ₂ := by
  rw [Path.trans]
  apply eq_of_subset_of_subset
  · rintro x ⟨⟨t, ht0, ht1⟩, hxt⟩
    by_cases h : t ≤ 1 / 2
    · left
      use ⟨2 * t, ⟨by linarith, by linarith⟩⟩
      rw [← γ₁.extend_extends]
      rwa [coe_mk_mk, Function.comp_apply, if_pos h] at hxt
    · right
      use ⟨2 * t - 1, ⟨by linarith, by linarith⟩⟩
      rw [← γ₂.extend_extends]
      rwa [coe_mk_mk, Function.comp_apply, if_neg h] at hxt
  · rintro x (⟨⟨t, ht0, ht1⟩, hxt⟩ | ⟨⟨t, ht0, ht1⟩, hxt⟩)
    · use ⟨t / 2, ⟨by linarith, by linarith⟩⟩
      have : t / 2 ≤ 1 / 2 := (div_le_div_iff_of_pos_right (zero_lt_two : (0 : ℝ) < 2)).mpr ht1
      rw [coe_mk_mk, Function.comp_apply, if_pos this, Subtype.coe_mk]
      ring_nf
      rwa [γ₁.extend_extends]
    · by_cases h : t = 0
      · use ⟨1 / 2, ⟨by linarith, by linarith⟩⟩
        rw [coe_mk_mk, Function.comp_apply, if_pos le_rfl, Subtype.coe_mk,
          mul_one_div_cancel (two_ne_zero' ℝ)]
        rw [γ₁.extend_one]
        rwa [← γ₂.extend_extends, h, γ₂.extend_zero] at hxt
      · use ⟨(t + 1) / 2, ⟨by linarith, by linarith⟩⟩
        replace h : t ≠ 0 := h
        have ht0 := lt_of_le_of_ne ht0 h.symm
        have : ¬(t + 1) / 2 ≤ 1 / 2 := by
          rw [not_le]
          linarith
        rw [coe_mk_mk, Function.comp_apply, Subtype.coe_mk, if_neg this]
        ring_nf
        rwa [γ₂.extend_extends]

/-- Image of a path from `x` to `y` by a map which is continuous on the path. -/
def map' (γ : Path x y) {f : X → Y} (h : ContinuousOn f (range γ)) : Path (f x) (f y) where
  toFun := f ∘ γ
  continuous_toFun := h.comp_continuous γ.continuous (fun x ↦ mem_range_self x)
  source' := by simp
  target' := by simp

/-- Image of a path from `x` to `y` by a continuous map -/
def map (γ : Path x y) {f : X → Y} (h : Continuous f) :
    Path (f x) (f y) := γ.map' h.continuousOn

@[simp]
theorem map_coe (γ : Path x y) {f : X → Y} (h : Continuous f) :
    (γ.map h : I → Y) = f ∘ γ := by
  ext t
  rfl

@[simp]
theorem map_symm (γ : Path x y) {f : X → Y} (h : Continuous f) :
    (γ.map h).symm = γ.symm.map h :=
  rfl

@[simp]
theorem map_trans (γ : Path x y) (γ' : Path y z) {f : X → Y}
    (h : Continuous f) : (γ.trans γ').map h = (γ.map h).trans (γ'.map h) := by
  ext t
  rw [trans_apply, map_coe, Function.comp_apply, trans_apply]
  split_ifs <;> rfl

@[simp]
theorem map_id (γ : Path x y) : γ.map continuous_id = γ := by
  ext
  rfl

@[simp]
theorem map_map (γ : Path x y) {Z : Type*} [TopologicalSpace Z]
    {f : X → Y} (hf : Continuous f) {g : Y → Z} (hg : Continuous g) :
    (γ.map hf).map hg = γ.map (hg.comp hf) := by
  ext
  rfl

/-- Casting a path from `x` to `y` to a path from `x'` to `y'` when `x' = x` and `y' = y` -/
def cast (γ : Path x y) {x' y'} (hx : x' = x) (hy : y' = y) : Path x' y' where
  toFun := γ
  continuous_toFun := γ.continuous
  source' := by simp [hx]
  target' := by simp [hy]

@[simp]
theorem symm_cast {a₁ a₂ b₁ b₂ : X} (γ : Path a₂ b₂) (ha : a₁ = a₂) (hb : b₁ = b₂) :
    (γ.cast ha hb).symm = γ.symm.cast hb ha :=
  rfl

@[simp]
theorem trans_cast {a₁ a₂ b₁ b₂ c₁ c₂ : X} (γ : Path a₂ b₂)
    (γ' : Path b₂ c₂) (ha : a₁ = a₂) (hb : b₁ = b₂) (hc : c₁ = c₂) :
    (γ.cast ha hb).trans (γ'.cast hb hc) = (γ.trans γ').cast ha hc :=
  rfl

@[simp]
theorem cast_coe (γ : Path x y) {x' y'} (hx : x' = x) (hy : y' = y) : (γ.cast hx hy : I → X) = γ :=
  rfl

@[continuity, fun_prop]
theorem symm_continuous_family {ι : Type*} [TopologicalSpace ι]
    {a b : ι → X} (γ : ∀ t : ι, Path (a t) (b t)) (h : Continuous ↿γ) :
    Continuous ↿fun t => (γ t).symm :=
  h.comp (continuous_id.prodMap continuous_symm)

@[continuity]
theorem continuous_symm : Continuous (symm : Path x y → Path y x) :=
  continuous_uncurry_iff.mp <| symm_continuous_family _ (by fun_prop)

@[continuity]
theorem continuous_uncurry_extend_of_continuous_family {ι : Type*} [TopologicalSpace ι]
    {a b : ι → X} (γ : ∀ t : ι, Path (a t) (b t)) (h : Continuous ↿γ) :
    Continuous ↿fun t => (γ t).extend := by
  apply h.comp (continuous_id.prodMap continuous_projIcc)
  exact zero_le_one

@[continuity]
theorem trans_continuous_family {ι : Type*} [TopologicalSpace ι]
    {a b c : ι → X} (γ₁ : ∀ t : ι, Path (a t) (b t)) (h₁ : Continuous ↿γ₁)
    (γ₂ : ∀ t : ι, Path (b t) (c t)) (h₂ : Continuous ↿γ₂) :
    Continuous ↿fun t => (γ₁ t).trans (γ₂ t) := by
  have h₁' := Path.continuous_uncurry_extend_of_continuous_family γ₁ h₁
  have h₂' := Path.continuous_uncurry_extend_of_continuous_family γ₂ h₂
  simp only [HasUncurry.uncurry, CoeFun.coe, Path.trans, (· ∘ ·)]
  refine Continuous.if_le ?_ ?_ (continuous_subtype_val.comp continuous_snd) continuous_const ?_
  · change
      Continuous ((fun p : ι × ℝ => (γ₁ p.1).extend p.2) ∘ Prod.map id (fun x => 2 * x : I → ℝ))
    exact h₁'.comp (continuous_id.prodMap <| continuous_const.mul continuous_subtype_val)
  · change
      Continuous ((fun p : ι × ℝ => (γ₂ p.1).extend p.2) ∘ Prod.map id (fun x => 2 * x - 1 : I → ℝ))
    exact
      h₂'.comp
        (continuous_id.prodMap <|
          (continuous_const.mul continuous_subtype_val).sub continuous_const)
  · rintro st hst
    simp [hst, mul_inv_cancel₀ (two_ne_zero' ℝ)]

@[continuity, fun_prop]
theorem _root_.Continuous.path_trans {f : Y → Path x y} {g : Y → Path y z} :
    Continuous f → Continuous g → Continuous fun t => (f t).trans (g t) := by
  intro hf hg
  apply continuous_uncurry_iff.mp
  exact trans_continuous_family _ (continuous_uncurry_iff.mpr hf) _ (continuous_uncurry_iff.mpr hg)

@[continuity, fun_prop]
theorem continuous_trans {x y z : X} : Continuous fun ρ : Path x y × Path y z => ρ.1.trans ρ.2 := by
  fun_prop


/-! #### Product of paths -/
section Prod

variable {a₁ a₂ a₃ : X} {b₁ b₂ b₃ : Y}

/-- Given a path in `X` and a path in `Y`, we can take their pointwise product to get a path in
`X × Y`. -/
protected def prod (γ₁ : Path a₁ a₂) (γ₂ : Path b₁ b₂) : Path (a₁, b₁) (a₂, b₂) where
  toContinuousMap := ContinuousMap.prodMk γ₁.toContinuousMap γ₂.toContinuousMap
  source' := by simp
  target' := by simp

@[simp]
theorem prod_coe (γ₁ : Path a₁ a₂) (γ₂ : Path b₁ b₂) :
    ⇑(γ₁.prod γ₂) = fun t => (γ₁ t, γ₂ t) :=
  rfl

/-- Path composition commutes with products -/
theorem trans_prod_eq_prod_trans (γ₁ : Path a₁ a₂) (δ₁ : Path a₂ a₃) (γ₂ : Path b₁ b₂)
    (δ₂ : Path b₂ b₃) : (γ₁.prod γ₂).trans (δ₁.prod δ₂) = (γ₁.trans δ₁).prod (γ₂.trans δ₂) := by
  ext t <;>
  unfold Path.trans <;>
  simp only [Path.coe_mk_mk, Path.prod_coe, Function.comp_apply] <;>
  split_ifs <;>
  rfl

end Prod

section Pi

variable {χ : ι → Type*} [∀ i, TopologicalSpace (χ i)] {as bs cs : ∀ i, χ i}

/-- Given a family of paths, one in each Xᵢ, we take their pointwise product to get a path in
Π i, Xᵢ. -/
protected def pi (γ : ∀ i, Path (as i) (bs i)) : Path as bs where
  toContinuousMap := ContinuousMap.pi fun i => (γ i).toContinuousMap
  source' := by simp
  target' := by simp

@[simp]
theorem pi_coe (γ : ∀ i, Path (as i) (bs i)) : ⇑(Path.pi γ) = fun t i => γ i t :=
  rfl

/-- Path composition commutes with products -/
theorem trans_pi_eq_pi_trans (γ₀ : ∀ i, Path (as i) (bs i)) (γ₁ : ∀ i, Path (bs i) (cs i)) :
    (Path.pi γ₀).trans (Path.pi γ₁) = Path.pi fun i => (γ₀ i).trans (γ₁ i) := by
  ext t i
  unfold Path.trans
  simp only [Path.coe_mk_mk, Function.comp_apply, pi_coe]
  split_ifs <;> rfl

end Pi

/-! #### Pointwise multiplication/addition of two paths in a topological (additive) group -/


/-- Pointwise multiplication of paths in a topological group. The additive version is probably more
useful. -/
@[to_additive "Pointwise addition of paths in a topological additive group."]
protected def mul [Mul X] [ContinuousMul X] {a₁ b₁ a₂ b₂ : X} (γ₁ : Path a₁ b₁) (γ₂ : Path a₂ b₂) :
    Path (a₁ * a₂) (b₁ * b₂) :=
  (γ₁.prod γ₂).map continuous_mul

@[to_additive]
protected theorem mul_apply [Mul X] [ContinuousMul X] {a₁ b₁ a₂ b₂ : X} (γ₁ : Path a₁ b₁)
    (γ₂ : Path a₂ b₂) (t : unitInterval) : (γ₁.mul γ₂) t = γ₁ t * γ₂ t :=
  rfl

/-! #### Truncating a path -/


/-- `γ.truncate t₀ t₁` is the path which follows the path `γ` on the time interval `[t₀, t₁]`
and stays still otherwise. -/
def truncate {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b) (t₀ t₁ : ℝ) :
    Path (γ.extend <| min t₀ t₁) (γ.extend t₁) where
  toFun s := γ.extend (min (max s t₀) t₁)
  continuous_toFun :=
    γ.continuous_extend.comp ((continuous_subtype_val.max continuous_const).min continuous_const)
  source' := by
    simp only [min_def, max_def']
    split_ifs with h₁ h₂ h₃ h₄
    · simp [γ.extend_of_le_zero h₁]
    · congr
      linarith
    · have h₄ : t₁ ≤ 0 := le_of_lt (by simpa using h₂)
      simp [γ.extend_of_le_zero h₄, γ.extend_of_le_zero h₁]
    all_goals rfl
  target' := by
    simp only [min_def, max_def']
    split_ifs with h₁ h₂ h₃
    · simp [γ.extend_of_one_le h₂]
    · rfl
    · have h₄ : 1 ≤ t₀ := le_of_lt (by simpa using h₁)
      simp [γ.extend_of_one_le h₄, γ.extend_of_one_le (h₄.trans h₃)]
    · rfl

/-- `γ.truncateOfLE t₀ t₁ h`, where `h : t₀ ≤ t₁` is `γ.truncate t₀ t₁`
casted as a path from `γ.extend t₀` to `γ.extend t₁`. -/
def truncateOfLE {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b) {t₀ t₁ : ℝ}
    (h : t₀ ≤ t₁) : Path (γ.extend t₀) (γ.extend t₁) :=
  (γ.truncate t₀ t₁).cast (by rw [min_eq_left h]) rfl

theorem truncate_range {a b : X} (γ : Path a b) {t₀ t₁ : ℝ} :
    range (γ.truncate t₀ t₁) ⊆ range γ := by
  rw [← γ.extend_range]
  simp only [range_subset_iff, SetCoe.exists, SetCoe.forall]
  intro x _hx
  simp only [DFunLike.coe, Path.truncate, mem_range_self]

/-- For a path `γ`, `γ.truncate` gives a "continuous family of paths", by which we mean
the uncurried function which maps `(t₀, t₁, s)` to `γ.truncate t₀ t₁ s` is continuous. -/
@[continuity]
theorem truncate_continuous_family {a b : X} (γ : Path a b) :
    Continuous (fun x => γ.truncate x.1 x.2.1 x.2.2 : ℝ × ℝ × I → X) :=
  γ.continuous_extend.comp
    (((continuous_subtype_val.comp (continuous_snd.comp continuous_snd)).max continuous_fst).min
      (continuous_fst.comp continuous_snd))

@[continuity]
theorem truncate_const_continuous_family {a b : X} (γ : Path a b)
    (t : ℝ) : Continuous ↿(γ.truncate t) := by
  have key : Continuous (fun x => (t, x) : ℝ × I → ℝ × ℝ × I) := by fun_prop
  exact γ.truncate_continuous_family.comp key

@[simp]
theorem truncate_self {a b : X} (γ : Path a b) (t : ℝ) :
    γ.truncate t t = (Path.refl <| γ.extend t).cast (by rw [min_self]) rfl := by
  ext x
  rw [cast_coe]
  simp only [truncate, DFunLike.coe, refl, min_def, max_def]
  split_ifs with h₁ h₂ <;> congr

theorem truncate_zero_zero {a b : X} (γ : Path a b) :
    γ.truncate 0 0 = (Path.refl a).cast (by rw [min_self, γ.extend_zero]) γ.extend_zero := by
  convert γ.truncate_self 0

theorem truncate_one_one {a b : X} (γ : Path a b) :
    γ.truncate 1 1 = (Path.refl b).cast (by rw [min_self, γ.extend_one]) γ.extend_one := by
  convert γ.truncate_self 1

@[simp]
theorem truncate_zero_one {a b : X} (γ : Path a b) :
    γ.truncate 0 1 = γ.cast (by simp [zero_le_one, extend_zero]) (by simp) := by
  ext x
  rw [cast_coe]
  have : ↑x ∈ (Icc 0 1 : Set ℝ) := x.2
  rw [truncate, coe_mk_mk, max_eq_left this.1, min_eq_left this.2, extend_extends']

/-! #### Reparametrising a path -/


/-- Given a path `γ` and a function `f : I → I` where `f 0 = 0` and `f 1 = 1`, `γ.reparam f` is the
path defined by `γ ∘ f`.
-/
def reparam (γ : Path x y) (f : I → I) (hfcont : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    Path x y where
  toFun := γ ∘ f
  continuous_toFun := by fun_prop
  source' := by simp [hf₀]
  target' := by simp [hf₁]

@[simp]
theorem coe_reparam (γ : Path x y) {f : I → I} (hfcont : Continuous f) (hf₀ : f 0 = 0)
    (hf₁ : f 1 = 1) : ⇑(γ.reparam f hfcont hf₀ hf₁) = γ ∘ f :=
  rfl

@[simp]
theorem reparam_id (γ : Path x y) : γ.reparam id continuous_id rfl rfl = γ := by
  ext
  rfl

theorem range_reparam (γ : Path x y) {f : I → I} (hfcont : Continuous f) (hf₀ : f 0 = 0)
    (hf₁ : f 1 = 1) : range (γ.reparam f hfcont hf₀ hf₁) = range γ := by
  change range (γ ∘ f) = range γ
  have : range f = univ := by
    rw [range_eq_univ]
    intro t
    have h₁ : Continuous (Set.IccExtend (zero_le_one' ℝ) f) := by continuity
    have := intermediate_value_Icc (zero_le_one' ℝ) h₁.continuousOn
    · rw [IccExtend_left, IccExtend_right, Icc.mk_zero, Icc.mk_one, hf₀, hf₁] at this
      rcases this t.2 with ⟨w, hw₁, hw₂⟩
      rw [IccExtend_of_mem _ _ hw₁] at hw₂
      exact ⟨_, hw₂⟩
  rw [range_comp, this, image_univ]

theorem refl_reparam {f : I → I} (hfcont : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    (refl x).reparam f hfcont hf₀ hf₁ = refl x := by
  ext
  simp

/-! #### Concatenating countably many paths -/

/-- The concatenation of countably many paths leading up to some point `x` as a function. The
corresponding path is defined separately because continuity takes some effort to prove. -/
def countableConcatFun {X : Type*} [TopologicalSpace X] {s : ℕ → X}
    (γ : (n : ℕ) → Path (s n) (s n.succ)) (x : X) : I → X := fun t ↦ by
  let n := Nat.log 2 ⌊(σ t).1⁻¹⌋₊
  refine if ht : t < 1 then γ n ⟨2 * (1 - σ t * (2 ^ n : ℕ)), ?_, ?_⟩ else x
  all_goals have ht' := symm_one ▸ symm_lt_symm.2 ht; have ht'' := coe_pos.2 ht'
  · suffices (σ t : ℝ) * (2 ^ n : ℕ) ≤ 1 by linarith
    calc
      _ ≤ (σ t).1 * ⌊(σ t).1⁻¹⌋₊ := ?_
      _ ≤ (σ t).1 * (σ t).1⁻¹    := by gcongr; exact Nat.floor_le <| by simp [t.2.2]
      _ = 1                      := mul_inv_cancel₀ ht''.ne'
    gcongr
    exact Nat.pow_log_le_self _ (Nat.floor_pos.2 <| (one_le_inv₀ ht'').2 (σ t).2.2).ne'
  · suffices h : 1 ≤ (σ t : ℝ) * (2 * (2 ^ n : ℕ)) by rw [mul_left_comm] at h; linarith
    refine (mul_inv_cancel₀ ht''.ne').symm.le.trans <|
      mul_le_mul_of_nonneg_left ?_ (σ t).2.1
    rw [← Nat.cast_ofNat, ← Nat.cast_mul, ← Nat.pow_succ']
    exact (Nat.lt_succ_floor _).le.trans <| Nat.cast_le.2 <| Nat.succ_le_of_lt <|
      Nat.lt_pow_succ_log_self one_lt_two _

/-- On closed intervals [1 - 2 ^ n, 1 - 2 ^ (n + 1)], `countableConcatFun γ x` agrees with a
reparametrisation of `γ n`. -/
lemma countableConcatFun_eqOn {X : Type*} [TopologicalSpace X] {s : ℕ → X}
    (γ : (n : ℕ) → Path (s n) (s n.succ)) {x : X} (n : ℕ) :
    Set.EqOn (countableConcatFun γ x) (fun t ↦ (γ n).extend (2 * (1 - (1 - t) * (2 ^ n))))
    (Set.Icc (σ ⟨(2 ^ n)⁻¹, by simp [inv_le_one₀, one_le_pow₀]⟩)
      (σ ⟨(2 ^ (n+1))⁻¹, by simp [inv_le_one₀, one_le_pow₀]⟩)) := fun t ht ↦ by
  simp only [Set.mem_Icc, ← Subtype.coe_le_coe, coe_symm_eq] at ht
  have ht' : t < 1 := coe_lt_one.1 <| ht.2.trans_lt <| by simp
  have ht'' : 0 < 1 - t.1 := by linarith [coe_lt_one.2 ht']
  simp only [countableConcatFun, ht', ↓reduceDIte, coe_symm_eq]
  by_cases hn : Nat.log 2 ⌊(1 - t : ℝ)⁻¹⌋₊ = n
  · refine congr (by rw [hn]) ?_
    rw [Set.projIcc_of_mem _ <| Set.mem_Icc.1 ⟨?_, ?_⟩]
    · simp [hn]
    · have h := mul_le_mul_of_nonneg_right ht.1 (a := 2 ^ n) (by simp)
      rw [sub_mul, inv_mul_cancel₀ (by simp)] at h
      linarith
    · have h := mul_le_mul_of_nonneg_right ht.2 (a := 2 ^ (n+1)) (by simp)
      rw [sub_mul, inv_mul_cancel₀ (by simp), pow_succ] at h
      linarith
  · replace hn : Nat.log 2 ⌊(1 - t : ℝ)⁻¹⌋₊ = n + 1 := by
      refine le_antisymm ?_ <| n.succ_le_of_lt <| (Ne.symm hn).lt_of_le ?_
      · refine (Nat.log_mono_right <| Nat.floor_le_floor <| inv_anti₀ (by simp) <|
          le_sub_comm.1 ht.2).trans ?_
        rw [← Nat.cast_ofNat (R := ℝ), ← Nat.cast_pow, inv_inv, Nat.floor_natCast,
          Nat.log_pow one_lt_two _]
      · refine le_trans ?_ <| Nat.log_mono_right <| Nat.floor_le_floor <| inv_anti₀ ht'' <|
          sub_le_comm.1 ht.1
        rw [← Nat.cast_ofNat (R := ℝ), ← Nat.cast_pow, inv_inv, Nat.floor_natCast,
          Nat.log_pow one_lt_two _]
    have ht'' : 2 * (1 - (1 - t.1) * 2 ^ n) = 1 := by
      suffices h : t.1 = 1 - (2 ^ (n + 1))⁻¹ by
        rw [h, pow_succ]; simp [mul_sub, show (2 : ℝ) - 1 = 1 by ring]
      refine le_antisymm ht.2 ?_
      rw [sub_le_comm, ← hn, ← Nat.cast_ofNat (R := ℝ), ← Nat.cast_pow]
      refine le_trans (by rw [inv_inv]) <| inv_anti₀ (by simp) <| (Nat.cast_le.2 <|
        Nat.pow_log_le_self 2 ?_).trans <| Nat.floor_le (inv_pos.2 ht'').le
      exact (Nat.floor_pos.2 <| (one_le_inv₀ ht'').2 (σ t).2.2).ne'
    rw [ht'', extend_one]; convert (γ (n + 1)).source
    simp [hn, pow_succ]
    linarith

/-- The concatenation of countably many paths leading up to some point `x`. -/
def countableConcat {X : Type*} [TopologicalSpace X] {s : ℕ → X}
    (γ : (n : ℕ) → Path (s n) (s n.succ)) (x : X) {b : ℕ → Set X} (hb : (𝓝 x).HasAntitoneBasis b)
    (hγ : ∀ n t, γ n t ∈ b n) : Path (s 0) x where
  toFun := countableConcatFun γ x
  continuous_toFun := by
    refine continuous_iff_continuousAt.2 fun t ↦ ?_
    by_cases ht : t < 1
    · have ht' := symm_one ▸ symm_lt_symm.2 ht; have ht'' := coe_pos.2 ht'
      have hγ' : ∀ n, ContinuousOn (countableConcatFun γ x) _ :=
        fun n ↦ (Continuous.continuousOn (by continuity)).congr <| countableConcatFun_eqOn γ n
      cases h : Nat.log 2 ⌊(σ t : ℝ)⁻¹⌋₊ with
      | zero =>
        refine ContinuousOn.continuousAt (s := Set.Iic ⟨2⁻¹, by simp, ?_⟩) ?_ ?_
        · convert hγ' 0 using 1
          rw [← Set.Icc_bot, show (⊥ : I) = 0 by rfl]; convert rfl using 2 <;> ext
          all_goals simp [show (1 : ℝ) - 2⁻¹ = 2⁻¹ by ring, (one_div (2 : ℝ)) ▸ one_half_lt_one.le]
        · refine Iic_mem_nhds <| Subtype.coe_lt_coe.1 (?_ : t.1 < 2⁻¹)
          rw [Nat.log_eq_zero_iff, or_iff_left one_lt_two.not_le, Nat.floor_lt (inv_pos.2 ht'').le,
            inv_lt_comm₀ (by exact ht'') two_pos, coe_symm_eq, lt_sub_comm] at h
          exact h.trans_eq (by ring)
      | succ n =>
        refine ContinuousOn.continuousAt (s := Set.Icc
          ⟨1 - (2 ^ n)⁻¹, by simp [inv_le_one_of_one_le₀ <| one_le_pow₀ one_le_two (M₀ := ℝ)]⟩
          ⟨1 - (2 ^ (n + 2))⁻¹, by
            simp [inv_le_one_of_one_le₀ <| one_le_pow₀ one_le_two (M₀ := ℝ)]⟩) ?_ ?_
        · convert (hγ' n).union_isClosed isClosed_Icc isClosed_Icc <| hγ' (n + 1) using 1
          rw [add_assoc, one_add_one_eq_two, Set.Icc_union_Icc_eq_Icc]
          · rfl
          · simp only [symm_le_symm, Subtype.mk_le_mk]
            exact inv_anti₀ (by simp) <| pow_le_pow_right₀ one_le_two (by simp)
          · simp only [symm_le_symm, Subtype.mk_le_mk]
            exact inv_anti₀ (by simp) <| pow_le_pow_right₀ one_le_two (by simp)
        · refine Icc_mem_nhds ?_ ?_ <;> rw [← Subtype.coe_lt_coe, Subtype.coe_mk]
          · replace h := h.symm.le; rw [← Nat.pow_le_iff_le_log one_lt_two (Nat.floor_pos.2 <|
              (one_le_inv₀ ht'').2 (σ t).2.2).ne', Nat.le_floor_iff (inv_pos.2 ht'').le,
              le_inv_comm₀ (by simp) ht'', coe_symm_eq, sub_le_comm] at h
            refine (sub_lt_sub_left (inv_strictAnti₀ (by simp) ?_) 1).trans_le h
            rw [Nat.cast_pow, Nat.cast_ofNat]
            exact pow_lt_pow_right₀ one_lt_two n.lt_succ_self
          · replace h := h.trans_lt (Nat.lt_succ_self _); rw [← Nat.lt_pow_iff_log_lt one_lt_two
              (Nat.floor_pos.2 <| (one_le_inv₀ ht'').2 (σ t).2.2).ne', Nat.floor_lt
              (inv_pos.2 ht'').le, inv_lt_comm₀ ht'' (by simp), coe_symm_eq, lt_sub_comm] at h
            exact h.trans_eq <| by simp
    · rw [unitInterval.lt_one_iff_ne_one, not_ne_iff] at ht; rw [ht]
      unfold ContinuousAt
      convert hb.1.tendsto_right_iff.2 fun n _ ↦ ?_ using 1
      · simp [countableConcatFun]
      rw [eventually_nhds_iff]
      use Set.Ioi ⟨1 - (2 ^ n)⁻¹, by rw [sub_nonneg, inv_le_one₀] <;> simp [one_le_pow₀], by simp⟩
      refine ⟨fun t ht ↦ ?_, isOpen_Ioi, by simp [← coe_lt_one]⟩
      by_cases ht' : t < 1
      · have ht'' := symm_one ▸ symm_lt_symm.2 ht'; have ht''' := coe_pos.2 ht''
        simp only [countableConcatFun, ht', reduceDIte]
        convert hb.2 _ <| hγ (Nat.log 2 _) _ using 1
        rw [← Nat.pow_le_iff_le_log one_lt_two (Nat.floor_pos.2 <| (one_le_inv₀ ht''').2
          (σ t).2.2).ne', Nat.le_floor_iff (inv_pos.2 ht''').le, le_inv_comm₀ (by simp) ht''',
          coe_symm_eq, sub_le_comm]
        apply le_of_lt; simpa using ht
      · rw [unitInterval.lt_one_iff_ne_one, not_ne_iff] at ht'; rw [ht']
        simp [countableConcatFun, mem_of_mem_nhds <| hb.1.mem_of_mem trivial]
  source' := by simp [countableConcatFun]
  target' := by simp [countableConcatFun]

/-- Evaluating `Path.countableConcat` at 1-(1-t/2)/2^n yields `γ n t`. -/
lemma countableConcat_applyAt {X : Type*} [TopologicalSpace X] {s : ℕ → X}
    {γ : (n : ℕ) → Path (s n) (s n.succ)} {x : X} {b : ℕ → Set X} {hb : (𝓝 x).HasAntitoneBasis b}
    {hγ : ∀ n t, γ n t ∈ b n} (n : ℕ) (t : I) :
    countableConcat γ x hb hγ (σ ⟨(1 - t / 2) / 2 ^ n,
      div_nonneg (by linarith [t.2.2]) (by simp),
      (div_le_one₀ (by simp)).2 <| by
        linarith [one_le_pow₀ (M₀ := ℝ) one_le_two (n := n), t.2.1]⟩) =
    γ n t := by
  rw [countableConcat, coe_mk_mk]
  refine (countableConcatFun_eqOn γ n ⟨?_, ?_⟩).trans ?_
  · rw [symm_le_symm, Subtype.mk_le_mk, ← one_div]
    exact div_le_div_of_nonneg_right (by linarith [t.2.1]) (by simp)
  · rw [symm_le_symm, Subtype.mk_le_mk, pow_succ', ← one_div, ← div_div]
    exact div_le_div_of_nonneg_right (by linarith [t.2.2]) (by simp)
  · simp [mul_div_cancel₀ t.1 two_pos.ne']

/-- The concatenation of a sequence of paths is the same as the concatenation of the first path
with the concatenation of the remaining paths. -/
lemma countableConcat_eq_trans {X : Type*} [TopologicalSpace X] {s : ℕ → X}
    {γ : (n : ℕ) → Path (s n) (s n.succ)} {x : X} {b : ℕ → Set X} {hb : (𝓝 x).HasAntitoneBasis b}
    {hγ : ∀ n t, γ n t ∈ b n} : countableConcat γ x hb hγ = (γ 0).trans
      (countableConcat (fun n ↦ γ (n + 1)) x hb fun n t ↦ hb.2 n.le_succ <| hγ (n + 1) t) := by
  ext t
  by_cases ht : (t : ℝ) ≤ 1 / 2 <;> dsimp [trans, countableConcat] <;> simp only [ht, ↓reduceIte]
  · refine (countableConcatFun_eqOn γ 0 ?_).trans <| by simp
    simpa [← Subtype.coe_le_coe, show (1 - 2⁻¹ : ℝ) = 2⁻¹ by ring] using ht
  · apply lt_of_not_le at ht
    by_cases ht' : t < 1
    · dsimp [extend, IccExtend, countableConcatFun]
      have ht'' : 0 < 1 - t.1 := by linarith [unitInterval.coe_lt_one.2 ht']
      have h : (projIcc 0 1 one_pos.le (2 * t.1 - 1) : ℝ) = 2 * t - 1 := by
        rw [projIcc_of_mem _ ⟨by linarith, by linarith⟩]
      simp only [ht', ↓reduceDIte, ← Subtype.coe_lt_coe, h, Icc.coe_one,
        show 2 * t.1 - 1 < 1 by linarith]
      refine congr (congrArg (fun n ↦ ⇑(γ n)) ?_) ?_
      · rw [h, ← sub_add, ← add_sub_right_comm, one_add_one_eq_two, ← mul_one_sub,
          mul_inv, ← div_eq_inv_mul, Nat.floor_div_ofNat, Nat.log_div_base]
        refine (Nat.sub_one_add_one (Nat.log_pos one_lt_two ?_).ne').symm
        rw [Nat.le_floor_iff (inv_pos.2 ht'').le]
        exact le_inv_of_le_inv₀ ht'' <| by linarith
      · rw [Subtype.mk_eq_mk, ← sub_add, ← add_sub_right_comm, one_add_one_eq_two, ← mul_one_sub,
          mul_inv, ← div_eq_inv_mul]
        rw [Nat.floor_div_ofNat, Nat.log_div_base]
        simp_rw [Nat.cast_pow]; rw [pow_sub₀ _ two_pos.ne' ?_]
        · ring
        · rw [← Nat.pow_le_iff_le_log one_lt_two <| (Nat.floor_pos.2 <| (one_le_inv₀ ht'').2
            (by exact (σ t).2.2)).ne', Nat.le_floor_iff (inv_pos.2 ht'').le]
          exact le_inv_of_le_inv₀ ht'' <| by linarith
    · rw [show t = 1 by simpa [unitInterval.lt_one_iff_ne_one] using ht']
      simp [show (2 - 1 : ℝ) = 1 by ring, countableConcatFun]

end Path
