/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.UnitInterval

/-!
# Path connectedness

## Main definitions

In the file the unit interval `[0, 1]` in `ℝ` is denoted by `I`, and `X` is a topological space.

* `Path (x y : X)` is the type of paths from `x` to `y`, i.e., continuous maps from `I` to `X`
  mapping `0` to `x` and `1` to `y`.
* `Path.map` is the image of a path under a continuous map.
* `Joined (x y : X)` means there is a path between `x` and `y`.
* `Joined.somePath (h : Joined x y)` selects some path between two points `x` and `y`.
* `pathComponent (x : X)` is the set of points joined to `x`.
* `PathConnectedSpace X` is a predicate class asserting that `X` is non-empty and every two
  points of `X` are joined.

Then there are corresponding relative notions for `F : Set X`.

* `JoinedIn F (x y : X)` means there is a path `γ` joining `x` to `y` with values in `F`.
* `JoinedIn.somePath (h : JoinedIn F x y)` selects a path from `x` to `y` inside `F`.
* `pathComponentIn F (x : X)` is the set of points joined to `x` in `F`.
* `IsPathConnected F` asserts that `F` is non-empty and every two
  points of `F` are joined in `F`.
* `LocPathConnectedSpace X` is a predicate class asserting that `X` is locally path-connected:
  each point has a basis of path-connected neighborhoods (we do *not* ask these to be open).

## Main theorems

* `Joined` and `JoinedIn F` are transitive relations.

One can link the absolute and relative version in two directions, using `(univ : Set X)` or the
subtype `↥F`.

* `pathConnectedSpace_iff_univ : PathConnectedSpace X ↔ IsPathConnected (univ : Set X)`
* `isPathConnected_iff_pathConnectedSpace : IsPathConnected F ↔ PathConnectedSpace ↥F`

For locally path connected spaces, we have
* `pathConnectedSpace_iff_connectedSpace : PathConnectedSpace X ↔ ConnectedSpace X`
* `IsOpen.isConnected_iff_isPathConnected (U_op : IsOpen U) : IsPathConnected U ↔ IsConnected U`

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
-- porting note (#5171): removed @[nolint has_nonempty_instance]
structure Path (x y : X) extends C(I, X) where
  /-- The start point of a `Path`. -/
  source' : toFun 0 = x
  /-- The end point of a `Path`. -/
  target' : toFun 1 = y

instance Path.funLike : FunLike (Path x y) I X where
  coe := fun γ ↦ ⇑γ.toContinuousMap
  coe_injective' := fun γ₁ γ₂ h => by
    simp only [DFunLike.coe_fn_eq] at h
    cases γ₁; cases γ₂; congr

-- Porting note (#10754): added this instance so that we can use `FunLike.coe` for `CoeFun`
-- this also fixed very strange `simp` timeout issues
instance Path.continuousMapClass : ContinuousMapClass (Path x y) I X where
  map_continuous γ := show Continuous γ.toContinuousMap by fun_prop

-- Porting note: not necessary in light of the instance above
/-
instance : CoeFun (Path x y) fun _ => I → X :=
  ⟨fun p => p.toFun⟩
-/

@[ext]
protected theorem Path.ext : ∀ {γ₁ γ₂ : Path x y}, (γ₁ : I → X) = γ₂ → γ₁ = γ₂ := by
  rintro ⟨⟨x, h11⟩, h12, h13⟩ ⟨⟨x, h21⟩, h22, h23⟩ rfl
  rfl

namespace Path

@[simp]
theorem coe_mk_mk (f : I → X) (h₁) (h₂ : f 0 = x) (h₃ : f 1 = y) :
    ⇑(mk ⟨f, h₁⟩ h₂ h₃ : Path x y) = f :=
  rfl
-- Porting note: the name `Path.coe_mk` better refers to a new lemma below

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

-- Porting note: this is needed because of the `Path.continuousMapClass` instance
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

/- porting note: because of the `DFunLike` instance, we already have a coercion to `C(I, X)`
so we avoid adding another.
--instance : Coe (Path x y) C(I, X) :=
  --⟨fun γ => γ.1⟩
-/

/-- The following instance defines the topology on the path space to be induced from the
compact-open topology on the space `C(I,X)` of continuous maps from `I` to `X`.
-/
instance topologicalSpace : TopologicalSpace (Path x y) :=
  TopologicalSpace.induced ((↑) : _ → C(I, X)) ContinuousMap.compactOpen

theorem continuous_eval : Continuous fun p : Path x y × I => p.1 p.2 :=
  ContinuousMap.continuous_eval.comp <|
    (continuous_induced_dom (α := Path x y)).prod_map continuous_id

@[continuity]
theorem _root_.Continuous.path_eval {Y} [TopologicalSpace Y] {f : Y → Path x y} {g : Y → I}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun y => f y (g y) :=
  Continuous.comp continuous_eval (hf.prod_mk hg)

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
      have : t / 2 ≤ 1 / 2 := (div_le_div_right (zero_lt_two : (0 : ℝ) < 2)).mpr ht1
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
  h.comp (continuous_id.prod_map continuous_symm)

@[continuity]
theorem continuous_symm : Continuous (symm : Path x y → Path y x) :=
  continuous_uncurry_iff.mp <| symm_continuous_family _ (continuous_fst.path_eval continuous_snd)

@[continuity]
theorem continuous_uncurry_extend_of_continuous_family {ι : Type*} [TopologicalSpace ι]
    {a b : ι → X} (γ : ∀ t : ι, Path (a t) (b t)) (h : Continuous ↿γ) :
    Continuous ↿fun t => (γ t).extend := by
  apply h.comp (continuous_id.prod_map continuous_projIcc)
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
    exact h₁'.comp (continuous_id.prod_map <| continuous_const.mul continuous_subtype_val)
  · change
      Continuous ((fun p : ι × ℝ => (γ₂ p.1).extend p.2) ∘ Prod.map id (fun x => 2 * x - 1 : I → ℝ))
    exact
      h₂'.comp
        (continuous_id.prod_map <|
          (continuous_const.mul continuous_subtype_val).sub continuous_const)
  · rintro st hst
    simp [hst, mul_inv_cancel₀ (two_ne_zero' ℝ)]

@[continuity]
theorem _root_.Continuous.path_trans {f : Y → Path x y} {g : Y → Path y z} :
    Continuous f → Continuous g → Continuous fun t => (f t).trans (g t) := by
  intro hf hg
  apply continuous_uncurry_iff.mp
  exact trans_continuous_family _ (continuous_uncurry_iff.mpr hf) _ (continuous_uncurry_iff.mpr hg)

@[continuity]
theorem continuous_trans {x y z : X} : Continuous fun ρ : Path x y × Path y z => ρ.1.trans ρ.2 :=
  continuous_fst.path_trans continuous_snd

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


/-- `γ.truncate t₀ t₁` is the path which follows the path `γ` on the
  time interval `[t₀, t₁]` and stays still otherwise. -/
def truncate {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b) (t₀ t₁ : ℝ) :
    Path (γ.extend <| min t₀ t₁) (γ.extend t₁) where
  toFun s := γ.extend (min (max s t₀) t₁)
  continuous_toFun :=
    γ.continuous_extend.comp ((continuous_subtype_val.max continuous_const).min continuous_const)
  source' := by
    simp only [min_def, max_def']
    norm_cast
    split_ifs with h₁ h₂ h₃ h₄
    · simp [γ.extend_of_le_zero h₁]
    · congr
      linarith
    · have h₄ : t₁ ≤ 0 := le_of_lt (by simpa using h₂)
      simp [γ.extend_of_le_zero h₄, γ.extend_of_le_zero h₁]
    all_goals rfl
  target' := by
    simp only [min_def, max_def']
    norm_cast
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

/-- For a path `γ`, `γ.truncate` gives a "continuous family of paths", by which we
  mean the uncurried function which maps `(t₀, t₁, s)` to `γ.truncate t₀ t₁ s` is continuous. -/
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

@[simp 1001] -- Porting note: increase `simp` priority so left-hand side doesn't simplify
theorem truncate_zero_zero {a b : X} (γ : Path a b) :
    γ.truncate 0 0 = (Path.refl a).cast (by rw [min_self, γ.extend_zero]) γ.extend_zero := by
  convert γ.truncate_self 0

@[simp 1001] -- Porting note: increase `simp` priority so left-hand side doesn't simplify
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
-- Porting note: this seems like it was poorly named (was: `coe_to_fun`)

@[simp]
theorem reparam_id (γ : Path x y) : γ.reparam id continuous_id rfl rfl = γ := by
  ext
  rfl

theorem range_reparam (γ : Path x y) {f : I → I} (hfcont : Continuous f) (hf₀ : f 0 = 0)
    (hf₁ : f 1 = 1) : range (γ.reparam f hfcont hf₀ hf₁) = range γ := by
  change range (γ ∘ f) = range γ
  have : range f = univ := by
    rw [range_iff_surjective]
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

end Path

/-! ### Being joined by a path -/


/-- The relation "being joined by a path". This is an equivalence relation. -/
def Joined (x y : X) : Prop :=
  Nonempty (Path x y)

@[refl]
theorem Joined.refl (x : X) : Joined x x :=
  ⟨Path.refl x⟩

/-- When two points are joined, choose some path from `x` to `y`. -/
def Joined.somePath (h : Joined x y) : Path x y :=
  Nonempty.some h

@[symm]
theorem Joined.symm {x y : X} (h : Joined x y) : Joined y x :=
  ⟨h.somePath.symm⟩

@[trans]
theorem Joined.trans {x y z : X} (hxy : Joined x y) (hyz : Joined y z) : Joined x z :=
  ⟨hxy.somePath.trans hyz.somePath⟩

variable (X)

/-- The setoid corresponding the equivalence relation of being joined by a continuous path. -/
def pathSetoid : Setoid X where
  r := Joined
  iseqv := Equivalence.mk Joined.refl Joined.symm Joined.trans

/-- The quotient type of points of a topological space modulo being joined by a continuous path. -/
def ZerothHomotopy :=
  Quotient (pathSetoid X)

instance ZerothHomotopy.inhabited : Inhabited (ZerothHomotopy ℝ) :=
  ⟨@Quotient.mk' ℝ (pathSetoid ℝ) 0⟩

variable {X}

/-! ### Being joined by a path inside a set -/


/-- The relation "being joined by a path in `F`". Not quite an equivalence relation since it's not
reflexive for points that do not belong to `F`. -/
def JoinedIn (F : Set X) (x y : X) : Prop :=
  ∃ γ : Path x y, ∀ t, γ t ∈ F

variable {F : Set X}

theorem JoinedIn.mem (h : JoinedIn F x y) : x ∈ F ∧ y ∈ F := by
  rcases h with ⟨γ, γ_in⟩
  have : γ 0 ∈ F ∧ γ 1 ∈ F := by constructor <;> apply γ_in
  simpa using this

theorem JoinedIn.source_mem (h : JoinedIn F x y) : x ∈ F :=
  h.mem.1

theorem JoinedIn.target_mem (h : JoinedIn F x y) : y ∈ F :=
  h.mem.2

/-- When `x` and `y` are joined in `F`, choose a path from `x` to `y` inside `F` -/
def JoinedIn.somePath (h : JoinedIn F x y) : Path x y :=
  Classical.choose h

theorem JoinedIn.somePath_mem (h : JoinedIn F x y) (t : I) : h.somePath t ∈ F :=
  Classical.choose_spec h t

/-- If `x` and `y` are joined in the set `F`, then they are joined in the subtype `F`. -/
theorem JoinedIn.joined_subtype (h : JoinedIn F x y) :
    Joined (⟨x, h.source_mem⟩ : F) (⟨y, h.target_mem⟩ : F) :=
  ⟨{  toFun := fun t => ⟨h.somePath t, h.somePath_mem t⟩
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }⟩

theorem JoinedIn.ofLine {f : ℝ → X} (hf : ContinuousOn f I) (h₀ : f 0 = x) (h₁ : f 1 = y)
    (hF : f '' I ⊆ F) : JoinedIn F x y :=
  ⟨Path.ofLine hf h₀ h₁, fun t => hF <| Path.ofLine_mem hf h₀ h₁ t⟩

theorem JoinedIn.joined (h : JoinedIn F x y) : Joined x y :=
  ⟨h.somePath⟩

theorem joinedIn_iff_joined (x_in : x ∈ F) (y_in : y ∈ F) :
    JoinedIn F x y ↔ Joined (⟨x, x_in⟩ : F) (⟨y, y_in⟩ : F) :=
  ⟨fun h => h.joined_subtype, fun h => ⟨h.somePath.map continuous_subtype_val, by simp⟩⟩

@[simp]
theorem joinedIn_univ : JoinedIn univ x y ↔ Joined x y := by
  simp [JoinedIn, Joined, exists_true_iff_nonempty]

theorem JoinedIn.mono {U V : Set X} (h : JoinedIn U x y) (hUV : U ⊆ V) : JoinedIn V x y :=
  ⟨h.somePath, fun t => hUV (h.somePath_mem t)⟩

theorem JoinedIn.refl (h : x ∈ F) : JoinedIn F x x :=
  ⟨Path.refl x, fun _t => h⟩

@[symm]
theorem JoinedIn.symm (h : JoinedIn F x y) : JoinedIn F y x := by
  cases' h.mem with hx hy
  simp_all only [joinedIn_iff_joined]
  exact h.symm

theorem JoinedIn.trans (hxy : JoinedIn F x y) (hyz : JoinedIn F y z) : JoinedIn F x z := by
  cases' hxy.mem with hx hy
  cases' hyz.mem with hx hy
  simp_all only [joinedIn_iff_joined]
  exact hxy.trans hyz

theorem Specializes.joinedIn (h : x ⤳ y) (hx : x ∈ F) (hy : y ∈ F) : JoinedIn F x y := by
  refine ⟨⟨⟨Set.piecewise {1} (const I y) (const I x), ?_⟩, by simp, by simp⟩, fun t ↦ ?_⟩
  · exact isClosed_singleton.continuous_piecewise_of_specializes continuous_const continuous_const
      fun _ ↦ h
  · simp only [Path.coe_mk_mk, piecewise]
    split_ifs <;> assumption

theorem Inseparable.joinedIn (h : Inseparable x y) (hx : x ∈ F) (hy : y ∈ F) : JoinedIn F x y :=
  h.specializes.joinedIn hx hy

/-! ### Path component -/


/-- The path component of `x` is the set of points that can be joined to `x`. -/
def pathComponent (x : X) :=
  { y | Joined x y }

@[simp]
theorem mem_pathComponent_self (x : X) : x ∈ pathComponent x :=
  Joined.refl x

@[simp]
theorem pathComponent.nonempty (x : X) : (pathComponent x).Nonempty :=
  ⟨x, mem_pathComponent_self x⟩

theorem mem_pathComponent_of_mem (h : x ∈ pathComponent y) : y ∈ pathComponent x :=
  Joined.symm h

theorem pathComponent_symm : x ∈ pathComponent y ↔ y ∈ pathComponent x :=
  ⟨fun h => mem_pathComponent_of_mem h, fun h => mem_pathComponent_of_mem h⟩

theorem pathComponent_congr (h : x ∈ pathComponent y) : pathComponent x = pathComponent y := by
  ext z
  constructor
  · intro h'
    rw [pathComponent_symm]
    exact (h.trans h').symm
  · intro h'
    rw [pathComponent_symm] at h' ⊢
    exact h'.trans h

theorem pathComponent_subset_component (x : X) : pathComponent x ⊆ connectedComponent x :=
  fun y h =>
  (isConnected_range h.somePath.continuous).subset_connectedComponent ⟨0, by simp⟩ ⟨1, by simp⟩

/-- The path component of `x` in `F` is the set of points that can be joined to `x` in `F`. -/
def pathComponentIn (x : X) (F : Set X) :=
  { y | JoinedIn F x y }

@[simp]
theorem pathComponentIn_univ (x : X) : pathComponentIn x univ = pathComponent x := by
  simp [pathComponentIn, pathComponent, JoinedIn, Joined, exists_true_iff_nonempty]

theorem Joined.mem_pathComponent (hyz : Joined y z) (hxy : y ∈ pathComponent x) :
    z ∈ pathComponent x :=
  hxy.trans hyz

/-! ### Path connected sets -/


/-- A set `F` is path connected if it contains a point that can be joined to all other in `F`. -/
def IsPathConnected (F : Set X) : Prop :=
  ∃ x ∈ F, ∀ {y}, y ∈ F → JoinedIn F x y

theorem isPathConnected_iff_eq : IsPathConnected F ↔ ∃ x ∈ F, pathComponentIn x F = F := by
  constructor <;> rintro ⟨x, x_in, h⟩ <;> use x, x_in
  · ext y
    exact ⟨fun hy => hy.mem.2, h⟩
  · intro y y_in
    rwa [← h] at y_in

theorem IsPathConnected.joinedIn (h : IsPathConnected F) :
    ∀ᵉ (x ∈ F) (y ∈ F), JoinedIn F x y := fun _x x_in _y y_in =>
  let ⟨_b, _b_in, hb⟩ := h
  (hb x_in).symm.trans (hb y_in)

theorem isPathConnected_iff :
    IsPathConnected F ↔ F.Nonempty ∧ ∀ᵉ (x ∈ F) (y ∈ F), JoinedIn F x y :=
  ⟨fun h =>
    ⟨let ⟨b, b_in, _hb⟩ := h; ⟨b, b_in⟩, h.joinedIn⟩,
    fun ⟨⟨b, b_in⟩, h⟩ => ⟨b, b_in, fun x_in => h _ b_in _ x_in⟩⟩

/-- If `f` is continuous on `F` and `F` is path-connected, so is `f(F)`. -/
theorem IsPathConnected.image' (hF : IsPathConnected F)
    {f : X → Y} (hf : ContinuousOn f F) : IsPathConnected (f '' F) := by
  rcases hF with ⟨x, x_in, hx⟩
  use f x, mem_image_of_mem f x_in
  rintro _ ⟨y, y_in, rfl⟩
  refine ⟨(hx y_in).somePath.map' ?_, fun t ↦ ⟨_, (hx y_in).somePath_mem t, rfl⟩⟩
  exact hf.mono (range_subset_iff.2 (hx y_in).somePath_mem)

/-- If `f` is continuous and `F` is path-connected, so is `f(F)`. -/
theorem IsPathConnected.image (hF : IsPathConnected F) {f : X → Y}
    (hf : Continuous f) : IsPathConnected (f '' F) := hF.image' hf.continuousOn

/-- If `f : X → Y` is a `Inducing`, `f(F)` is path-connected iff `F` is. -/
nonrec theorem Inducing.isPathConnected_iff {f : X → Y} (hf : Inducing f) :
    IsPathConnected F ↔ IsPathConnected (f '' F) := by
  refine ⟨fun hF ↦ hF.image hf.continuous, fun hF ↦ ?_⟩
  simp? [isPathConnected_iff] at hF ⊢ says
    simp only [isPathConnected_iff, image_nonempty, mem_image, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂] at hF ⊢
  refine ⟨hF.1, fun x hx y hy ↦ ?_⟩
  rcases hF.2 x hx y hy with ⟨γ, hγ⟩
  choose γ' hγ' hγγ' using hγ
  have key₁ : Inseparable x (γ' 0) := by rw [← hf.inseparable_iff, hγγ' 0, γ.source]
  have key₂ : Inseparable (γ' 1) y := by rw [← hf.inseparable_iff, hγγ' 1, γ.target]
  refine key₁.joinedIn hx (hγ' 0) |>.trans ⟨⟨⟨γ', ?_⟩, rfl, rfl⟩, hγ'⟩ |>.trans
    (key₂.joinedIn (hγ' 1) hy)
  simpa [hf.continuous_iff] using γ.continuous.congr fun t ↦ (hγγ' t).symm

/-- If `h : X → Y` is a homeomorphism, `h(s)` is path-connected iff `s` is. -/
@[simp]
theorem Homeomorph.isPathConnected_image {s : Set X} (h : X ≃ₜ Y) :
    IsPathConnected (h '' s) ↔ IsPathConnected s :=
  h.inducing.isPathConnected_iff.symm

/-- If `h : X → Y` is a homeomorphism, `h⁻¹(s)` is path-connected iff `s` is. -/
@[simp]
theorem Homeomorph.isPathConnected_preimage {s : Set Y} (h : X ≃ₜ Y) :
    IsPathConnected (h ⁻¹' s) ↔ IsPathConnected s := by
  rw [← Homeomorph.image_symm]; exact h.symm.isPathConnected_image

theorem IsPathConnected.mem_pathComponent (h : IsPathConnected F) (x_in : x ∈ F) (y_in : y ∈ F) :
    y ∈ pathComponent x :=
  (h.joinedIn x x_in y y_in).joined

theorem IsPathConnected.subset_pathComponent (h : IsPathConnected F) (x_in : x ∈ F) :
    F ⊆ pathComponent x := fun _y y_in => h.mem_pathComponent x_in y_in

theorem isPathConnected_singleton (x : X) : IsPathConnected ({x} : Set X) := by
  refine ⟨x, rfl, ?_⟩
  rintro y rfl
  exact JoinedIn.refl rfl

theorem IsPathConnected.union {U V : Set X} (hU : IsPathConnected U) (hV : IsPathConnected V)
    (hUV : (U ∩ V).Nonempty) : IsPathConnected (U ∪ V) := by
  rcases hUV with ⟨x, xU, xV⟩
  use x, Or.inl xU
  rintro y (yU | yV)
  · exact (hU.joinedIn x xU y yU).mono subset_union_left
  · exact (hV.joinedIn x xV y yV).mono subset_union_right

/-- If a set `W` is path-connected, then it is also path-connected when seen as a set in a smaller
ambient type `U` (when `U` contains `W`). -/
theorem IsPathConnected.preimage_coe {U W : Set X} (hW : IsPathConnected W) (hWU : W ⊆ U) :
    IsPathConnected (((↑) : U → X) ⁻¹' W) := by
  rcases hW with ⟨x, x_in, hx⟩
  use ⟨x, hWU x_in⟩, by simp [x_in]
  rintro ⟨y, hyU⟩ hyW
  exact ⟨(hx hyW).joined_subtype.somePath.map (continuous_inclusion hWU), by simp⟩

theorem IsPathConnected.exists_path_through_family {n : ℕ}
    {s : Set X} (h : IsPathConnected s) (p : Fin (n + 1) → X) (hp : ∀ i, p i ∈ s) :
    ∃ γ : Path (p 0) (p n), range γ ⊆ s ∧ ∀ i, p i ∈ range γ := by
  let p' : ℕ → X := fun k => if h : k < n + 1 then p ⟨k, h⟩ else p ⟨0, n.zero_lt_succ⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : Path (p' 0) (p' n), (∀ i ≤ n, p' i ∈ range γ) ∧ range γ ⊆ s := by
    have hp' : ∀ i ≤ n, p' i ∈ s := by
      intro i hi
      simp [p', Nat.lt_succ_of_le hi, hp]
    clear_value p'
    clear hp p
    induction' n with n hn
    · use Path.refl (p' 0)
      constructor
      · rintro i hi
        rw [Nat.le_zero.mp hi]
        exact ⟨0, rfl⟩
      · rw [range_subset_iff]
        rintro _x
        exact hp' 0 le_rfl
    · rcases hn fun i hi => hp' i <| Nat.le_succ_of_le hi with ⟨γ₀, hγ₀⟩
      rcases h.joinedIn (p' n) (hp' n n.le_succ) (p' <| n + 1) (hp' (n + 1) <| le_rfl) with
        ⟨γ₁, hγ₁⟩
      let γ : Path (p' 0) (p' <| n + 1) := γ₀.trans γ₁
      use γ
      have range_eq : range γ = range γ₀ ∪ range γ₁ := γ₀.trans_range γ₁
      constructor
      · rintro i hi
        by_cases hi' : i ≤ n
        · rw [range_eq]
          left
          exact hγ₀.1 i hi'
        · rw [not_le, ← Nat.succ_le_iff] at hi'
          have : i = n.succ := le_antisymm hi hi'
          rw [this]
          use 1
          exact γ.target
      · rw [range_eq]
        apply union_subset hγ₀.2
        rw [range_subset_iff]
        exact hγ₁
  have hpp' : ∀ k < n + 1, p k = p' k := by
    intro k hk
    simp only [p', hk, dif_pos]
    congr
    ext
    rw [Fin.val_cast_of_lt hk]
  use γ.cast (hpp' 0 n.zero_lt_succ) (hpp' n n.lt_succ_self)
  simp only [γ.cast_coe]
  refine And.intro hγ.2 ?_
  rintro ⟨i, hi⟩
  suffices p ⟨i, hi⟩ = p' i by convert hγ.1 i (Nat.le_of_lt_succ hi)
  rw [← hpp' i hi]
  suffices i = i % n.succ by congr
  rw [Nat.mod_eq_of_lt hi]

theorem IsPathConnected.exists_path_through_family' {n : ℕ}
    {s : Set X} (h : IsPathConnected s) (p : Fin (n + 1) → X) (hp : ∀ i, p i ∈ s) :
    ∃ (γ : Path (p 0) (p n)) (t : Fin (n + 1) → I), (∀ t, γ t ∈ s) ∧ ∀ i, γ (t i) = p i := by
  rcases h.exists_path_through_family p hp with ⟨γ, hγ⟩
  rcases hγ with ⟨h₁, h₂⟩
  simp only [range, mem_setOf_eq] at h₂
  rw [range_subset_iff] at h₁
  choose! t ht using h₂
  exact ⟨γ, t, h₁, ht⟩

/-! ### Path connected spaces -/


/-- A topological space is path-connected if it is non-empty and every two points can be
joined by a continuous path. -/
class PathConnectedSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- A path-connected space must be nonempty. -/
  nonempty : Nonempty X
  /-- Any two points in a path-connected space must be joined by a continuous path. -/
  joined : ∀ x y : X, Joined x y

theorem pathConnectedSpace_iff_zerothHomotopy :
    PathConnectedSpace X ↔ Nonempty (ZerothHomotopy X) ∧ Subsingleton (ZerothHomotopy X) := by
  letI := pathSetoid X
  constructor
  · intro h
    refine ⟨(nonempty_quotient_iff _).mpr h.1, ⟨?_⟩⟩
    rintro ⟨x⟩ ⟨y⟩
    exact Quotient.sound (PathConnectedSpace.joined x y)
  · unfold ZerothHomotopy
    rintro ⟨h, h'⟩
    exact ⟨(nonempty_quotient_iff _).mp h, fun x y => Quotient.exact <| Subsingleton.elim ⟦x⟧ ⟦y⟧⟩

namespace PathConnectedSpace

variable [PathConnectedSpace X]

/-- Use path-connectedness to build a path between two points. -/
def somePath (x y : X) : Path x y :=
  Nonempty.some (joined x y)

end PathConnectedSpace

theorem isPathConnected_iff_pathConnectedSpace : IsPathConnected F ↔ PathConnectedSpace F := by
  rw [isPathConnected_iff]
  constructor
  · rintro ⟨⟨x, x_in⟩, h⟩
    refine ⟨⟨⟨x, x_in⟩⟩, ?_⟩
    rintro ⟨y, y_in⟩ ⟨z, z_in⟩
    have H := h y y_in z z_in
    rwa [joinedIn_iff_joined y_in z_in] at H
  · rintro ⟨⟨x, x_in⟩, H⟩
    refine ⟨⟨x, x_in⟩, fun y y_in z z_in => ?_⟩
    rw [joinedIn_iff_joined y_in z_in]
    apply H

theorem pathConnectedSpace_iff_univ : PathConnectedSpace X ↔ IsPathConnected (univ : Set X) := by
  constructor
  · intro h
    haveI := @PathConnectedSpace.nonempty X _ _
    inhabit X
    refine ⟨default, mem_univ _, ?_⟩
    intros y _hy
    simpa using PathConnectedSpace.joined default y
  · intro h
    have h' := h.joinedIn
    cases' h with x h
    exact ⟨⟨x⟩, by simpa using h'⟩

theorem isPathConnected_univ [PathConnectedSpace X] : IsPathConnected (univ : Set X) :=
  pathConnectedSpace_iff_univ.mp inferInstance

theorem isPathConnected_range [PathConnectedSpace X] {f : X → Y} (hf : Continuous f) :
    IsPathConnected (range f) := by
  rw [← image_univ]
  exact isPathConnected_univ.image hf

theorem Function.Surjective.pathConnectedSpace [PathConnectedSpace X]
    {f : X → Y} (hf : Surjective f) (hf' : Continuous f) : PathConnectedSpace Y := by
  rw [pathConnectedSpace_iff_univ, ← hf.range_eq]
  exact isPathConnected_range hf'

instance Quotient.instPathConnectedSpace {s : Setoid X} [PathConnectedSpace X] :
    PathConnectedSpace (Quotient s) :=
  (surjective_quotient_mk' X).pathConnectedSpace continuous_coinduced_rng

/-- This is a special case of `NormedSpace.instPathConnectedSpace` (and
`TopologicalAddGroup.pathConnectedSpace`). It exists only to simplify dependencies. -/
instance Real.instPathConnectedSpace : PathConnectedSpace ℝ where
  joined x y := ⟨⟨⟨fun (t : I) ↦ (1 - t) * x + t * y, by fun_prop⟩, by simp, by simp⟩⟩
  nonempty := inferInstance

theorem pathConnectedSpace_iff_eq : PathConnectedSpace X ↔ ∃ x : X, pathComponent x = univ := by
  simp [pathConnectedSpace_iff_univ, isPathConnected_iff_eq]

-- see Note [lower instance priority]
instance (priority := 100) PathConnectedSpace.connectedSpace [PathConnectedSpace X] :
    ConnectedSpace X := by
  rw [connectedSpace_iff_connectedComponent]
  rcases isPathConnected_iff_eq.mp (pathConnectedSpace_iff_univ.mp ‹_›) with ⟨x, _x_in, hx⟩
  use x
  rw [← univ_subset_iff]
  exact (by simpa using hx : pathComponent x = univ) ▸ pathComponent_subset_component x

theorem IsPathConnected.isConnected (hF : IsPathConnected F) : IsConnected F := by
  rw [isConnected_iff_connectedSpace]
  rw [isPathConnected_iff_pathConnectedSpace] at hF
  exact @PathConnectedSpace.connectedSpace _ _ hF

namespace PathConnectedSpace

variable [PathConnectedSpace X]

theorem exists_path_through_family {n : ℕ} (p : Fin (n + 1) → X) :
    ∃ γ : Path (p 0) (p n), ∀ i, p i ∈ range γ := by
  have : IsPathConnected (univ : Set X) := pathConnectedSpace_iff_univ.mp (by infer_instance)
  rcases this.exists_path_through_family p fun _i => True.intro with ⟨γ, -, h⟩
  exact ⟨γ, h⟩

theorem exists_path_through_family' {n : ℕ} (p : Fin (n + 1) → X) :
    ∃ (γ : Path (p 0) (p n)) (t : Fin (n + 1) → I), ∀ i, γ (t i) = p i := by
  have : IsPathConnected (univ : Set X) := pathConnectedSpace_iff_univ.mp (by infer_instance)
  rcases this.exists_path_through_family' p fun _i => True.intro with ⟨γ, t, -, h⟩
  exact ⟨γ, t, h⟩

end PathConnectedSpace

/-! ### Locally path connected spaces -/


/-- A topological space is locally path connected, at every point, path connected
neighborhoods form a neighborhood basis. -/
class LocPathConnectedSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- Each neighborhood filter has a basis of path-connected neighborhoods. -/
  path_connected_basis : ∀ x : X, (𝓝 x).HasBasis (fun s : Set X => s ∈ 𝓝 x ∧ IsPathConnected s) id

export LocPathConnectedSpace (path_connected_basis)

theorem locPathConnected_of_bases {p : ι → Prop} {s : X → ι → Set X}
    (h : ∀ x, (𝓝 x).HasBasis p (s x)) (h' : ∀ x i, p i → IsPathConnected (s x i)) :
    LocPathConnectedSpace X := by
  constructor
  intro x
  apply (h x).to_hasBasis
  · intro i pi
    exact ⟨s x i, ⟨(h x).mem_of_mem pi, h' x i pi⟩, by rfl⟩
  · rintro U ⟨U_in, _hU⟩
    rcases (h x).mem_iff.mp U_in with ⟨i, pi, hi⟩
    tauto

theorem pathConnectedSpace_iff_connectedSpace [LocPathConnectedSpace X] :
    PathConnectedSpace X ↔ ConnectedSpace X := by
  constructor
  · intro h
    infer_instance
  · intro hX
    rw [pathConnectedSpace_iff_eq]
    use Classical.arbitrary X
    refine IsClopen.eq_univ ⟨?_, ?_⟩ (by simp)
    · rw [isClosed_iff_nhds]
      intro y H
      rcases (path_connected_basis y).ex_mem with ⟨U, ⟨U_in, hU⟩⟩
      rcases H U U_in with ⟨z, hz, hz'⟩
      exact (hU.joinedIn z hz y <| mem_of_mem_nhds U_in).joined.mem_pathComponent hz'
    · rw [isOpen_iff_mem_nhds]
      intro y y_in
      rcases (path_connected_basis y).ex_mem with ⟨U, ⟨U_in, hU⟩⟩
      apply mem_of_superset U_in
      rw [← pathComponent_congr y_in]
      exact hU.subset_pathComponent (mem_of_mem_nhds U_in)

theorem pathConnected_subset_basis [LocPathConnectedSpace X] {U : Set X} (h : IsOpen U)
    (hx : x ∈ U) : (𝓝 x).HasBasis (fun s : Set X => s ∈ 𝓝 x ∧ IsPathConnected s ∧ s ⊆ U) id :=
  (path_connected_basis x).hasBasis_self_subset (IsOpen.mem_nhds h hx)

theorem locPathConnected_of_isOpen [LocPathConnectedSpace X] {U : Set X} (h : IsOpen U) :
    LocPathConnectedSpace U :=
  ⟨by
    rintro ⟨x, x_in⟩
    rw [nhds_subtype_eq_comap]
    constructor
    intro V
    rw [(HasBasis.comap ((↑) : U → X) (pathConnected_subset_basis h x_in)).mem_iff]
    constructor
    · rintro ⟨W, ⟨W_in, hW, hWU⟩, hWV⟩
      exact ⟨Subtype.val ⁻¹' W, ⟨⟨preimage_mem_comap W_in, hW.preimage_coe hWU⟩, hWV⟩⟩
    · rintro ⟨W, ⟨W_in, hW⟩, hWV⟩
      refine
        ⟨(↑) '' W,
          ⟨Filter.image_coe_mem_of_mem_comap (IsOpen.mem_nhds h x_in) W_in,
            hW.image continuous_subtype_val, Subtype.coe_image_subset U W⟩,
          ?_⟩
      rintro x ⟨y, ⟨y_in, hy⟩⟩
      rw [← Subtype.coe_injective hy]
      tauto⟩

theorem IsOpen.isConnected_iff_isPathConnected [LocPathConnectedSpace X] {U : Set X}
    (U_op : IsOpen U) : IsPathConnected U ↔ IsConnected U := by
  rw [isConnected_iff_connectedSpace, isPathConnected_iff_pathConnectedSpace]
  haveI := locPathConnected_of_isOpen U_op
  exact pathConnectedSpace_iff_connectedSpace
