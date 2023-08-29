/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.Topology.Algebra.Order.ProjIcc
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Topology.UnitInterval

#align_import topology.path_connected from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

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

## Main theorems

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

open Classical Topology Filter unitInterval Set Function

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x y z : X} {ι : Type*}

/-! ### Paths -/

/-- Continuous path connecting two points `x` and `y` in a topological space -/
-- porting note: removed @[nolint has_nonempty_instance]
structure Path (x y : X) extends C(I, X) where
  /-- The start point of a `Path`. -/
  source' : toFun 0 = x
  /-- The end point of a `Path`. -/
  target' : toFun 1 = y
#align path Path

-- porting note: added this instance so that we can use `FunLike.coe` for `CoeFun`
-- this also fixed very strange `simp` timeout issues
instance Path.continuousMapClass : ContinuousMapClass (Path x y) I X where
  coe := fun γ ↦ ⇑γ.toContinuousMap
  coe_injective' := fun γ₁ γ₂ h => by
    simp only [FunLike.coe_fn_eq] at h
    -- ⊢ γ₁ = γ₂
    cases γ₁; cases γ₂; congr
    -- ⊢ { toContinuousMap := toContinuousMap✝, source' := source'✝, target' := targe …
              -- ⊢ { toContinuousMap := toContinuousMap✝¹, source' := source'✝¹, target' := tar …
                        -- 🎉 no goals
  map_continuous := fun γ => by continuity
                                -- 🎉 no goals

-- porting note: not necessary in light of the instance above
/-
instance : CoeFun (Path x y) fun _ => I → X :=
  ⟨fun p => p.toFun⟩
-/

@[ext]
protected theorem Path.ext : ∀ {γ₁ γ₂ : Path x y}, (γ₁ : I → X) = γ₂ → γ₁ = γ₂ := by
  rintro ⟨⟨x, h11⟩, h12, h13⟩ ⟨⟨x, h21⟩, h22, h23⟩ rfl
  -- ⊢ { toContinuousMap := ContinuousMap.mk x, source' := h12, target' := h13 } =  …
  rfl
  -- 🎉 no goals
#align path.ext Path.ext

namespace Path

@[simp]
theorem coe_mk_mk (f : I → X) (h₁) (h₂ : f 0 = x) (h₃ : f 1 = y) :
    ⇑(mk ⟨f, h₁⟩ h₂ h₃ : Path x y) = f :=
  rfl
#align path.coe_mk Path.coe_mk_mk
-- porting note: the name `Path.coe_mk` better refers to a new lemma below

variable (γ : Path x y)

@[continuity]
protected theorem continuous : Continuous γ :=
  γ.continuous_toFun
#align path.continuous Path.continuous

@[simp]
protected theorem source : γ 0 = x :=
  γ.source'
#align path.source Path.source

@[simp]
protected theorem target : γ 1 = y :=
  γ.target'
#align path.target Path.target

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def simps.apply : I → X :=
  γ
#align path.simps.apply Path.simps.apply

initialize_simps_projections Path (toFun → simps.apply, -toContinuousMap)

@[simp]
theorem coe_toContinuousMap : ⇑γ.toContinuousMap = γ :=
  rfl
#align path.coe_to_continuous_map Path.coe_toContinuousMap

-- porting note: this is needed because of the `Path.continuousMapClass` instance
@[simp]
theorem coe_mk : ⇑(γ : C(I, X)) = γ :=
  rfl

/-- Any function `φ : Π (a : α), Path (x a) (y a)` can be seen as a function `α × I → X`. -/
instance hasUncurryPath {X α : Type*} [TopologicalSpace X] {x y : α → X} :
    HasUncurry (∀ a : α, Path (x a) (y a)) (α × I) X :=
  ⟨fun φ p => φ p.1 p.2⟩
#align path.has_uncurry_path Path.hasUncurryPath

/-- The constant path from a point to itself -/
@[refl, simps]
def refl (x : X) : Path x x where
  toFun _t := x
  continuous_toFun := continuous_const
  source' := rfl
  target' := rfl
#align path.refl Path.refl

@[simp]
theorem refl_range {a : X} : range (Path.refl a) = {a} := by simp [Path.refl, CoeFun.coe]
                                                             -- 🎉 no goals
#align path.refl_range Path.refl_range

/-- The reverse of a path from `x` to `y`, as a path from `y` to `x` -/
@[symm, simps]
def symm (γ : Path x y) : Path y x where
  toFun := γ ∘ σ
  continuous_toFun := by continuity
                         -- 🎉 no goals
  source' := by simpa [-Path.target] using γ.target
                -- 🎉 no goals
  target' := by simpa [-Path.source] using γ.source
                -- 🎉 no goals
#align path.symm Path.symm

@[simp]
theorem symm_symm {γ : Path x y} : γ.symm.symm = γ := by
  ext t
  -- ⊢ ↑(symm (symm γ)) t = ↑γ t
  show γ (σ (σ t)) = γ t
  -- ⊢ ↑γ (σ (σ t)) = ↑γ t
  rw [unitInterval.symm_symm]
  -- 🎉 no goals
#align path.symm_symm Path.symm_symm

@[simp]
theorem refl_symm {a : X} : (Path.refl a).symm = Path.refl a := by
  ext
  -- ⊢ ↑(symm (refl a)) x✝ = ↑(refl a) x✝
  rfl
  -- 🎉 no goals
#align path.refl_symm Path.refl_symm

@[simp]
theorem symm_range {a b : X} (γ : Path a b) : range γ.symm = range γ := by
  ext x
  -- ⊢ x ∈ range ↑(symm γ) ↔ x ∈ range ↑γ
  simp only [mem_range, Path.symm, FunLike.coe, unitInterval.symm, SetCoe.exists, comp_apply,
    Subtype.coe_mk]
  constructor <;> rintro ⟨y, hy, hxy⟩ <;> refine' ⟨1 - y, mem_iff_one_sub_mem.mp hy, _⟩ <;>
  -- ⊢ (∃ x_1 h, ContinuousMap.toFun γ.toContinuousMap { val := 1 - x_1, property : …
                  -- ⊢ ∃ x_1 h, ContinuousMap.toFun γ.toContinuousMap { val := x_1, property := h } …
                  -- ⊢ ∃ x_1 h, ContinuousMap.toFun γ.toContinuousMap { val := 1 - x_1, property := …
                                          -- ⊢ ContinuousMap.toFun γ.toContinuousMap { val := 1 - y, property := (_ : 1 - y …
                                          -- ⊢ ContinuousMap.toFun γ.toContinuousMap { val := 1 - (1 - y), property := (_ : …
    convert hxy
    -- 🎉 no goals
    -- ⊢ 1 - (1 - y) = y
  simp
  -- 🎉 no goals
#align path.symm_range Path.symm_range

/-! #### Space of paths -/


open ContinuousMap

/- porting note: because of the new `FunLike` instance, we already have a coercion to `C(I, X)`
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
  continuous_eval'.comp <| (continuous_induced_dom (α := Path x y)).prod_map continuous_id
#align path.continuous_eval Path.continuous_eval

@[continuity]
theorem _root_.Continuous.path_eval {Y} [TopologicalSpace Y] {f : Y → Path x y} {g : Y → I}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun y => f y (g y) :=
  Continuous.comp continuous_eval (hf.prod_mk hg)
#align continuous.path_eval Continuous.path_eval

theorem continuous_uncurry_iff {Y} [TopologicalSpace Y] {g : Y → Path x y} :
    Continuous ↿g ↔ Continuous g :=
  Iff.symm <| continuous_induced_rng.trans
    ⟨fun h => continuous_uncurry_of_continuous ⟨_, h⟩,
    continuous_of_continuous_uncurry (fun (y : Y) ↦ ContinuousMap.mk (g y))⟩
#align path.continuous_uncurry_iff Path.continuous_uncurry_iff

/-- A continuous map extending a path to `ℝ`, constant before `0` and after `1`. -/
def extend : ℝ → X :=
  IccExtend zero_le_one γ
#align path.extend Path.extend

/-- See Note [continuity lemma statement]. -/
theorem _root_.Continuous.path_extend {γ : Y → Path x y} {f : Y → ℝ} (hγ : Continuous ↿γ)
    (hf : Continuous f) : Continuous fun t => (γ t).extend (f t) :=
  Continuous.IccExtend hγ hf
#align continuous.path_extend Continuous.path_extend

/-- A useful special case of `Continuous.path_extend`. -/
@[continuity]
theorem continuous_extend : Continuous γ.extend :=
  γ.continuous.Icc_extend'
#align path.continuous_extend Path.continuous_extend

theorem _root_.Filter.Tendsto.path_extend {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {l r : Y → X} {y : Y} {l₁ : Filter ℝ} {l₂ : Filter X} {γ : ∀ y, Path (l y) (r y)}
    (hγ : Tendsto (↿γ) (𝓝 y ×ˢ l₁.map (projIcc 0 1 zero_le_one)) l₂) :
    Tendsto (↿fun x => (γ x).extend) (𝓝 y ×ˢ l₁) l₂ :=
  Filter.Tendsto.IccExtend _ hγ
#align filter.tendsto.path_extend Filter.Tendsto.path_extend

theorem _root_.ContinuousAt.path_extend {g : Y → ℝ} {l r : Y → X} (γ : ∀ y, Path (l y) (r y))
    {y : Y} (hγ : ContinuousAt (↿γ) (y, projIcc 0 1 zero_le_one (g y))) (hg : ContinuousAt g y) :
    ContinuousAt (fun i => (γ i).extend (g i)) y :=
  hγ.IccExtend (fun x => γ x) hg
#align continuous_at.path_extend ContinuousAt.path_extend

@[simp]
theorem extend_extends {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b) {t : ℝ}
    (ht : t ∈ (Icc 0 1 : Set ℝ)) : γ.extend t = γ ⟨t, ht⟩ :=
  IccExtend_of_mem _ γ ht
#align path.extend_extends Path.extend_extends

theorem extend_zero : γ.extend 0 = x := by simp
                                           -- 🎉 no goals
#align path.extend_zero Path.extend_zero

theorem extend_one : γ.extend 1 = y := by simp
                                          -- 🎉 no goals
#align path.extend_one Path.extend_one

@[simp]
theorem extend_extends' {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b)
    (t : (Icc 0 1 : Set ℝ)) : γ.extend t = γ t :=
  IccExtend_val _ γ t
#align path.extend_extends' Path.extend_extends'

@[simp]
theorem extend_range {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b) :
    range γ.extend = range γ :=
  IccExtend_range _ γ
#align path.extend_range Path.extend_range

theorem extend_of_le_zero {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b) {t : ℝ}
    (ht : t ≤ 0) : γ.extend t = a :=
  (IccExtend_of_le_left _ _ ht).trans γ.source
#align path.extend_of_le_zero Path.extend_of_le_zero

theorem extend_of_one_le {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b) {t : ℝ}
    (ht : 1 ≤ t) : γ.extend t = b :=
  (IccExtend_of_right_le _ _ ht).trans γ.target
#align path.extend_of_one_le Path.extend_of_one_le

@[simp]
theorem refl_extend {X : Type*} [TopologicalSpace X] {a : X} : (Path.refl a).extend = fun _ => a :=
  rfl
#align path.refl_extend Path.refl_extend

/-- The path obtained from a map defined on `ℝ` by restriction to the unit interval. -/
def ofLine {f : ℝ → X} (hf : ContinuousOn f I) (h₀ : f 0 = x) (h₁ : f 1 = y) : Path x y where
  toFun := f ∘ ((↑) : unitInterval → ℝ)
  continuous_toFun := hf.comp_continuous continuous_subtype_val Subtype.prop
  source' := h₀
  target' := h₁
#align path.of_line Path.ofLine

theorem ofLine_mem {f : ℝ → X} (hf : ContinuousOn f I) (h₀ : f 0 = x) (h₁ : f 1 = y) :
    ∀ t, ofLine hf h₀ h₁ t ∈ f '' I := fun ⟨t, t_in⟩ => ⟨t, t_in, rfl⟩
#align path.of_line_mem Path.ofLine_mem

attribute [local simp] Iic_def

/-- Concatenation of two paths from `x` to `y` and from `y` to `z`, putting the first
path on `[0, 1/2]` and the second one on `[1/2, 1]`. -/
@[trans]
def trans (γ : Path x y) (γ' : Path y z) : Path x z where
  toFun := (fun t : ℝ => if t ≤ 1 / 2 then γ.extend (2 * t) else γ'.extend (2 * t - 1)) ∘ (↑)
  continuous_toFun := by
    refine'
      (Continuous.if_le _ _ continuous_id continuous_const (by norm_num)).comp
        continuous_subtype_val <;>
    continuity
    -- 🎉 no goals
    -- 🎉 no goals
  source' := by norm_num
                -- 🎉 no goals
  target' := by norm_num
                -- 🎉 no goals
#align path.trans Path.trans

theorem trans_apply (γ : Path x y) (γ' : Path y z) (t : I) :
    (γ.trans γ') t =
      if h : (t : ℝ) ≤ 1 / 2 then γ ⟨2 * t, (mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩⟩
      else γ' ⟨2 * t - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t.2.2⟩⟩ :=
  show ite _ _ _ = _ by split_ifs <;> rw [extend_extends]
                        -- ⊢ extend γ (2 * ↑t) = ↑γ { val := 2 * ↑t, property := (_ : 2 * ↑t ∈ I) }
                                      -- 🎉 no goals
                                      -- 🎉 no goals
#align path.trans_apply Path.trans_apply

@[simp]
theorem trans_symm (γ : Path x y) (γ' : Path y z) : (γ.trans γ').symm = γ'.symm.trans γ.symm := by
  ext t
  -- ⊢ ↑(symm (trans γ γ')) t = ↑(trans (symm γ') (symm γ)) t
  simp only [trans_apply, ← one_div, symm_apply, not_le, Function.comp_apply]
  -- ⊢ (if h : ↑(σ t) ≤ 1 / 2 then ↑γ { val := 2 * ↑(σ t), property := (_ : 2 * ↑(σ …
  split_ifs with h h₁ h₂ <;> rw [coe_symm_eq] at h
                             -- ⊢ ↑γ { val := 2 * ↑(σ t), property := (_ : 2 * ↑(σ t) ∈ I) } = ↑γ' (σ { val := …
                             -- ⊢ ↑γ { val := 2 * ↑(σ t), property := (_ : 2 * ↑(σ t) ∈ I) } = ↑γ (σ { val :=  …
                             -- ⊢ ↑γ' { val := 2 * ↑(σ t) - 1, property := (_ : 2 * ↑(σ t) - 1 ∈ I) } = ↑γ' (σ …
                             -- ⊢ ↑γ' { val := 2 * ↑(σ t) - 1, property := (_ : 2 * ↑(σ t) - 1 ∈ I) } = ↑γ (σ  …
  · have ht : (t : ℝ) = 1 / 2 := by linarith
    -- ⊢ ↑γ { val := 2 * ↑(σ t), property := (_ : 2 * ↑(σ t) ∈ I) } = ↑γ' (σ { val := …
    norm_num [ht]
    -- 🎉 no goals
  · refine' congr_arg _ (Subtype.ext _)
    -- ⊢ ↑{ val := 2 * ↑(σ t), property := (_ : 2 * ↑(σ t) ∈ I) } = ↑(σ { val := 2 *  …
    norm_num [sub_sub_eq_add_sub, mul_sub]
    -- 🎉 no goals
  · refine' congr_arg _ (Subtype.ext _)
    -- ⊢ ↑{ val := 2 * ↑(σ t) - 1, property := (_ : 2 * ↑(σ t) - 1 ∈ I) } = ↑(σ { val …
    norm_num [mul_sub, h]
    -- ⊢ 2 - 2 * ↑t - 1 = 1 - 2 * ↑t
    ring -- TODO norm_num should really do this
    -- 🎉 no goals
  · exfalso
    -- ⊢ False
    linarith
    -- 🎉 no goals
#align path.trans_symm Path.trans_symm

@[simp]
theorem refl_trans_refl {X : Type*} [TopologicalSpace X] {a : X} :
    (Path.refl a).trans (Path.refl a) = Path.refl a := by
  ext
  -- ⊢ ↑(trans (refl a) (refl a)) x✝ = ↑(refl a) x✝
  simp only [Path.trans, ite_self, one_div, Path.refl_extend]
  -- ⊢ ↑{ toContinuousMap := ContinuousMap.mk ((fun t => a) ∘ Subtype.val), source' …
  rfl
  -- 🎉 no goals
#align path.refl_trans_refl Path.refl_trans_refl

theorem trans_range {X : Type*} [TopologicalSpace X] {a b c : X} (γ₁ : Path a b) (γ₂ : Path b c) :
    range (γ₁.trans γ₂) = range γ₁ ∪ range γ₂ := by
  rw [Path.trans]
  -- ⊢ range ↑{ toContinuousMap := ContinuousMap.mk ((fun t => if t ≤ 1 / 2 then ex …
  apply eq_of_subset_of_subset
  -- ⊢ range ↑{ toContinuousMap := ContinuousMap.mk ((fun t => if t ≤ 1 / 2 then ex …
  · rintro x ⟨⟨t, ht0, ht1⟩, hxt⟩
    -- ⊢ x ∈ range ↑γ₁ ∪ range ↑γ₂
    by_cases h : t ≤ 1 / 2
    -- ⊢ x ∈ range ↑γ₁ ∪ range ↑γ₂
    · left
      -- ⊢ x ∈ range ↑γ₁
      use ⟨2 * t, ⟨by linarith, by linarith⟩⟩
      -- ⊢ ↑γ₁ { val := 2 * t, property := (_ : 0 ≤ 2 * t ∧ 2 * t ≤ 1) } = x
      rw [← γ₁.extend_extends]
      -- ⊢ extend γ₁ (2 * t) = x
      rwa [coe_mk_mk, Function.comp_apply, if_pos h] at hxt
      -- 🎉 no goals
    · right
      -- ⊢ x ∈ range ↑γ₂
      use ⟨2 * t - 1, ⟨by linarith, by linarith⟩⟩
      -- ⊢ ↑γ₂ { val := 2 * t - 1, property := (_ : 0 ≤ 2 * t - 1 ∧ 2 * t - 1 ≤ 1) } = x
      rw [← γ₂.extend_extends]
      -- ⊢ extend γ₂ (2 * t - 1) = x
      rwa [coe_mk_mk, Function.comp_apply, if_neg h] at hxt
      -- 🎉 no goals
  · rintro x (⟨⟨t, ht0, ht1⟩, hxt⟩ | ⟨⟨t, ht0, ht1⟩, hxt⟩)
    -- ⊢ x ∈ range ↑{ toContinuousMap := ContinuousMap.mk ((fun t => if t ≤ 1 / 2 the …
    · use ⟨t / 2, ⟨by linarith, by linarith⟩⟩
      -- ⊢ ↑{ toContinuousMap := ContinuousMap.mk ((fun t => if t ≤ 1 / 2 then extend γ …
      have : t / 2 ≤ 1 / 2 := (div_le_div_right (zero_lt_two : (0 : ℝ) < 2)).mpr ht1
      -- ⊢ ↑{ toContinuousMap := ContinuousMap.mk ((fun t => if t ≤ 1 / 2 then extend γ …
      rw [coe_mk_mk, Function.comp_apply, if_pos this, Subtype.coe_mk]
      -- ⊢ extend γ₁ (2 * (t / 2)) = x
      ring_nf
      -- ⊢ extend γ₁ t = x
      rwa [γ₁.extend_extends]
      -- 🎉 no goals
    · by_cases h : t = 0
      -- ⊢ x ∈ range ↑{ toContinuousMap := ContinuousMap.mk ((fun t => if t ≤ 1 / 2 the …
      · use ⟨1 / 2, ⟨by linarith, by linarith⟩⟩
        -- ⊢ ↑{ toContinuousMap := ContinuousMap.mk ((fun t => if t ≤ 1 / 2 then extend γ …
        rw [coe_mk_mk, Function.comp_apply, if_pos le_rfl, Subtype.coe_mk,
          mul_one_div_cancel (two_ne_zero' ℝ)]
        rw [γ₁.extend_one]
        -- ⊢ b = x
        rwa [← γ₂.extend_extends, h, γ₂.extend_zero] at hxt
        -- 🎉 no goals
      · use ⟨(t + 1) / 2, ⟨by linarith, by linarith⟩⟩
        -- ⊢ ↑{ toContinuousMap := ContinuousMap.mk ((fun t => if t ≤ 1 / 2 then extend γ …
        replace h : t ≠ 0 := h
        -- ⊢ ↑{ toContinuousMap := ContinuousMap.mk ((fun t => if t ≤ 1 / 2 then extend γ …
        have ht0 := lt_of_le_of_ne ht0 h.symm
        -- ⊢ ↑{ toContinuousMap := ContinuousMap.mk ((fun t => if t ≤ 1 / 2 then extend γ …
        have : ¬(t + 1) / 2 ≤ 1 / 2 := by
          rw [not_le]
          linarith
        rw [coe_mk_mk, Function.comp_apply, Subtype.coe_mk, if_neg this]
        -- ⊢ extend γ₂ (2 * ((t + 1) / 2) - 1) = x
        ring_nf
        -- ⊢ extend γ₂ t = x
        rwa [γ₂.extend_extends]
        -- 🎉 no goals
#align path.trans_range Path.trans_range

/-- Image of a path from `x` to `y` by a map which is continuous on the path. -/
def map' (γ : Path x y) {Y : Type*} [TopologicalSpace Y] {f : X → Y}
    (h : ContinuousOn f (range γ)) : Path (f x) (f y) where
  toFun := f ∘ γ
  continuous_toFun := h.comp_continuous γ.continuous (fun x ↦ mem_range_self x)
  source' := by simp
                -- 🎉 no goals
  target' := by simp
                -- 🎉 no goals

/-- Image of a path from `x` to `y` by a continuous map -/
def map (γ : Path x y) {Y : Type*} [TopologicalSpace Y] {f : X → Y} (h : Continuous f) :
    Path (f x) (f y) := γ.map' h.continuousOn
#align path.map Path.map

@[simp]
theorem map_coe (γ : Path x y) {Y : Type*} [TopologicalSpace Y] {f : X → Y} (h : Continuous f) :
    (γ.map h : I → Y) = f ∘ γ := by
  ext t
  -- ⊢ ↑(map γ h) t = (f ∘ ↑γ) t
  rfl
  -- 🎉 no goals
#align path.map_coe Path.map_coe

@[simp]
theorem map_symm (γ : Path x y) {Y : Type*} [TopologicalSpace Y] {f : X → Y} (h : Continuous f) :
    (γ.map h).symm = γ.symm.map h :=
  rfl
#align path.map_symm Path.map_symm

@[simp]
theorem map_trans (γ : Path x y) (γ' : Path y z) {Y : Type*} [TopologicalSpace Y] {f : X → Y}
    (h : Continuous f) : (γ.trans γ').map h = (γ.map h).trans (γ'.map h) := by
  ext t
  -- ⊢ ↑(map (trans γ γ') h) t = ↑(trans (map γ h) (map γ' h)) t
  rw [trans_apply, map_coe, Function.comp_apply, trans_apply]
  -- ⊢ f (if h : ↑t ≤ 1 / 2 then ↑γ { val := 2 * ↑t, property := (_ : 2 * ↑t ∈ I) } …
  split_ifs <;> rfl
  -- ⊢ f (↑γ { val := 2 * ↑t, property := (_ : 2 * ↑t ∈ I) }) = ↑(map γ h) { val := …
                -- 🎉 no goals
                -- 🎉 no goals
#align path.map_trans Path.map_trans

@[simp]
theorem map_id (γ : Path x y) : γ.map continuous_id = γ := by
  ext
  -- ⊢ ↑(map γ (_ : Continuous id)) x✝ = ↑γ x✝
  rfl
  -- 🎉 no goals
#align path.map_id Path.map_id

@[simp]
theorem map_map (γ : Path x y) {Y : Type*} [TopologicalSpace Y] {Z : Type*} [TopologicalSpace Z]
    {f : X → Y} (hf : Continuous f) {g : Y → Z} (hg : Continuous g) :
    (γ.map hf).map hg = γ.map (hg.comp hf) := by
  ext
  -- ⊢ ↑(map (map γ hf) hg) x✝ = ↑(map γ (_ : Continuous (g ∘ f))) x✝
  rfl
  -- 🎉 no goals
#align path.map_map Path.map_map

/-- Casting a path from `x` to `y` to a path from `x'` to `y'` when `x' = x` and `y' = y` -/
def cast (γ : Path x y) {x' y'} (hx : x' = x) (hy : y' = y) : Path x' y' where
  toFun := γ
  continuous_toFun := γ.continuous
  source' := by simp [hx]
                -- 🎉 no goals
  target' := by simp [hy]
                -- 🎉 no goals
#align path.cast Path.cast

@[simp]
theorem symm_cast {X : Type*} [TopologicalSpace X] {a₁ a₂ b₁ b₂ : X} (γ : Path a₂ b₂)
    (ha : a₁ = a₂) (hb : b₁ = b₂) : (γ.cast ha hb).symm = γ.symm.cast hb ha :=
  rfl
#align path.symm_cast Path.symm_cast

@[simp]
theorem trans_cast {X : Type*} [TopologicalSpace X] {a₁ a₂ b₁ b₂ c₁ c₂ : X} (γ : Path a₂ b₂)
    (γ' : Path b₂ c₂) (ha : a₁ = a₂) (hb : b₁ = b₂) (hc : c₁ = c₂) :
    (γ.cast ha hb).trans (γ'.cast hb hc) = (γ.trans γ').cast ha hc :=
  rfl
#align path.trans_cast Path.trans_cast

@[simp]
theorem cast_coe (γ : Path x y) {x' y'} (hx : x' = x) (hy : y' = y) : (γ.cast hx hy : I → X) = γ :=
  rfl
#align path.cast_coe Path.cast_coe

@[continuity]
theorem symm_continuous_family {X ι : Type*} [TopologicalSpace X] [TopologicalSpace ι]
    {a b : ι → X} (γ : ∀ t : ι, Path (a t) (b t)) (h : Continuous ↿γ) :
    Continuous ↿fun t => (γ t).symm :=
  h.comp (continuous_id.prod_map continuous_symm)
#align path.symm_continuous_family Path.symm_continuous_family

@[continuity]
theorem continuous_symm : Continuous (symm : Path x y → Path y x) :=
  continuous_uncurry_iff.mp <| symm_continuous_family _ (continuous_fst.path_eval continuous_snd)
#align path.continuous_symm Path.continuous_symm

@[continuity]
theorem continuous_uncurry_extend_of_continuous_family {X ι : Type*} [TopologicalSpace X]
    [TopologicalSpace ι] {a b : ι → X} (γ : ∀ t : ι, Path (a t) (b t)) (h : Continuous ↿γ) :
    Continuous ↿fun t => (γ t).extend := by
  refine' h.comp (continuous_id.prod_map continuous_projIcc)
  -- ⊢ 0 ≤ 1
  exact zero_le_one
  -- 🎉 no goals
#align path.continuous_uncurry_extend_of_continuous_family Path.continuous_uncurry_extend_of_continuous_family

@[continuity]
theorem trans_continuous_family {X ι : Type*} [TopologicalSpace X] [TopologicalSpace ι]
    {a b c : ι → X} (γ₁ : ∀ t : ι, Path (a t) (b t)) (h₁ : Continuous ↿γ₁)
    (γ₂ : ∀ t : ι, Path (b t) (c t)) (h₂ : Continuous ↿γ₂) :
    Continuous ↿fun t => (γ₁ t).trans (γ₂ t) := by
  have h₁' := Path.continuous_uncurry_extend_of_continuous_family γ₁ h₁
  -- ⊢ Continuous ↿fun t => trans (γ₁ t) (γ₂ t)
  have h₂' := Path.continuous_uncurry_extend_of_continuous_family γ₂ h₂
  -- ⊢ Continuous ↿fun t => trans (γ₁ t) (γ₂ t)
  simp only [HasUncurry.uncurry, CoeFun.coe, Path.trans, (· ∘ ·)]
  -- ⊢ Continuous fun p => ↑{ toContinuousMap := ContinuousMap.mk fun x => if ↑x ≤  …
  refine' Continuous.if_le _ _ (continuous_subtype_val.comp continuous_snd) continuous_const _
  · change
      Continuous ((fun p : ι × ℝ => (γ₁ p.1).extend p.2) ∘ Prod.map id (fun x => 2 * x : I → ℝ))
    exact h₁'.comp (continuous_id.prod_map <| continuous_const.mul continuous_subtype_val)
    -- 🎉 no goals
  · change
      Continuous ((fun p : ι × ℝ => (γ₂ p.1).extend p.2) ∘ Prod.map id (fun x => 2 * x - 1 : I → ℝ))
    exact
      h₂'.comp
        (continuous_id.prod_map <|
          (continuous_const.mul continuous_subtype_val).sub continuous_const)
  · rintro st hst
    -- ⊢ extend (γ₁ st.fst) (2 * ↑st.snd) = extend (γ₂ st.fst) (2 * ↑st.snd - 1)
    simp [hst, mul_inv_cancel (two_ne_zero' ℝ)]
    -- 🎉 no goals
#align path.trans_continuous_family Path.trans_continuous_family

@[continuity]
theorem _root_.Continuous.path_trans {f : Y → Path x y} {g : Y → Path y z} :
    Continuous f → Continuous g → Continuous fun t => (f t).trans (g t) := by
  intro hf hg
  -- ⊢ Continuous fun t => trans (f t) (g t)
  apply continuous_uncurry_iff.mp
  -- ⊢ Continuous ↿fun t => trans (f t) (g t)
  exact trans_continuous_family _ (continuous_uncurry_iff.mpr hf) _ (continuous_uncurry_iff.mpr hg)
  -- 🎉 no goals
#align continuous.path_trans Continuous.path_trans

@[continuity]
theorem continuous_trans {x y z : X} : Continuous fun ρ : Path x y × Path y z => ρ.1.trans ρ.2 :=
  continuous_fst.path_trans continuous_snd
#align path.continuous_trans Path.continuous_trans

/-! #### Product of paths -/


section Prod

variable {a₁ a₂ a₃ : X} {b₁ b₂ b₃ : Y}

/-- Given a path in `X` and a path in `Y`, we can take their pointwise product to get a path in
`X × Y`. -/
protected def prod (γ₁ : Path a₁ a₂) (γ₂ : Path b₁ b₂) : Path (a₁, b₁) (a₂, b₂) where
  toContinuousMap := ContinuousMap.prodMk γ₁.toContinuousMap γ₂.toContinuousMap
  source' := by simp
                -- 🎉 no goals
  target' := by simp
                -- 🎉 no goals
#align path.prod Path.prod

@[simp]
theorem prod_coe (γ₁ : Path a₁ a₂) (γ₂ : Path b₁ b₂) :
    ⇑(γ₁.prod γ₂) = fun t => (γ₁ t, γ₂ t) :=
  rfl
#align path.prod_coe_fn Path.prod_coe

/-- Path composition commutes with products -/
theorem trans_prod_eq_prod_trans (γ₁ : Path a₁ a₂) (δ₁ : Path a₂ a₃) (γ₂ : Path b₁ b₂)
    (δ₂ : Path b₂ b₃) : (γ₁.prod γ₂).trans (δ₁.prod δ₂) = (γ₁.trans δ₁).prod (γ₂.trans δ₂) := by
  ext t <;>
  -- ⊢ (↑(trans (Path.prod γ₁ γ₂) (Path.prod δ₁ δ₂)) t).fst = (↑(Path.prod (trans γ …
  unfold Path.trans <;>
  -- ⊢ (↑{ toContinuousMap := ContinuousMap.mk ((fun t => if t ≤ 1 / 2 then extend  …
  -- ⊢ (↑{ toContinuousMap := ContinuousMap.mk ((fun t => if t ≤ 1 / 2 then extend  …
  simp only [Path.coe_mk_mk, Path.prod_coe, Function.comp_apply] <;>
  -- ⊢ (if ↑t ≤ 1 / 2 then extend (Path.prod γ₁ γ₂) (2 * ↑t) else extend (Path.prod …
  -- ⊢ (if ↑t ≤ 1 / 2 then extend (Path.prod γ₁ γ₂) (2 * ↑t) else extend (Path.prod …
  split_ifs <;>
  -- ⊢ (extend (Path.prod γ₁ γ₂) (2 * ↑t)).fst = extend γ₁ (2 * ↑t)
  -- ⊢ (extend (Path.prod γ₁ γ₂) (2 * ↑t)).snd = extend γ₂ (2 * ↑t)
  rfl
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
#align path.trans_prod_eq_prod_trans Path.trans_prod_eq_prod_trans

end Prod

section Pi

variable {χ : ι → Type*} [∀ i, TopologicalSpace (χ i)] {as bs cs : ∀ i, χ i}

/-- Given a family of paths, one in each Xᵢ, we take their pointwise product to get a path in
Π i, Xᵢ. -/
protected def pi (γ : ∀ i, Path (as i) (bs i)) : Path as bs where
  toContinuousMap := ContinuousMap.pi fun i => (γ i).toContinuousMap
  source' := by simp
                -- 🎉 no goals
  target' := by simp
                -- 🎉 no goals
#align path.pi Path.pi

@[simp]
theorem pi_coe (γ : ∀ i, Path (as i) (bs i)) : ⇑(Path.pi γ) = fun t i => γ i t :=
  rfl
#align path.pi_coe_fn Path.pi_coe

/-- Path composition commutes with products -/
theorem trans_pi_eq_pi_trans (γ₀ : ∀ i, Path (as i) (bs i)) (γ₁ : ∀ i, Path (bs i) (cs i)) :
    (Path.pi γ₀).trans (Path.pi γ₁) = Path.pi fun i => (γ₀ i).trans (γ₁ i) := by
  ext t i
  -- ⊢ ↑(trans (Path.pi γ₀) (Path.pi γ₁)) t i = ↑(Path.pi fun i => trans (γ₀ i) (γ₁ …
  unfold Path.trans
  -- ⊢ ↑{ toContinuousMap := ContinuousMap.mk ((fun t => if t ≤ 1 / 2 then extend ( …
  simp only [Path.coe_mk_mk, Function.comp_apply, pi_coe]
  -- ⊢ ite (↑t ≤ 1 / 2) (extend (Path.pi γ₀) (2 * ↑t)) (extend (Path.pi γ₁) (2 * ↑t …
  split_ifs <;> rfl
  -- ⊢ extend (Path.pi γ₀) (2 * ↑t) i = extend (γ₀ i) (2 * ↑t)
                -- 🎉 no goals
                -- 🎉 no goals
#align path.trans_pi_eq_pi_trans Path.trans_pi_eq_pi_trans

end Pi

/-! #### Pointwise multiplication/addition of two paths in a topological (additive) group -/


/-- Pointwise multiplication of paths in a topological group. The additive version is probably more
useful. -/
@[to_additive "Pointwise addition of paths in a topological additive group."]
protected def mul [Mul X] [ContinuousMul X] {a₁ b₁ a₂ b₂ : X} (γ₁ : Path a₁ b₁) (γ₂ : Path a₂ b₂) :
    Path (a₁ * a₂) (b₁ * b₂) :=
  (γ₁.prod γ₂).map continuous_mul
#align path.mul Path.mul
#align path.add Path.add

@[to_additive]
protected theorem mul_apply [Mul X] [ContinuousMul X] {a₁ b₁ a₂ b₂ : X} (γ₁ : Path a₁ b₁)
    (γ₂ : Path a₂ b₂) (t : unitInterval) : (γ₁.mul γ₂) t = γ₁ t * γ₂ t :=
  rfl
#align path.mul_apply Path.mul_apply
#align path.add_apply Path.add_apply

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
    -- ⊢ extend γ (if (if t₀ ≤ ↑0 then ↑0 else t₀) ≤ t₁ then if t₀ ≤ ↑0 then ↑0 else  …
    norm_cast
    -- ⊢ extend γ (if (if t₀ ≤ 0 then 0 else t₀) ≤ t₁ then if t₀ ≤ 0 then 0 else t₀ e …
    split_ifs with h₁ h₂ h₃ h₄
    · simp [γ.extend_of_le_zero h₁]
      -- 🎉 no goals
    · congr
      -- ⊢ 0 = t₁
      linarith
      -- 🎉 no goals
    · have h₄ : t₁ ≤ 0 := le_of_lt (by simpa using h₂)
      -- ⊢ extend γ t₁ = extend γ t₀
      simp [γ.extend_of_le_zero h₄, γ.extend_of_le_zero h₁]
      -- 🎉 no goals
    all_goals rfl
    -- 🎉 no goals
  target' := by
    simp only [min_def, max_def']
    -- ⊢ extend γ (if (if t₀ ≤ ↑1 then ↑1 else t₀) ≤ t₁ then if t₀ ≤ ↑1 then ↑1 else  …
    norm_cast
    -- ⊢ extend γ (if (if t₀ ≤ 1 then 1 else t₀) ≤ t₁ then if t₀ ≤ 1 then 1 else t₀ e …
    split_ifs with h₁ h₂ h₃
    · simp [γ.extend_of_one_le h₂]
      -- 🎉 no goals
    · rfl
      -- 🎉 no goals
    · have h₄ : 1 ≤ t₀ := le_of_lt (by simpa using h₁)
      -- ⊢ extend γ t₀ = extend γ t₁
      simp [γ.extend_of_one_le h₄, γ.extend_of_one_le (h₄.trans h₃)]
      -- 🎉 no goals
    · rfl
      -- 🎉 no goals
#align path.truncate Path.truncate

/-- `γ.truncateOfLE t₀ t₁ h`, where `h : t₀ ≤ t₁` is `γ.truncate t₀ t₁`
  casted as a path from `γ.extend t₀` to `γ.extend t₁`. -/
def truncateOfLE {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b) {t₀ t₁ : ℝ}
    (h : t₀ ≤ t₁) : Path (γ.extend t₀) (γ.extend t₁) :=
  (γ.truncate t₀ t₁).cast (by rw [min_eq_left h]) rfl
                              -- 🎉 no goals
#align path.truncate_of_le Path.truncateOfLE

theorem truncate_range {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b) {t₀ t₁ : ℝ} :
    range (γ.truncate t₀ t₁) ⊆ range γ := by
  rw [← γ.extend_range]
  -- ⊢ range ↑(truncate γ t₀ t₁) ⊆ range (extend γ)
  simp only [range_subset_iff, SetCoe.exists, SetCoe.forall]
  -- ⊢ ∀ (x : ℝ) (h : x ∈ I), ↑(truncate γ t₀ t₁) { val := x, property := h } ∈ ran …
  intro x _hx
  -- ⊢ ↑(truncate γ t₀ t₁) { val := x, property := _hx } ∈ range (extend γ)
  simp only [FunLike.coe, Path.truncate, mem_range_self]
  -- 🎉 no goals
#align path.truncate_range Path.truncate_range

/-- For a path `γ`, `γ.truncate` gives a "continuous family of paths", by which we
  mean the uncurried function which maps `(t₀, t₁, s)` to `γ.truncate t₀ t₁ s` is continuous. -/
@[continuity]
theorem truncate_continuous_family {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b) :
    Continuous (fun x => γ.truncate x.1 x.2.1 x.2.2 : ℝ × ℝ × I → X) :=
  γ.continuous_extend.comp
    (((continuous_subtype_val.comp (continuous_snd.comp continuous_snd)).max continuous_fst).min
      (continuous_fst.comp continuous_snd))
#align path.truncate_continuous_family Path.truncate_continuous_family

@[continuity]
theorem truncate_const_continuous_family {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b)
    (t : ℝ) : Continuous ↿(γ.truncate t) := by
  have key : Continuous (fun x => (t, x) : ℝ × I → ℝ × ℝ × I) := by continuity
  -- ⊢ Continuous ↿(truncate γ t)
  exact γ.truncate_continuous_family.comp key
  -- 🎉 no goals
#align path.truncate_const_continuous_family Path.truncate_const_continuous_family

@[simp]
theorem truncate_self {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b) (t : ℝ) :
    γ.truncate t t = (Path.refl <| γ.extend t).cast (by rw [min_self]) rfl := by
                                                        -- 🎉 no goals
  ext x
  -- ⊢ ↑(truncate γ t t) x = ↑(cast (refl (extend γ t)) (_ : extend γ (min t t) = e …
  rw [cast_coe]
  -- ⊢ ↑(truncate γ t t) x = ↑(refl (extend γ t)) x
  simp only [truncate, FunLike.coe, refl, min_def, max_def]
  -- ⊢ extend γ (if (if ↑x ≤ t then t else ↑x) ≤ t then if ↑x ≤ t then t else ↑x el …
  split_ifs with h₁ h₂ <;> congr
                           -- 🎉 no goals
                           -- 🎉 no goals
                           -- 🎉 no goals
#align path.truncate_self Path.truncate_self

@[simp 1001] -- porting note: increase `simp` priority so left-hand side doesn't simplify
theorem truncate_zero_zero {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b) :
    γ.truncate 0 0 = (Path.refl a).cast (by rw [min_self, γ.extend_zero]) γ.extend_zero := by
                                            -- 🎉 no goals
  convert γ.truncate_self 0
  -- 🎉 no goals
#align path.truncate_zero_zero Path.truncate_zero_zero

@[simp 1001] -- porting note: increase `simp` priority so left-hand side doesn't simplify
theorem truncate_one_one {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b) :
    γ.truncate 1 1 = (Path.refl b).cast (by rw [min_self, γ.extend_one]) γ.extend_one := by
                                            -- 🎉 no goals
  convert γ.truncate_self 1
  -- 🎉 no goals
#align path.truncate_one_one Path.truncate_one_one

@[simp]
theorem truncate_zero_one {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b) :
    γ.truncate 0 1 = γ.cast (by simp [zero_le_one, extend_zero]) (by simp) := by
                                -- 🎉 no goals
                                                                     -- 🎉 no goals
  ext x
  -- ⊢ ↑(truncate γ 0 1) x = ↑(cast γ (_ : extend γ (min 0 1) = a) (_ : extend γ 1  …
  rw [cast_coe]
  -- ⊢ ↑(truncate γ 0 1) x = ↑γ x
  have : ↑x ∈ (Icc 0 1 : Set ℝ) := x.2
  -- ⊢ ↑(truncate γ 0 1) x = ↑γ x
  rw [truncate, coe_mk_mk, max_eq_left this.1, min_eq_left this.2, extend_extends']
  -- 🎉 no goals
#align path.truncate_zero_one Path.truncate_zero_one

/-! #### Reparametrising a path -/


/-- Given a path `γ` and a function `f : I → I` where `f 0 = 0` and `f 1 = 1`, `γ.reparam f` is the
path defined by `γ ∘ f`.
-/
def reparam (γ : Path x y) (f : I → I) (hfcont : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    Path x y where
  toFun := γ ∘ f
  continuous_toFun := by continuity
                         -- 🎉 no goals
  source' := by simp [hf₀]
                -- 🎉 no goals
  target' := by simp [hf₁]
                -- 🎉 no goals
#align path.reparam Path.reparam

@[simp]
theorem coe_reparam (γ : Path x y) {f : I → I} (hfcont : Continuous f) (hf₀ : f 0 = 0)
    (hf₁ : f 1 = 1) : ⇑(γ.reparam f hfcont hf₀ hf₁) = γ ∘ f :=
  rfl
#align path.coe_to_fun Path.coe_reparam
-- porting note: this seems like it was poorly named (was: `coe_to_fun`)

@[simp]
theorem reparam_id (γ : Path x y) : γ.reparam id continuous_id rfl rfl = γ := by
  ext
  -- ⊢ ↑(reparam γ id (_ : Continuous id) (_ : id 0 = id 0) (_ : id 1 = id 1)) x✝ = …
  rfl
  -- 🎉 no goals
#align path.reparam_id Path.reparam_id

theorem range_reparam (γ : Path x y) {f : I → I} (hfcont : Continuous f) (hf₀ : f 0 = 0)
    (hf₁ : f 1 = 1) : range (γ.reparam f hfcont hf₀ hf₁) = range γ := by
  change range (γ ∘ f) = range γ
  -- ⊢ range (↑γ ∘ f) = range ↑γ
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
  -- 🎉 no goals
#align path.range_reparam Path.range_reparam

theorem refl_reparam {f : I → I} (hfcont : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    (refl x).reparam f hfcont hf₀ hf₁ = refl x := by
  ext
  -- ⊢ ↑(reparam (refl x) f hfcont hf₀ hf₁) x✝ = ↑(refl x) x✝
  simp
  -- 🎉 no goals
#align path.refl_reparam Path.refl_reparam

end Path

/-! ### Being joined by a path -/


/-- The relation "being joined by a path". This is an equivalence relation. -/
def Joined (x y : X) : Prop :=
  Nonempty (Path x y)
#align joined Joined

@[refl]
theorem Joined.refl (x : X) : Joined x x :=
  ⟨Path.refl x⟩
#align joined.refl Joined.refl

/-- When two points are joined, choose some path from `x` to `y`. -/
def Joined.somePath (h : Joined x y) : Path x y :=
  Nonempty.some h
#align joined.some_path Joined.somePath

@[symm]
theorem Joined.symm {x y : X} (h : Joined x y) : Joined y x :=
  ⟨h.somePath.symm⟩
#align joined.symm Joined.symm

@[trans]
theorem Joined.trans {x y z : X} (hxy : Joined x y) (hyz : Joined y z) : Joined x z :=
  ⟨hxy.somePath.trans hyz.somePath⟩
#align joined.trans Joined.trans

variable (X)

/-- The setoid corresponding the equivalence relation of being joined by a continuous path. -/
def pathSetoid : Setoid X where
  r := Joined
  iseqv := Equivalence.mk Joined.refl Joined.symm Joined.trans
#align path_setoid pathSetoid

/-- The quotient type of points of a topological space modulo being joined by a continuous path. -/
def ZerothHomotopy :=
  Quotient (pathSetoid X)
#align zeroth_homotopy ZerothHomotopy

instance ZerothHomotopy.inhabited : Inhabited (ZerothHomotopy ℝ) :=
  ⟨@Quotient.mk' ℝ (pathSetoid ℝ) 0⟩

variable {X}

/-! ### Being joined by a path inside a set -/


/-- The relation "being joined by a path in `F`". Not quite an equivalence relation since it's not
reflexive for points that do not belong to `F`. -/
def JoinedIn (F : Set X) (x y : X) : Prop :=
  ∃ γ : Path x y, ∀ t, γ t ∈ F
#align joined_in JoinedIn

variable {F : Set X}

theorem JoinedIn.mem (h : JoinedIn F x y) : x ∈ F ∧ y ∈ F := by
  rcases h with ⟨γ, γ_in⟩
  -- ⊢ x ∈ F ∧ y ∈ F
  have : γ 0 ∈ F ∧ γ 1 ∈ F := by constructor <;> apply γ_in
  -- ⊢ x ∈ F ∧ y ∈ F
  simpa using this
  -- 🎉 no goals
#align joined_in.mem JoinedIn.mem

theorem JoinedIn.source_mem (h : JoinedIn F x y) : x ∈ F :=
  h.mem.1
#align joined_in.source_mem JoinedIn.source_mem

theorem JoinedIn.target_mem (h : JoinedIn F x y) : y ∈ F :=
  h.mem.2
#align joined_in.target_mem JoinedIn.target_mem

/-- When `x` and `y` are joined in `F`, choose a path from `x` to `y` inside `F` -/
def JoinedIn.somePath (h : JoinedIn F x y) : Path x y :=
  Classical.choose h
#align joined_in.some_path JoinedIn.somePath

theorem JoinedIn.somePath_mem (h : JoinedIn F x y) (t : I) : h.somePath t ∈ F :=
  Classical.choose_spec h t
#align joined_in.some_path_mem JoinedIn.somePath_mem

/-- If `x` and `y` are joined in the set `F`, then they are joined in the subtype `F`. -/
theorem JoinedIn.joined_subtype (h : JoinedIn F x y) :
    Joined (⟨x, h.source_mem⟩ : F) (⟨y, h.target_mem⟩ : F) :=
  ⟨{  toFun := fun t => ⟨h.somePath t, h.somePath_mem t⟩
      continuous_toFun := by continuity
                             -- 🎉 no goals
      source' := by simp
                    -- 🎉 no goals
      target' := by simp }⟩
                    -- 🎉 no goals
#align joined_in.joined_subtype JoinedIn.joined_subtype

theorem JoinedIn.ofLine {f : ℝ → X} (hf : ContinuousOn f I) (h₀ : f 0 = x) (h₁ : f 1 = y)
    (hF : f '' I ⊆ F) : JoinedIn F x y :=
  ⟨Path.ofLine hf h₀ h₁, fun t => hF <| Path.ofLine_mem hf h₀ h₁ t⟩
#align joined_in.of_line JoinedIn.ofLine

theorem JoinedIn.joined (h : JoinedIn F x y) : Joined x y :=
  ⟨h.somePath⟩
#align joined_in.joined JoinedIn.joined

theorem joinedIn_iff_joined (x_in : x ∈ F) (y_in : y ∈ F) :
    JoinedIn F x y ↔ Joined (⟨x, x_in⟩ : F) (⟨y, y_in⟩ : F) :=
  ⟨fun h => h.joined_subtype, fun h => ⟨h.somePath.map continuous_subtype_val, by simp⟩⟩
                                                                                  -- 🎉 no goals
#align joined_in_iff_joined joinedIn_iff_joined

@[simp]
theorem joinedIn_univ : JoinedIn univ x y ↔ Joined x y := by
  simp [JoinedIn, Joined, exists_true_iff_nonempty]
  -- 🎉 no goals
#align joined_in_univ joinedIn_univ

theorem JoinedIn.mono {U V : Set X} (h : JoinedIn U x y) (hUV : U ⊆ V) : JoinedIn V x y :=
  ⟨h.somePath, fun t => hUV (h.somePath_mem t)⟩
#align joined_in.mono JoinedIn.mono

theorem JoinedIn.refl (h : x ∈ F) : JoinedIn F x x :=
  ⟨Path.refl x, fun _t => h⟩
#align joined_in.refl JoinedIn.refl

@[symm]
theorem JoinedIn.symm (h : JoinedIn F x y) : JoinedIn F y x := by
  cases' h.mem with hx hy
  -- ⊢ JoinedIn F y x
  simp_all [joinedIn_iff_joined]
  -- ⊢ Joined { val := y, property := (_ : y ∈ F) } { val := x, property := (_ : x  …
  exact h.symm
  -- 🎉 no goals
#align joined_in.symm JoinedIn.symm

theorem JoinedIn.trans (hxy : JoinedIn F x y) (hyz : JoinedIn F y z) : JoinedIn F x z := by
  cases' hxy.mem with hx hy
  -- ⊢ JoinedIn F x z
  cases' hyz.mem with hx hy
  -- ⊢ JoinedIn F x z
  simp_all [joinedIn_iff_joined]
  -- ⊢ Joined { val := x, property := (_ : x ∈ F) } { val := z, property := (_ : z  …
  exact hxy.trans hyz
  -- 🎉 no goals
#align joined_in.trans JoinedIn.trans

/-! ### Path component -/


/-- The path component of `x` is the set of points that can be joined to `x`. -/
def pathComponent (x : X) :=
  { y | Joined x y }
#align path_component pathComponent

@[simp]
theorem mem_pathComponent_self (x : X) : x ∈ pathComponent x :=
  Joined.refl x
#align mem_path_component_self mem_pathComponent_self

@[simp]
theorem pathComponent.nonempty (x : X) : (pathComponent x).Nonempty :=
  ⟨x, mem_pathComponent_self x⟩
#align path_component.nonempty pathComponent.nonempty

theorem mem_pathComponent_of_mem (h : x ∈ pathComponent y) : y ∈ pathComponent x :=
  Joined.symm h
#align mem_path_component_of_mem mem_pathComponent_of_mem

theorem pathComponent_symm : x ∈ pathComponent y ↔ y ∈ pathComponent x :=
  ⟨fun h => mem_pathComponent_of_mem h, fun h => mem_pathComponent_of_mem h⟩
#align path_component_symm pathComponent_symm

theorem pathComponent_congr (h : x ∈ pathComponent y) : pathComponent x = pathComponent y := by
  ext z
  -- ⊢ z ∈ pathComponent x ↔ z ∈ pathComponent y
  constructor
  -- ⊢ z ∈ pathComponent x → z ∈ pathComponent y
  · intro h'
    -- ⊢ z ∈ pathComponent y
    rw [pathComponent_symm]
    -- ⊢ y ∈ pathComponent z
    exact (h.trans h').symm
    -- 🎉 no goals
  · intro h'
    -- ⊢ z ∈ pathComponent x
    rw [pathComponent_symm] at h' ⊢
    -- ⊢ x ∈ pathComponent z
    exact h'.trans h
    -- 🎉 no goals
#align path_component_congr pathComponent_congr

theorem pathComponent_subset_component (x : X) : pathComponent x ⊆ connectedComponent x :=
  fun y h =>
  (isConnected_range h.somePath.continuous).subset_connectedComponent ⟨0, by simp⟩ ⟨1, by simp⟩
                                                                             -- 🎉 no goals
                                                                                          -- 🎉 no goals
#align path_component_subset_component pathComponent_subset_component

/-- The path component of `x` in `F` is the set of points that can be joined to `x` in `F`. -/
def pathComponentIn (x : X) (F : Set X) :=
  { y | JoinedIn F x y }
#align path_component_in pathComponentIn

@[simp]
theorem pathComponentIn_univ (x : X) : pathComponentIn x univ = pathComponent x := by
  simp [pathComponentIn, pathComponent, JoinedIn, Joined, exists_true_iff_nonempty]
  -- 🎉 no goals
#align path_component_in_univ pathComponentIn_univ

theorem Joined.mem_pathComponent (hyz : Joined y z) (hxy : y ∈ pathComponent x) :
    z ∈ pathComponent x :=
  hxy.trans hyz
#align joined.mem_path_component Joined.mem_pathComponent

/-! ### Path connected sets -/


/-- A set `F` is path connected if it contains a point that can be joined to all other in `F`. -/
def IsPathConnected (F : Set X) : Prop :=
  ∃ x ∈ F, ∀ {y}, y ∈ F → JoinedIn F x y
#align is_path_connected IsPathConnected

theorem isPathConnected_iff_eq : IsPathConnected F ↔ ∃ x ∈ F, pathComponentIn x F = F := by
  constructor <;> rintro ⟨x, x_in, h⟩ <;> use x, x_in
  -- ⊢ IsPathConnected F → ∃ x, x ∈ F ∧ pathComponentIn x F = F
                  -- ⊢ ∃ x, x ∈ F ∧ pathComponentIn x F = F
                  -- ⊢ IsPathConnected F
                                          -- ⊢ pathComponentIn x F = F
                                          -- ⊢ ∀ {y : X}, y ∈ F → JoinedIn F x y
  · ext y
    -- ⊢ y ∈ pathComponentIn x F ↔ y ∈ F
    exact ⟨fun hy => hy.mem.2, h⟩
    -- 🎉 no goals
  · intro y y_in
    -- ⊢ JoinedIn F x y
    rwa [← h] at y_in
    -- 🎉 no goals
#align is_path_connected_iff_eq isPathConnected_iff_eq

theorem IsPathConnected.joinedIn (h : IsPathConnected F) :
    ∀ (x) (_ : x ∈ F) (y) (_ : y ∈ F), JoinedIn F x y := fun _x x_in _y y_in =>
  let ⟨_b, _b_in, hb⟩ := h
  (hb x_in).symm.trans (hb y_in)
#align is_path_connected.joined_in IsPathConnected.joinedIn

theorem isPathConnected_iff :
    IsPathConnected F ↔ F.Nonempty ∧ ∀ (x) (_ : x ∈ F) (y) (_ : y ∈ F), JoinedIn F x y :=
  ⟨fun h =>
    ⟨let ⟨b, b_in, _hb⟩ := h; ⟨b, b_in⟩, h.joinedIn⟩,
    fun ⟨⟨b, b_in⟩, h⟩ => ⟨b, b_in, fun x_in => h _ b_in _ x_in⟩⟩
#align is_path_connected_iff isPathConnected_iff

theorem IsPathConnected.image' {Y : Type*} [TopologicalSpace Y] (hF : IsPathConnected F)
    {f : X → Y} (hf : ContinuousOn f F) : IsPathConnected (f '' F) := by
  rcases hF with ⟨x, x_in, hx⟩
  -- ⊢ IsPathConnected (f '' F)
  use f x, mem_image_of_mem f x_in
  -- ⊢ ∀ {y : Y}, y ∈ f '' F → JoinedIn (f '' F) (f x) y
  rintro _ ⟨y, y_in, rfl⟩
  -- ⊢ JoinedIn (f '' F) (f x) (f y)
  refine ⟨(hx y_in).somePath.map' ?_, fun t ↦ ⟨_, (hx y_in).somePath_mem t, rfl⟩⟩
  -- ⊢ ContinuousOn f (range ↑(JoinedIn.somePath (_ : JoinedIn F x y)))
  exact hf.mono (range_subset_iff.2 (hx y_in).somePath_mem)
  -- 🎉 no goals

theorem IsPathConnected.image {Y : Type*} [TopologicalSpace Y] (hF : IsPathConnected F) {f : X → Y}
    (hf : Continuous f) : IsPathConnected (f '' F) := hF.image' hf.continuousOn
#align is_path_connected.image IsPathConnected.image

theorem IsPathConnected.mem_pathComponent (h : IsPathConnected F) (x_in : x ∈ F) (y_in : y ∈ F) :
    y ∈ pathComponent x :=
  (h.joinedIn x x_in y y_in).joined
#align is_path_connected.mem_path_component IsPathConnected.mem_pathComponent

theorem IsPathConnected.subset_pathComponent (h : IsPathConnected F) (x_in : x ∈ F) :
    F ⊆ pathComponent x := fun _y y_in => h.mem_pathComponent x_in y_in
#align is_path_connected.subset_path_component IsPathConnected.subset_pathComponent

theorem isPathConnected_singleton (x : X) : IsPathConnected ({x} : Set X) := by
  refine ⟨x, rfl, ?_⟩
  -- ⊢ ∀ {y : X}, y ∈ {x} → JoinedIn {x} x y
  rintro y rfl
  -- ⊢ JoinedIn {y} y y
  exact JoinedIn.refl rfl
  -- 🎉 no goals

theorem IsPathConnected.union {U V : Set X} (hU : IsPathConnected U) (hV : IsPathConnected V)
    (hUV : (U ∩ V).Nonempty) : IsPathConnected (U ∪ V) := by
  rcases hUV with ⟨x, xU, xV⟩
  -- ⊢ IsPathConnected (U ∪ V)
  use x, Or.inl xU
  -- ⊢ ∀ {y : X}, y ∈ U ∪ V → JoinedIn (U ∪ V) x y
  rintro y (yU | yV)
  -- ⊢ JoinedIn (U ∪ V) x y
  · exact (hU.joinedIn x xU y yU).mono (subset_union_left U V)
    -- 🎉 no goals
  · exact (hV.joinedIn x xV y yV).mono (subset_union_right U V)
    -- 🎉 no goals
#align is_path_connected.union IsPathConnected.union

/-- If a set `W` is path-connected, then it is also path-connected when seen as a set in a smaller
ambient type `U` (when `U` contains `W`). -/
theorem IsPathConnected.preimage_coe {U W : Set X} (hW : IsPathConnected W) (hWU : W ⊆ U) :
    IsPathConnected (((↑) : U → X) ⁻¹' W) := by
  rcases hW with ⟨x, x_in, hx⟩
  -- ⊢ IsPathConnected (Subtype.val ⁻¹' W)
  use ⟨x, hWU x_in⟩, by simp [x_in]
  -- ⊢ ∀ {y : { x // x ∈ U }}, y ∈ Subtype.val ⁻¹' W → JoinedIn (Subtype.val ⁻¹' W) …
  rintro ⟨y, hyU⟩ hyW
  -- ⊢ JoinedIn (Subtype.val ⁻¹' W) { val := x, property := (_ : x ∈ U) } { val :=  …
  exact ⟨(hx hyW).joined_subtype.somePath.map (continuous_inclusion hWU), by simp⟩
  -- 🎉 no goals
#align is_path_connected.preimage_coe IsPathConnected.preimage_coe

theorem IsPathConnected.exists_path_through_family {X : Type*} [TopologicalSpace X] {n : ℕ}
    {s : Set X} (h : IsPathConnected s) (p : Fin (n + 1) → X) (hp : ∀ i, p i ∈ s) :
    ∃ γ : Path (p 0) (p n), range γ ⊆ s ∧ ∀ i, p i ∈ range γ := by
  let p' : ℕ → X := fun k => if h : k < n + 1 then p ⟨k, h⟩ else p ⟨0, n.zero_lt_succ⟩
  -- ⊢ ∃ γ, range ↑γ ⊆ s ∧ ∀ (i : Fin (n + 1)), p i ∈ range ↑γ
  obtain ⟨γ, hγ⟩ : ∃ γ : Path (p' 0) (p' n), (∀ i ≤ n, p' i ∈ range γ) ∧ range γ ⊆ s := by
    have hp' : ∀ i ≤ n, p' i ∈ s := by
      intro i hi
      simp [Nat.lt_succ_of_le hi, hp]
    clear_value p'
    clear hp p
    induction' n with n hn
    · use Path.refl (p' 0)
      · constructor
        · rintro i hi
          rw [le_zero_iff.mp hi]
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
    simp only [hk, dif_pos]
    congr
    ext
    rw [Fin.val_cast_of_lt hk]
  use γ.cast (hpp' 0 n.zero_lt_succ) (hpp' n n.lt_succ_self)
  -- ⊢ range ↑(Path.cast γ (_ : p ↑0 = p' 0) (_ : p ↑n = p' n)) ⊆ s ∧ ∀ (i : Fin (n …
  simp only [γ.cast_coe]
  -- ⊢ range ↑γ ⊆ s ∧ ∀ (i : Fin (n + 1)), p i ∈ range ↑γ
  refine' And.intro hγ.2 _
  -- ⊢ ∀ (i : Fin (n + 1)), p i ∈ range ↑γ
  rintro ⟨i, hi⟩
  -- ⊢ p { val := i, isLt := hi } ∈ range ↑γ
  suffices p ⟨i, hi⟩ = p' i by convert hγ.1 i (Nat.le_of_lt_succ hi)
  -- ⊢ p { val := i, isLt := hi } = p' i
  rw [← hpp' i hi]
  -- ⊢ p { val := i, isLt := hi } = p ↑i
  suffices i = i % n.succ by congr
  -- ⊢ i = i % Nat.succ n
  rw [Nat.mod_eq_of_lt hi]
  -- 🎉 no goals
#align is_path_connected.exists_path_through_family IsPathConnected.exists_path_through_family

theorem IsPathConnected.exists_path_through_family' {X : Type*} [TopologicalSpace X] {n : ℕ}
    {s : Set X} (h : IsPathConnected s) (p : Fin (n + 1) → X) (hp : ∀ i, p i ∈ s) :
    ∃ (γ : Path (p 0) (p n)) (t : Fin (n + 1) → I), (∀ t, γ t ∈ s) ∧ ∀ i, γ (t i) = p i := by
  rcases h.exists_path_through_family p hp with ⟨γ, hγ⟩
  -- ⊢ ∃ γ t, (∀ (t : ↑I), ↑γ t ∈ s) ∧ ∀ (i : Fin (n + 1)), ↑γ (t i) = p i
  rcases hγ with ⟨h₁, h₂⟩
  -- ⊢ ∃ γ t, (∀ (t : ↑I), ↑γ t ∈ s) ∧ ∀ (i : Fin (n + 1)), ↑γ (t i) = p i
  simp only [range, mem_setOf_eq] at h₂
  -- ⊢ ∃ γ t, (∀ (t : ↑I), ↑γ t ∈ s) ∧ ∀ (i : Fin (n + 1)), ↑γ (t i) = p i
  rw [range_subset_iff] at h₁
  -- ⊢ ∃ γ t, (∀ (t : ↑I), ↑γ t ∈ s) ∧ ∀ (i : Fin (n + 1)), ↑γ (t i) = p i
  choose! t ht using h₂
  -- ⊢ ∃ γ t, (∀ (t : ↑I), ↑γ t ∈ s) ∧ ∀ (i : Fin (n + 1)), ↑γ (t i) = p i
  exact ⟨γ, t, h₁, ht⟩
  -- 🎉 no goals
#align is_path_connected.exists_path_through_family' IsPathConnected.exists_path_through_family'

/-! ### Path connected spaces -/


/-- A topological space is path-connected if it is non-empty and every two points can be
joined by a continuous path. -/
class PathConnectedSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- A path-connected space must be nonempty. -/
  Nonempty : Nonempty X
  /-- Any two points in a path-connected space must be joined by a continuous path. -/
  Joined : ∀ x y : X, Joined x y
#align path_connected_space PathConnectedSpace

theorem pathConnectedSpace_iff_zerothHomotopy :
    PathConnectedSpace X ↔ Nonempty (ZerothHomotopy X) ∧ Subsingleton (ZerothHomotopy X) := by
  letI := pathSetoid X
  -- ⊢ PathConnectedSpace X ↔ Nonempty (ZerothHomotopy X) ∧ Subsingleton (ZerothHom …
  constructor
  -- ⊢ PathConnectedSpace X → Nonempty (ZerothHomotopy X) ∧ Subsingleton (ZerothHom …
  · intro h
    -- ⊢ Nonempty (ZerothHomotopy X) ∧ Subsingleton (ZerothHomotopy X)
    refine' ⟨(nonempty_quotient_iff _).mpr h.1, ⟨_⟩⟩
    -- ⊢ ∀ (a b : ZerothHomotopy X), a = b
    rintro ⟨x⟩ ⟨y⟩
    -- ⊢ Quot.mk Setoid.r x = Quot.mk Setoid.r y
    exact Quotient.sound (PathConnectedSpace.Joined x y)
    -- 🎉 no goals
  · unfold ZerothHomotopy
    -- ⊢ Nonempty (Quotient (pathSetoid X)) ∧ Subsingleton (Quotient (pathSetoid X))  …
    rintro ⟨h, h'⟩
    -- ⊢ PathConnectedSpace X
    skip
    -- ⊢ PathConnectedSpace X
    exact ⟨(nonempty_quotient_iff _).mp h, fun x y => Quotient.exact <| Subsingleton.elim ⟦x⟧ ⟦y⟧⟩
    -- 🎉 no goals
#align path_connected_space_iff_zeroth_homotopy pathConnectedSpace_iff_zerothHomotopy

namespace PathConnectedSpace

variable [PathConnectedSpace X]

/-- Use path-connectedness to build a path between two points. -/
def somePath (x y : X) : Path x y :=
  Nonempty.some (Joined x y)
#align path_connected_space.some_path PathConnectedSpace.somePath

end PathConnectedSpace

theorem isPathConnected_iff_pathConnectedSpace : IsPathConnected F ↔ PathConnectedSpace F := by
  rw [isPathConnected_iff]
  -- ⊢ (Set.Nonempty F ∧ ∀ (x : X), x ∈ F → ∀ (y : X), y ∈ F → JoinedIn F x y) ↔ Pa …
  constructor
  -- ⊢ (Set.Nonempty F ∧ ∀ (x : X), x ∈ F → ∀ (y : X), y ∈ F → JoinedIn F x y) → Pa …
  · rintro ⟨⟨x, x_in⟩, h⟩
    -- ⊢ PathConnectedSpace ↑F
    refine' ⟨⟨⟨x, x_in⟩⟩, _⟩
    -- ⊢ ∀ (x y : ↑F), Joined x y
    rintro ⟨y, y_in⟩ ⟨z, z_in⟩
    -- ⊢ Joined { val := y, property := y_in } { val := z, property := z_in }
    have H := h y y_in z z_in
    -- ⊢ Joined { val := y, property := y_in } { val := z, property := z_in }
    rwa [joinedIn_iff_joined y_in z_in] at H
    -- 🎉 no goals
  · rintro ⟨⟨x, x_in⟩, H⟩
    -- ⊢ Set.Nonempty F ∧ ∀ (x : X), x ∈ F → ∀ (y : X), y ∈ F → JoinedIn F x y
    refine' ⟨⟨x, x_in⟩, fun y y_in z z_in => _⟩
    -- ⊢ JoinedIn F y z
    rw [joinedIn_iff_joined y_in z_in]
    -- ⊢ Joined { val := y, property := y_in } { val := z, property := z_in }
    apply H
    -- 🎉 no goals
#align is_path_connected_iff_path_connected_space isPathConnected_iff_pathConnectedSpace

theorem pathConnectedSpace_iff_univ : PathConnectedSpace X ↔ IsPathConnected (univ : Set X) := by
  constructor
  -- ⊢ PathConnectedSpace X → IsPathConnected univ
  · intro h
    -- ⊢ IsPathConnected univ
    haveI := @PathConnectedSpace.Nonempty X _ _
    -- ⊢ IsPathConnected univ
    inhabit X
    -- ⊢ IsPathConnected univ
    refine' ⟨default, mem_univ _, _⟩
    -- ⊢ ∀ {y : X}, y ∈ univ → JoinedIn univ default y
    intros y _hy
    -- ⊢ JoinedIn univ default y
    simpa using PathConnectedSpace.Joined default y
    -- 🎉 no goals
  · intro h
    -- ⊢ PathConnectedSpace X
    have h' := h.joinedIn
    -- ⊢ PathConnectedSpace X
    cases' h with x h
    -- ⊢ PathConnectedSpace X
    exact ⟨⟨x⟩, by simpa using h'⟩
    -- 🎉 no goals
#align path_connected_space_iff_univ pathConnectedSpace_iff_univ

theorem isPathConnected_univ [PathConnectedSpace X] : IsPathConnected (univ : Set X) :=
  pathConnectedSpace_iff_univ.mp inferInstance

theorem isPathConnected_range [PathConnectedSpace X] {f : X → Y} (hf : Continuous f) :
    IsPathConnected (range f) := by
  rw [← image_univ]
  -- ⊢ IsPathConnected (f '' univ)
  exact isPathConnected_univ.image hf
  -- 🎉 no goals

theorem Function.Surjective.pathConnectedSpace [PathConnectedSpace X]
  {f : X → Y} (hf : Surjective f) (hf' : Continuous f) : PathConnectedSpace Y := by
  rw [pathConnectedSpace_iff_univ, ← hf.range_eq]
  -- ⊢ IsPathConnected (range f)
  exact isPathConnected_range hf'
  -- 🎉 no goals

instance Quotient.instPathConnectedSpace {s : Setoid X} [PathConnectedSpace X] :
    PathConnectedSpace (Quotient s) :=
  (surjective_quotient_mk X).pathConnectedSpace continuous_coinduced_rng

/-- This is a special case of `NormedSpace.path_connected` (and
`TopologicalAddGroup.pathConnectedSpace`). It exists only to simplify dependencies. -/
instance Real.instPathConnectedSpace : PathConnectedSpace ℝ where
  Nonempty := inferInstance
  Joined := fun x y ↦ ⟨⟨⟨fun (t : I) ↦ (1 - t) * x + t * y, by continuity⟩, by simp, by simp⟩⟩
                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
                                                                                        -- 🎉 no goals

theorem pathConnectedSpace_iff_eq : PathConnectedSpace X ↔ ∃ x : X, pathComponent x = univ := by
  simp [pathConnectedSpace_iff_univ, isPathConnected_iff_eq]
  -- 🎉 no goals
#align path_connected_space_iff_eq pathConnectedSpace_iff_eq

-- see Note [lower instance priority]
instance (priority := 100) PathConnectedSpace.connectedSpace [PathConnectedSpace X] :
    ConnectedSpace X := by
  rw [connectedSpace_iff_connectedComponent]
  -- ⊢ ∃ x, connectedComponent x = univ
  rcases isPathConnected_iff_eq.mp (pathConnectedSpace_iff_univ.mp ‹_›) with ⟨x, _x_in, hx⟩
  -- ⊢ ∃ x, connectedComponent x = univ
  use x
  -- ⊢ connectedComponent x = univ
  rw [← univ_subset_iff]
  -- ⊢ univ ⊆ connectedComponent x
  exact (by simpa using hx : pathComponent x = univ) ▸ pathComponent_subset_component x
  -- 🎉 no goals
#align path_connected_space.connected_space PathConnectedSpace.connectedSpace

theorem IsPathConnected.isConnected (hF : IsPathConnected F) : IsConnected F := by
  rw [isConnected_iff_connectedSpace]
  -- ⊢ ConnectedSpace ↑F
  rw [isPathConnected_iff_pathConnectedSpace] at hF
  -- ⊢ ConnectedSpace ↑F
  exact @PathConnectedSpace.connectedSpace _ _ hF
  -- 🎉 no goals
#align is_path_connected.is_connected IsPathConnected.isConnected

namespace PathConnectedSpace

variable [PathConnectedSpace X]

theorem exists_path_through_family {n : ℕ} (p : Fin (n + 1) → X) :
    ∃ γ : Path (p 0) (p n), ∀ i, p i ∈ range γ := by
  have : IsPathConnected (univ : Set X) := pathConnectedSpace_iff_univ.mp (by infer_instance)
  -- ⊢ ∃ γ, ∀ (i : Fin (n + 1)), p i ∈ range ↑γ
  rcases this.exists_path_through_family p fun _i => True.intro with ⟨γ, -, h⟩
  -- ⊢ ∃ γ, ∀ (i : Fin (n + 1)), p i ∈ range ↑γ
  exact ⟨γ, h⟩
  -- 🎉 no goals
#align path_connected_space.exists_path_through_family PathConnectedSpace.exists_path_through_family

theorem exists_path_through_family' {n : ℕ} (p : Fin (n + 1) → X) :
    ∃ (γ : Path (p 0) (p n)) (t : Fin (n + 1) → I), ∀ i, γ (t i) = p i := by
  have : IsPathConnected (univ : Set X) := pathConnectedSpace_iff_univ.mp (by infer_instance)
  -- ⊢ ∃ γ t, ∀ (i : Fin (n + 1)), ↑γ (t i) = p i
  rcases this.exists_path_through_family' p fun _i => True.intro with ⟨γ, t, -, h⟩
  -- ⊢ ∃ γ t, ∀ (i : Fin (n + 1)), ↑γ (t i) = p i
  exact ⟨γ, t, h⟩
  -- 🎉 no goals
#align path_connected_space.exists_path_through_family' PathConnectedSpace.exists_path_through_family'

end PathConnectedSpace

/-! ### Locally path connected spaces -/


/-- A topological space is locally path connected, at every point, path connected
neighborhoods form a neighborhood basis. -/
class LocPathConnectedSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- Each neighborhood filter has a basis of path-connected neighborhoods. -/
  path_connected_basis : ∀ x : X, (𝓝 x).HasBasis (fun s : Set X => s ∈ 𝓝 x ∧ IsPathConnected s) id
#align loc_path_connected_space LocPathConnectedSpace

export LocPathConnectedSpace (path_connected_basis)

theorem locPathConnected_of_bases {p : ι → Prop} {s : X → ι → Set X}
    (h : ∀ x, (𝓝 x).HasBasis p (s x)) (h' : ∀ x i, p i → IsPathConnected (s x i)) :
    LocPathConnectedSpace X := by
  constructor
  -- ⊢ ∀ (x : X), HasBasis (𝓝 x) (fun s => s ∈ 𝓝 x ∧ IsPathConnected s) id
  intro x
  -- ⊢ HasBasis (𝓝 x) (fun s => s ∈ 𝓝 x ∧ IsPathConnected s) id
  apply (h x).to_hasBasis
  -- ⊢ ∀ (i : ι), p i → ∃ i', (i' ∈ 𝓝 x ∧ IsPathConnected i') ∧ id i' ⊆ s x i
  · intro i pi
    -- ⊢ ∃ i', (i' ∈ 𝓝 x ∧ IsPathConnected i') ∧ id i' ⊆ s x i
    exact ⟨s x i, ⟨(h x).mem_of_mem pi, h' x i pi⟩, by rfl⟩
    -- 🎉 no goals
  · rintro U ⟨U_in, _hU⟩
    -- ⊢ ∃ i, p i ∧ s x i ⊆ id U
    rcases(h x).mem_iff.mp U_in with ⟨i, pi, hi⟩
    -- ⊢ ∃ i, p i ∧ s x i ⊆ id U
    tauto
    -- 🎉 no goals
#align loc_path_connected_of_bases locPathConnected_of_bases

theorem pathConnectedSpace_iff_connectedSpace [LocPathConnectedSpace X] :
    PathConnectedSpace X ↔ ConnectedSpace X := by
  constructor
  -- ⊢ PathConnectedSpace X → ConnectedSpace X
  · intro h
    -- ⊢ ConnectedSpace X
    infer_instance
    -- 🎉 no goals
  · intro hX
    -- ⊢ PathConnectedSpace X
    rw [pathConnectedSpace_iff_eq]
    -- ⊢ ∃ x, pathComponent x = univ
    use Classical.arbitrary X
    -- ⊢ pathComponent (Classical.arbitrary X) = univ
    refine' IsClopen.eq_univ ⟨_, _⟩ (by simp)
    -- ⊢ IsOpen (pathComponent (Classical.arbitrary X))
    · rw [isOpen_iff_mem_nhds]
      -- ⊢ ∀ (a : X), a ∈ pathComponent (Classical.arbitrary X) → pathComponent (Classi …
      intro y y_in
      -- ⊢ pathComponent (Classical.arbitrary X) ∈ 𝓝 y
      rcases(path_connected_basis y).ex_mem with ⟨U, ⟨U_in, hU⟩⟩
      -- ⊢ pathComponent (Classical.arbitrary X) ∈ 𝓝 y
      apply mem_of_superset U_in
      -- ⊢ U ⊆ pathComponent (Classical.arbitrary X)
      rw [← pathComponent_congr y_in]
      -- ⊢ U ⊆ pathComponent y
      exact hU.subset_pathComponent (mem_of_mem_nhds U_in)
      -- 🎉 no goals
    · rw [isClosed_iff_nhds]
      -- ⊢ ∀ (x : X), (∀ (U : Set X), U ∈ 𝓝 x → Set.Nonempty (U ∩ pathComponent (Classi …
      intro y H
      -- ⊢ y ∈ pathComponent (Classical.arbitrary X)
      rcases(path_connected_basis y).ex_mem with ⟨U, ⟨U_in, hU⟩⟩
      -- ⊢ y ∈ pathComponent (Classical.arbitrary X)
      rcases H U U_in with ⟨z, hz, hz'⟩
      -- ⊢ y ∈ pathComponent (Classical.arbitrary X)
      exact (hU.joinedIn z hz y <| mem_of_mem_nhds U_in).joined.mem_pathComponent hz'
      -- 🎉 no goals
#align path_connected_space_iff_connected_space pathConnectedSpace_iff_connectedSpace

theorem pathConnected_subset_basis [LocPathConnectedSpace X] {U : Set X} (h : IsOpen U)
    (hx : x ∈ U) : (𝓝 x).HasBasis (fun s : Set X => s ∈ 𝓝 x ∧ IsPathConnected s ∧ s ⊆ U) id :=
  (path_connected_basis x).hasBasis_self_subset (IsOpen.mem_nhds h hx)
#align path_connected_subset_basis pathConnected_subset_basis

theorem locPathConnected_of_isOpen [LocPathConnectedSpace X] {U : Set X} (h : IsOpen U) :
    LocPathConnectedSpace U :=
  ⟨by
    rintro ⟨x, x_in⟩
    -- ⊢ HasBasis (𝓝 { val := x, property := x_in }) (fun s => s ∈ 𝓝 { val := x, prop …
    rw [nhds_subtype_eq_comap]
    -- ⊢ HasBasis (comap Subtype.val (𝓝 x)) (fun s => s ∈ comap Subtype.val (𝓝 x) ∧ I …
    constructor
    -- ⊢ ∀ (t : Set ↑U), t ∈ comap Subtype.val (𝓝 x) ↔ ∃ i, (i ∈ comap Subtype.val (𝓝 …
    intro V
    -- ⊢ V ∈ comap Subtype.val (𝓝 x) ↔ ∃ i, (i ∈ comap Subtype.val (𝓝 x) ∧ IsPathConn …
    rw [(HasBasis.comap ((↑) : U → X) (pathConnected_subset_basis h x_in)).mem_iff]
    -- ⊢ (∃ i, (i ∈ 𝓝 x ∧ IsPathConnected i ∧ i ⊆ U) ∧ Subtype.val ⁻¹' id i ⊆ V) ↔ ∃  …
    constructor
    -- ⊢ (∃ i, (i ∈ 𝓝 x ∧ IsPathConnected i ∧ i ⊆ U) ∧ Subtype.val ⁻¹' id i ⊆ V) → ∃  …
    · rintro ⟨W, ⟨W_in, hW, hWU⟩, hWV⟩
      -- ⊢ ∃ i, (i ∈ comap Subtype.val (𝓝 x) ∧ IsPathConnected i) ∧ id i ⊆ V
      exact ⟨Subtype.val ⁻¹' W, ⟨⟨preimage_mem_comap W_in, hW.preimage_coe hWU⟩, hWV⟩⟩
      -- 🎉 no goals
    · rintro ⟨W, ⟨W_in, hW⟩, hWV⟩
      -- ⊢ ∃ i, (i ∈ 𝓝 x ∧ IsPathConnected i ∧ i ⊆ U) ∧ Subtype.val ⁻¹' id i ⊆ V
      refine'
        ⟨(↑) '' W,
          ⟨Filter.image_coe_mem_of_mem_comap (IsOpen.mem_nhds h x_in) W_in,
            hW.image continuous_subtype_val, Subtype.coe_image_subset U W⟩,
          _⟩
      rintro x ⟨y, ⟨y_in, hy⟩⟩
      -- ⊢ x ∈ V
      rw [← Subtype.coe_injective hy]
      -- ⊢ y ∈ V
      tauto⟩
      -- 🎉 no goals
#align loc_path_connected_of_is_open locPathConnected_of_isOpen

theorem IsOpen.isConnected_iff_isPathConnected [LocPathConnectedSpace X] {U : Set X}
    (U_op : IsOpen U) : IsPathConnected U ↔ IsConnected U := by
  rw [isConnected_iff_connectedSpace, isPathConnected_iff_pathConnectedSpace]
  -- ⊢ PathConnectedSpace ↑U ↔ ConnectedSpace ↑U
  haveI := locPathConnected_of_isOpen U_op
  -- ⊢ PathConnectedSpace ↑U ↔ ConnectedSpace ↑U
  exact pathConnectedSpace_iff_connectedSpace
  -- 🎉 no goals
#align is_open.is_connected_iff_is_path_connected IsOpen.isConnected_iff_isPathConnected
