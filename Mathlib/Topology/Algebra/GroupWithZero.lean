/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Topological group with zero

In this file we define `HasContinuousInv₀` to be a mixin typeclass a type with `Inv` and
`Zero` (e.g., a `GroupWithZero`) such that `fun x ↦ x⁻¹` is continuous at all nonzero points. Any
normed (semi)field has this property. Currently the only example of `HasContinuousInv₀` in
`mathlib` which is not a normed field is the type `NNReal` (a.k.a. `ℝ≥0`) of nonnegative real
numbers.

Then we prove lemmas about continuity of `x ↦ x⁻¹` and `f / g` providing dot-style `*.inv₀` and
`*.div` operations on `Filter.Tendsto`, `ContinuousAt`, `ContinuousWithinAt`, `ContinuousOn`,
and `Continuous`. As a special case, we provide `*.div_const` operations that require only
`DivInvMonoid` and `ContinuousMul` instances.

All lemmas about `(⁻¹)` use `inv₀` in their names because lemmas without `₀` are used for
`IsTopologicalGroup`s. We also use `'` in the typeclass name `HasContinuousInv₀` for the sake of
consistency of notation.

On a `GroupWithZero` with continuous multiplication, we also define left and right multiplication
as homeomorphisms.
-/
open Topology Filter Function

/-!
### A `DivInvMonoid` with continuous multiplication

If `G₀` is a `DivInvMonoid` with continuous `(*)`, then `(/y)` is continuous for any `y`. In this
section we prove lemmas that immediately follow from this fact providing `*.div_const` dot-style
operations on `Filter.Tendsto`, `ContinuousAt`, `ContinuousWithinAt`, `ContinuousOn`, and
`Continuous`.
-/


variable {α β G₀ : Type*}

section DivConst

variable [DivInvMonoid G₀] [TopologicalSpace G₀] [ContinuousMul G₀] {f : α → G₀} {s : Set α}
  {l : Filter α}

theorem Filter.Tendsto.div_const {x : G₀} (hf : Tendsto f l (𝓝 x)) (y : G₀) :
    Tendsto (fun a ↦ f a / y) l (𝓝 (x / y)) := by
  simpa only [div_eq_mul_inv] using hf.mul tendsto_const_nhds

variable [TopologicalSpace α]

nonrec theorem ContinuousAt.div_const {a : α} (hf : ContinuousAt f a) (y : G₀) :
    ContinuousAt (fun x ↦ f x / y) a :=
  hf.div_const y

nonrec theorem ContinuousWithinAt.div_const {a} (hf : ContinuousWithinAt f s a) (y : G₀) :
    ContinuousWithinAt (fun x ↦ f x / y) s a :=
  hf.div_const _

theorem ContinuousOn.div_const (hf : ContinuousOn f s) (y : G₀) :
    ContinuousOn (fun x ↦ f x / y) s := by
  simpa only [div_eq_mul_inv] using hf.mul continuousOn_const

@[continuity, fun_prop]
theorem Continuous.div_const (hf : Continuous f) (y : G₀) : Continuous fun x ↦ f x / y := by
  simpa only [div_eq_mul_inv] using hf.mul continuous_const

end DivConst

/-- A type with `0` and `Inv` such that `fun x ↦ x⁻¹` is continuous at all nonzero points. Any
normed (semi)field has this property. -/
class HasContinuousInv₀ (G₀ : Type*) [Zero G₀] [Inv G₀] [TopologicalSpace G₀] : Prop where
  /-- The map `fun x ↦ x⁻¹` is continuous at all nonzero points. -/
  continuousAt_inv₀ : ∀ ⦃x : G₀⦄, x ≠ 0 → ContinuousAt Inv.inv x

export HasContinuousInv₀ (continuousAt_inv₀)

section Inv₀

variable [Zero G₀] [Inv G₀] [TopologicalSpace G₀] [HasContinuousInv₀ G₀] {l : Filter α} {f : α → G₀}
  {s : Set α} {a : α}

/-!
### Continuity of `fun x ↦ x⁻¹` at a non-zero point

We define `HasContinuousInv₀` to be a `GroupWithZero` such that the operation `x ↦ x⁻¹`
is continuous at all nonzero points. In this section we prove dot-style `*.inv₀` lemmas for
`Filter.Tendsto`, `ContinuousAt`, `ContinuousWithinAt`, `ContinuousOn`, and `Continuous`.
-/

theorem tendsto_inv₀ {x : G₀} (hx : x ≠ 0) : Tendsto Inv.inv (𝓝 x) (𝓝 x⁻¹) :=
  continuousAt_inv₀ hx

theorem continuousOn_inv₀ : ContinuousOn (Inv.inv : G₀ → G₀) {0}ᶜ := fun _x hx ↦
  (continuousAt_inv₀ hx).continuousWithinAt

/-- If a function converges to a nonzero value, its inverse converges to the inverse of this value.
We use the name `Filter.Tendsto.inv₀` as `Filter.Tendsto.inv` is already used in multiplicative
topological groups. -/
theorem Filter.Tendsto.inv₀ {a : G₀} (hf : Tendsto f l (𝓝 a)) (ha : a ≠ 0) :
    Tendsto (fun x ↦ (f x)⁻¹) l (𝓝 a⁻¹) :=
  (tendsto_inv₀ ha).comp hf

variable [TopologicalSpace α]

nonrec theorem ContinuousWithinAt.inv₀ (hf : ContinuousWithinAt f s a) (ha : f a ≠ 0) :
    ContinuousWithinAt (fun x ↦ (f x)⁻¹) s a :=
  hf.inv₀ ha

@[fun_prop]
nonrec theorem ContinuousAt.inv₀ (hf : ContinuousAt f a) (ha : f a ≠ 0) :
    ContinuousAt (fun x ↦ (f x)⁻¹) a :=
  hf.inv₀ ha

@[continuity, fun_prop]
theorem Continuous.inv₀ (hf : Continuous f) (h0 : ∀ x, f x ≠ 0) : Continuous fun x ↦ (f x)⁻¹ :=
  continuous_iff_continuousAt.2 fun x ↦ (hf.tendsto x).inv₀ (h0 x)

@[fun_prop]
theorem ContinuousOn.inv₀ (hf : ContinuousOn f s) (h0 : ∀ x ∈ s, f x ≠ 0) :
    ContinuousOn (fun x ↦ (f x)⁻¹) s := fun x hx ↦ (hf x hx).inv₀ (h0 x hx)

end Inv₀

section GroupWithZero

variable [GroupWithZero G₀] [TopologicalSpace G₀] [HasContinuousInv₀ G₀]

/-- If `G₀` is a group with zero with topology such that `x ↦ x⁻¹` is continuous at all nonzero
points. Then the coercion `G₀ˣ → G₀` is a topological embedding. -/
theorem Units.isEmbedding_val₀ : IsEmbedding (val : G₀ˣ → G₀) :=
  embedding_val_mk <| (continuousOn_inv₀ (G₀ := G₀)).mono fun _ ↦ IsUnit.ne_zero

/-- If a group with zero has continuous inversion, then its group of units is homeomorphic to
the set of nonzero elements. -/
noncomputable def unitsHomeomorphNeZero : G₀ˣ ≃ₜ {g : G₀ // g ≠ 0} :=
  Units.isEmbedding_val₀.toHomeomorph.trans <| show _ ≃ₜ {g | _} from .setCongr <|
    Set.ext fun x ↦ (Units.exists_iff_ne_zero (p := (· = x))).trans <| by simp

end GroupWithZero

section NhdsInv

variable [GroupWithZero G₀] [TopologicalSpace G₀] [HasContinuousInv₀ G₀] {x : G₀}

lemma nhds_inv₀ (hx : x ≠ 0) : 𝓝 x⁻¹ = (𝓝 x)⁻¹ := by
  refine le_antisymm (inv_le_iff_le_inv.1 ?_) (tendsto_inv₀ hx)
  simpa only [inv_inv] using tendsto_inv₀ (inv_ne_zero hx)

lemma tendsto_inv_iff₀ {l : Filter α} {f : α → G₀} (hx : x ≠ 0) :
    Tendsto (fun x ↦ (f x)⁻¹) l (𝓝 x⁻¹) ↔ Tendsto f l (𝓝 x) := by
  simp only [nhds_inv₀ hx, ← Filter.comap_inv, tendsto_comap_iff, Function.comp_def, inv_inv]

end NhdsInv

/-!
### Continuity of division

If `G₀` is a `GroupWithZero` with `x ↦ x⁻¹` continuous at all nonzero points and `(*)`, then
division `(/)` is continuous at any point where the denominator is continuous.
-/

section Div

variable [GroupWithZero G₀] [TopologicalSpace G₀] [HasContinuousInv₀ G₀] [ContinuousMul G₀]
  {f g : α → G₀}

theorem Filter.Tendsto.div {l : Filter α} {a b : G₀} (hf : Tendsto f l (𝓝 a))
    (hg : Tendsto g l (𝓝 b)) (hy : b ≠ 0) : Tendsto (f / g) l (𝓝 (a / b)) := by
  simpa only [div_eq_mul_inv] using hf.mul (hg.inv₀ hy)

theorem Filter.tendsto_mul_iff_of_ne_zero [T1Space G₀] {f g : α → G₀} {l : Filter α} {x y : G₀}
    (hg : Tendsto g l (𝓝 y)) (hy : y ≠ 0) :
    Tendsto (fun n ↦ f n * g n) l (𝓝 <| x * y) ↔ Tendsto f l (𝓝 x) := by
  refine ⟨fun hfg ↦ ?_, fun hf ↦ hf.mul hg⟩
  rw [← mul_div_cancel_right₀ x hy]
  refine Tendsto.congr' ?_ (hfg.div hg hy)
  exact (hg.eventually_ne hy).mono fun n hn ↦ mul_div_cancel_right₀ _ hn

variable [TopologicalSpace α] [TopologicalSpace β] {s : Set α} {a : α}

nonrec theorem ContinuousWithinAt.div (hf : ContinuousWithinAt f s a)
    (hg : ContinuousWithinAt g s a) (h₀ : g a ≠ 0) : ContinuousWithinAt (f / g) s a :=
  hf.div hg h₀

theorem ContinuousOn.div (hf : ContinuousOn f s) (hg : ContinuousOn g s) (h₀ : ∀ x ∈ s, g x ≠ 0) :
    ContinuousOn (f / g) s := fun x hx ↦ (hf x hx).div (hg x hx) (h₀ x hx)

/-- Continuity at a point of the result of dividing two functions continuous at that point, where
the denominator is nonzero. -/
nonrec theorem ContinuousAt.div (hf : ContinuousAt f a) (hg : ContinuousAt g a) (h₀ : g a ≠ 0) :
    ContinuousAt (f / g) a :=
  hf.div hg h₀

@[continuity]
theorem Continuous.div (hf : Continuous f) (hg : Continuous g) (h₀ : ∀ x, g x ≠ 0) :
    Continuous (f / g) := by simpa only [div_eq_mul_inv] using hf.mul (hg.inv₀ h₀)

theorem continuousOn_div : ContinuousOn (fun p : G₀ × G₀ ↦ p.1 / p.2) { p | p.2 ≠ 0 } :=
  continuousOn_fst.div continuousOn_snd fun _ ↦ id

@[fun_prop]
theorem Continuous.div₀ (hf : Continuous f) (hg : Continuous g) (h₀ : ∀ x, g x ≠ 0) :
    Continuous (fun x ↦ f x / g x) := by
  simpa only [div_eq_mul_inv] using hf.mul (hg.inv₀ h₀)

@[fun_prop]
theorem ContinuousAt.div₀ (hf : ContinuousAt f a) (hg : ContinuousAt g a) (h₀ : g a ≠ 0) :
    ContinuousAt (fun x ↦ f x / g x) a := ContinuousAt.div hf hg h₀

@[fun_prop]
theorem ContinuousOn.div₀ (hf : ContinuousOn f s) (hg : ContinuousOn g s) (h₀ : ∀ x ∈ s, g x ≠ 0) :
    ContinuousOn (fun x ↦ f x / g x) s := ContinuousOn.div hf hg h₀

/-- The function `f x / g x` is discontinuous when `g x = 0`. However, under appropriate
conditions, `h x (f x / g x)` is still continuous.  The condition is that if `g a = 0` then `h x y`
must tend to `h a 0` when `x` tends to `a`, with no information about `y`. This is represented by
the `⊤` filter.  Note: `tendsto_prod_top_iff` characterizes this convergence in uniform spaces.  See
also `Filter.prod_top` and `Filter.mem_prod_top`. -/
theorem ContinuousAt.comp_div_cases {f g : α → G₀} (h : α → G₀ → β) (hf : ContinuousAt f a)
    (hg : ContinuousAt g a) (hh : g a ≠ 0 → ContinuousAt ↿h (a, f a / g a))
    (h2h : g a = 0 → Tendsto ↿h (𝓝 a ×ˢ ⊤) (𝓝 (h a 0))) :
    ContinuousAt (fun x ↦ h x (f x / g x)) a := by
  change ContinuousAt (↿h ∘ fun x ↦ (x, f x / g x)) a
  by_cases hga : g a = 0
  · rw [ContinuousAt]
    simp_rw [comp_apply, hga, div_zero]
    exact (h2h hga).comp (continuousAt_id.tendsto.prodMk tendsto_top)
  · fun_prop (disch := assumption)

/-- `h x (f x / g x)` is continuous under certain conditions, even if the denominator is sometimes
  `0`. See docstring of `ContinuousAt.comp_div_cases`. -/
theorem Continuous.comp_div_cases {f g : α → G₀} (h : α → G₀ → β) (hf : Continuous f)
    (hg : Continuous g) (hh : ∀ a, g a ≠ 0 → ContinuousAt ↿h (a, f a / g a))
    (h2h : ∀ a, g a = 0 → Tendsto ↿h (𝓝 a ×ˢ ⊤) (𝓝 (h a 0))) :
    Continuous fun x ↦ h x (f x / g x) :=
  continuous_iff_continuousAt.mpr fun a ↦
    hf.continuousAt.comp_div_cases _ hg.continuousAt (hh a) (h2h a)

end Div

/-! ### Left and right multiplication as homeomorphisms -/


namespace Homeomorph

variable [TopologicalSpace α] [GroupWithZero α] [ContinuousMul α]

/-- Left multiplication by a nonzero element in a `GroupWithZero` with continuous multiplication
is a homeomorphism of the underlying type. -/
protected def mulLeft₀ (c : α) (hc : c ≠ 0) : α ≃ₜ α :=
  { Equiv.mulLeft₀ c hc with
    continuous_toFun := continuous_mul_left _
    continuous_invFun := continuous_mul_left _ }

/-- Right multiplication by a nonzero element in a `GroupWithZero` with continuous multiplication
is a homeomorphism of the underlying type. -/
protected def mulRight₀ (c : α) (hc : c ≠ 0) : α ≃ₜ α :=
  { Equiv.mulRight₀ c hc with
    continuous_toFun := continuous_mul_right _
    continuous_invFun := continuous_mul_right _ }

@[simp]
theorem coe_mulLeft₀ (c : α) (hc : c ≠ 0) : ⇑(Homeomorph.mulLeft₀ c hc) = (c * ·) :=
  rfl

@[simp]
theorem mulLeft₀_symm_apply (c : α) (hc : c ≠ 0) :
    ((Homeomorph.mulLeft₀ c hc).symm : α → α) = (c⁻¹ * ·) :=
  rfl

@[simp]
theorem coe_mulRight₀ (c : α) (hc : c ≠ 0) : ⇑(Homeomorph.mulRight₀ c hc) = (· * c) :=
  rfl

@[simp]
theorem mulRight₀_symm_apply (c : α) (hc : c ≠ 0) :
    ((Homeomorph.mulRight₀ c hc).symm : α → α) = (· * c⁻¹) :=
  rfl

end Homeomorph

section map_comap

variable [TopologicalSpace G₀] [GroupWithZero G₀] [ContinuousMul G₀] {a : G₀}

theorem map_mul_left_nhds₀ (ha : a ≠ 0) (b : G₀) : map (a * ·) (𝓝 b) = 𝓝 (a * b) :=
  (Homeomorph.mulLeft₀ a ha).map_nhds_eq b

theorem map_mul_left_nhds_one₀ (ha : a ≠ 0) : map (a * ·) (𝓝 1) = 𝓝 (a) := by
  rw [map_mul_left_nhds₀ ha, mul_one]

theorem map_mul_right_nhds₀ (ha : a ≠ 0) (b : G₀) : map (· * a) (𝓝 b) = 𝓝 (b * a) :=
  (Homeomorph.mulRight₀ a ha).map_nhds_eq b

theorem map_mul_right_nhds_one₀ (ha : a ≠ 0) : map (· * a) (𝓝 1) = 𝓝 (a) := by
  rw [map_mul_right_nhds₀ ha, one_mul]

theorem nhds_translation_mul_inv₀ (ha : a ≠ 0) : comap (· * a⁻¹) (𝓝 1) = 𝓝 a :=
  ((Homeomorph.mulRight₀ a ha).symm.comap_nhds_eq 1).trans <| by simp

/-- If a group with zero has continuous multiplication and `fun x ↦ x⁻¹` is continuous at one,
then it is continuous at any unit. -/
theorem HasContinuousInv₀.of_nhds_one (h : Tendsto Inv.inv (𝓝 (1 : G₀)) (𝓝 1)) :
    HasContinuousInv₀ G₀ where
  continuousAt_inv₀ x hx := by
    have hx' := inv_ne_zero hx
    rw [ContinuousAt, ← map_mul_left_nhds_one₀ hx, ← nhds_translation_mul_inv₀ hx',
      tendsto_map'_iff, tendsto_comap_iff]
    simpa only [Function.comp_def, mul_inv_rev, mul_inv_cancel_right₀ hx']

end map_comap

section ZPow

variable [GroupWithZero G₀] [TopologicalSpace G₀] [HasContinuousInv₀ G₀] [ContinuousMul G₀]

theorem continuousAt_zpow₀ (x : G₀) (m : ℤ) (h : x ≠ 0 ∨ 0 ≤ m) :
    ContinuousAt (fun x ↦ x ^ m) x := by
  rcases m with m | m
  · simpa only [Int.ofNat_eq_coe, zpow_natCast] using continuousAt_pow x m
  · simp only [zpow_negSucc]
    have hx : x ≠ 0 := h.resolve_right (Int.negSucc_lt_zero m).not_ge
    exact (continuousAt_pow x (m + 1)).inv₀ (pow_ne_zero _ hx)

theorem continuousOn_zpow₀ (m : ℤ) : ContinuousOn (fun x : G₀ ↦ x ^ m) {0}ᶜ := fun _x hx ↦
  (continuousAt_zpow₀ _ _ (Or.inl hx)).continuousWithinAt

theorem Filter.Tendsto.zpow₀ {f : α → G₀} {l : Filter α} {a : G₀} (hf : Tendsto f l (𝓝 a)) (m : ℤ)
    (h : a ≠ 0 ∨ 0 ≤ m) : Tendsto (fun x ↦ f x ^ m) l (𝓝 (a ^ m)) :=
  (continuousAt_zpow₀ _ m h).tendsto.comp hf

variable {X : Type*} [TopologicalSpace X] {a : X} {s : Set X} {f : X → G₀}

@[fun_prop]
nonrec theorem ContinuousAt.zpow₀ (hf : ContinuousAt f a) (m : ℤ) (h : f a ≠ 0 ∨ 0 ≤ m) :
    ContinuousAt (fun x ↦ f x ^ m) a :=
  hf.zpow₀ m h

nonrec theorem ContinuousWithinAt.zpow₀ (hf : ContinuousWithinAt f s a) (m : ℤ)
    (h : f a ≠ 0 ∨ 0 ≤ m) : ContinuousWithinAt (fun x ↦ f x ^ m) s a :=
  hf.zpow₀ m h

@[fun_prop]
theorem ContinuousOn.zpow₀ (hf : ContinuousOn f s) (m : ℤ) (h : ∀ a ∈ s, f a ≠ 0 ∨ 0 ≤ m) :
    ContinuousOn (fun x ↦ f x ^ m) s := fun a ha ↦ (hf a ha).zpow₀ m (h a ha)

@[continuity, fun_prop]
theorem Continuous.zpow₀ (hf : Continuous f) (m : ℤ) (h0 : ∀ a, f a ≠ 0 ∨ 0 ≤ m) :
    Continuous fun x ↦ f x ^ m :=
  continuous_iff_continuousAt.2 fun x ↦ (hf.tendsto x).zpow₀ m (h0 x)

end ZPow
