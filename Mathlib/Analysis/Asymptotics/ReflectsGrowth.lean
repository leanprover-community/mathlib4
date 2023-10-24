/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Asymptotics.Theta

/-!
# Families with linear ordered asymptotics

We say that a function `g : ι → β` with linearly ordered codomain
*reflects growth rate* of a family of functions `f : ι → α → E` along a filter `l : Filter α` if

- `f i =o[l] f j` whenever `g i < g j`;
- `f i =O[l] f j` whenever `g i ≤ g j`
  (the actual definition assumes `g i = g j`
  because the case `g i < g j` follows from the previous assumption);
- `∃ᶠ x in l, f i x ≠ 0`.

The name is motivated by the following properties
of a triple `(f, g, l)` satisfying the above axioms.

- `f i =o[l] f j ↔ g i < g j`, see `Asymptotics.ReflectsGrowth.isLittleO`;
- `f i =O[l] f j ↔ g i ≤ g j`, see `Asymptotics.ReflectsGrowth.isBigO`;
- `f i =Θ[l] f j ↔ g i = g j`, see `Asymptotics.ReflectsGrowth.isTheta`.

## Keywords

asymptotics
-/

open Filter Bornology
open scoped Topology

namespace Asymptotics

section

variable {ι α β E : Type*} [LinearOrder β] [NormedAddCommGroup E] {f : ι → α → E} {g : ι → β}
  {l : Filter α} {i j : ι}

/-- A function `g : ι → β` with linear ordered codomain *reflects growth*
of a family of functions `f : ι → α → E`,
if `f i =o[l] f j` iff `g i < g j` and `f i =O[l] f j` iff `g i ≤ g j`.

The actual definition assumes only two implications
-/
structure ReflectsGrowth (f : ι → α → E) (g : ι → β) (l : Filter α) : Prop where
  isLittleO_of_lt {i j} : g i < g j → f i =o[l] f j
  isBigO_of_eq {i j} : g i = g j → f i =O[l] f j
  frequently_ne {i} : ∃ᶠ x in l, f i x ≠ 0

namespace ReflectsGrowth

lemma isBigO (h : ReflectsGrowth f g l) : f i =O[l] f j ↔ g i ≤ g j:=
  ⟨fun hO ↦ not_lt.1 fun hlt ↦ (h.isLittleO_of_lt hlt).not_isBigO h.frequently_ne hO, fun hle ↦
    hle.eq_or_lt.elim h.isBigO_of_eq fun hij ↦ (h.isLittleO_of_lt hij).isBigO⟩

lemma isLittleO (h : ReflectsGrowth f g l) : f i =o[l] f j ↔ g i < g j := by
  cases lt_or_le (g i) (g j) with
  | inl hij => simp [hij, h.isLittleO_of_lt]
  | inr hji => simp [hji.not_lt, (h.isBigO.2 hji).not_isLittleO h.frequently_ne]

lemma isTheta (h : ReflectsGrowth f g l) : f i =Θ[l] f j ↔ g i = g j := by
  simp only [IsTheta, h.isBigO, le_antisymm_iff]

lemma congr_right {γ : Type*} [LinearOrder γ] {g' : ι → γ} (h : ReflectsGrowth f g l)
    (hg : ∀ {i j}, g i < g j ↔ g' i < g' j) : ReflectsGrowth f g' l where
  isLittleO_of_lt hij := h.isLittleO.2 <| hg.2 hij
  isBigO_of_eq hij := h.isBigO.2 <| not_lt.1 <| mt hg.1 hij.not_gt
  frequently_ne := h.frequently_ne

lemma congr_left_isTheta {E' : Type*} [NormedAddCommGroup E'] {f' : ι → α → E'}
    (h : ReflectsGrowth f g l) (hf : ∀ {i}, f i =Θ[l] f' i) : ReflectsGrowth f' g l where
  isLittleO_of_lt := hf.isLittleO_congr_left.1 ∘ hf.isLittleO_congr_right.1 ∘ h.isLittleO.2
  isBigO_of_eq := hf.isBigO_congr_left.1 ∘ hf.isBigO_congr_right.1 ∘ h.isBigO_of_eq
  frequently_ne := (hf.eq_zero_iff.and_frequently h.frequently_ne).mono fun _ h ↦ mt h.1.2 h.2

lemma congr_left {f' : ι → α → E} (h : ReflectsGrowth f g l) (hf : ∀ {i}, f i =ᶠ[l] f' i) :
    ReflectsGrowth f' g l :=
  h.congr_left_isTheta hf.isTheta

protected lemma comp {ι' : Type*} (h : ReflectsGrowth f g l) (u : ι' → ι) :
    ReflectsGrowth (f ∘ u) (g ∘ u) l :=
  { h with }

end ReflectsGrowth

variable [Zero ι] [Zero β]

structure ReflectsGrowth₀ (f : ι → α → E) (g : ι → β) (l : Filter α)
    extends ReflectsGrowth f g l where
  protected map_zero : g 0 = 0 := by simp
  isTheta_map_zero_one : f 0 =Θ[l] (1 : α → ℝ)

namespace ReflectsGrowth₀

lemma isTheta_one_right (h : ReflectsGrowth₀ f g l) {a} : f a =Θ[l] (1 : α → ℝ) ↔ g a = 0 := by
  simp_rw [← h.isTheta_map_zero_one.isTheta_congr_right, h.isTheta, h.map_zero]

lemma isBigO_one_right (h : ReflectsGrowth₀ f g l) {a} : f a =O[l] (1 : α → ℝ) ↔ g a ≤ 0 := by
  simp_rw [← h.isTheta_map_zero_one.isBigO_congr_right, h.isBigO, h.map_zero]

lemma isBigO_one_left (h : ReflectsGrowth₀ f g l) {a} : (1 : α → ℝ) =O[l] f a ↔ 0 ≤ g a := by
  simp_rw [← h.isTheta_map_zero_one.isBigO_congr_left, h.isBigO, h.map_zero]

lemma isLittleO_one_right (h : ReflectsGrowth₀ f g l) {a} :
    f a =o[l] (1 : α → ℝ) ↔ g a < 0 := by
  simp_rw [← h.isTheta_map_zero_one.isLittleO_congr_right, h.isLittleO, h.map_zero]

lemma isLittleO_one_left (h : ReflectsGrowth₀ f g l) {a} :
    (1 : α → ℝ) =o[l] f a ↔ 0 < g a := by
  simp_rw [← h.isTheta_map_zero_one.isLittleO_congr_left, h.isLittleO, h.map_zero]

lemma isBoundedUnder_le_norm (h : ReflectsGrowth₀ f g l) {a} :
    IsBoundedUnder (· ≤ ·) l (‖f a ·‖) ↔ g a ≤ 0 :=
  (isBigO_one_iff _).symm.trans h.isBigO_one_right

lemma tendsto_zero (h : ReflectsGrowth₀ f g l) {a} : Tendsto (f a) l (𝓝 0) ↔ g a < 0 :=
  (isLittleO_one_iff ℝ).symm.trans h.isLittleO_one_right

lemma tendsto_norm_atTop (h : ReflectsGrowth₀ f g l) {a} :
    Tendsto (‖f a ·‖) l atTop ↔ 0 < g a :=
  (isLittleO_one_left_iff _).symm.trans h.isLittleO_one_left

end ReflectsGrowth₀

end

section

variable {G α H E : Type*} [AddGroup G] [LinearOrderedAddCommGroup H] [NormedAddCommGroup E]
  {f : G → α → E} {g : G →+ H} {l : Filter α}

structure ReflectsGrowthAddMul (f : G → α → E) (g : G →+ H) (l : Filter α) : Prop where
  eventuallyEq_norm_map_add (a b : G) : (‖f (a + b) ·‖) =ᶠ[l] fun x ↦ ‖f a x‖ * ‖f b x‖
  tendsto_of_pos {a : G} (ha : 0 < g a) : Tendsto (‖f a ·‖) l atTop
  isBigO_of_eq_zero {a : G} (ha : g a = 0) : (1 : α → ℝ) =O[l] f a
  frequently_ne {a : G} : ∃ᶠ x in l, f a x ≠ 0

namespace ReflectsGrowthAddMul

lemma eventuallyEq_norm_map_zero (h : ReflectsGrowthAddMul f g l) : (‖f 0 ·‖) =ᶠ[l] 1 := by
  rcases (h.isBigO_of_eq_zero (map_zero g)).bound with ⟨C, hC⟩
  filter_upwards [h.eventuallyEq_norm_map_add 0 0, hC] with x hx₀ hx₁
  have : ‖f 0 x‖ ≠ 0 := fun h ↦ by simp [h, one_pos.not_le] at hx₁
  rwa [add_zero, left_eq_mul₀ this] at hx₀

lemma isTheta_map_zero_one (h : ReflectsGrowthAddMul f g l) : f 0 =Θ[l] (1 : α → ℝ) :=
  h.eventuallyEq_norm_map_zero.isTheta.of_norm_left

lemma reflectsGrowth₀ (h : ReflectsGrowthAddMul f g l) : ReflectsGrowth₀ f g l where
  isLittleO_of_lt {a b} hlt := .of_norm_norm <|
    calc
      (‖f a ·‖) = (1 * ‖f a ·‖) := (one_mul _).symm
      _ =o[l] fun x ↦ ‖f (b - a) x‖ * ‖f a x‖ := by
        refine .mul_isBigO ?_ (isBigO_refl _ _)
        simp only [isLittleO_one_left_iff, norm_norm]
        exact h.tendsto_of_pos <| by rwa [map_sub, sub_pos]
      _ =ᶠ[l] (‖f b ·‖) := by simpa using (h.eventuallyEq_norm_map_add (b - a) a).symm
  isBigO_of_eq {a b} heq := .of_norm_norm <|
    calc
      (‖f a ·‖) = (1 * ‖f a ·‖) := (one_mul _).symm
      _ =O[l] fun x ↦ ‖f (b - a) x‖ * ‖f a x‖ :=
        (h.isBigO_of_eq_zero <| by simp [heq]).norm_right.mul (isBigO_refl _ _)
      _ =ᶠ[l] (‖f b ·‖) := by simpa using (h.eventuallyEq_norm_map_add (b - a) a).symm
  frequently_ne := h.frequently_ne
  isTheta_map_zero_one := h.isTheta_map_zero_one

lemma isLittleO (h : ReflectsGrowthAddMul f g l) {a b} : f a =o[l] f b ↔ g a < g b :=
  h.reflectsGrowth₀.isLittleO

lemma isBigO (h : ReflectsGrowthAddMul f g l) {a b} : f a =O[l] f b ↔ g a ≤ g b :=
  h.reflectsGrowth₀.isBigO

lemma isTheta (h : ReflectsGrowthAddMul f g l) {a b} : f a =Θ[l] f b ↔ g a = g b :=
  h.reflectsGrowth₀.isTheta

lemma isTheta_one_right (h : ReflectsGrowthAddMul f g l) {a} : f a =Θ[l] (1 : α → ℝ) ↔ g a = 0 :=
  h.reflectsGrowth₀.isTheta_one_right

lemma isBigO_one_right (h : ReflectsGrowthAddMul f g l) {a} : f a =O[l] (1 : α → ℝ) ↔ g a ≤ 0 :=
  h.reflectsGrowth₀.isBigO_one_right

lemma isBigO_one_left (h : ReflectsGrowthAddMul f g l) {a} : (1 : α → ℝ) =O[l] f a ↔ 0 ≤ g a :=
  h.reflectsGrowth₀.isBigO_one_left

lemma isLittleO_one_right (h : ReflectsGrowthAddMul f g l) {a} : f a =o[l] (1 : α → ℝ) ↔ g a < 0 :=
  h.reflectsGrowth₀.isLittleO_one_right

lemma isLittleO_one_left (h : ReflectsGrowthAddMul f g l) {a} : (1 : α → ℝ) =o[l] f a ↔ 0 < g a :=
  h.reflectsGrowth₀.isLittleO_one_left

lemma isBoundedUnder_le_norm (h : ReflectsGrowthAddMul f g l) {a} :
    IsBoundedUnder (· ≤ ·) l (‖f a ·‖) ↔ g a ≤ 0 :=
  h.reflectsGrowth₀.isBoundedUnder_le_norm

lemma tendsto_zero (h : ReflectsGrowthAddMul f g l) {a} : Tendsto (f a) l (𝓝 0) ↔ g a < 0 :=
  h.reflectsGrowth₀.tendsto_zero

lemma tendsto_norm_atTop (h : ReflectsGrowthAddMul f g l) {a} :
    Tendsto (‖f a ·‖) l atTop ↔ 0 < g a :=
  (isLittleO_one_left_iff _).symm.trans h.isLittleO_one_left

lemma mono (hl : ReflectsGrowthAddMul f g l) {l'} (hle : l' ≤ l)
    (h₀ : ∀ {a}, ∃ᶠ x in l', f a x ≠ 0) : ReflectsGrowthAddMul f g l' where
  eventuallyEq_norm_map_add a b := (hl.eventuallyEq_norm_map_add a b).filter_mono hle
  tendsto_of_pos hpos := (hl.tendsto_of_pos hpos).mono_left hle
  isBigO_of_eq_zero hzero := (hl.isBigO_of_eq_zero hzero).mono hle
  frequently_ne := h₀
  
end ReflectsGrowthAddMul

lemma reflectsGrowthAddMul_zpow_cobounded {𝕜 : Type*} [NormedDivisionRing 𝕜] :
    ReflectsGrowthAddMul (fun (n : ℤ) (x : 𝕜) ↦ x ^ n) (AddMonoidHom.id ℤ) (cobounded 𝕜) where
  eventuallyEq_norm_map_add _ _ := (eventually_ne_cobounded 0).mono fun x hx ↦ by
    simp only [zpow_add₀ hx, norm_mul]
  -- tendsto_of_pos h := tendsto_abs_atTop_atTop.comp (tendsto_zpow_atTop_atTop h)
  isBigO_of_eq_zero _ := by simp_all [isBoundedUnder_const]
  frequently_ne := (eventually_ne_cobounded 0).frequently.mono fun _ ↦ zpow_ne_zero _

lemma reflectsGrowthAddMul_zpow_atTop :
    ReflectsGrowthAddMul (fun (n : ℤ) (x : ℝ) ↦ x ^ n) (AddMonoidHom.id ℤ) atTop where
  eventuallyEq_norm_map_add _ _ := (eventually_ne_atTop 0).mono fun x hx ↦ by
    simp only [zpow_add₀ hx, norm_mul]
  tendsto_of_pos h := tendsto_abs_atTop_atTop.comp (tendsto_zpow_atTop_atTop h)
  isBigO_of_eq_zero _ := by simp_all [isBigO_refl, Pi.one_def]
  frequently_ne := (eventually_ne_atTop 0).frequently.mono fun _ ↦ zpow_ne_zero _

@[simp]
lemma isLittleO_zpow_zpow_atTop {m n : ℤ} : (· ^ m : ℝ → ℝ) =o[atTop] (· ^ n) ↔ m < n :=
  reflectsGrowthAddMul_zpow_atTop.isLittleO

lemma reflectsGrowth_pow_atTop : ReflectsGrowth (fun (n : ℕ) (x : ℝ) ↦ x ^ n) id atTop :=
  reflectsGrowthAddMul_zpow_atTop
