/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Order.Monovary
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.FieldSimp

/-!
# Product of convex functions

This file proves that the product of convex functions is convex, provided they monovary.

As corollaries, we also prove that `x ↦ x ^ n` is convex
* `Even.convexOn_pow`: for even `n : ℕ`.
* `convexOn_pow`: over $[0, +∞)$ for `n : ℕ`.
* `convexOn_zpow`: over $(0, +∞)$ For `n : ℤ`.
-/

open Set

variable {𝕜 E F G : Type*}

section LinearOrderedCommRing
variable [CommRing 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [CommRing E] [LinearOrder E] [IsStrictOrderedRing E]
  [AddCommGroup F] [LinearOrder F] [IsOrderedAddMonoid F]
  [AddCommGroup G] [Module 𝕜 G]
  [Module 𝕜 E] [Module 𝕜 F] [Module E F] [IsScalarTower 𝕜 E F] [SMulCommClass 𝕜 E F]
  [IsOrderedModule 𝕜 F] [IsStrictOrderedModule E F] {s : Set G} {f : G → E} {g : G → F}

lemma ConvexOn.smul' (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x)
    (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : MonovaryOn f g s) : ConvexOn 𝕜 s (f • g) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab ↦ ?_⟩
  dsimp
  refine
    (smul_le_smul (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab) (hf₀ <| hf.1 hx hy ha hb hab) <|
      add_nonneg (smul_nonneg ha <| hg₀ hx) <| smul_nonneg hb <| hg₀ hy).trans ?_
  calc
      _ = (a * a) • (f x • g x) + (b * b) • (f y • g y) + (a * b) • (f x • g y + f y • g x) := ?_
    _ ≤ (a * a) • (f x • g x) + (b * b) • (f y • g y) + (a * b) • (f x • g x + f y • g y) := by
        gcongr _ + (a * b) • ?_; exact hfg.smul_add_smul_le_smul_add_smul hx hy
    _ = (a * (a + b)) • (f x • g x) + (b * (a + b)) • (f y • g y) := by
        simp only [mul_add, add_smul, smul_add, mul_comm _ a]; abel
    _ = _ := by simp_rw [hab, mul_one]
  simp only [add_smul, smul_add]
  rw [← smul_smul_smul_comm a, ← smul_smul_smul_comm b, ← smul_smul_smul_comm a b,
    ← smul_smul_smul_comm b b, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_comm b,
    add_comm _ ((b * b) • f y • g y), add_add_add_comm, add_comm ((a * b) • f y • g x)]

lemma ConcaveOn.smul' [IsOrderedModule 𝕜 E] (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f • g) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab ↦ ?_⟩
  dsimp
  refine (smul_le_smul (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)
    (add_nonneg (smul_nonneg ha <| hf₀ hx) <| smul_nonneg hb <| hf₀ hy)
    (hg₀ <| hf.1 hx hy ha hb hab)).trans' ?_
  calc a • f x • g x + b • f y • g y
        = (a * (a + b)) • (f x • g x) + (b * (a + b)) • (f y • g y) := by simp_rw [hab, mul_one]
    _ = (a * a) • (f x • g x) + (b * b) • (f y • g y) + (a * b) • (f x • g x + f y • g y) := by
        simp only [mul_add, add_smul, smul_add, mul_comm _ a]; abel
    _ ≤ (a * a) • (f x • g x) + (b * b) • (f y • g y) + (a * b) • (f x • g y + f y • g x) := by
        gcongr _ + (a * b) • ?_; exact hfg.smul_add_smul_le_smul_add_smul hx hy
    _ = _ := ?_
  simp only [add_smul, smul_add]
  rw [← smul_smul_smul_comm a, ← smul_smul_smul_comm b, ← smul_smul_smul_comm a b,
    ← smul_smul_smul_comm b b, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_comm b a,
    add_comm ((a * b) • f x • g y), add_comm ((a * b) • f x • g y), add_add_add_comm]

lemma ConvexOn.smul'' [IsOrderedModule 𝕜 E] (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0) (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f • g) := by
  rw [← neg_smul_neg]
  exact hf.neg.smul' hg.neg (fun x hx ↦ neg_nonneg.2 <| hf₀ hx) (fun x hx ↦ neg_nonneg.2 <| hg₀ hx)
    hfg.neg

lemma ConcaveOn.smul'' (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0)
    (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : MonovaryOn f g s) : ConvexOn 𝕜 s (f • g) := by
  rw [← neg_smul_neg]
  exact hf.neg.smul' hg.neg (fun x hx ↦ neg_nonneg.2 <| hf₀ hx) (fun x hx ↦ neg_nonneg.2 <| hg₀ hx)
    hfg.neg

lemma ConvexOn.smul_concaveOn (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f • g) := by
  rw [← neg_convexOn_iff, ← smul_neg]
  exact hf.smul' hg.neg hf₀ (fun x hx ↦ neg_nonneg.2 <| hg₀ hx) hfg.neg_right

lemma ConcaveOn.smul_convexOn [IsOrderedModule 𝕜 E] (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : MonovaryOn f g s) :
    ConvexOn 𝕜 s (f • g) := by
  rw [← neg_concaveOn_iff, ← smul_neg]
  exact hf.smul' hg.neg hf₀ (fun x hx ↦ neg_nonneg.2 <| hg₀ hx) hfg.neg_right

lemma ConvexOn.smul_concaveOn' [IsOrderedModule 𝕜 E] (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : MonovaryOn f g s) :
    ConvexOn 𝕜 s (f • g) := by
  rw [← neg_concaveOn_iff, ← smul_neg]
  exact hf.smul'' hg.neg hf₀ (fun x hx ↦ neg_nonpos.2 <| hg₀ hx) hfg.neg_right

lemma ConcaveOn.smul_convexOn' (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f • g) := by
  rw [← neg_convexOn_iff, ← smul_neg]
  exact hf.smul'' hg.neg hf₀ (fun x hx ↦ neg_nonpos.2 <| hg₀ hx) hfg.neg_right

variable [IsOrderedModule 𝕜 E] [IsScalarTower 𝕜 E E] [SMulCommClass 𝕜 E E] {f g : G → E}

lemma ConvexOn.mul (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x)
    (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : MonovaryOn f g s) :
    ConvexOn 𝕜 s (f * g) := hf.smul' hg hf₀ hg₀ hfg

lemma ConcaveOn.mul (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f * g) := hf.smul' hg hf₀ hg₀ hfg

lemma ConvexOn.mul' (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0)
    (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f * g) := hf.smul'' hg hf₀ hg₀ hfg

lemma ConcaveOn.mul' (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0)
    (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : MonovaryOn f g s) :
    ConvexOn 𝕜 s (f * g) := hf.smul'' hg hf₀ hg₀ hfg

lemma ConvexOn.mul_concaveOn (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f * g) := hf.smul_concaveOn hg hf₀ hg₀ hfg

lemma ConcaveOn.mul_convexOn (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : MonovaryOn f g s) :
    ConvexOn 𝕜 s (f * g) := hf.smul_convexOn hg hf₀ hg₀ hfg

lemma ConvexOn.mul_concaveOn' (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : MonovaryOn f g s) :
    ConvexOn 𝕜 s (f * g) := hf.smul_concaveOn' hg hf₀ hg₀ hfg

lemma ConcaveOn.mul_convexOn' (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
    (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : AntivaryOn f g s) :
    ConcaveOn 𝕜 s (f • g) := hf.smul_convexOn' hg hf₀ hg₀ hfg

lemma ConvexOn.pow (hf : ConvexOn 𝕜 s f) (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) :
    ∀ n, ConvexOn 𝕜 s (f ^ n)
  | 0 => by simpa using convexOn_const 1 hf.1
  | n + 1 => by
    rw [pow_succ']
    exact hf.mul (hf.pow hf₀ _) hf₀ (fun x hx ↦ pow_nonneg (hf₀ hx) _) <|
      (monovaryOn_self f s).pow_right₀ hf₀ n

/-- `x^n`, `n : ℕ` is convex on `[0, +∞)` for all `n`. -/
lemma convexOn_pow : ∀ n, ConvexOn 𝕜 (Ici 0) fun x : 𝕜 ↦ x ^ n :=
  (convexOn_id <| convex_Ici _).pow fun _ ↦ id

/-- `x^n`, `n : ℕ` is convex on the whole real line whenever `n` is even. -/
protected lemma Even.convexOn_pow {n : ℕ} (hn : Even n) : ConvexOn 𝕜 univ fun x : 𝕜 ↦ x ^ n := by
  obtain ⟨n, rfl⟩ := hn
  simp_rw [← two_mul, pow_mul]
  refine ConvexOn.pow ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ sub_nonneg.1 ?_⟩
    (fun _ _ ↦ by positivity) _
  calc
    (0 : 𝕜) ≤ (a * b) * (x - y) ^ 2 := by positivity
    _ = _ := by obtain rfl := eq_sub_of_add_eq hab; simp only [smul_eq_mul]; ring

end LinearOrderedCommRing

section LinearOrderedField
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

open Int in
/-- `x^m`, `m : ℤ` is convex on `(0, +∞)` for all `m`. -/
lemma convexOn_zpow : ∀ n : ℤ, ConvexOn 𝕜 (Ioi 0) fun x : 𝕜 ↦ x ^ n
  | (n : ℕ) => by
    simp_rw [zpow_natCast]
    exact (convexOn_pow n).subset Ioi_subset_Ici_self (convex_Ioi _)
  | -[n+1] => by
    simp_rw [zpow_negSucc, ← inv_pow]
    refine (convexOn_iff_forall_pos.2 ⟨convex_Ioi _, ?_⟩).pow (fun x (hx : 0 < x) ↦ by positivity) _
    rintro x (hx : 0 < x) y (hy : 0 < y) a b ha hb hab
    simp only [smul_eq_mul]
    field_simp
    rw [div_le_div_iff₀, ← sub_nonneg]
    · calc
        0 ≤ a * b * (x - y) ^ 2 := by positivity
        _ = _ := by obtain rfl := eq_sub_of_add_eq hab; ring
    all_goals positivity

end LinearOrderedField
