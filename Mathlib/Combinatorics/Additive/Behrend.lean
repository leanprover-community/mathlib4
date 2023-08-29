/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.Additive.SalemSpencer
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Complex.ExponentialBounds

#align_import combinatorics.additive.behrend from "leanprover-community/mathlib"@"4fa54b337f7d52805480306db1b1439c741848c8"

/-!
# Behrend's bound on Roth numbers

This file proves Behrend's lower bound on Roth numbers. This says that we can find a subset of
`{1, ..., n}` of size `n / exp (O (sqrt (log n)))` which does not contain arithmetic progressions of
length `3`.

The idea is that the sphere (in the `n` dimensional Euclidean space) doesn't contain arithmetic
progressions (literally) because the corresponding ball is strictly convex. Thus we can take
integer points on that sphere and map them onto `ℕ` in a way that preserves arithmetic progressions
(`Behrend.map`).

## Main declarations

* `Behrend.sphere`: The intersection of the Euclidean sphere with the positive integer quadrant.
  This is the set that we will map on `ℕ`.
* `Behrend.map`: Given a natural number `d`, `Behrend.map d : ℕⁿ → ℕ` reads off the coordinates as
  digits in base `d`.
* `Behrend.card_sphere_le_rothNumberNat`: Implicit lower bound on Roth numbers in terms of
  `Behrend.sphere`.
* `Behrend.roth_lower_bound`: Behrend's explicit lower bound on Roth numbers.

## References

* [Bryan Gillespie, *Behrend’s Construction*]
  (http://www.epsilonsmall.com/resources/behrends-construction/behrend.pdf)
* Behrend, F. A., "On sets of integers which contain no three terms in arithmetical progression"
* [Wikipedia, *Salem-Spencer set*](https://en.wikipedia.org/wiki/Salem–Spencer_set)

## Tags

Salem-Spencer, Behrend construction, arithmetic progression, sphere, strictly convex
-/


open Nat hiding log

open Finset Real

open scoped BigOperators Pointwise

namespace Behrend

variable {α β : Type*} {n d k N : ℕ} {x : Fin n → ℕ}

/-!
### Turning the sphere into a Salem-Spencer set

We define `Behrend.sphere`, the intersection of the $L^2$ sphere with the positive quadrant of
integer points. Because the $L^2$ closed ball is strictly convex, the $L^2$ sphere and
`Behrend.sphere` are Salem-Spencer (`addSalemSpencer_sphere`). Then we can turn this set in
`Fin n → ℕ` into a set in `ℕ` using `Behrend.map`, which preserves `AddSalemSpencer` because it is
an additive monoid homomorphism.
-/


/-- The box `{0, ..., d - 1}^n` as a `Finset`. -/
def box (n d : ℕ) : Finset (Fin n → ℕ) :=
  Fintype.piFinset fun _ => range d
#align behrend.box Behrend.box

theorem mem_box : x ∈ box n d ↔ ∀ i, x i < d := by simp only [box, Fintype.mem_piFinset, mem_range]
                                                   -- 🎉 no goals
#align behrend.mem_box Behrend.mem_box

@[simp]
theorem card_box : (box n d).card = d ^ n := by simp [box]
                                                -- 🎉 no goals
#align behrend.card_box Behrend.card_box

@[simp]
theorem box_zero : box (n + 1) 0 = ∅ := by simp [box]
                                           -- 🎉 no goals
#align behrend.box_zero Behrend.box_zero

/-- The intersection of the sphere of radius `sqrt k` with the integer points in the positive
quadrant. -/
def sphere (n d k : ℕ) : Finset (Fin n → ℕ) :=
  (box n d).filter fun x => ∑ i, x i ^ 2 = k
#align behrend.sphere Behrend.sphere

theorem sphere_zero_subset : sphere n d 0 ⊆ 0 := fun x => by simp [sphere, Function.funext_iff]
                                                             -- 🎉 no goals
#align behrend.sphere_zero_subset Behrend.sphere_zero_subset

@[simp]
theorem sphere_zero_right (n k : ℕ) : sphere (n + 1) 0 k = ∅ := by simp [sphere]
                                                                   -- 🎉 no goals
#align behrend.sphere_zero_right Behrend.sphere_zero_right

theorem sphere_subset_box : sphere n d k ⊆ box n d :=
  filter_subset _ _
#align behrend.sphere_subset_box Behrend.sphere_subset_box

theorem norm_of_mem_sphere {x : Fin n → ℕ} (hx : x ∈ sphere n d k) :
    ‖(PiLp.equiv 2 _).symm ((↑) ∘ x : Fin n → ℝ)‖ = Real.sqrt k := by
  rw [EuclideanSpace.norm_eq]
  -- ⊢ Real.sqrt (∑ i : Fin n, ‖↑(PiLp.equiv 2 fun a => ℝ).symm (Nat.cast ∘ x) i‖ ^ …
  dsimp
  -- ⊢ Real.sqrt (∑ i : Fin n, |↑(x i)| ^ 2) = Real.sqrt ↑k
  simp_rw [abs_cast, ← cast_pow, ← cast_sum, (mem_filter.1 hx).2]
  -- 🎉 no goals
#align behrend.norm_of_mem_sphere Behrend.norm_of_mem_sphere

theorem sphere_subset_preimage_metric_sphere : (sphere n d k : Set (Fin n → ℕ)) ⊆
    (fun x : Fin n → ℕ => (PiLp.equiv 2 _).symm ((↑) ∘ x : Fin n → ℝ)) ⁻¹'
      Metric.sphere (0 : PiLp 2 fun _ : Fin n => ℝ) (Real.sqrt k) :=
  fun x hx => by rw [Set.mem_preimage, mem_sphere_zero_iff_norm, norm_of_mem_sphere hx]
                 -- 🎉 no goals
#align behrend.sphere_subset_preimage_metric_sphere Behrend.sphere_subset_preimage_metric_sphere

/-- The map that appears in Behrend's bound on Roth numbers. -/
@[simps]
def map (d : ℕ) : (Fin n → ℕ) →+ ℕ where
  toFun a := ∑ i, a i * d ^ (i : ℕ)
  map_zero' := by simp_rw [Pi.zero_apply, zero_mul, sum_const_zero]
                  -- 🎉 no goals
  map_add' a b := by simp_rw [Pi.add_apply, add_mul, sum_add_distrib]
                     -- 🎉 no goals
#align behrend.map Behrend.map

-- @[simp] -- Porting note: simp can prove this
theorem map_zero (d : ℕ) (a : Fin 0 → ℕ) : map d a = 0 := by simp [map]
                                                             -- 🎉 no goals
#align behrend.map_zero Behrend.map_zero

theorem map_succ (a : Fin (n + 1) → ℕ) :
    map d a = a 0 + (∑ x : Fin n, a x.succ * d ^ (x : ℕ)) * d := by
  simp [map, Fin.sum_univ_succ, _root_.pow_succ', ← mul_assoc, ← sum_mul]
  -- 🎉 no goals
#align behrend.map_succ Behrend.map_succ

theorem map_succ' (a : Fin (n + 1) → ℕ) : map d a = a 0 + map d (a ∘ Fin.succ) * d :=
  map_succ _
#align behrend.map_succ' Behrend.map_succ'

theorem map_monotone (d : ℕ) : Monotone (map d : (Fin n → ℕ) → ℕ) := fun x y h => by
  dsimp; exact sum_le_sum fun i _ => Nat.mul_le_mul_right _ <| h i
  -- ⊢ ∑ i : Fin n, x i * d ^ ↑i ≤ ∑ i : Fin n, y i * d ^ ↑i
         -- 🎉 no goals
#align behrend.map_monotone Behrend.map_monotone

theorem map_mod (a : Fin n.succ → ℕ) : map d a % d = a 0 % d := by
  rw [map_succ, Nat.add_mul_mod_self_right]
  -- 🎉 no goals
#align behrend.map_mod Behrend.map_mod

theorem map_eq_iff {x₁ x₂ : Fin n.succ → ℕ} (hx₁ : ∀ i, x₁ i < d) (hx₂ : ∀ i, x₂ i < d) :
    map d x₁ = map d x₂ ↔ x₁ 0 = x₂ 0 ∧ map d (x₁ ∘ Fin.succ) = map d (x₂ ∘ Fin.succ) := by
  refine' ⟨fun h => _, fun h => by rw [map_succ', map_succ', h.1, h.2]⟩
  -- ⊢ x₁ 0 = x₂ 0 ∧ ↑(map d) (x₁ ∘ Fin.succ) = ↑(map d) (x₂ ∘ Fin.succ)
  have : x₁ 0 = x₂ 0 := by
    rw [← mod_eq_of_lt (hx₁ _), ← map_mod, ← mod_eq_of_lt (hx₂ _), ← map_mod, h]
  rw [map_succ, map_succ, this, add_right_inj, mul_eq_mul_right_iff] at h
  -- ⊢ x₁ 0 = x₂ 0 ∧ ↑(map d) (x₁ ∘ Fin.succ) = ↑(map d) (x₂ ∘ Fin.succ)
  exact ⟨this, h.resolve_right (pos_of_gt (hx₁ 0)).ne'⟩
  -- 🎉 no goals
#align behrend.map_eq_iff Behrend.map_eq_iff

theorem map_injOn : {x : Fin n → ℕ | ∀ i, x i < d}.InjOn (map d) := by
  intro x₁ hx₁ x₂ hx₂ h
  -- ⊢ x₁ = x₂
  induction' n with n ih
  -- ⊢ x₁ = x₂
  · simp
    -- 🎉 no goals
  rw [forall_const] at ih
  -- ⊢ x₁ = x₂
  ext i
  -- ⊢ x₁ i = x₂ i
  have x := (map_eq_iff hx₁ hx₂).1 h
  -- ⊢ x₁ i = x₂ i
  refine' Fin.cases x.1 (congr_fun <| ih (fun _ => _) (fun _ => _) x.2) i
  -- ⊢ x₁ (Fin.succ x✝) < d
  · exact hx₁ _
    -- 🎉 no goals
  · exact hx₂ _
    -- 🎉 no goals
#align behrend.map_inj_on Behrend.map_injOn

theorem map_le_of_mem_box (hx : x ∈ box n d) :
    map (2 * d - 1) x ≤ ∑ i : Fin n, (d - 1) * (2 * d - 1) ^ (i : ℕ) :=
  map_monotone (2 * d - 1) fun _ => Nat.le_pred_of_lt <| mem_box.1 hx _
#align behrend.map_le_of_mem_box Behrend.map_le_of_mem_box

nonrec theorem addSalemSpencer_sphere : AddSalemSpencer (sphere n d k : Set (Fin n → ℕ)) := by
  set f : (Fin n → ℕ) →+ EuclideanSpace ℝ (Fin n) :=
    { toFun := fun f => ((↑) : ℕ → ℝ) ∘ f
      map_zero' := funext fun _ => cast_zero
      map_add' := fun _ _ => funext fun _ => cast_add _ _ }
  refine' AddSalemSpencer.of_image (f.toAddFreimanHom (sphere n d k : Set (Fin n → ℕ)) 2) _ _
  -- ⊢ Set.InjOn ↑(AddMonoidHom.toAddFreimanHom (↑(sphere n d k)) 2 f) ↑(sphere n d …
  · exact cast_injective.comp_left.injOn _
    -- 🎉 no goals
  refine' (addSalemSpencer_sphere 0 <| Real.sqrt k).mono (Set.image_subset_iff.2 fun x => _)
  -- ⊢ x ∈ ↑(sphere n d k) → x ∈ ↑(AddMonoidHom.toAddFreimanHom (↑(sphere n d k)) 2 …
  rw [Set.mem_preimage, mem_sphere_zero_iff_norm]
  -- ⊢ x ∈ ↑(sphere n d k) → ‖↑(AddMonoidHom.toAddFreimanHom (↑(sphere n d k)) 2 f) …
  exact norm_of_mem_sphere
  -- 🎉 no goals
#align behrend.add_salem_spencer_sphere Behrend.addSalemSpencer_sphere

theorem addSalemSpencer_image_sphere :
    AddSalemSpencer ((sphere n d k).image (map (2 * d - 1)) : Set ℕ) := by
  rw [coe_image]
  -- ⊢ AddSalemSpencer (↑(map (2 * d - 1)) '' ↑(sphere n d k))
  refine' @AddSalemSpencer.image _ (Fin n → ℕ) ℕ _ _ (sphere n d k) _ (map (2 * d - 1))
    (map_injOn.mono _) addSalemSpencer_sphere
  · exact x
    -- 🎉 no goals
  rw [Set.add_subset_iff]
  -- ⊢ ∀ (x : Fin n → ℕ), x ∈ ↑(sphere n d k) → ∀ (y : Fin n → ℕ), y ∈ ↑(sphere n d …
  rintro a ha b hb i
  -- ⊢ (a + b) i < 2 * d - 1
  have hai := mem_box.1 (sphere_subset_box ha) i
  -- ⊢ (a + b) i < 2 * d - 1
  have hbi := mem_box.1 (sphere_subset_box hb) i
  -- ⊢ (a + b) i < 2 * d - 1
  rw [lt_tsub_iff_right, ← succ_le_iff, two_mul]
  -- ⊢ succ ((a + b) i + 1) ≤ d + d
  exact (add_add_add_comm _ _ 1 1).trans_le (_root_.add_le_add hai hbi)
  -- 🎉 no goals
#align behrend.add_salem_spencer_image_sphere Behrend.addSalemSpencer_image_sphere

theorem sum_sq_le_of_mem_box (hx : x ∈ box n d) : ∑ i : Fin n, x i ^ 2 ≤ n * (d - 1) ^ 2 := by
  rw [mem_box] at hx
  -- ⊢ ∑ i : Fin n, x i ^ 2 ≤ n * (d - 1) ^ 2
  have : ∀ i, x i ^ 2 ≤ (d - 1) ^ 2 := fun i =>
    Nat.pow_le_pow_of_le_left (Nat.le_pred_of_lt (hx i)) _
  exact (sum_le_card_nsmul univ _ _ fun i _ => this i).trans (by rw [card_fin, smul_eq_mul])
  -- 🎉 no goals
#align behrend.sum_sq_le_of_mem_box Behrend.sum_sq_le_of_mem_box

theorem sum_eq : (∑ i : Fin n, d * (2 * d + 1) ^ (i : ℕ)) = ((2 * d + 1) ^ n - 1) / 2 := by
  refine' (Nat.div_eq_of_eq_mul_left zero_lt_two _).symm
  -- ⊢ (2 * d + 1) ^ n - 1 = (∑ i : Fin n, d * (2 * d + 1) ^ ↑i) * 2
  rw [← sum_range fun i => d * (2 * d + 1) ^ (i : ℕ), ← mul_sum, mul_right_comm, mul_comm d, ←
    geom_sum_mul_add, add_tsub_cancel_right, mul_comm]
#align behrend.sum_eq Behrend.sum_eq

theorem sum_lt : (∑ i : Fin n, d * (2 * d + 1) ^ (i : ℕ)) < (2 * d + 1) ^ n :=
  sum_eq.trans_lt <| (Nat.div_le_self _ 2).trans_lt <| pred_lt (pow_pos (succ_pos _) _).ne'
#align behrend.sum_lt Behrend.sum_lt

theorem card_sphere_le_rothNumberNat (n d k : ℕ) :
    (sphere n d k).card ≤ rothNumberNat ((2 * d - 1) ^ n) := by
  cases n
  -- ⊢ card (sphere zero d k) ≤ ↑rothNumberNat ((2 * d - 1) ^ zero)
  · dsimp; refine' (card_le_univ _).trans_eq _; simp
    -- ⊢ card (sphere 0 d k) ≤ ↑rothNumberNat 1
           -- ⊢ Fintype.card (Fin 0 → ℕ) = ↑rothNumberNat 1
                                                -- 🎉 no goals
  cases d
  -- ⊢ card (sphere (succ n✝) zero k) ≤ ↑rothNumberNat ((2 * zero - 1) ^ succ n✝)
  · simp
    -- 🎉 no goals
  refine' addSalemSpencer_image_sphere.le_rothNumberNat _ _ (card_image_of_injOn _)
  · intro; assumption
    -- ⊢ ℕ
           -- 🎉 no goals
  · simp only [subset_iff, mem_image, and_imp, forall_exists_index, mem_range,
      forall_apply_eq_imp_iff₂, sphere, mem_filter]
    rintro _ x hx _ rfl
    -- ⊢ ↑(map (2 * succ n✝ - 1)) x < (2 * succ n✝ - 1) ^ succ n✝¹
    exact (map_le_of_mem_box hx).trans_lt sum_lt
    -- 🎉 no goals
  refine' map_injOn.mono fun x => _
  -- ⊢ Fin (succ n✝¹) → ℕ
  · intro; assumption
    -- ⊢ ℕ
           -- 🎉 no goals
  simp only [mem_coe, sphere, mem_filter, mem_box, and_imp, two_mul]
  -- ⊢ (∀ (i : Fin (succ n✝¹)), x i < succ n✝) → ∑ i : Fin (succ n✝¹), x i ^ 2 = k  …
  exact fun h _ i => (h i).trans_le le_self_add
  -- 🎉 no goals
#align behrend.card_sphere_le_roth_number_nat Behrend.card_sphere_le_rothNumberNat

/-!
### Optimization

Now that we know how to turn the integer points of any sphere into a Salem-Spencer set, we find a
sphere containing many integer points by the pigeonhole principle. This gives us an implicit bound
that we then optimize by tweaking the parameters. The (almost) optimal parameters are
`Behrend.nValue` and `Behrend.dValue`.
-/


theorem exists_large_sphere_aux (n d : ℕ) : ∃ k ∈ range (n * (d - 1) ^ 2 + 1),
    (↑(d ^ n) / (↑(n * (d - 1) ^ 2) + 1) : ℝ) ≤ (sphere n d k).card := by
  refine' exists_le_card_fiber_of_nsmul_le_card_of_maps_to (fun x hx => _) nonempty_range_succ _
  -- ⊢ ∑ i : Fin n, x i ^ 2 ∈ range (n * (d - 1) ^ 2 + 1)
  · rw [mem_range, lt_succ_iff]
    -- ⊢ ∑ i : Fin n, x i ^ 2 ≤ n * (d - 1) ^ 2
    exact sum_sq_le_of_mem_box hx
    -- 🎉 no goals
  · rw [card_range, _root_.nsmul_eq_mul, mul_div_assoc', cast_add_one, mul_div_cancel_left,
      card_box]
    exact (cast_add_one_pos _).ne'
    -- 🎉 no goals
#align behrend.exists_large_sphere_aux Behrend.exists_large_sphere_aux

theorem exists_large_sphere (n d : ℕ) : ∃ k, (d ^ n / ↑(n * d ^ 2) : ℝ) ≤ (sphere n d k).card := by
  obtain ⟨k, -, hk⟩ := exists_large_sphere_aux n d
  -- ⊢ ∃ k, ↑d ^ ↑n / ↑(n * d ^ 2) ≤ ↑(card (sphere n d k))
  refine' ⟨k, _⟩
  -- ⊢ ↑d ^ ↑n / ↑(n * d ^ 2) ≤ ↑(card (sphere n d k))
  obtain rfl | hn := n.eq_zero_or_pos
  -- ⊢ ↑d ^ ↑0 / ↑(0 * d ^ 2) ≤ ↑(card (sphere 0 d k))
  · simp
    -- 🎉 no goals
  obtain rfl | hd := d.eq_zero_or_pos
  -- ⊢ ↑0 ^ ↑n / ↑(n * 0 ^ 2) ≤ ↑(card (sphere n 0 k))
  · simp
    -- 🎉 no goals
  rw [rpow_nat_cast, ← cast_pow]
  -- ⊢ ↑(d ^ n) / ↑(n * d ^ 2) ≤ ↑(card (sphere n d k))
  refine' (div_le_div_of_le_left _ _ _).trans hk
  · exact cast_nonneg _
    -- 🎉 no goals
  · exact cast_add_one_pos _
    -- 🎉 no goals
  simp only [← le_sub_iff_add_le', cast_mul, ← mul_sub, cast_pow, cast_sub hd, sub_sq, one_pow,
    cast_one, mul_one, sub_add, sub_sub_self]
  apply one_le_mul_of_one_le_of_one_le
  -- ⊢ 1 ≤ ↑n
  · rwa [one_le_cast]
    -- 🎉 no goals
  rw [_root_.le_sub_iff_add_le]
  -- ⊢ 1 + 1 ≤ 2 * ↑d
  norm_num
  -- ⊢ 1 ≤ d
  exact one_le_cast.2 hd
  -- 🎉 no goals
#align behrend.exists_large_sphere Behrend.exists_large_sphere

theorem bound_aux' (n d : ℕ) : (d ^ n / ↑(n * d ^ 2) : ℝ) ≤ rothNumberNat ((2 * d - 1) ^ n) :=
  let ⟨_, h⟩ := exists_large_sphere n d
  h.trans <| cast_le.2 <| card_sphere_le_rothNumberNat _ _ _
#align behrend.bound_aux' Behrend.bound_aux'

theorem bound_aux (hd : d ≠ 0) (hn : 2 ≤ n) :
    (d ^ (n - 2) / n : ℝ) ≤ rothNumberNat ((2 * d - 1) ^ n) := by
  convert bound_aux' n d using 1
  -- ⊢ ↑d ^ (↑n - 2) / ↑n = ↑d ^ ↑n / ↑(n * d ^ 2)
  rw [cast_mul, cast_pow, mul_comm, ← div_div, ← cast_two, ← cast_sub hn, rpow_nat_cast,
    rpow_nat_cast, pow_sub₀ _ (cast_ne_zero.2 hd) hn, ← div_eq_mul_inv]
#align behrend.bound_aux Behrend.bound_aux

open scoped Filter Topology

open Real

section NumericalBounds

theorem log_two_mul_two_le_sqrt_log_eight : log 2 * 2 ≤ sqrt (log 8) := by
  have : (8 : ℝ) = 2 ^ ((3 : ℕ) : ℝ) := by rw [rpow_nat_cast]; norm_num
  -- ⊢ log 2 * 2 ≤ Real.sqrt (log 8)
  rw [this, log_rpow zero_lt_two (3 : ℕ)]
  -- ⊢ log 2 * 2 ≤ Real.sqrt (↑3 * log 2)
  apply le_sqrt_of_sq_le
  -- ⊢ (log 2 * 2) ^ 2 ≤ ↑3 * log 2
  rw [mul_pow, sq (log 2), mul_assoc, mul_comm]
  -- ⊢ log 2 * 2 ^ 2 * log 2 ≤ ↑3 * log 2
  refine' mul_le_mul_of_nonneg_right _ (log_nonneg one_le_two)
  -- ⊢ log 2 * 2 ^ 2 ≤ ↑3
  rw [← le_div_iff]
  -- ⊢ log 2 ≤ ↑3 / 2 ^ 2
  apply log_two_lt_d9.le.trans
  -- ⊢ 0.6931471808 ≤ ↑3 / 2 ^ 2
  all_goals norm_num1
  -- 🎉 no goals
#align behrend.log_two_mul_two_le_sqrt_log_eight Behrend.log_two_mul_two_le_sqrt_log_eight

theorem two_div_one_sub_two_div_e_le_eight : 2 / (1 - 2 / exp 1) ≤ 8 := by
  rw [div_le_iff, mul_sub, mul_one, mul_div_assoc', le_sub_comm, div_le_iff (exp_pos _)]
  -- ⊢ 8 * 2 ≤ (8 - 2) * exp 1
  · have : 16 < 6 * (2.7182818283 : ℝ) := by norm_num
    -- ⊢ 8 * 2 ≤ (8 - 2) * exp 1
    linarith [exp_one_gt_d9]
    -- 🎉 no goals
  rw [sub_pos, div_lt_one] <;> exact exp_one_gt_d9.trans' (by norm_num)
  -- ⊢ 2 < exp 1
                               -- 🎉 no goals
                               -- 🎉 no goals
#align behrend.two_div_one_sub_two_div_e_le_eight Behrend.two_div_one_sub_two_div_e_le_eight

theorem le_sqrt_log (hN : 4096 ≤ N) : log (2 / (1 - 2 / exp 1)) * (69 / 50) ≤ sqrt (log ↑N) := by
  have : ((12 : ℕ) : ℝ) * log 2 ≤ log N := by
    rw [← log_rpow zero_lt_two, log_le_log, rpow_nat_cast]
    · norm_num1
      exact_mod_cast hN
    · exact rpow_pos_of_pos zero_lt_two _
    rw [cast_pos]
    exact hN.trans_lt' (by norm_num1)
  refine' (mul_le_mul_of_nonneg_right ((log_le_log _ <| by norm_num1).2
      two_div_one_sub_two_div_e_le_eight) <| by norm_num1).trans _
  · refine' div_pos zero_lt_two _
    -- ⊢ 0 < 1 - 2 / exp 1
    rw [sub_pos, div_lt_one (exp_pos _)]
    -- ⊢ 2 < exp 1
    exact exp_one_gt_d9.trans_le' (by norm_num1)
    -- 🎉 no goals
  have l8 : log 8 = (3 : ℕ) * log 2 := by
    rw [← log_rpow zero_lt_two, rpow_nat_cast]
    norm_num
  rw [l8]
  -- ⊢ ↑3 * log 2 * (69 / 50) ≤ Real.sqrt (log ↑N)
  apply le_sqrt_of_sq_le (le_trans _ this)
  -- ⊢ (↑3 * log 2 * (69 / 50)) ^ 2 ≤ ↑12 * log 2
  rw [mul_right_comm, mul_pow, sq (log 2), ← mul_assoc]
  -- ⊢ (↑3 * (69 / 50)) ^ 2 * log 2 * log 2 ≤ ↑12 * log 2
  apply mul_le_mul_of_nonneg_right _ (log_nonneg one_le_two)
  -- ⊢ (↑3 * (69 / 50)) ^ 2 * log 2 ≤ ↑12
  rw [← le_div_iff']
  -- ⊢ log 2 ≤ ↑12 / (↑3 * (69 / 50)) ^ 2
  · exact log_two_lt_d9.le.trans (by norm_num1)
    -- 🎉 no goals
  exact sq_pos_of_ne_zero _ (by norm_num1)
  -- 🎉 no goals
#align behrend.le_sqrt_log Behrend.le_sqrt_log

theorem exp_neg_two_mul_le {x : ℝ} (hx : 0 < x) : exp (-2 * x) < exp (2 - ⌈x⌉₊) / ⌈x⌉₊ := by
  have h₁ := ceil_lt_add_one hx.le
  -- ⊢ exp (-2 * x) < exp (2 - ↑⌈x⌉₊) / ↑⌈x⌉₊
  have h₂ : 1 - x ≤ 2 - ⌈x⌉₊ := by
    rw [_root_.le_sub_iff_add_le]
    apply (add_le_add_left h₁.le _).trans_eq
    rw [← add_assoc, sub_add_cancel]
    linarith
  refine' lt_of_le_of_lt _ (div_lt_div_of_lt_left (exp_pos _) (cast_pos.2 <| ceil_pos.2 hx) h₁)
  -- ⊢ exp (-2 * x) ≤ exp (2 - ↑⌈x⌉₊) / (x + 1)
  refine' le_trans _ (div_le_div_of_le_of_nonneg (exp_le_exp.2 h₂) <| add_nonneg hx.le zero_le_one)
  -- ⊢ exp (-2 * x) ≤ exp (1 - x) / (x + 1)
  rw [le_div_iff (add_pos hx zero_lt_one), ← le_div_iff' (exp_pos _), ← exp_sub, neg_mul,
    sub_neg_eq_add, two_mul, sub_add_add_cancel, add_comm _ x]
  refine' le_trans _ (add_one_le_exp_of_nonneg <| add_nonneg hx.le zero_le_one)
  -- ⊢ x + 1 ≤ x + 1 + 1
  exact le_add_of_nonneg_right zero_le_one
  -- 🎉 no goals
#align behrend.exp_neg_two_mul_le Behrend.exp_neg_two_mul_le

theorem div_lt_floor {x : ℝ} (hx : 2 / (1 - 2 / exp 1) ≤ x) : x / exp 1 < (⌊x / 2⌋₊ : ℝ) := by
  apply lt_of_le_of_lt _ (sub_one_lt_floor _)
  -- ⊢ x / exp 1 ≤ x / 2 - 1
  have : 0 < 1 - 2 / exp 1 := by
    rw [sub_pos, div_lt_one (exp_pos _)]
    exact lt_of_le_of_lt (by norm_num) exp_one_gt_d9
  rwa [le_sub_comm, div_eq_mul_one_div x, div_eq_mul_one_div x, ← mul_sub, div_sub', ←
    div_eq_mul_one_div, mul_div_assoc', one_le_div, ← div_le_iff this]
  · exact zero_lt_two
    -- 🎉 no goals
  · exact two_ne_zero
    -- 🎉 no goals
#align behrend.div_lt_floor Behrend.div_lt_floor

theorem ceil_lt_mul {x : ℝ} (hx : 50 / 19 ≤ x) : (⌈x⌉₊ : ℝ) < 1.38 * x := by
  refine' (ceil_lt_add_one <| hx.trans' <| by norm_num).trans_le _
  -- ⊢ x + 1 ≤ 1.38 * x
  rw [← le_sub_iff_add_le', ← sub_one_mul]
  -- ⊢ 1 ≤ (1.38 - 1) * x
  have : (1.38 : ℝ) = 69 / 50 := by norm_num
  -- ⊢ 1 ≤ (1.38 - 1) * x
  rwa [this, show (69 / 50 - 1 : ℝ) = (50 / 19)⁻¹ by norm_num1, ←
    div_eq_inv_mul, one_le_div]
  norm_num1
  -- 🎉 no goals
#align behrend.ceil_lt_mul Behrend.ceil_lt_mul

end NumericalBounds

/-- The (almost) optimal value of `n` in `Behrend.bound_aux`. -/
noncomputable def nValue (N : ℕ) : ℕ :=
  ⌈sqrt (log N)⌉₊
#align behrend.n_value Behrend.nValue

/-- The (almost) optimal value of `d` in `Behrend.bound_aux`. -/
noncomputable def dValue (N : ℕ) : ℕ :=
  ⌊(N : ℝ) ^ (1 / nValue N : ℝ) / 2⌋₊
#align behrend.d_value Behrend.dValue

theorem nValue_pos (hN : 2 ≤ N) : 0 < nValue N :=
  ceil_pos.2 <| Real.sqrt_pos.2 <| log_pos <| one_lt_cast.2 <| hN
#align behrend.n_value_pos Behrend.nValue_pos

theorem two_le_nValue (hN : 3 ≤ N) : 2 ≤ nValue N := by
  refine' succ_le_of_lt (lt_ceil.2 <| lt_sqrt_of_sq_lt _)
  -- ⊢ ↑1 ^ 2 < log ↑N
  rw [cast_one, one_pow, lt_log_iff_exp_lt]
  -- ⊢ exp 1 < ↑N
  refine' lt_of_lt_of_le _ (cast_le.2 hN)
  -- ⊢ exp 1 < ↑3
  · exact exp_one_lt_d9.trans_le (by norm_num)
    -- 🎉 no goals
  rw [cast_pos]
  -- ⊢ 0 < N
  exact (zero_lt_succ _).trans_le hN
  -- 🎉 no goals
#align behrend.two_le_n_value Behrend.two_le_nValue

theorem three_le_nValue (hN : 64 ≤ N) : 3 ≤ nValue N := by
  rw [nValue, ← lt_iff_add_one_le, lt_ceil, cast_two]
  -- ⊢ 2 < Real.sqrt (log ↑N)
  apply lt_sqrt_of_sq_lt
  -- ⊢ 2 ^ 2 < log ↑N
  have : (2 : ℝ) ^ ((6 : ℕ) : ℝ) ≤ N := by
    rw [rpow_nat_cast]
    exact (cast_le.2 hN).trans' (by norm_num1)
  apply lt_of_lt_of_le _ ((log_le_log (rpow_pos_of_pos zero_lt_two _) _).2 this)
  -- ⊢ 2 ^ 2 < log (2 ^ ↑6)
  rw [log_rpow zero_lt_two, ← div_lt_iff']
  · exact log_two_gt_d9.trans_le' (by norm_num1)
    -- 🎉 no goals
  · norm_num1
    -- 🎉 no goals
  rw [cast_pos]
  -- ⊢ 0 < N
  exact hN.trans_lt' (by norm_num1)
  -- 🎉 no goals
#align behrend.three_le_n_value Behrend.three_le_nValue

theorem dValue_pos (hN₃ : 8 ≤ N) : 0 < dValue N := by
  have hN₀ : 0 < (N : ℝ) := cast_pos.2 (succ_pos'.trans_le hN₃)
  -- ⊢ 0 < dValue N
  rw [dValue, floor_pos, ← log_le_log zero_lt_one, log_one, log_div _ two_ne_zero, log_rpow hN₀,
    div_mul_eq_mul_div, one_mul, sub_nonneg, le_div_iff]
  · have : (nValue N : ℝ) ≤ 2 * sqrt (log N) := by
      apply (ceil_lt_add_one <| sqrt_nonneg _).le.trans
      rw [two_mul, add_le_add_iff_left]
      apply le_sqrt_of_sq_le
      rw [one_pow, le_log_iff_exp_le hN₀]
      exact (exp_one_lt_d9.le.trans <| by norm_num).trans (cast_le.2 hN₃)
    apply (mul_le_mul_of_nonneg_left this <| log_nonneg one_le_two).trans _
    -- ⊢ log 2 * (2 * Real.sqrt (log ↑N)) ≤ log ↑N
    rw [← mul_assoc, ← le_div_iff (Real.sqrt_pos.2 <| log_pos <| one_lt_cast.2 _), div_sqrt]
    -- ⊢ log 2 * 2 ≤ Real.sqrt (log ↑N)
    · apply log_two_mul_two_le_sqrt_log_eight.trans
      -- ⊢ Real.sqrt (log 8) ≤ Real.sqrt (log ↑N)
      apply Real.sqrt_le_sqrt
      -- ⊢ log 8 ≤ log ↑N
      rw [log_le_log _ hN₀]
      -- ⊢ 8 ≤ ↑N
      · exact_mod_cast hN₃
        -- 🎉 no goals
      · norm_num
        -- 🎉 no goals
    exact hN₃.trans_lt' (by norm_num)
    -- 🎉 no goals
  · exact cast_pos.2 (nValue_pos <| hN₃.trans' <| by norm_num)
    -- 🎉 no goals
  · exact (rpow_pos_of_pos hN₀ _).ne'
    -- 🎉 no goals
  · exact div_pos (rpow_pos_of_pos hN₀ _) zero_lt_two
    -- 🎉 no goals
#align behrend.d_value_pos Behrend.dValue_pos

theorem le_N (hN : 2 ≤ N) : (2 * dValue N - 1) ^ nValue N ≤ N := by
  have : (2 * dValue N - 1) ^ nValue N ≤ (2 * dValue N) ^ nValue N :=
    Nat.pow_le_pow_of_le_left (Nat.sub_le _ _) _
  apply this.trans
  -- ⊢ (2 * dValue N) ^ nValue N ≤ N
  suffices ((2 * dValue N) ^ nValue N : ℝ) ≤ N by exact_mod_cast this
  -- ⊢ (2 * ↑(dValue N)) ^ ↑(nValue N) ≤ ↑N
  suffices i : (2 * dValue N : ℝ) ≤ (N : ℝ) ^ (1 / nValue N : ℝ)
  -- ⊢ (2 * ↑(dValue N)) ^ ↑(nValue N) ≤ ↑N
  · apply (rpow_le_rpow (mul_nonneg zero_le_two (cast_nonneg _)) i (cast_nonneg _)).trans
    -- ⊢ (↑N ^ (1 / ↑(nValue N))) ^ ↑(nValue N) ≤ ↑N
    rw [← rpow_mul (cast_nonneg _), one_div_mul_cancel, rpow_one]
    -- ⊢ ↑(nValue N) ≠ 0
    rw [cast_ne_zero]
    -- ⊢ nValue N ≠ 0
    apply (nValue_pos hN).ne'
    -- 🎉 no goals
  rw [← le_div_iff']
  -- ⊢ ↑(dValue N) ≤ ↑N ^ (1 / ↑(nValue N)) / 2
  · exact floor_le (div_nonneg (rpow_nonneg_of_nonneg (cast_nonneg _) _) zero_le_two)
    -- 🎉 no goals
  apply zero_lt_two
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align behrend.le_N Behrend.le_N

theorem bound (hN : 4096 ≤ N) : (N : ℝ) ^ (1 / nValue N : ℝ) / exp 1 < dValue N := by
  apply div_lt_floor _
  -- ⊢ 2 / (1 - 2 / exp 1) ≤ ↑N ^ (1 / ↑(nValue N))
  rw [← log_le_log, log_rpow, mul_comm, ← div_eq_mul_one_div]
  · apply le_trans _ (div_le_div_of_le_left _ _ (ceil_lt_mul _).le)
    rw [mul_comm, ← div_div, div_sqrt, le_div_iff]
    · norm_num; exact le_sqrt_log hN
      -- ⊢ log (2 / (1 - 2 / exp 1)) * (69 / 50) ≤ Real.sqrt (log ↑N)
                -- 🎉 no goals
    · norm_num1
      -- 🎉 no goals
    · apply log_nonneg
      -- ⊢ 1 ≤ ↑N
      rw [one_le_cast]
      -- ⊢ 1 ≤ N
      exact hN.trans' (by norm_num1)
      -- 🎉 no goals
    · rw [cast_pos, lt_ceil, cast_zero, Real.sqrt_pos]
      -- ⊢ 0 < log ↑N
      refine' log_pos _
      -- ⊢ 1 < ↑N
      rw [one_lt_cast]
      -- ⊢ 1 < N
      exact hN.trans_lt' (by norm_num1)
      -- 🎉 no goals
    apply le_sqrt_of_sq_le
    -- ⊢ (50 / 19) ^ 2 ≤ log ↑N
    have : ((12 : ℕ) : ℝ) * log 2 ≤ log N := by
      rw [← log_rpow zero_lt_two, log_le_log, rpow_nat_cast]
      · norm_num1
        exact_mod_cast hN
      · exact rpow_pos_of_pos zero_lt_two _
      rw [cast_pos]
      exact hN.trans_lt' (by norm_num1)
    refine' le_trans _ this
    -- ⊢ (50 / 19) ^ 2 ≤ ↑12 * log 2
    rw [← div_le_iff']
    -- ⊢ (50 / 19) ^ 2 / ↑12 ≤ log 2
    · exact log_two_gt_d9.le.trans' (by norm_num1)
      -- 🎉 no goals
    · norm_num1
      -- 🎉 no goals
  · rw [cast_pos]
    -- ⊢ 0 < N
    exact hN.trans_lt' (by norm_num1)
    -- 🎉 no goals
  · refine' div_pos zero_lt_two _
    -- ⊢ 0 < 1 - 2 / exp 1
    rw [sub_pos, div_lt_one (exp_pos _)]
    -- ⊢ 2 < exp 1
    exact lt_of_le_of_lt (by norm_num1) exp_one_gt_d9
    -- 🎉 no goals
  apply rpow_pos_of_pos
  -- ⊢ 0 < ↑N
  rw [cast_pos]
  -- ⊢ 0 < N
  exact hN.trans_lt' (by norm_num1)
  -- 🎉 no goals
#align behrend.bound Behrend.bound

theorem roth_lower_bound_explicit (hN : 4096 ≤ N) :
    (N : ℝ) * exp (-4 * sqrt (log N)) < rothNumberNat N := by
  let n := nValue N
  -- ⊢ ↑N * exp (-4 * Real.sqrt (log ↑N)) < ↑(↑rothNumberNat N)
  have hn : 0 < (n : ℝ) := cast_pos.2 (nValue_pos <| hN.trans' <| by norm_num1)
  -- ⊢ ↑N * exp (-4 * Real.sqrt (log ↑N)) < ↑(↑rothNumberNat N)
  have hd : 0 < dValue N := dValue_pos (hN.trans' <| by norm_num1)
  -- ⊢ ↑N * exp (-4 * Real.sqrt (log ↑N)) < ↑(↑rothNumberNat N)
  have hN₀ : 0 < (N : ℝ) := cast_pos.2 (hN.trans' <| by norm_num1)
  -- ⊢ ↑N * exp (-4 * Real.sqrt (log ↑N)) < ↑(↑rothNumberNat N)
  have hn₂ : 2 ≤ n := two_le_nValue (hN.trans' <| by norm_num1)
  -- ⊢ ↑N * exp (-4 * Real.sqrt (log ↑N)) < ↑(↑rothNumberNat N)
  have : (2 * dValue N - 1) ^ n ≤ N := le_N (hN.trans' <| by norm_num1)
  -- ⊢ ↑N * exp (-4 * Real.sqrt (log ↑N)) < ↑(↑rothNumberNat N)
  refine' ((bound_aux hd.ne' hn₂).trans <| cast_le.2 <| rothNumberNat.mono this).trans_lt' _
  -- ⊢ ↑N * exp (-4 * Real.sqrt (log ↑N)) < ↑(dValue N) ^ (↑n - 2) / ↑n
  conv_rhs => rw [← cast_two, ← cast_sub hn₂, rpow_nat_cast]
  -- ⊢ ↑N * exp (-4 * Real.sqrt (log ↑N)) < ↑(dValue N) ^ (n - 2) / ↑n
  refine' (div_lt_div_of_lt hn <| pow_lt_pow_of_lt_left (bound hN) _ _).trans_le' _
  · exact div_nonneg (rpow_nonneg_of_nonneg (cast_nonneg _) _) (exp_pos _).le
    -- 🎉 no goals
  · exact tsub_pos_of_lt (three_le_nValue <| hN.trans' <| by norm_num1)
    -- 🎉 no goals
  rw [← rpow_nat_cast, div_rpow (rpow_nonneg_of_nonneg hN₀.le _) (exp_pos _).le, ← rpow_mul hN₀.le,
    mul_comm (_ / _), mul_one_div, cast_sub hn₂, cast_two, same_sub_div hn.ne', exp_one_rpow,
    div_div, rpow_sub hN₀, rpow_one, div_div, div_eq_mul_inv]
  refine' mul_le_mul_of_nonneg_left _ (cast_nonneg _)
  -- ⊢ exp (-4 * Real.sqrt (log ↑N)) ≤ (↑N ^ (2 / ↑n) * (exp (↑n - 2) * ↑n))⁻¹
  rw [mul_inv, mul_inv, ← exp_neg, ← rpow_neg (cast_nonneg _), neg_sub, ← div_eq_mul_inv]
  -- ⊢ exp (-4 * Real.sqrt (log ↑N)) ≤ ↑N ^ (-(2 / ↑n)) * (exp (2 - ↑n) / ↑n)
  have : exp (-4 * sqrt (log N)) = exp (-2 * sqrt (log N)) * exp (-2 * sqrt (log N)) := by
    rw [← exp_add, ← add_mul]
    norm_num
  rw [this]
  -- ⊢ exp (-2 * Real.sqrt (log ↑N)) * exp (-2 * Real.sqrt (log ↑N)) ≤ ↑N ^ (-(2 /  …
  refine' mul_le_mul _ (exp_neg_two_mul_le <| Real.sqrt_pos.2 <| log_pos _).le (exp_pos _).le <|
      rpow_nonneg_of_nonneg (cast_nonneg _) _
  · rw [← le_log_iff_exp_le (rpow_pos_of_pos hN₀ _), log_rpow hN₀, ← le_div_iff, mul_div_assoc,
      div_sqrt, neg_mul, neg_le_neg_iff, div_mul_eq_mul_div, div_le_iff hn]
    · exact mul_le_mul_of_nonneg_left (le_ceil _) zero_le_two
      -- 🎉 no goals
    refine' Real.sqrt_pos.2 (log_pos _)
    -- ⊢ 1 < ↑N
    rw [one_lt_cast]
    -- ⊢ 1 < N
    exact hN.trans_lt' (by norm_num1)
    -- 🎉 no goals
  · rw [one_lt_cast]
    -- ⊢ 1 < N
    exact hN.trans_lt' (by norm_num1)
    -- 🎉 no goals
#align behrend.roth_lower_bound_explicit Behrend.roth_lower_bound_explicit

theorem exp_four_lt : exp 4 < 64 := by
  rw [show (64 : ℝ) = 2 ^ ((6 : ℕ) : ℝ) by rw [rpow_nat_cast]; norm_num1,
    ← lt_log_iff_exp_lt (rpow_pos_of_pos zero_lt_two _), log_rpow zero_lt_two, ← div_lt_iff']
  exact log_two_gt_d9.trans_le' (by norm_num1)
  -- ⊢ 0 < ↑6
  norm_num
  -- 🎉 no goals
#align behrend.exp_four_lt Behrend.exp_four_lt

theorem four_zero_nine_six_lt_exp_sixteen : 4096 < exp 16 := by
  rw [← log_lt_iff_lt_exp (show (0 : ℝ) < 4096 by norm_num), show (4096 : ℝ) = 2 ^ 12 by norm_cast,
    log_rpow zero_lt_two]
  have : 12 * (0.6931471808 : ℝ) < 16 := by norm_num
  -- ⊢ 12 * log 2 < 16
  linarith [log_two_lt_d9]
  -- 🎉 no goals
#align behrend.four_zero_nine_six_lt_exp_sixteen Behrend.four_zero_nine_six_lt_exp_sixteen

theorem lower_bound_le_one' (hN : 2 ≤ N) (hN' : N ≤ 4096) :
    (N : ℝ) * exp (-4 * sqrt (log N)) ≤ 1 := by
  rw [← log_le_log (mul_pos (cast_pos.2 (zero_lt_two.trans_le hN)) (exp_pos _)) zero_lt_one,
    log_one, log_mul (cast_pos.2 (zero_lt_two.trans_le hN)).ne' (exp_pos _).ne', log_exp, neg_mul, ←
    sub_eq_add_neg, sub_nonpos, ←
    div_le_iff (Real.sqrt_pos.2 <| log_pos <| one_lt_cast.2 <| one_lt_two.trans_le hN), div_sqrt,
    sqrt_le_left zero_le_four, log_le_iff_le_exp (cast_pos.2 (zero_lt_two.trans_le hN))]
  norm_num1
  -- ⊢ ↑N ≤ exp 16
  apply le_trans _ four_zero_nine_six_lt_exp_sixteen.le
  -- ⊢ ↑N ≤ 4096
  exact_mod_cast hN'
  -- 🎉 no goals
#align behrend.lower_bound_le_one' Behrend.lower_bound_le_one'

theorem lower_bound_le_one (hN : 1 ≤ N) (hN' : N ≤ 4096) :
    (N : ℝ) * exp (-4 * sqrt (log N)) ≤ 1 := by
  obtain rfl | hN := hN.eq_or_lt
  -- ⊢ ↑1 * exp (-4 * Real.sqrt (log ↑1)) ≤ 1
  · norm_num
    -- 🎉 no goals
  · exact lower_bound_le_one' hN hN'
    -- 🎉 no goals
#align behrend.lower_bound_le_one Behrend.lower_bound_le_one

theorem roth_lower_bound : (N : ℝ) * exp (-4 * sqrt (log N)) ≤ rothNumberNat N := by
  obtain rfl | hN := Nat.eq_zero_or_pos N
  -- ⊢ ↑0 * exp (-4 * Real.sqrt (log ↑0)) ≤ ↑(↑rothNumberNat 0)
  · norm_num
    -- 🎉 no goals
  obtain h₁ | h₁ := le_or_lt 4096 N
  -- ⊢ ↑N * exp (-4 * Real.sqrt (log ↑N)) ≤ ↑(↑rothNumberNat N)
  · exact (roth_lower_bound_explicit h₁).le
    -- 🎉 no goals
  · apply (lower_bound_le_one hN h₁.le).trans
    -- ⊢ 1 ≤ ↑(↑rothNumberNat N)
    simpa using rothNumberNat.monotone hN
    -- 🎉 no goals
#align behrend.roth_lower_bound Behrend.roth_lower_bound

end Behrend
