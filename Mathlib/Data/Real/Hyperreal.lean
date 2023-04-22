/-
Copyright (c) 2019 Abhimanyu Pallavi Sudhir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhimanyu Pallavi Sudhir

! This file was ported from Lean 3 source module data.real.hyperreal
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Filter.FilterProduct
import Mathbin.Analysis.SpecificLimits.Basic

/-!
# Construction of the hyperreal numbers as an ultraproduct of real sequences.
-/


open Filter Filter.Germ

open Topology Classical

/-- Hyperreal numbers on the ultrafilter extending the cofinite filter -/
def Hyperreal : Type :=
  Germ (hyperfilter ℕ : Filter ℕ) ℝ deriving LinearOrderedField, Inhabited
#align hyperreal Hyperreal

namespace Hyperreal

-- mathport name: «exprℝ*»
notation "ℝ*" => Hyperreal

noncomputable instance : CoeTC ℝ ℝ* :=
  ⟨fun x => (↑x : Germ _ _)⟩

@[simp, norm_cast]
theorem coe_eq_coe {x y : ℝ} : (x : ℝ*) = y ↔ x = y :=
  Germ.const_inj
#align hyperreal.coe_eq_coe Hyperreal.coe_eq_coe

theorem coe_ne_coe {x y : ℝ} : (x : ℝ*) ≠ y ↔ x ≠ y :=
  coe_eq_coe.Not
#align hyperreal.coe_ne_coe Hyperreal.coe_ne_coe

@[simp, norm_cast]
theorem coe_eq_zero {x : ℝ} : (x : ℝ*) = 0 ↔ x = 0 :=
  coe_eq_coe
#align hyperreal.coe_eq_zero Hyperreal.coe_eq_zero

@[simp, norm_cast]
theorem coe_eq_one {x : ℝ} : (x : ℝ*) = 1 ↔ x = 1 :=
  coe_eq_coe
#align hyperreal.coe_eq_one Hyperreal.coe_eq_one

@[norm_cast]
theorem coe_ne_zero {x : ℝ} : (x : ℝ*) ≠ 0 ↔ x ≠ 0 :=
  coe_ne_coe
#align hyperreal.coe_ne_zero Hyperreal.coe_ne_zero

@[norm_cast]
theorem coe_ne_one {x : ℝ} : (x : ℝ*) ≠ 1 ↔ x ≠ 1 :=
  coe_ne_coe
#align hyperreal.coe_ne_one Hyperreal.coe_ne_one

@[simp, norm_cast]
theorem coe_one : ↑(1 : ℝ) = (1 : ℝ*) :=
  rfl
#align hyperreal.coe_one Hyperreal.coe_one

@[simp, norm_cast]
theorem coe_zero : ↑(0 : ℝ) = (0 : ℝ*) :=
  rfl
#align hyperreal.coe_zero Hyperreal.coe_zero

@[simp, norm_cast]
theorem coe_inv (x : ℝ) : ↑x⁻¹ = (x⁻¹ : ℝ*) :=
  rfl
#align hyperreal.coe_inv Hyperreal.coe_inv

@[simp, norm_cast]
theorem coe_neg (x : ℝ) : ↑(-x) = (-x : ℝ*) :=
  rfl
#align hyperreal.coe_neg Hyperreal.coe_neg

@[simp, norm_cast]
theorem coe_add (x y : ℝ) : ↑(x + y) = (x + y : ℝ*) :=
  rfl
#align hyperreal.coe_add Hyperreal.coe_add

@[simp, norm_cast]
theorem coe_bit0 (x : ℝ) : ↑(bit0 x) = (bit0 x : ℝ*) :=
  rfl
#align hyperreal.coe_bit0 Hyperreal.coe_bit0

@[simp, norm_cast]
theorem coe_bit1 (x : ℝ) : ↑(bit1 x) = (bit1 x : ℝ*) :=
  rfl
#align hyperreal.coe_bit1 Hyperreal.coe_bit1

@[simp, norm_cast]
theorem coe_mul (x y : ℝ) : ↑(x * y) = (x * y : ℝ*) :=
  rfl
#align hyperreal.coe_mul Hyperreal.coe_mul

@[simp, norm_cast]
theorem coe_div (x y : ℝ) : ↑(x / y) = (x / y : ℝ*) :=
  rfl
#align hyperreal.coe_div Hyperreal.coe_div

@[simp, norm_cast]
theorem coe_sub (x y : ℝ) : ↑(x - y) = (x - y : ℝ*) :=
  rfl
#align hyperreal.coe_sub Hyperreal.coe_sub

@[simp, norm_cast]
theorem coe_le_coe {x y : ℝ} : (x : ℝ*) ≤ y ↔ x ≤ y :=
  Germ.const_le_iff
#align hyperreal.coe_le_coe Hyperreal.coe_le_coe

@[simp, norm_cast]
theorem coe_lt_coe {x y : ℝ} : (x : ℝ*) < y ↔ x < y :=
  Germ.const_lt_iff
#align hyperreal.coe_lt_coe Hyperreal.coe_lt_coe

@[simp, norm_cast]
theorem coe_nonneg {x : ℝ} : 0 ≤ (x : ℝ*) ↔ 0 ≤ x :=
  coe_le_coe
#align hyperreal.coe_nonneg Hyperreal.coe_nonneg

@[simp, norm_cast]
theorem coe_pos {x : ℝ} : 0 < (x : ℝ*) ↔ 0 < x :=
  coe_lt_coe
#align hyperreal.coe_pos Hyperreal.coe_pos

@[simp, norm_cast]
theorem coe_abs (x : ℝ) : ((|x| : ℝ) : ℝ*) = |x| :=
  const_abs x
#align hyperreal.coe_abs Hyperreal.coe_abs

@[simp, norm_cast]
theorem coe_max (x y : ℝ) : ((max x y : ℝ) : ℝ*) = max x y :=
  Germ.const_max _ _
#align hyperreal.coe_max Hyperreal.coe_max

@[simp, norm_cast]
theorem coe_min (x y : ℝ) : ((min x y : ℝ) : ℝ*) = min x y :=
  Germ.const_min _ _
#align hyperreal.coe_min Hyperreal.coe_min

/-- Construct a hyperreal number from a sequence of real numbers. -/
noncomputable def ofSeq (f : ℕ → ℝ) : ℝ* :=
  (↑f : Germ (hyperfilter ℕ : Filter ℕ) ℝ)
#align hyperreal.of_seq Hyperreal.ofSeq

/-- A sample infinitesimal hyperreal-/
noncomputable def epsilon : ℝ* :=
  ofSeq fun n => n⁻¹
#align hyperreal.epsilon Hyperreal.epsilon

/-- A sample infinite hyperreal-/
noncomputable def omega : ℝ* :=
  ofSeq coe
#align hyperreal.omega Hyperreal.omega

-- mathport name: hyperreal.epsilon
scoped notation "ε" => Hyperreal.epsilon

-- mathport name: hyperreal.omega
scoped notation "ω" => Hyperreal.omega

@[simp]
theorem inv_omega : ω⁻¹ = ε :=
  rfl
#align hyperreal.inv_omega Hyperreal.inv_omega

@[simp]
theorem inv_epsilon : ε⁻¹ = ω :=
  @inv_inv _ _ ω
#align hyperreal.inv_epsilon Hyperreal.inv_epsilon

theorem omega_pos : 0 < ω :=
  Germ.coe_pos.2 <|
    mem_hyperfilter_of_finite_compl <|
      by
      convert Set.finite_singleton 0
      simp [Set.eq_singleton_iff_unique_mem]
#align hyperreal.omega_pos Hyperreal.omega_pos

theorem epsilon_pos : 0 < ε :=
  inv_pos_of_pos omega_pos
#align hyperreal.epsilon_pos Hyperreal.epsilon_pos

theorem epsilon_ne_zero : ε ≠ 0 :=
  epsilon_pos.ne'
#align hyperreal.epsilon_ne_zero Hyperreal.epsilon_ne_zero

theorem omega_ne_zero : ω ≠ 0 :=
  omega_pos.ne'
#align hyperreal.omega_ne_zero Hyperreal.omega_ne_zero

theorem epsilon_mul_omega : ε * ω = 1 :=
  @inv_mul_cancel _ _ ω omega_ne_zero
#align hyperreal.epsilon_mul_omega Hyperreal.epsilon_mul_omega

theorem lt_of_tendsto_zero_of_pos {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0)) :
    ∀ {r : ℝ}, 0 < r → ofSeq f < (r : ℝ*) :=
  by
  simp only [Metric.tendsto_atTop, Real.dist_eq, sub_zero, lt_def] at hf⊢
  intro r hr; cases' hf r hr with N hf'
  have hs : { i : ℕ | f i < r }ᶜ ⊆ { i : ℕ | i ≤ N } := fun i hi1 =>
    le_of_lt
      (by
        simp only [lt_iff_not_ge] <;>
          exact fun hi2 => hi1 (lt_of_le_of_lt (le_abs_self _) (hf' i hi2)) :
        i < N)
  exact mem_hyperfilter_of_finite_compl ((Set.finite_le_nat N).Subset hs)
#align hyperreal.lt_of_tendsto_zero_of_pos Hyperreal.lt_of_tendsto_zero_of_pos

theorem neg_lt_of_tendsto_zero_of_pos {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0)) :
    ∀ {r : ℝ}, 0 < r → (-r : ℝ*) < ofSeq f := fun r hr =>
  have hg := hf.neg
  neg_lt_of_neg_lt (by rw [neg_zero] at hg <;> exact lt_of_tendsto_zero_of_pos hg hr)
#align hyperreal.neg_lt_of_tendsto_zero_of_pos Hyperreal.neg_lt_of_tendsto_zero_of_pos

theorem gt_of_tendsto_zero_of_neg {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0)) :
    ∀ {r : ℝ}, r < 0 → (r : ℝ*) < ofSeq f := fun r hr => by
  rw [← neg_neg r, coe_neg] <;> exact neg_lt_of_tendsto_zero_of_pos hf (neg_pos.mpr hr)
#align hyperreal.gt_of_tendsto_zero_of_neg Hyperreal.gt_of_tendsto_zero_of_neg

theorem epsilon_lt_pos (x : ℝ) : 0 < x → ε < x :=
  lt_of_tendsto_zero_of_pos tendsto_inverse_atTop_nhds_0_nat
#align hyperreal.epsilon_lt_pos Hyperreal.epsilon_lt_pos

/-- Standard part predicate -/
def IsSt (x : ℝ*) (r : ℝ) :=
  ∀ δ : ℝ, 0 < δ → (r - δ : ℝ*) < x ∧ x < r + δ
#align hyperreal.is_st Hyperreal.IsSt

/-- Standard part function: like a "round" to ℝ instead of ℤ -/
noncomputable def st : ℝ* → ℝ := fun x => if h : ∃ r, IsSt x r then Classical.choose h else 0
#align hyperreal.st Hyperreal.st

/-- A hyperreal number is infinitesimal if its standard part is 0 -/
def Infinitesimal (x : ℝ*) :=
  IsSt x 0
#align hyperreal.infinitesimal Hyperreal.Infinitesimal

/-- A hyperreal number is positive infinite if it is larger than all real numbers -/
def InfinitePos (x : ℝ*) :=
  ∀ r : ℝ, ↑r < x
#align hyperreal.infinite_pos Hyperreal.InfinitePos

/-- A hyperreal number is negative infinite if it is smaller than all real numbers -/
def InfiniteNeg (x : ℝ*) :=
  ∀ r : ℝ, x < r
#align hyperreal.infinite_neg Hyperreal.InfiniteNeg

/-- A hyperreal number is infinite if it is infinite positive or infinite negative -/
def Infinite (x : ℝ*) :=
  InfinitePos x ∨ InfiniteNeg x
#align hyperreal.infinite Hyperreal.Infinite

/-!
### Some facts about `st`
-/


private theorem is_st_unique' (x : ℝ*) (r s : ℝ) (hr : IsSt x r) (hs : IsSt x s) (hrs : r < s) :
    False := by
  have hrs' := half_pos <| sub_pos_of_lt hrs
  have hr' := (hr _ hrs').2
  have hs' := (hs _ hrs').1
  have h : s - (s - r) / 2 = r + (s - r) / 2 := by linarith
  norm_cast  at *
  rw [h] at hs'
  exact not_lt_of_lt hs' hr'
#align hyperreal.is_st_unique' hyperreal.is_st_unique'

theorem isSt_unique {x : ℝ*} {r s : ℝ} (hr : IsSt x r) (hs : IsSt x s) : r = s :=
  by
  rcases lt_trichotomy r s with (h | h | h)
  · exact False.elim (is_st_unique' x r s hr hs h)
  · exact h
  · exact False.elim (is_st_unique' x s r hs hr h)
#align hyperreal.is_st_unique Hyperreal.isSt_unique

theorem not_infinite_of_exists_st {x : ℝ*} : (∃ r : ℝ, IsSt x r) → ¬Infinite x := fun he hi =>
  Exists.dcases_on he fun r hr =>
    hi.elim (fun hip => not_lt_of_lt (hr 2 zero_lt_two).2 (hip <| r + 2)) fun hin =>
      not_lt_of_lt (hr 2 zero_lt_two).1 (hin <| r - 2)
#align hyperreal.not_infinite_of_exists_st Hyperreal.not_infinite_of_exists_st

theorem isSt_supₛ {x : ℝ*} (hni : ¬Infinite x) : IsSt x (supₛ { y : ℝ | (y : ℝ*) < x }) :=
  let S : Set ℝ := { y : ℝ | (y : ℝ*) < x }
  let R : _ := supₛ S
  have hnile := not_forall.mp (not_or.mp hni).1
  have hnige := not_forall.mp (not_or.mp hni).2
  Exists.dcases_on hnile <|
    Exists.dcases_on hnige fun r₁ hr₁ r₂ hr₂ =>
      have HR₁ : S.Nonempty :=
        ⟨r₁ - 1, lt_of_lt_of_le (coe_lt_coe.2 <| sub_one_lt _) (not_lt.mp hr₁)⟩
      have HR₂ : BddAbove S :=
        ⟨r₂, fun y hy => le_of_lt (coe_lt_coe.1 (lt_of_lt_of_le hy (not_lt.mp hr₂)))⟩
      fun δ hδ =>
      ⟨lt_of_not_le fun c =>
          have hc : ∀ y ∈ S, y ≤ R - δ := fun y hy =>
            coe_le_coe.1 <| le_of_lt <| lt_of_lt_of_le hy c
          not_lt_of_le (csupₛ_le HR₁ hc) <| sub_lt_self R hδ,
        lt_of_not_le fun c =>
          have hc : ↑(R + δ / 2) < x :=
            lt_of_lt_of_le (add_lt_add_left (coe_lt_coe.2 (half_lt_self hδ)) R) c
          not_lt_of_le (le_csupₛ HR₂ hc) <| (lt_add_iff_pos_right _).mpr <| half_pos hδ⟩
#align hyperreal.is_st_Sup Hyperreal.isSt_supₛ

theorem exists_st_of_not_infinite {x : ℝ*} (hni : ¬Infinite x) : ∃ r : ℝ, IsSt x r :=
  ⟨supₛ { y : ℝ | (y : ℝ*) < x }, isSt_supₛ hni⟩
#align hyperreal.exists_st_of_not_infinite Hyperreal.exists_st_of_not_infinite

theorem st_eq_supₛ {x : ℝ*} : st x = supₛ { y : ℝ | (y : ℝ*) < x } :=
  by
  unfold st; split_ifs
  · exact is_st_unique (Classical.choose_spec h) (is_st_Sup (not_infinite_of_exists_st h))
  · cases' not_imp_comm.mp exists_st_of_not_infinite h with H H
    · rw [(Set.ext fun i => ⟨fun hi => Set.mem_univ i, fun hi => H i⟩ :
          { y : ℝ | (y : ℝ*) < x } = Set.univ)]
      exact real.Sup_univ.symm
    · rw [(Set.ext fun i =>
            ⟨fun hi => False.elim (not_lt_of_lt (H i) hi), fun hi =>
              False.elim (Set.not_mem_empty i hi)⟩ :
          { y : ℝ | (y : ℝ*) < x } = ∅)]
      exact real.Sup_empty.symm
#align hyperreal.st_eq_Sup Hyperreal.st_eq_supₛ

theorem exists_st_iff_not_infinite {x : ℝ*} : (∃ r : ℝ, IsSt x r) ↔ ¬Infinite x :=
  ⟨not_infinite_of_exists_st, exists_st_of_not_infinite⟩
#align hyperreal.exists_st_iff_not_infinite Hyperreal.exists_st_iff_not_infinite

theorem infinite_iff_not_exists_st {x : ℝ*} : Infinite x ↔ ¬∃ r : ℝ, IsSt x r :=
  iff_not_comm.mp exists_st_iff_not_infinite
#align hyperreal.infinite_iff_not_exists_st Hyperreal.infinite_iff_not_exists_st

theorem st_infinite {x : ℝ*} (hi : Infinite x) : st x = 0 :=
  by
  unfold st; split_ifs
  · exact False.elim ((infinite_iff_not_exists_st.mp hi) h)
  · rfl
#align hyperreal.st_infinite Hyperreal.st_infinite

theorem st_of_isSt {x : ℝ*} {r : ℝ} (hxr : IsSt x r) : st x = r :=
  by
  unfold st; split_ifs
  · exact is_st_unique (Classical.choose_spec h) hxr
  · exact False.elim (h ⟨r, hxr⟩)
#align hyperreal.st_of_is_st Hyperreal.st_of_isSt

theorem isSt_st_of_isSt {x : ℝ*} {r : ℝ} (hxr : IsSt x r) : IsSt x (st x) := by
  rwa [st_of_is_st hxr]
#align hyperreal.is_st_st_of_is_st Hyperreal.isSt_st_of_isSt

theorem isSt_st_of_exists_st {x : ℝ*} (hx : ∃ r : ℝ, IsSt x r) : IsSt x (st x) :=
  Exists.dcases_on hx fun r => isSt_st_of_isSt
#align hyperreal.is_st_st_of_exists_st Hyperreal.isSt_st_of_exists_st

theorem isSt_st {x : ℝ*} (hx : st x ≠ 0) : IsSt x (st x) :=
  by
  unfold st; split_ifs
  · exact Classical.choose_spec h
  · exact False.elim (hx (by unfold st <;> split_ifs <;> rfl))
#align hyperreal.is_st_st Hyperreal.isSt_st

theorem isSt_st' {x : ℝ*} (hx : ¬Infinite x) : IsSt x (st x) :=
  isSt_st_of_exists_st <| exists_st_of_not_infinite hx
#align hyperreal.is_st_st' Hyperreal.isSt_st'

theorem isSt_refl_real (r : ℝ) : IsSt r r := fun δ hδ =>
  ⟨sub_lt_self _ (coe_lt_coe.2 hδ), lt_add_of_pos_right _ (coe_lt_coe.2 hδ)⟩
#align hyperreal.is_st_refl_real Hyperreal.isSt_refl_real

theorem st_id_real (r : ℝ) : st r = r :=
  st_of_isSt (isSt_refl_real r)
#align hyperreal.st_id_real Hyperreal.st_id_real

theorem eq_of_isSt_real {r s : ℝ} : IsSt r s → r = s :=
  isSt_unique (isSt_refl_real r)
#align hyperreal.eq_of_is_st_real Hyperreal.eq_of_isSt_real

theorem isSt_real_iff_eq {r s : ℝ} : IsSt r s ↔ r = s :=
  ⟨eq_of_isSt_real, fun hrs => by rw [hrs] <;> exact is_st_refl_real s⟩
#align hyperreal.is_st_real_iff_eq Hyperreal.isSt_real_iff_eq

theorem isSt_symm_real {r s : ℝ} : IsSt r s ↔ IsSt s r := by
  rw [is_st_real_iff_eq, is_st_real_iff_eq, eq_comm]
#align hyperreal.is_st_symm_real Hyperreal.isSt_symm_real

theorem isSt_trans_real {r s t : ℝ} : IsSt r s → IsSt s t → IsSt r t := by
  rw [is_st_real_iff_eq, is_st_real_iff_eq, is_st_real_iff_eq] <;> exact Eq.trans
#align hyperreal.is_st_trans_real Hyperreal.isSt_trans_real

theorem isSt_inj_real {r₁ r₂ s : ℝ} (h1 : IsSt r₁ s) (h2 : IsSt r₂ s) : r₁ = r₂ :=
  Eq.trans (eq_of_isSt_real h1) (eq_of_isSt_real h2).symm
#align hyperreal.is_st_inj_real Hyperreal.isSt_inj_real

theorem isSt_iff_abs_sub_lt_delta {x : ℝ*} {r : ℝ} : IsSt x r ↔ ∀ δ : ℝ, 0 < δ → |x - r| < δ := by
  simp only [abs_sub_lt_iff, sub_lt_iff_lt_add, is_st, and_comm', add_comm]
#align hyperreal.is_st_iff_abs_sub_lt_delta Hyperreal.isSt_iff_abs_sub_lt_delta

theorem isSt_add {x y : ℝ*} {r s : ℝ} : IsSt x r → IsSt y s → IsSt (x + y) (r + s) :=
  fun hxr hys d hd =>
  have hxr' := hxr (d / 2) (half_pos hd)
  have hys' := hys (d / 2) (half_pos hd)
  ⟨by convert add_lt_add hxr'.1 hys'.1 using 1 <;> norm_cast <;> linarith, by
    convert add_lt_add hxr'.2 hys'.2 using 1 <;> norm_cast <;> linarith⟩
#align hyperreal.is_st_add Hyperreal.isSt_add

theorem isSt_neg {x : ℝ*} {r : ℝ} (hxr : IsSt x r) : IsSt (-x) (-r) := fun d hd =>
  show -(r : ℝ*) - d < -x ∧ -x < -r + d by cases hxr d hd <;> constructor <;> linarith
#align hyperreal.is_st_neg Hyperreal.isSt_neg

theorem isSt_sub {x y : ℝ*} {r s : ℝ} : IsSt x r → IsSt y s → IsSt (x - y) (r - s) := fun hxr hys =>
  by rw [sub_eq_add_neg, sub_eq_add_neg] <;> exact is_st_add hxr (is_st_neg hys)
#align hyperreal.is_st_sub Hyperreal.isSt_sub

-- (st x < st y) → (x < y) → (x ≤ y) → (st x ≤ st y)
theorem lt_of_isSt_lt {x y : ℝ*} {r s : ℝ} (hxr : IsSt x r) (hys : IsSt y s) : r < s → x < y :=
  fun hrs => by
  have hrs' : 0 < (s - r) / 2 := half_pos (sub_pos.mpr hrs)
  have hxr' := (hxr _ hrs').2
  have hys' := (hys _ hrs').1
  have H1 : r + (s - r) / 2 = (r + s) / 2 := by linarith
  have H2 : s - (s - r) / 2 = (r + s) / 2 := by linarith
  norm_cast  at *
  rw [H1] at hxr'
  rw [H2] at hys'
  exact lt_trans hxr' hys'
#align hyperreal.lt_of_is_st_lt Hyperreal.lt_of_isSt_lt

theorem isSt_le_of_le {x y : ℝ*} {r s : ℝ} (hrx : IsSt x r) (hsy : IsSt y s) : x ≤ y → r ≤ s := by
  rw [← not_lt, ← not_lt, not_imp_not] <;> exact lt_of_is_st_lt hsy hrx
#align hyperreal.is_st_le_of_le Hyperreal.isSt_le_of_le

theorem st_le_of_le {x y : ℝ*} (hix : ¬Infinite x) (hiy : ¬Infinite y) : x ≤ y → st x ≤ st y :=
  have hx' := isSt_st' hix
  have hy' := isSt_st' hiy
  isSt_le_of_le hx' hy'
#align hyperreal.st_le_of_le Hyperreal.st_le_of_le

theorem lt_of_st_lt {x y : ℝ*} (hix : ¬Infinite x) (hiy : ¬Infinite y) : st x < st y → x < y :=
  have hx' := isSt_st' hix
  have hy' := isSt_st' hiy
  lt_of_isSt_lt hx' hy'
#align hyperreal.lt_of_st_lt Hyperreal.lt_of_st_lt

/-!
### Basic lemmas about infinite
-/


theorem infinitePos_def {x : ℝ*} : InfinitePos x ↔ ∀ r : ℝ, ↑r < x := by rw [iff_eq_eq] <;> rfl
#align hyperreal.infinite_pos_def Hyperreal.infinitePos_def

theorem infiniteNeg_def {x : ℝ*} : InfiniteNeg x ↔ ∀ r : ℝ, x < r := by rw [iff_eq_eq] <;> rfl
#align hyperreal.infinite_neg_def Hyperreal.infiniteNeg_def

theorem ne_zero_of_infinite {x : ℝ*} : Infinite x → x ≠ 0 := fun hI h0 =>
  Or.cases_on hI (fun hip => lt_irrefl (0 : ℝ*) ((by rwa [← h0] : InfinitePos 0) 0)) fun hin =>
    lt_irrefl (0 : ℝ*) ((by rwa [← h0] : InfiniteNeg 0) 0)
#align hyperreal.ne_zero_of_infinite Hyperreal.ne_zero_of_infinite

theorem not_infinite_zero : ¬Infinite 0 := fun hI => ne_zero_of_infinite hI rfl
#align hyperreal.not_infinite_zero Hyperreal.not_infinite_zero

theorem pos_of_infinitePos {x : ℝ*} : InfinitePos x → 0 < x := fun hip => hip 0
#align hyperreal.pos_of_infinite_pos Hyperreal.pos_of_infinitePos

theorem neg_of_infiniteNeg {x : ℝ*} : InfiniteNeg x → x < 0 := fun hin => hin 0
#align hyperreal.neg_of_infinite_neg Hyperreal.neg_of_infiniteNeg

theorem not_infinitePos_of_infiniteNeg {x : ℝ*} : InfiniteNeg x → ¬InfinitePos x := fun hn hp =>
  not_lt_of_lt (hn 1) (hp 1)
#align hyperreal.not_infinite_pos_of_infinite_neg Hyperreal.not_infinitePos_of_infiniteNeg

theorem not_infiniteNeg_of_infinitePos {x : ℝ*} : InfinitePos x → ¬InfiniteNeg x :=
  imp_not_comm.mp not_infinitePos_of_infiniteNeg
#align hyperreal.not_infinite_neg_of_infinite_pos Hyperreal.not_infiniteNeg_of_infinitePos

theorem infiniteNeg_neg_of_infinitePos {x : ℝ*} : InfinitePos x → InfiniteNeg (-x) := fun hp r =>
  neg_lt.mp (hp (-r))
#align hyperreal.infinite_neg_neg_of_infinite_pos Hyperreal.infiniteNeg_neg_of_infinitePos

theorem infinitePos_neg_of_infiniteNeg {x : ℝ*} : InfiniteNeg x → InfinitePos (-x) := fun hp r =>
  lt_neg.mp (hp (-r))
#align hyperreal.infinite_pos_neg_of_infinite_neg Hyperreal.infinitePos_neg_of_infiniteNeg

theorem infinitePos_iff_infiniteNeg_neg {x : ℝ*} : InfinitePos x ↔ InfiniteNeg (-x) :=
  ⟨infiniteNeg_neg_of_infinitePos, fun hin => neg_neg x ▸ infinitePos_neg_of_infiniteNeg hin⟩
#align hyperreal.infinite_pos_iff_infinite_neg_neg Hyperreal.infinitePos_iff_infiniteNeg_neg

theorem infiniteNeg_iff_infinitePos_neg {x : ℝ*} : InfiniteNeg x ↔ InfinitePos (-x) :=
  ⟨infinitePos_neg_of_infiniteNeg, fun hin => neg_neg x ▸ infiniteNeg_neg_of_infinitePos hin⟩
#align hyperreal.infinite_neg_iff_infinite_pos_neg Hyperreal.infiniteNeg_iff_infinitePos_neg

theorem infinite_iff_infinite_neg {x : ℝ*} : Infinite x ↔ Infinite (-x) :=
  ⟨fun hi =>
    Or.cases_on hi (fun hip => Or.inr (infiniteNeg_neg_of_infinitePos hip)) fun hin =>
      Or.inl (infinitePos_neg_of_infiniteNeg hin),
    fun hi =>
    Or.cases_on hi (fun hipn => Or.inr (infiniteNeg_iff_infinitePos_neg.mpr hipn)) fun hinp =>
      Or.inl (infinitePos_iff_infiniteNeg_neg.mpr hinp)⟩
#align hyperreal.infinite_iff_infinite_neg Hyperreal.infinite_iff_infinite_neg

theorem not_infinite_of_infinitesimal {x : ℝ*} : Infinitesimal x → ¬Infinite x := fun hi hI =>
  have hi' := hi 2 zero_lt_two
  Or.dcases_on hI
    (fun hip =>
      have hip' := hip 2
      not_lt_of_lt hip' (by convert hi'.2 <;> exact (zero_add 2).symm))
    fun hin =>
    have hin' := hin (-2)
    not_lt_of_lt hin' (by convert hi'.1 <;> exact (zero_sub 2).symm)
#align hyperreal.not_infinite_of_infinitesimal Hyperreal.not_infinite_of_infinitesimal

theorem not_infinitesimal_of_infinite {x : ℝ*} : Infinite x → ¬Infinitesimal x :=
  imp_not_comm.mp not_infinite_of_infinitesimal
#align hyperreal.not_infinitesimal_of_infinite Hyperreal.not_infinitesimal_of_infinite

theorem not_infinitesimal_of_infinitePos {x : ℝ*} : InfinitePos x → ¬Infinitesimal x := fun hp =>
  not_infinitesimal_of_infinite (Or.inl hp)
#align hyperreal.not_infinitesimal_of_infinite_pos Hyperreal.not_infinitesimal_of_infinitePos

theorem not_infinitesimal_of_infiniteNeg {x : ℝ*} : InfiniteNeg x → ¬Infinitesimal x := fun hn =>
  not_infinitesimal_of_infinite (Or.inr hn)
#align hyperreal.not_infinitesimal_of_infinite_neg Hyperreal.not_infinitesimal_of_infiniteNeg

theorem infinitePos_iff_infinite_and_pos {x : ℝ*} : InfinitePos x ↔ Infinite x ∧ 0 < x :=
  ⟨fun hip => ⟨Or.inl hip, hip 0⟩, fun ⟨hi, hp⟩ =>
    hi.casesOn (fun hip => hip) fun hin => False.elim (not_lt_of_lt hp (hin 0))⟩
#align hyperreal.infinite_pos_iff_infinite_and_pos Hyperreal.infinitePos_iff_infinite_and_pos

theorem infiniteNeg_iff_infinite_and_neg {x : ℝ*} : InfiniteNeg x ↔ Infinite x ∧ x < 0 :=
  ⟨fun hip => ⟨Or.inr hip, hip 0⟩, fun ⟨hi, hp⟩ =>
    hi.casesOn (fun hin => False.elim (not_lt_of_lt hp (hin 0))) fun hip => hip⟩
#align hyperreal.infinite_neg_iff_infinite_and_neg Hyperreal.infiniteNeg_iff_infinite_and_neg

theorem infinitePos_iff_infinite_of_pos {x : ℝ*} (hp : 0 < x) : InfinitePos x ↔ Infinite x := by
  rw [infinite_pos_iff_infinite_and_pos] <;> exact ⟨fun hI => hI.1, fun hI => ⟨hI, hp⟩⟩
#align hyperreal.infinite_pos_iff_infinite_of_pos Hyperreal.infinitePos_iff_infinite_of_pos

theorem infinitePos_iff_infinite_of_nonneg {x : ℝ*} (hp : 0 ≤ x) : InfinitePos x ↔ Infinite x :=
  Or.cases_on (lt_or_eq_of_le hp) infinitePos_iff_infinite_of_pos fun h => by
    rw [h.symm] <;>
      exact
        ⟨fun hIP => False.elim (not_infinite_zero (Or.inl hIP)), fun hI =>
          False.elim (not_infinite_zero hI)⟩
#align hyperreal.infinite_pos_iff_infinite_of_nonneg Hyperreal.infinitePos_iff_infinite_of_nonneg

theorem infiniteNeg_iff_infinite_of_neg {x : ℝ*} (hn : x < 0) : InfiniteNeg x ↔ Infinite x := by
  rw [infinite_neg_iff_infinite_and_neg] <;> exact ⟨fun hI => hI.1, fun hI => ⟨hI, hn⟩⟩
#align hyperreal.infinite_neg_iff_infinite_of_neg Hyperreal.infiniteNeg_iff_infinite_of_neg

theorem infinitePos_abs_iff_infinite_abs {x : ℝ*} : InfinitePos (|x|) ↔ Infinite (|x|) :=
  infinitePos_iff_infinite_of_nonneg (abs_nonneg _)
#align hyperreal.infinite_pos_abs_iff_infinite_abs Hyperreal.infinitePos_abs_iff_infinite_abs

theorem infinite_iff_infinitePos_abs {x : ℝ*} : Infinite x ↔ InfinitePos (|x|) :=
  ⟨fun hi d =>
    Or.cases_on hi (fun hip => by rw [abs_of_pos (hip 0)] <;> exact hip d) fun hin => by
      rw [abs_of_neg (hin 0)] <;> exact lt_neg.mp (hin (-d)),
    fun hipa => by
    rcases lt_trichotomy x 0 with (h | h | h)
    · exact Or.inr (infinite_neg_iff_infinite_pos_neg.mpr (by rwa [abs_of_neg h] at hipa))
    · exact False.elim (ne_zero_of_infinite (Or.inl (by rw [h] <;> rwa [h, abs_zero] at hipa)) h)
    · exact Or.inl (by rwa [abs_of_pos h] at hipa)⟩
#align hyperreal.infinite_iff_infinite_pos_abs Hyperreal.infinite_iff_infinitePos_abs

theorem infinite_iff_infinite_abs {x : ℝ*} : Infinite x ↔ Infinite (|x|) := by
  rw [← infinite_pos_iff_infinite_of_nonneg (abs_nonneg _), infinite_iff_infinite_pos_abs]
#align hyperreal.infinite_iff_infinite_abs Hyperreal.infinite_iff_infinite_abs

theorem infinite_iff_abs_lt_abs {x : ℝ*} : Infinite x ↔ ∀ r : ℝ, (|r| : ℝ*) < |x| :=
  ⟨fun hI r => coe_abs r ▸ infinite_iff_infinitePos_abs.mp hI (|r|), fun hR =>
    Or.cases_on (max_choice x (-x))
      (fun h => Or.inl fun r => lt_of_le_of_lt (le_abs_self _) (h ▸ hR r)) fun h =>
      Or.inr fun r => neg_lt_neg_iff.mp <| lt_of_le_of_lt (neg_le_abs_self _) (h ▸ hR r)⟩
#align hyperreal.infinite_iff_abs_lt_abs Hyperreal.infinite_iff_abs_lt_abs

theorem infinitePos_add_not_infiniteNeg {x y : ℝ*} :
    InfinitePos x → ¬InfiniteNeg y → InfinitePos (x + y) :=
  by
  intro hip hnin r
  cases' not_forall.mp hnin with r₂ hr₂
  convert add_lt_add_of_lt_of_le (hip (r + -r₂)) (not_lt.mp hr₂) using 1
  simp
#align hyperreal.infinite_pos_add_not_infinite_neg Hyperreal.infinitePos_add_not_infiniteNeg

theorem not_infiniteNeg_add_infinitePos {x y : ℝ*} :
    ¬InfiniteNeg x → InfinitePos y → InfinitePos (x + y) := fun hx hy => by
  rw [add_comm] <;> exact infinite_pos_add_not_infinite_neg hy hx
#align hyperreal.not_infinite_neg_add_infinite_pos Hyperreal.not_infiniteNeg_add_infinitePos

theorem infiniteNeg_add_not_infinitePos {x y : ℝ*} :
    InfiniteNeg x → ¬InfinitePos y → InfiniteNeg (x + y) := by
  rw [@infinite_neg_iff_infinite_pos_neg x, @infinite_pos_iff_infinite_neg_neg y,
      @infinite_neg_iff_infinite_pos_neg (x + y), neg_add] <;>
    exact infinite_pos_add_not_infinite_neg
#align hyperreal.infinite_neg_add_not_infinite_pos Hyperreal.infiniteNeg_add_not_infinitePos

theorem not_infinitePos_add_infiniteNeg {x y : ℝ*} :
    ¬InfinitePos x → InfiniteNeg y → InfiniteNeg (x + y) := fun hx hy => by
  rw [add_comm] <;> exact infinite_neg_add_not_infinite_pos hy hx
#align hyperreal.not_infinite_pos_add_infinite_neg Hyperreal.not_infinitePos_add_infiniteNeg

theorem infinitePos_add_infinitePos {x y : ℝ*} :
    InfinitePos x → InfinitePos y → InfinitePos (x + y) := fun hx hy =>
  infinitePos_add_not_infiniteNeg hx (not_infiniteNeg_of_infinitePos hy)
#align hyperreal.infinite_pos_add_infinite_pos Hyperreal.infinitePos_add_infinitePos

theorem infiniteNeg_add_infiniteNeg {x y : ℝ*} :
    InfiniteNeg x → InfiniteNeg y → InfiniteNeg (x + y) := fun hx hy =>
  infiniteNeg_add_not_infinitePos hx (not_infinitePos_of_infiniteNeg hy)
#align hyperreal.infinite_neg_add_infinite_neg Hyperreal.infiniteNeg_add_infiniteNeg

theorem infinitePos_add_not_infinite {x y : ℝ*} :
    InfinitePos x → ¬Infinite y → InfinitePos (x + y) := fun hx hy =>
  infinitePos_add_not_infiniteNeg hx (not_or.mp hy).2
#align hyperreal.infinite_pos_add_not_infinite Hyperreal.infinitePos_add_not_infinite

theorem infiniteNeg_add_not_infinite {x y : ℝ*} :
    InfiniteNeg x → ¬Infinite y → InfiniteNeg (x + y) := fun hx hy =>
  infiniteNeg_add_not_infinitePos hx (not_or.mp hy).1
#align hyperreal.infinite_neg_add_not_infinite Hyperreal.infiniteNeg_add_not_infinite

theorem infinitePos_of_tendsto_top {f : ℕ → ℝ} (hf : Tendsto f atTop atTop) :
    InfinitePos (ofSeq f) := fun r =>
  have hf' := tendsto_atTop_atTop.mp hf
  Exists.cases_on (hf' (r + 1)) fun i hi =>
    have hi' : ∀ a : ℕ, f a < r + 1 → a < i := fun a => by
      rw [← not_le, ← not_le] <;> exact not_imp_not.mpr (hi a)
    have hS : { a : ℕ | r < f a }ᶜ ⊆ { a : ℕ | a ≤ i } := by
      simp only [Set.compl_setOf, not_lt] <;>
        exact fun a har => le_of_lt (hi' a (lt_of_le_of_lt har (lt_add_one _)))
    Germ.coe_lt.2 <| mem_hyperfilter_of_finite_compl <| (Set.finite_le_nat _).Subset hS
#align hyperreal.infinite_pos_of_tendsto_top Hyperreal.infinitePos_of_tendsto_top

theorem infiniteNeg_of_tendsto_bot {f : ℕ → ℝ} (hf : Tendsto f atTop atBot) :
    InfiniteNeg (ofSeq f) := fun r =>
  have hf' := tendsto_atTop_atBot.mp hf
  Exists.cases_on (hf' (r - 1)) fun i hi =>
    have hi' : ∀ a : ℕ, r - 1 < f a → a < i := fun a => by
      rw [← not_le, ← not_le] <;> exact not_imp_not.mpr (hi a)
    have hS : { a : ℕ | f a < r }ᶜ ⊆ { a : ℕ | a ≤ i } := by
      simp only [Set.compl_setOf, not_lt] <;>
        exact fun a har => le_of_lt (hi' a (lt_of_lt_of_le (sub_one_lt _) har))
    Germ.coe_lt.2 <| mem_hyperfilter_of_finite_compl <| (Set.finite_le_nat _).Subset hS
#align hyperreal.infinite_neg_of_tendsto_bot Hyperreal.infiniteNeg_of_tendsto_bot

theorem not_infinite_neg {x : ℝ*} : ¬Infinite x → ¬Infinite (-x) :=
  not_imp_not.mpr infinite_iff_infinite_neg.mpr
#align hyperreal.not_infinite_neg Hyperreal.not_infinite_neg

theorem not_infinite_add {x y : ℝ*} (hx : ¬Infinite x) (hy : ¬Infinite y) : ¬Infinite (x + y) :=
  have hx' := exists_st_of_not_infinite hx
  have hy' := exists_st_of_not_infinite hy
  Exists.cases_on hx' <|
    Exists.cases_on hy' fun r hr s hs => not_infinite_of_exists_st <| ⟨s + r, isSt_add hs hr⟩
#align hyperreal.not_infinite_add Hyperreal.not_infinite_add

theorem not_infinite_iff_exist_lt_gt {x : ℝ*} : ¬Infinite x ↔ ∃ r s : ℝ, (r : ℝ*) < x ∧ x < s :=
  ⟨fun hni =>
    Exists.dcases_on (not_forall.mp (not_or.mp hni).1) <|
      Exists.dcases_on (not_forall.mp (not_or.mp hni).2) fun r hr s hs => by
        rw [not_lt] at hr hs <;>
          exact
            ⟨r - 1, s + 1,
              ⟨lt_of_lt_of_le (by rw [sub_eq_add_neg] <;> norm_num) hr,
                lt_of_le_of_lt hs (by norm_num)⟩⟩,
    fun hrs =>
    Exists.dcases_on hrs fun r hr =>
      Exists.dcases_on hr fun s hs =>
        not_or.mpr ⟨not_forall.mpr ⟨s, lt_asymm hs.2⟩, not_forall.mpr ⟨r, lt_asymm hs.1⟩⟩⟩
#align hyperreal.not_infinite_iff_exist_lt_gt Hyperreal.not_infinite_iff_exist_lt_gt

theorem not_infinite_real (r : ℝ) : ¬Infinite r := by
  rw [not_infinite_iff_exist_lt_gt] <;>
    exact ⟨r - 1, r + 1, coe_lt_coe.2 <| sub_one_lt r, coe_lt_coe.2 <| lt_add_one r⟩
#align hyperreal.not_infinite_real Hyperreal.not_infinite_real

theorem not_real_of_infinite {x : ℝ*} : Infinite x → ∀ r : ℝ, x ≠ r := fun hi r hr =>
  not_infinite_real r <| @Eq.subst _ Infinite _ _ hr hi
#align hyperreal.not_real_of_infinite Hyperreal.not_real_of_infinite

/-!
### Facts about `st` that require some infinite machinery
-/


private theorem is_st_mul' {x y : ℝ*} {r s : ℝ} (hxr : IsSt x r) (hys : IsSt y s) (hs : s ≠ 0) :
    IsSt (x * y) (r * s) :=
  have hxr' := isSt_iff_abs_sub_lt_delta.mp hxr
  have hys' := isSt_iff_abs_sub_lt_delta.mp hys
  have h :=
    not_infinite_iff_exist_lt_gt.mp <|
      not_imp_not.mpr infinite_iff_infinite_abs.mpr <| not_infinite_of_exists_st ⟨r, hxr⟩
  Exists.cases_on h fun u h' =>
    Exists.cases_on h' fun t ⟨hu, ht⟩ =>
      isSt_iff_abs_sub_lt_delta.mpr fun d hd =>
        calc
          |x * y - r * s| = |x * (y - s) + (x - r) * s| := by
            rw [mul_sub, sub_mul, add_sub, sub_add_cancel]
          _ ≤ |x * (y - s)| + |(x - r) * s| := (abs_add _ _)
          _ ≤ |x| * |y - s| + |x - r| * |s| := by simp only [abs_mul]
          _ ≤ |x| * (d / t / 2 : ℝ) + (d / |s| / 2 : ℝ) * |s| :=
            (add_le_add
              (mul_le_mul_of_nonneg_left
                  (le_of_lt <|
                    hys' _ <|
                      half_pos <| div_pos hd <| coe_pos.1 <| lt_of_le_of_lt (abs_nonneg x) ht) <|
                abs_nonneg _)
              (mul_le_mul_of_nonneg_right
                  (le_of_lt <| hxr' _ <| half_pos <| div_pos hd <| abs_pos.2 hs) <|
                abs_nonneg _))
          _ = (d / 2 * (|x| / t) + d / 2 : ℝ*) :=
            by
            push_cast [-Filter.Germ.const_div]
            -- TODO: Why wasn't `hyperreal.coe_div` used?
            have : (|s| : ℝ*) ≠ 0 := by simpa
            have : (2 : ℝ*) ≠ 0 := two_ne_zero
            field_simp [*, add_mul, mul_add, mul_assoc, mul_comm, mul_left_comm]
          _ < (d / 2 * 1 + d / 2 : ℝ*) :=
            (add_lt_add_right
              (mul_lt_mul_of_pos_left ((div_lt_one <| lt_of_le_of_lt (abs_nonneg x) ht).mpr ht) <|
                half_pos <| coe_pos.2 hd)
              _)
          _ = (d : ℝ*) := by rw [mul_one, add_halves]
          
#align hyperreal.is_st_mul' hyperreal.is_st_mul'

theorem isSt_mul {x y : ℝ*} {r s : ℝ} (hxr : IsSt x r) (hys : IsSt y s) : IsSt (x * y) (r * s) :=
  have h :=
    not_infinite_iff_exist_lt_gt.mp <|
      not_imp_not.mpr infinite_iff_infinite_abs.mpr <| not_infinite_of_exists_st ⟨r, hxr⟩
  Exists.cases_on h fun u h' =>
    Exists.cases_on h' fun t ⟨hu, ht⟩ => by
      by_cases hs : s = 0
      · apply is_st_iff_abs_sub_lt_delta.mpr
        intro d hd
        have hys' : _ :=
          is_st_iff_abs_sub_lt_delta.mp hys (d / t)
            (div_pos hd (coe_pos.1 (lt_of_le_of_lt (abs_nonneg x) ht)))
        rw [hs, coe_zero, sub_zero] at hys'
        rw [hs, MulZeroClass.mul_zero, coe_zero, sub_zero, abs_mul, mul_comm, ←
          div_mul_cancel (d : ℝ*) (ne_of_gt (lt_of_le_of_lt (abs_nonneg x) ht)), ← coe_div]
        exact mul_lt_mul'' hys' ht (abs_nonneg _) (abs_nonneg _)
      exact is_st_mul' hxr hys hs
#align hyperreal.is_st_mul Hyperreal.isSt_mul

--AN INFINITE LEMMA THAT REQUIRES SOME MORE ST MACHINERY
theorem not_infinite_mul {x y : ℝ*} (hx : ¬Infinite x) (hy : ¬Infinite y) : ¬Infinite (x * y) :=
  have hx' := exists_st_of_not_infinite hx
  have hy' := exists_st_of_not_infinite hy
  Exists.cases_on hx' <|
    Exists.cases_on hy' fun r hr s hs => not_infinite_of_exists_st <| ⟨s * r, isSt_mul hs hr⟩
#align hyperreal.not_infinite_mul Hyperreal.not_infinite_mul

---
theorem st_add {x y : ℝ*} (hx : ¬Infinite x) (hy : ¬Infinite y) : st (x + y) = st x + st y :=
  have hx' := isSt_st' hx
  have hy' := isSt_st' hy
  have hxy := isSt_st' (not_infinite_add hx hy)
  have hxy' := isSt_add hx' hy'
  isSt_unique hxy hxy'
#align hyperreal.st_add Hyperreal.st_add

theorem st_neg (x : ℝ*) : st (-x) = -st x :=
  if h : Infinite x then by
    rw [st_infinite h, st_infinite (infinite_iff_infinite_neg.mp h), neg_zero]
  else isSt_unique (isSt_st' (not_infinite_neg h)) (isSt_neg (isSt_st' h))
#align hyperreal.st_neg Hyperreal.st_neg

theorem st_mul {x y : ℝ*} (hx : ¬Infinite x) (hy : ¬Infinite y) : st (x * y) = st x * st y :=
  have hx' := isSt_st' hx
  have hy' := isSt_st' hy
  have hxy := isSt_st' (not_infinite_mul hx hy)
  have hxy' := isSt_mul hx' hy'
  isSt_unique hxy hxy'
#align hyperreal.st_mul Hyperreal.st_mul

/-!
### Basic lemmas about infinitesimal
-/


theorem infinitesimal_def {x : ℝ*} : Infinitesimal x ↔ ∀ r : ℝ, 0 < r → -(r : ℝ*) < x ∧ x < r :=
  ⟨fun hi r hr => by convert hi r hr <;> simp, fun hi d hd => by convert hi d hd <;> simp⟩
#align hyperreal.infinitesimal_def Hyperreal.infinitesimal_def

theorem lt_of_pos_of_infinitesimal {x : ℝ*} : Infinitesimal x → ∀ r : ℝ, 0 < r → x < r :=
  fun hi r hr => ((infinitesimal_def.mp hi) r hr).2
#align hyperreal.lt_of_pos_of_infinitesimal Hyperreal.lt_of_pos_of_infinitesimal

theorem lt_neg_of_pos_of_infinitesimal {x : ℝ*} : Infinitesimal x → ∀ r : ℝ, 0 < r → -↑r < x :=
  fun hi r hr => ((infinitesimal_def.mp hi) r hr).1
#align hyperreal.lt_neg_of_pos_of_infinitesimal Hyperreal.lt_neg_of_pos_of_infinitesimal

theorem gt_of_neg_of_infinitesimal {x : ℝ*} : Infinitesimal x → ∀ r : ℝ, r < 0 → ↑r < x :=
  fun hi r hr => by
  convert((infinitesimal_def.mp hi) (-r) (neg_pos.mpr hr)).1 <;> exact (neg_neg ↑r).symm
#align hyperreal.gt_of_neg_of_infinitesimal Hyperreal.gt_of_neg_of_infinitesimal

theorem abs_lt_real_iff_infinitesimal {x : ℝ*} : Infinitesimal x ↔ ∀ r : ℝ, r ≠ 0 → |x| < |r| :=
  ⟨fun hi r hr =>
    abs_lt.mpr (by rw [← coe_abs] <;> exact infinitesimal_def.mp hi (|r|) (abs_pos.2 hr)), fun hR =>
    infinitesimal_def.mpr fun r hr =>
      abs_lt.mp <| (abs_of_pos <| coe_pos.2 hr) ▸ hR r <| ne_of_gt hr⟩
#align hyperreal.abs_lt_real_iff_infinitesimal Hyperreal.abs_lt_real_iff_infinitesimal

theorem infinitesimal_zero : Infinitesimal 0 :=
  isSt_refl_real 0
#align hyperreal.infinitesimal_zero Hyperreal.infinitesimal_zero

theorem zero_of_infinitesimal_real {r : ℝ} : Infinitesimal r → r = 0 :=
  eq_of_isSt_real
#align hyperreal.zero_of_infinitesimal_real Hyperreal.zero_of_infinitesimal_real

theorem zero_iff_infinitesimal_real {r : ℝ} : Infinitesimal r ↔ r = 0 :=
  ⟨zero_of_infinitesimal_real, fun hr => by rw [hr] <;> exact infinitesimal_zero⟩
#align hyperreal.zero_iff_infinitesimal_real Hyperreal.zero_iff_infinitesimal_real

theorem infinitesimal_add {x y : ℝ*} (hx : Infinitesimal x) (hy : Infinitesimal y) :
    Infinitesimal (x + y) := by simpa only [add_zero] using is_st_add hx hy
#align hyperreal.infinitesimal_add Hyperreal.infinitesimal_add

theorem infinitesimal_neg {x : ℝ*} (hx : Infinitesimal x) : Infinitesimal (-x) := by
  simpa only [neg_zero] using is_st_neg hx
#align hyperreal.infinitesimal_neg Hyperreal.infinitesimal_neg

theorem infinitesimal_neg_iff {x : ℝ*} : Infinitesimal x ↔ Infinitesimal (-x) :=
  ⟨infinitesimal_neg, fun h => neg_neg x ▸ @infinitesimal_neg (-x) h⟩
#align hyperreal.infinitesimal_neg_iff Hyperreal.infinitesimal_neg_iff

theorem infinitesimal_mul {x y : ℝ*} (hx : Infinitesimal x) (hy : Infinitesimal y) :
    Infinitesimal (x * y) := by simpa only [MulZeroClass.mul_zero] using is_st_mul hx hy
#align hyperreal.infinitesimal_mul Hyperreal.infinitesimal_mul

theorem infinitesimal_of_tendsto_zero {f : ℕ → ℝ} :
    Tendsto f atTop (𝓝 0) → Infinitesimal (ofSeq f) := fun hf d hd => by
  rw [sub_eq_add_neg, ← coe_neg, ← coe_add, ← coe_add, zero_add, zero_add] <;>
    exact ⟨neg_lt_of_tendsto_zero_of_pos hf hd, lt_of_tendsto_zero_of_pos hf hd⟩
#align hyperreal.infinitesimal_of_tendsto_zero Hyperreal.infinitesimal_of_tendsto_zero

theorem infinitesimal_epsilon : Infinitesimal ε :=
  infinitesimal_of_tendsto_zero tendsto_inverse_atTop_nhds_0_nat
#align hyperreal.infinitesimal_epsilon Hyperreal.infinitesimal_epsilon

theorem not_real_of_infinitesimal_ne_zero (x : ℝ*) : Infinitesimal x → x ≠ 0 → ∀ r : ℝ, x ≠ r :=
  fun hi hx r hr =>
  hx <| hr.trans <| coe_eq_zero.2 <| isSt_unique (hr.symm ▸ isSt_refl_real r : IsSt x r) hi
#align hyperreal.not_real_of_infinitesimal_ne_zero Hyperreal.not_real_of_infinitesimal_ne_zero

theorem infinitesimal_sub_isSt {x : ℝ*} {r : ℝ} (hxr : IsSt x r) : Infinitesimal (x - r) :=
  show IsSt (x - r) 0 by
    rw [sub_eq_add_neg, ← add_neg_self r]
    exact is_st_add hxr (is_st_refl_real (-r))
#align hyperreal.infinitesimal_sub_is_st Hyperreal.infinitesimal_sub_isSt

theorem infinitesimal_sub_st {x : ℝ*} (hx : ¬Infinite x) : Infinitesimal (x - st x) :=
  infinitesimal_sub_isSt <| isSt_st' hx
#align hyperreal.infinitesimal_sub_st Hyperreal.infinitesimal_sub_st

theorem infinitePos_iff_infinitesimal_inv_pos {x : ℝ*} :
    InfinitePos x ↔ Infinitesimal x⁻¹ ∧ 0 < x⁻¹ :=
  ⟨fun hip =>
    ⟨infinitesimal_def.mpr fun r hr =>
        ⟨lt_trans (coe_lt_coe.2 (neg_neg_of_pos hr)) (inv_pos.2 (hip 0)),
          (inv_lt (coe_lt_coe.2 hr) (hip 0)).mp (by convert hip r⁻¹)⟩,
      inv_pos.2 <| hip 0⟩,
    fun ⟨hi, hp⟩ r =>
    @by_cases (r = 0) (↑r < x) (fun h => Eq.substr h (inv_pos.mp hp)) fun h =>
      lt_of_le_of_lt (coe_le_coe.2 (le_abs_self r))
        ((inv_lt_inv (inv_pos.mp hp) (coe_lt_coe.2 (abs_pos.2 h))).mp
          ((infinitesimal_def.mp hi) (|r|)⁻¹ (inv_pos.2 (abs_pos.2 h))).2)⟩
#align hyperreal.infinite_pos_iff_infinitesimal_inv_pos Hyperreal.infinitePos_iff_infinitesimal_inv_pos

theorem infiniteNeg_iff_infinitesimal_inv_neg {x : ℝ*} :
    InfiniteNeg x ↔ Infinitesimal x⁻¹ ∧ x⁻¹ < 0 :=
  ⟨fun hin =>
    by
    have hin' := infinitePos_iff_infinitesimal_inv_pos.mp (infinitePos_neg_of_infiniteNeg hin)
    rwa [infinitesimal_neg_iff, ← neg_pos, neg_inv], fun hin => by
    rwa [← neg_pos, infinitesimal_neg_iff, neg_inv, ← infinite_pos_iff_infinitesimal_inv_pos, ←
      infinite_neg_iff_infinite_pos_neg] at hin⟩
#align hyperreal.infinite_neg_iff_infinitesimal_inv_neg Hyperreal.infiniteNeg_iff_infinitesimal_inv_neg

theorem infinitesimal_inv_of_infinite {x : ℝ*} : Infinite x → Infinitesimal x⁻¹ := fun hi =>
  Or.cases_on hi (fun hip => (infinitePos_iff_infinitesimal_inv_pos.mp hip).1) fun hin =>
    (infiniteNeg_iff_infinitesimal_inv_neg.mp hin).1
#align hyperreal.infinitesimal_inv_of_infinite Hyperreal.infinitesimal_inv_of_infinite

theorem infinite_of_infinitesimal_inv {x : ℝ*} (h0 : x ≠ 0) (hi : Infinitesimal x⁻¹) : Infinite x :=
  by
  cases' lt_or_gt_of_ne h0 with hn hp
  · exact Or.inr (infinite_neg_iff_infinitesimal_inv_neg.mpr ⟨hi, inv_lt_zero.mpr hn⟩)
  · exact Or.inl (infinite_pos_iff_infinitesimal_inv_pos.mpr ⟨hi, inv_pos.mpr hp⟩)
#align hyperreal.infinite_of_infinitesimal_inv Hyperreal.infinite_of_infinitesimal_inv

theorem infinite_iff_infinitesimal_inv {x : ℝ*} (h0 : x ≠ 0) : Infinite x ↔ Infinitesimal x⁻¹ :=
  ⟨infinitesimal_inv_of_infinite, infinite_of_infinitesimal_inv h0⟩
#align hyperreal.infinite_iff_infinitesimal_inv Hyperreal.infinite_iff_infinitesimal_inv

theorem infinitesimal_pos_iff_infinitePos_inv {x : ℝ*} :
    InfinitePos x⁻¹ ↔ Infinitesimal x ∧ 0 < x := by
  convert infinite_pos_iff_infinitesimal_inv_pos <;> simp only [inv_inv]
#align hyperreal.infinitesimal_pos_iff_infinite_pos_inv Hyperreal.infinitesimal_pos_iff_infinitePos_inv

theorem infinitesimal_neg_iff_infiniteNeg_inv {x : ℝ*} :
    InfiniteNeg x⁻¹ ↔ Infinitesimal x ∧ x < 0 := by
  convert infinite_neg_iff_infinitesimal_inv_neg <;> simp only [inv_inv]
#align hyperreal.infinitesimal_neg_iff_infinite_neg_inv Hyperreal.infinitesimal_neg_iff_infiniteNeg_inv

theorem infinitesimal_iff_infinite_inv {x : ℝ*} (h : x ≠ 0) : Infinitesimal x ↔ Infinite x⁻¹ := by
  convert(infinite_iff_infinitesimal_inv (inv_ne_zero h)).symm <;> simp only [inv_inv]
#align hyperreal.infinitesimal_iff_infinite_inv Hyperreal.infinitesimal_iff_infinite_inv

/-!
### `st` stuff that requires infinitesimal machinery
-/


theorem isSt_of_tendsto {f : ℕ → ℝ} {r : ℝ} (hf : Tendsto f atTop (𝓝 r)) : IsSt (ofSeq f) r :=
  by
  have hg : Tendsto (fun n => f n - r) atTop (𝓝 0) := sub_self r ▸ hf.sub tendsto_const_nhds
  rw [← zero_add r, ← sub_add_cancel f fun n => r] <;>
    exact is_st_add (infinitesimal_of_tendsto_zero hg) (is_st_refl_real r)
#align hyperreal.is_st_of_tendsto Hyperreal.isSt_of_tendsto

theorem isSt_inv {x : ℝ*} {r : ℝ} (hi : ¬Infinitesimal x) : IsSt x r → IsSt x⁻¹ r⁻¹ := fun hxr =>
  have h : x ≠ 0 := fun h => hi (h.symm ▸ infinitesimal_zero)
  have H := exists_st_of_not_infinite <| not_imp_not.mpr (infinitesimal_iff_infinite_inv h).mpr hi
  Exists.cases_on H fun s hs =>
    have H' : IsSt 1 (r * s) := mul_inv_cancel h ▸ isSt_mul hxr hs
    have H'' : s = r⁻¹ := one_div r ▸ eq_one_div_of_mul_eq_one_right (eq_of_isSt_real H').symm
    H'' ▸ hs
#align hyperreal.is_st_inv Hyperreal.isSt_inv

theorem st_inv (x : ℝ*) : st x⁻¹ = (st x)⁻¹ :=
  by
  by_cases h0 : x = 0
  rw [h0, inv_zero, ← coe_zero, st_id_real, inv_zero]
  by_cases h1 : infinitesimal x
  rw [st_infinite ((infinitesimal_iff_infinite_inv h0).mp h1), st_of_is_st h1, inv_zero]
  by_cases h2 : Infinite x
  rw [st_of_is_st (infinitesimal_inv_of_infinite h2), st_infinite h2, inv_zero]
  exact st_of_is_st (is_st_inv h1 (is_st_st' h2))
#align hyperreal.st_inv Hyperreal.st_inv

/-!
### Infinite stuff that requires infinitesimal machinery
-/


theorem infinitePos_omega : InfinitePos ω :=
  infinitePos_iff_infinitesimal_inv_pos.mpr ⟨infinitesimal_epsilon, epsilon_pos⟩
#align hyperreal.infinite_pos_omega Hyperreal.infinitePos_omega

theorem infinite_omega : Infinite ω :=
  (infinite_iff_infinitesimal_inv omega_ne_zero).mpr infinitesimal_epsilon
#align hyperreal.infinite_omega Hyperreal.infinite_omega

theorem infinitePos_mul_of_infinitePos_not_infinitesimal_pos {x y : ℝ*} :
    InfinitePos x → ¬Infinitesimal y → 0 < y → InfinitePos (x * y) := fun hx hy₁ hy₂ r =>
  have hy₁' := not_forall.mp (by rw [infinitesimal_def] at hy₁ <;> exact hy₁)
  Exists.dcases_on hy₁' fun r₁ hy₁'' =>
    by
    have hyr := by rw [not_imp, ← abs_lt, not_lt, abs_of_pos hy₂] at hy₁'' <;> exact hy₁''
    rw [← div_mul_cancel r (ne_of_gt hyr.1), coe_mul] <;>
      exact mul_lt_mul (hx (r / r₁)) hyr.2 (coe_lt_coe.2 hyr.1) (le_of_lt (hx 0))
#align hyperreal.infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos Hyperreal.infinitePos_mul_of_infinitePos_not_infinitesimal_pos

theorem infinitePos_mul_of_not_infinitesimal_pos_infinitePos {x y : ℝ*} :
    ¬Infinitesimal x → 0 < x → InfinitePos y → InfinitePos (x * y) := fun hx hp hy => by
  rw [mul_comm] <;> exact infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos hy hx hp
#align hyperreal.infinite_pos_mul_of_not_infinitesimal_pos_infinite_pos Hyperreal.infinitePos_mul_of_not_infinitesimal_pos_infinitePos

theorem infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg {x y : ℝ*} :
    InfiniteNeg x → ¬Infinitesimal y → y < 0 → InfinitePos (x * y) := by
  rw [infinite_neg_iff_infinite_pos_neg, ← neg_pos, ← neg_mul_neg, infinitesimal_neg_iff] <;>
    exact infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos
#align hyperreal.infinite_pos_mul_of_infinite_neg_not_infinitesimal_neg Hyperreal.infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg

theorem infinitePos_mul_of_not_infinitesimal_neg_infiniteNeg {x y : ℝ*} :
    ¬Infinitesimal x → x < 0 → InfiniteNeg y → InfinitePos (x * y) := fun hx hp hy => by
  rw [mul_comm] <;> exact infinite_pos_mul_of_infinite_neg_not_infinitesimal_neg hy hx hp
#align hyperreal.infinite_pos_mul_of_not_infinitesimal_neg_infinite_neg Hyperreal.infinitePos_mul_of_not_infinitesimal_neg_infiniteNeg

theorem infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg {x y : ℝ*} :
    InfinitePos x → ¬Infinitesimal y → y < 0 → InfiniteNeg (x * y) := by
  rw [infinite_neg_iff_infinite_pos_neg, ← neg_pos, neg_mul_eq_mul_neg, infinitesimal_neg_iff] <;>
    exact infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos
#align hyperreal.infinite_neg_mul_of_infinite_pos_not_infinitesimal_neg Hyperreal.infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg

theorem infiniteNeg_mul_of_not_infinitesimal_neg_infinitePos {x y : ℝ*} :
    ¬Infinitesimal x → x < 0 → InfinitePos y → InfiniteNeg (x * y) := fun hx hp hy => by
  rw [mul_comm] <;> exact infinite_neg_mul_of_infinite_pos_not_infinitesimal_neg hy hx hp
#align hyperreal.infinite_neg_mul_of_not_infinitesimal_neg_infinite_pos Hyperreal.infiniteNeg_mul_of_not_infinitesimal_neg_infinitePos

theorem infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos {x y : ℝ*} :
    InfiniteNeg x → ¬Infinitesimal y → 0 < y → InfiniteNeg (x * y) := by
  rw [infinite_neg_iff_infinite_pos_neg, infinite_neg_iff_infinite_pos_neg, neg_mul_eq_neg_mul] <;>
    exact infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos
#align hyperreal.infinite_neg_mul_of_infinite_neg_not_infinitesimal_pos Hyperreal.infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos

theorem infiniteNeg_mul_of_not_infinitesimal_pos_infiniteNeg {x y : ℝ*} :
    ¬Infinitesimal x → 0 < x → InfiniteNeg y → InfiniteNeg (x * y) := fun hx hp hy => by
  rw [mul_comm] <;> exact infinite_neg_mul_of_infinite_neg_not_infinitesimal_pos hy hx hp
#align hyperreal.infinite_neg_mul_of_not_infinitesimal_pos_infinite_neg Hyperreal.infiniteNeg_mul_of_not_infinitesimal_pos_infiniteNeg

theorem infinitePos_mul_infinitePos {x y : ℝ*} :
    InfinitePos x → InfinitePos y → InfinitePos (x * y) := fun hx hy =>
  infinitePos_mul_of_infinitePos_not_infinitesimal_pos hx (not_infinitesimal_of_infinitePos hy)
    (hy 0)
#align hyperreal.infinite_pos_mul_infinite_pos Hyperreal.infinitePos_mul_infinitePos

theorem infiniteNeg_mul_infiniteNeg {x y : ℝ*} :
    InfiniteNeg x → InfiniteNeg y → InfinitePos (x * y) := fun hx hy =>
  infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg hx (not_infinitesimal_of_infiniteNeg hy)
    (hy 0)
#align hyperreal.infinite_neg_mul_infinite_neg Hyperreal.infiniteNeg_mul_infiniteNeg

theorem infinitePos_mul_infiniteNeg {x y : ℝ*} :
    InfinitePos x → InfiniteNeg y → InfiniteNeg (x * y) := fun hx hy =>
  infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg hx (not_infinitesimal_of_infiniteNeg hy)
    (hy 0)
#align hyperreal.infinite_pos_mul_infinite_neg Hyperreal.infinitePos_mul_infiniteNeg

theorem infiniteNeg_mul_infinitePos {x y : ℝ*} :
    InfiniteNeg x → InfinitePos y → InfiniteNeg (x * y) := fun hx hy =>
  infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos hx (not_infinitesimal_of_infinitePos hy)
    (hy 0)
#align hyperreal.infinite_neg_mul_infinite_pos Hyperreal.infiniteNeg_mul_infinitePos

theorem infinite_mul_of_infinite_not_infinitesimal {x y : ℝ*} :
    Infinite x → ¬Infinitesimal y → Infinite (x * y) := fun hx hy =>
  have h0 : y < 0 ∨ 0 < y := lt_or_gt_of_ne fun H0 => hy (Eq.substr H0 (isSt_refl_real 0))
  Or.dcases_on hx
    (Or.dcases_on h0
      (fun H0 Hx => Or.inr (infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg Hx hy H0))
      fun H0 Hx => Or.inl (infinitePos_mul_of_infinitePos_not_infinitesimal_pos Hx hy H0))
    (Or.dcases_on h0
      (fun H0 Hx => Or.inl (infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg Hx hy H0))
      fun H0 Hx => Or.inr (infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos Hx hy H0))
#align hyperreal.infinite_mul_of_infinite_not_infinitesimal Hyperreal.infinite_mul_of_infinite_not_infinitesimal

theorem infinite_mul_of_not_infinitesimal_infinite {x y : ℝ*} :
    ¬Infinitesimal x → Infinite y → Infinite (x * y) := fun hx hy => by
  rw [mul_comm] <;> exact infinite_mul_of_infinite_not_infinitesimal hy hx
#align hyperreal.infinite_mul_of_not_infinitesimal_infinite Hyperreal.infinite_mul_of_not_infinitesimal_infinite

theorem Infinite.mul {x y : ℝ*} : Infinite x → Infinite y → Infinite (x * y) := fun hx hy =>
  infinite_mul_of_infinite_not_infinitesimal hx (not_infinitesimal_of_infinite hy)
#align hyperreal.infinite.mul Hyperreal.Infinite.mul

end Hyperreal

namespace Tactic

open Positivity

private theorem hyperreal_coe_ne_zero {r : ℝ} : r ≠ 0 → (r : ℝ*) ≠ 0 :=
  Hyperreal.coe_ne_zero.2
#align tactic.hyperreal_coe_ne_zero tactic.hyperreal_coe_ne_zero

private theorem hyperreal_coe_nonneg {r : ℝ} : 0 ≤ r → 0 ≤ (r : ℝ*) :=
  Hyperreal.coe_nonneg.2
#align tactic.hyperreal_coe_nonneg tactic.hyperreal_coe_nonneg

private theorem hyperreal_coe_pos {r : ℝ} : 0 < r → 0 < (r : ℝ*) :=
  Hyperreal.coe_pos.2
#align tactic.hyperreal_coe_pos tactic.hyperreal_coe_pos

/-- Extension for the `positivity` tactic: cast from `ℝ` to `ℝ*`. -/
@[positivity]
unsafe def positivity_coe_real_hyperreal : expr → tactic strictness
  | q(@coe _ _ $(inst) $(a)) => do
    unify inst q(@coeToLift _ _ Hyperreal.hasCoeT)
    let strictness_a ← core a
    match strictness_a with
      | positive p => positive <$> mk_app `` hyperreal_coe_pos [p]
      | nonnegative p => nonnegative <$> mk_app `` hyperreal_coe_nonneg [p]
      | nonzero p => nonzero <$> mk_app `` hyperreal_coe_ne_zero [p]
  | e =>
    pp e >>= fail ∘ format.bracket "The expression " " is not of the form `(r : ℝ*)` for `r : ℝ`"
#align tactic.positivity_coe_real_hyperreal tactic.positivity_coe_real_hyperreal

end Tactic

