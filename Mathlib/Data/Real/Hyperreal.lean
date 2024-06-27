/-
Copyright (c) 2019 Abhimanyu Pallavi Sudhir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhimanyu Pallavi Sudhir
-/
import Mathlib.Order.Filter.FilterProduct
import Mathlib.Analysis.SpecificLimits.Basic

#align_import data.real.hyperreal from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Construction of the hyperreal numbers as an ultraproduct of real sequences.
-/


open scoped Classical
open Filter Germ Topology

/-- Hyperreal numbers on the ultrafilter extending the cofinite filter -/
def Hyperreal : Type :=
  Germ (hyperfilter ℕ : Filter ℕ) ℝ deriving Inhabited
#align hyperreal Hyperreal

namespace Hyperreal

@[inherit_doc] notation "ℝ*" => Hyperreal

noncomputable instance : LinearOrderedField ℝ* :=
  inferInstanceAs (LinearOrderedField (Germ _ _))

/-- Natural embedding `ℝ → ℝ*`. -/
@[coe] def ofReal : ℝ → ℝ* := const

noncomputable instance : CoeTC ℝ ℝ* := ⟨ofReal⟩

@[simp, norm_cast]
theorem coe_eq_coe {x y : ℝ} : (x : ℝ*) = y ↔ x = y :=
  Germ.const_inj
#align hyperreal.coe_eq_coe Hyperreal.coe_eq_coe

theorem coe_ne_coe {x y : ℝ} : (x : ℝ*) ≠ y ↔ x ≠ y :=
  coe_eq_coe.not
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

#noalign hyperreal.coe_bit0
#noalign hyperreal.coe_bit1

-- See note [no_index around OfNat.ofNat]
@[simp, norm_cast]
theorem coe_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((no_index (OfNat.ofNat n : ℝ)) : ℝ*) = OfNat.ofNat n :=
  rfl

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
theorem coe_abs (x : ℝ) : ((|x| : ℝ) : ℝ*) = |↑x| :=
  const_abs x
#align hyperreal.coe_abs Hyperreal.coe_abs

@[simp, norm_cast]
theorem coe_max (x y : ℝ) : ((max x y : ℝ) : ℝ*) = max ↑x ↑y :=
  Germ.const_max _ _
#align hyperreal.coe_max Hyperreal.coe_max

@[simp, norm_cast]
theorem coe_min (x y : ℝ) : ((min x y : ℝ) : ℝ*) = min ↑x ↑y :=
  Germ.const_min _ _
#align hyperreal.coe_min Hyperreal.coe_min

/-- Construct a hyperreal number from a sequence of real numbers. -/
def ofSeq (f : ℕ → ℝ) : ℝ* := (↑f : Germ (hyperfilter ℕ : Filter ℕ) ℝ)
#align hyperreal.of_seq Hyperreal.ofSeq

theorem ofSeq_surjective : Function.Surjective ofSeq := Quot.exists_rep

theorem ofSeq_lt_ofSeq {f g : ℕ → ℝ} : ofSeq f < ofSeq g ↔ ∀ᶠ n in hyperfilter ℕ, f n < g n :=
  Germ.coe_lt

/-- A sample infinitesimal hyperreal-/
noncomputable def epsilon : ℝ* :=
  ofSeq fun n => n⁻¹
#align hyperreal.epsilon Hyperreal.epsilon

/-- A sample infinite hyperreal-/
noncomputable def omega : ℝ* := ofSeq Nat.cast
#align hyperreal.omega Hyperreal.omega

@[inherit_doc] scoped notation "ε" => Hyperreal.epsilon
@[inherit_doc] scoped notation "ω" => Hyperreal.omega

@[simp]
theorem inv_omega : ω⁻¹ = ε :=
  rfl
#align hyperreal.inv_omega Hyperreal.inv_omega

@[simp]
theorem inv_epsilon : ε⁻¹ = ω :=
  @inv_inv _ _ ω
#align hyperreal.inv_epsilon Hyperreal.inv_epsilon

theorem omega_pos : 0 < ω :=
  Germ.coe_pos.2 <| Nat.hyperfilter_le_atTop <| (eventually_gt_atTop 0).mono fun _ ↦
    Nat.cast_pos.2
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
    ∀ {r : ℝ}, 0 < r → ofSeq f < (r : ℝ*) := fun hr ↦
  ofSeq_lt_ofSeq.2 <| (hf.eventually <| gt_mem_nhds hr).filter_mono Nat.hyperfilter_le_atTop
#align hyperreal.lt_of_tendsto_zero_of_pos Hyperreal.lt_of_tendsto_zero_of_pos

theorem neg_lt_of_tendsto_zero_of_pos {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0)) :
    ∀ {r : ℝ}, 0 < r → (-r : ℝ*) < ofSeq f := fun hr =>
  have hg := hf.neg
  neg_lt_of_neg_lt (by rw [neg_zero] at hg; exact lt_of_tendsto_zero_of_pos hg hr)
#align hyperreal.neg_lt_of_tendsto_zero_of_pos Hyperreal.neg_lt_of_tendsto_zero_of_pos

theorem gt_of_tendsto_zero_of_neg {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0)) :
    ∀ {r : ℝ}, r < 0 → (r : ℝ*) < ofSeq f := fun {r} hr => by
  rw [← neg_neg r, coe_neg]; exact neg_lt_of_tendsto_zero_of_pos hf (neg_pos.mpr hr)
#align hyperreal.gt_of_tendsto_zero_of_neg Hyperreal.gt_of_tendsto_zero_of_neg

theorem epsilon_lt_pos (x : ℝ) : 0 < x → ε < x :=
  lt_of_tendsto_zero_of_pos tendsto_inverse_atTop_nhds_zero_nat
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

theorem isSt_ofSeq_iff_tendsto {f : ℕ → ℝ} {r : ℝ} :
    IsSt (ofSeq f) r ↔ Tendsto f (hyperfilter ℕ) (𝓝 r) :=
  Iff.trans (forall₂_congr fun _ _ ↦ (ofSeq_lt_ofSeq.and ofSeq_lt_ofSeq).trans eventually_and.symm)
    (nhds_basis_Ioo_pos _).tendsto_right_iff.symm

theorem isSt_iff_tendsto {x : ℝ*} {r : ℝ} : IsSt x r ↔ x.Tendsto (𝓝 r) := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  exact isSt_ofSeq_iff_tendsto

theorem isSt_of_tendsto {f : ℕ → ℝ} {r : ℝ} (hf : Tendsto f atTop (𝓝 r)) : IsSt (ofSeq f) r :=
  isSt_ofSeq_iff_tendsto.2 <| hf.mono_left Nat.hyperfilter_le_atTop
#align hyperreal.is_st_of_tendsto Hyperreal.isSt_of_tendsto

-- Porting note: moved up, renamed
protected theorem IsSt.lt {x y : ℝ*} {r s : ℝ} (hxr : IsSt x r) (hys : IsSt y s) (hrs : r < s) :
    x < y := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rcases ofSeq_surjective y with ⟨g, rfl⟩
  rw [isSt_ofSeq_iff_tendsto] at hxr hys
  exact ofSeq_lt_ofSeq.2 <| hxr.eventually_lt hys hrs
#align hyperreal.lt_of_is_st_lt Hyperreal.IsSt.lt

theorem IsSt.unique {x : ℝ*} {r s : ℝ} (hr : IsSt x r) (hs : IsSt x s) : r = s := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rw [isSt_ofSeq_iff_tendsto] at hr hs
  exact tendsto_nhds_unique hr hs
#align hyperreal.is_st_unique Hyperreal.IsSt.unique

theorem IsSt.st_eq {x : ℝ*} {r : ℝ} (hxr : IsSt x r) : st x = r := by
  have h : ∃ r, IsSt x r := ⟨r, hxr⟩
  rw [st, dif_pos h]
  exact (Classical.choose_spec h).unique hxr
#align hyperreal.st_of_is_st Hyperreal.IsSt.st_eq

theorem IsSt.not_infinite {x : ℝ*} {r : ℝ} (h : IsSt x r) : ¬Infinite x := fun hi ↦
  hi.elim (fun hp ↦ lt_asymm (h 1 one_pos).2 (hp (r + 1))) fun hn ↦
    lt_asymm (h 1 one_pos).1 (hn (r - 1))

theorem not_infinite_of_exists_st {x : ℝ*} : (∃ r : ℝ, IsSt x r) → ¬Infinite x := fun ⟨_r, hr⟩ =>
  hr.not_infinite
#align hyperreal.not_infinite_of_exists_st Hyperreal.not_infinite_of_exists_st

theorem Infinite.st_eq {x : ℝ*} (hi : Infinite x) : st x = 0 :=
  dif_neg fun ⟨_r, hr⟩ ↦ hr.not_infinite hi
#align hyperreal.st_infinite Hyperreal.Infinite.st_eq

theorem isSt_sSup {x : ℝ*} (hni : ¬Infinite x) : IsSt x (sSup { y : ℝ | (y : ℝ*) < x }) :=
  let S : Set ℝ := { y : ℝ | (y : ℝ*) < x }
  let R : ℝ := sSup S
  let ⟨r₁, hr₁⟩ := not_forall.mp (not_or.mp hni).2
  let ⟨r₂, hr₂⟩ := not_forall.mp (not_or.mp hni).1
  have HR₁ : S.Nonempty :=
    ⟨r₁ - 1, lt_of_lt_of_le (coe_lt_coe.2 <| sub_one_lt _) (not_lt.mp hr₁)⟩
  have HR₂ : BddAbove S :=
    ⟨r₂, fun _y hy => le_of_lt (coe_lt_coe.1 (lt_of_lt_of_le hy (not_lt.mp hr₂)))⟩
  fun δ hδ =>
  ⟨lt_of_not_le fun c =>
      have hc : ∀ y ∈ S, y ≤ R - δ := fun _y hy =>
        coe_le_coe.1 <| le_of_lt <| lt_of_lt_of_le hy c
      not_lt_of_le (csSup_le HR₁ hc) <| sub_lt_self R hδ,
    lt_of_not_le fun c =>
      have hc : ↑(R + δ / 2) < x :=
        lt_of_lt_of_le (add_lt_add_left (coe_lt_coe.2 (half_lt_self hδ)) R) c
      not_lt_of_le (le_csSup HR₂ hc) <| (lt_add_iff_pos_right _).mpr <| half_pos hδ⟩
#align hyperreal.is_st_Sup Hyperreal.isSt_sSup

theorem exists_st_of_not_infinite {x : ℝ*} (hni : ¬Infinite x) : ∃ r : ℝ, IsSt x r :=
  ⟨sSup { y : ℝ | (y : ℝ*) < x }, isSt_sSup hni⟩
#align hyperreal.exists_st_of_not_infinite Hyperreal.exists_st_of_not_infinite

theorem st_eq_sSup {x : ℝ*} : st x = sSup { y : ℝ | (y : ℝ*) < x } := by
  rcases _root_.em (Infinite x) with (hx|hx)
  · rw [hx.st_eq]
    cases hx with
    | inl hx =>
      convert Real.sSup_univ.symm
      exact Set.eq_univ_of_forall hx
    | inr hx =>
      convert Real.sSup_empty.symm
      exact Set.eq_empty_of_forall_not_mem fun y hy ↦ hy.out.not_lt (hx _)
  · exact (isSt_sSup hx).st_eq
#align hyperreal.st_eq_Sup Hyperreal.st_eq_sSup

theorem exists_st_iff_not_infinite {x : ℝ*} : (∃ r : ℝ, IsSt x r) ↔ ¬Infinite x :=
  ⟨not_infinite_of_exists_st, exists_st_of_not_infinite⟩
#align hyperreal.exists_st_iff_not_infinite Hyperreal.exists_st_iff_not_infinite

theorem infinite_iff_not_exists_st {x : ℝ*} : Infinite x ↔ ¬∃ r : ℝ, IsSt x r :=
  iff_not_comm.mp exists_st_iff_not_infinite
#align hyperreal.infinite_iff_not_exists_st Hyperreal.infinite_iff_not_exists_st

theorem IsSt.isSt_st {x : ℝ*} {r : ℝ} (hxr : IsSt x r) : IsSt x (st x) := by
  rwa [hxr.st_eq]
#align hyperreal.is_st_st_of_is_st Hyperreal.IsSt.isSt_st

theorem isSt_st_of_exists_st {x : ℝ*} (hx : ∃ r : ℝ, IsSt x r) : IsSt x (st x) :=
  let ⟨_r, hr⟩ := hx; hr.isSt_st
#align hyperreal.is_st_st_of_exists_st Hyperreal.isSt_st_of_exists_st

theorem isSt_st' {x : ℝ*} (hx : ¬Infinite x) : IsSt x (st x) :=
  (isSt_sSup hx).isSt_st
#align hyperreal.is_st_st' Hyperreal.isSt_st'

theorem isSt_st {x : ℝ*} (hx : st x ≠ 0) : IsSt x (st x) :=
  isSt_st' <| mt Infinite.st_eq hx
#align hyperreal.is_st_st Hyperreal.isSt_st

theorem isSt_refl_real (r : ℝ) : IsSt r r := isSt_ofSeq_iff_tendsto.2 tendsto_const_nhds
#align hyperreal.is_st_refl_real Hyperreal.isSt_refl_real

theorem st_id_real (r : ℝ) : st r = r := (isSt_refl_real r).st_eq
#align hyperreal.st_id_real Hyperreal.st_id_real

theorem eq_of_isSt_real {r s : ℝ} : IsSt r s → r = s :=
  (isSt_refl_real r).unique
#align hyperreal.eq_of_is_st_real Hyperreal.eq_of_isSt_real

theorem isSt_real_iff_eq {r s : ℝ} : IsSt r s ↔ r = s :=
  ⟨eq_of_isSt_real, fun hrs => hrs ▸ isSt_refl_real r⟩
#align hyperreal.is_st_real_iff_eq Hyperreal.isSt_real_iff_eq

theorem isSt_symm_real {r s : ℝ} : IsSt r s ↔ IsSt s r := by
  rw [isSt_real_iff_eq, isSt_real_iff_eq, eq_comm]
#align hyperreal.is_st_symm_real Hyperreal.isSt_symm_real

theorem isSt_trans_real {r s t : ℝ} : IsSt r s → IsSt s t → IsSt r t := by
  rw [isSt_real_iff_eq, isSt_real_iff_eq, isSt_real_iff_eq]; exact Eq.trans
#align hyperreal.is_st_trans_real Hyperreal.isSt_trans_real

theorem isSt_inj_real {r₁ r₂ s : ℝ} (h1 : IsSt r₁ s) (h2 : IsSt r₂ s) : r₁ = r₂ :=
  Eq.trans (eq_of_isSt_real h1) (eq_of_isSt_real h2).symm
#align hyperreal.is_st_inj_real Hyperreal.isSt_inj_real

theorem isSt_iff_abs_sub_lt_delta {x : ℝ*} {r : ℝ} : IsSt x r ↔ ∀ δ : ℝ, 0 < δ → |x - ↑r| < δ := by
  simp only [abs_sub_lt_iff, sub_lt_iff_lt_add, IsSt, and_comm, add_comm]
#align hyperreal.is_st_iff_abs_sub_lt_delta Hyperreal.isSt_iff_abs_sub_lt_delta

theorem IsSt.map {x : ℝ*} {r : ℝ} (hxr : IsSt x r) {f : ℝ → ℝ} (hf : ContinuousAt f r) :
    IsSt (x.map f) (f r) := by
  rcases ofSeq_surjective x with ⟨g, rfl⟩
  exact isSt_ofSeq_iff_tendsto.2 <| hf.tendsto.comp (isSt_ofSeq_iff_tendsto.1 hxr)

theorem IsSt.map₂ {x y : ℝ*} {r s : ℝ} (hxr : IsSt x r) (hys : IsSt y s) {f : ℝ → ℝ → ℝ}
    (hf : ContinuousAt (Function.uncurry f) (r, s)) : IsSt (x.map₂ f y) (f r s) := by
  rcases ofSeq_surjective x with ⟨x, rfl⟩
  rcases ofSeq_surjective y with ⟨y, rfl⟩
  rw [isSt_ofSeq_iff_tendsto] at hxr hys
  exact isSt_ofSeq_iff_tendsto.2 <| hf.tendsto.comp (hxr.prod_mk_nhds hys)

theorem IsSt.add {x y : ℝ*} {r s : ℝ} (hxr : IsSt x r) (hys : IsSt y s) :
    IsSt (x + y) (r + s) := hxr.map₂ hys continuous_add.continuousAt
#align hyperreal.is_st_add Hyperreal.IsSt.add

theorem IsSt.neg {x : ℝ*} {r : ℝ} (hxr : IsSt x r) : IsSt (-x) (-r) :=
  hxr.map continuous_neg.continuousAt
#align hyperreal.is_st_neg Hyperreal.IsSt.neg

theorem IsSt.sub {x y : ℝ*} {r s : ℝ} (hxr : IsSt x r) (hys : IsSt y s) : IsSt (x - y) (r - s) :=
  hxr.map₂ hys continuous_sub.continuousAt
#align hyperreal.is_st_sub Hyperreal.IsSt.sub

theorem IsSt.le {x y : ℝ*} {r s : ℝ} (hrx : IsSt x r) (hsy : IsSt y s) (hxy : x ≤ y) : r ≤ s :=
  not_lt.1 fun h ↦ hxy.not_lt <| hsy.lt hrx h
#align hyperreal.is_st_le_of_le Hyperreal.IsSt.le

theorem st_le_of_le {x y : ℝ*} (hix : ¬Infinite x) (hiy : ¬Infinite y) : x ≤ y → st x ≤ st y :=
  (isSt_st' hix).le (isSt_st' hiy)
#align hyperreal.st_le_of_le Hyperreal.st_le_of_le

theorem lt_of_st_lt {x y : ℝ*} (hix : ¬Infinite x) (hiy : ¬Infinite y) : st x < st y → x < y :=
  (isSt_st' hix).lt (isSt_st' hiy)
#align hyperreal.lt_of_st_lt Hyperreal.lt_of_st_lt

/-!
### Basic lemmas about infinite
-/

theorem infinitePos_def {x : ℝ*} : InfinitePos x ↔ ∀ r : ℝ, ↑r < x := Iff.rfl
#align hyperreal.infinite_pos_def Hyperreal.infinitePos_def

theorem infiniteNeg_def {x : ℝ*} : InfiniteNeg x ↔ ∀ r : ℝ, x < r := Iff.rfl
#align hyperreal.infinite_neg_def Hyperreal.infiniteNeg_def

theorem InfinitePos.pos {x : ℝ*} (hip : InfinitePos x) : 0 < x := hip 0
#align hyperreal.pos_of_infinite_pos Hyperreal.InfinitePos.pos

theorem InfiniteNeg.lt_zero {x : ℝ*} : InfiniteNeg x → x < 0 := fun hin => hin 0
#align hyperreal.neg_of_infinite_neg Hyperreal.InfiniteNeg.lt_zero

theorem Infinite.ne_zero {x : ℝ*} (hI : Infinite x) : x ≠ 0 :=
  hI.elim (fun hip => hip.pos.ne') fun hin => hin.lt_zero.ne
#align hyperreal.ne_zero_of_infinite Hyperreal.Infinite.ne_zero

theorem not_infinite_zero : ¬Infinite 0 := fun hI => hI.ne_zero rfl
#align hyperreal.not_infinite_zero Hyperreal.not_infinite_zero

theorem InfiniteNeg.not_infinitePos {x : ℝ*} : InfiniteNeg x → ¬InfinitePos x := fun hn hp =>
  (hn 0).not_lt (hp 0)
#align hyperreal.not_infinite_pos_of_infinite_neg Hyperreal.InfiniteNeg.not_infinitePos

theorem InfinitePos.not_infiniteNeg {x : ℝ*} (hp : InfinitePos x) : ¬InfiniteNeg x := fun hn ↦
  hn.not_infinitePos hp
#align hyperreal.not_infinite_neg_of_infinite_pos Hyperreal.InfinitePos.not_infiniteNeg

theorem InfinitePos.neg {x : ℝ*} : InfinitePos x → InfiniteNeg (-x) := fun hp r =>
  neg_lt.mp (hp (-r))
#align hyperreal.infinite_neg_neg_of_infinite_pos Hyperreal.InfinitePos.neg

theorem InfiniteNeg.neg {x : ℝ*} : InfiniteNeg x → InfinitePos (-x) := fun hp r =>
  lt_neg.mp (hp (-r))
#align hyperreal.infinite_pos_neg_of_infinite_neg Hyperreal.InfiniteNeg.neg

-- Porting note: swapped LHS with RHS; added @[simp]
@[simp] theorem infiniteNeg_neg {x : ℝ*} : InfiniteNeg (-x) ↔ InfinitePos x :=
  ⟨fun hin => neg_neg x ▸ hin.neg, InfinitePos.neg⟩
#align hyperreal.infinite_pos_iff_infinite_neg_neg Hyperreal.infiniteNeg_negₓ

-- Porting note: swapped LHS with RHS; added @[simp]
@[simp] theorem infinitePos_neg {x : ℝ*} : InfinitePos (-x) ↔ InfiniteNeg x :=
  ⟨fun hin => neg_neg x ▸ hin.neg, InfiniteNeg.neg⟩
#align hyperreal.infinite_neg_iff_infinite_pos_neg Hyperreal.infinitePos_negₓ

-- Porting note: swapped LHS with RHS; added @[simp]
@[simp] theorem infinite_neg {x : ℝ*} : Infinite (-x) ↔ Infinite x :=
  or_comm.trans <| infiniteNeg_neg.or infinitePos_neg
#align hyperreal.infinite_iff_infinite_neg Hyperreal.infinite_negₓ

nonrec theorem Infinitesimal.not_infinite {x : ℝ*} (h : Infinitesimal x) : ¬Infinite x :=
  h.not_infinite
#align hyperreal.not_infinite_of_infinitesimal Hyperreal.Infinitesimal.not_infinite

theorem Infinite.not_infinitesimal {x : ℝ*} (h : Infinite x) : ¬Infinitesimal x := fun h' ↦
  h'.not_infinite h
#align hyperreal.not_infinitesimal_of_infinite Hyperreal.Infinite.not_infinitesimal

theorem InfinitePos.not_infinitesimal {x : ℝ*} (h : InfinitePos x) : ¬Infinitesimal x :=
  Infinite.not_infinitesimal (Or.inl h)
#align hyperreal.not_infinitesimal_of_infinite_pos Hyperreal.InfinitePos.not_infinitesimal

theorem InfiniteNeg.not_infinitesimal {x : ℝ*} (h : InfiniteNeg x) : ¬Infinitesimal x :=
  Infinite.not_infinitesimal (Or.inr h)
#align hyperreal.not_infinitesimal_of_infinite_neg Hyperreal.InfiniteNeg.not_infinitesimal

theorem infinitePos_iff_infinite_and_pos {x : ℝ*} : InfinitePos x ↔ Infinite x ∧ 0 < x :=
  ⟨fun hip => ⟨Or.inl hip, hip 0⟩, fun ⟨hi, hp⟩ =>
    hi.casesOn (fun hip => hip) fun hin => False.elim (not_lt_of_lt hp (hin 0))⟩
#align hyperreal.infinite_pos_iff_infinite_and_pos Hyperreal.infinitePos_iff_infinite_and_pos

theorem infiniteNeg_iff_infinite_and_neg {x : ℝ*} : InfiniteNeg x ↔ Infinite x ∧ x < 0 :=
  ⟨fun hip => ⟨Or.inr hip, hip 0⟩, fun ⟨hi, hp⟩ =>
    hi.casesOn (fun hin => False.elim (not_lt_of_lt hp (hin 0))) fun hip => hip⟩
#align hyperreal.infinite_neg_iff_infinite_and_neg Hyperreal.infiniteNeg_iff_infinite_and_neg

theorem infinitePos_iff_infinite_of_nonneg {x : ℝ*} (hp : 0 ≤ x) : InfinitePos x ↔ Infinite x :=
  .symm <| or_iff_left fun h ↦ h.lt_zero.not_le hp
#align hyperreal.infinite_pos_iff_infinite_of_nonneg Hyperreal.infinitePos_iff_infinite_of_nonneg

theorem infinitePos_iff_infinite_of_pos {x : ℝ*} (hp : 0 < x) : InfinitePos x ↔ Infinite x :=
  infinitePos_iff_infinite_of_nonneg hp.le
#align hyperreal.infinite_pos_iff_infinite_of_pos Hyperreal.infinitePos_iff_infinite_of_pos

theorem infiniteNeg_iff_infinite_of_neg {x : ℝ*} (hn : x < 0) : InfiniteNeg x ↔ Infinite x :=
  .symm <| or_iff_right fun h ↦ h.pos.not_lt hn
#align hyperreal.infinite_neg_iff_infinite_of_neg Hyperreal.infiniteNeg_iff_infinite_of_neg

theorem infinitePos_abs_iff_infinite_abs {x : ℝ*} : InfinitePos |x| ↔ Infinite |x| :=
  infinitePos_iff_infinite_of_nonneg (abs_nonneg _)
#align hyperreal.infinite_pos_abs_iff_infinite_abs Hyperreal.infinitePos_abs_iff_infinite_abs

-- Porting note: swapped LHS with RHS; added @[simp]
@[simp] theorem infinite_abs_iff {x : ℝ*} : Infinite |x| ↔ Infinite x := by
  cases le_total 0 x <;> simp [*, abs_of_nonneg, abs_of_nonpos, infinite_neg]
#align hyperreal.infinite_iff_infinite_abs Hyperreal.infinite_abs_iffₓ

-- Porting note: swapped LHS with RHS;
-- Porting note (#11215): TODO: make it a `simp` lemma
@[simp] theorem infinitePos_abs_iff_infinite {x : ℝ*} : InfinitePos |x| ↔ Infinite x :=
  infinitePos_abs_iff_infinite_abs.trans infinite_abs_iff
#align hyperreal.infinite_iff_infinite_pos_abs Hyperreal.infinitePos_abs_iff_infiniteₓ

theorem infinite_iff_abs_lt_abs {x : ℝ*} : Infinite x ↔ ∀ r : ℝ, (|r| : ℝ*) < |x| :=
  infinitePos_abs_iff_infinite.symm.trans ⟨fun hI r => coe_abs r ▸ hI |r|, fun hR r =>
    (le_abs_self _).trans_lt (hR r)⟩
#align hyperreal.infinite_iff_abs_lt_abs Hyperreal.infinite_iff_abs_lt_abs

theorem infinitePos_add_not_infiniteNeg {x y : ℝ*} :
    InfinitePos x → ¬InfiniteNeg y → InfinitePos (x + y) := by
  intro hip hnin r
  cases' not_forall.mp hnin with r₂ hr₂
  convert add_lt_add_of_lt_of_le (hip (r + -r₂)) (not_lt.mp hr₂) using 1
  simp
#align hyperreal.infinite_pos_add_not_infinite_neg Hyperreal.infinitePos_add_not_infiniteNeg

theorem not_infiniteNeg_add_infinitePos {x y : ℝ*} :
    ¬InfiniteNeg x → InfinitePos y → InfinitePos (x + y) := fun hx hy =>
  add_comm y x ▸ infinitePos_add_not_infiniteNeg hy hx
#align hyperreal.not_infinite_neg_add_infinite_pos Hyperreal.not_infiniteNeg_add_infinitePos

theorem infiniteNeg_add_not_infinitePos {x y : ℝ*} :
    InfiniteNeg x → ¬InfinitePos y → InfiniteNeg (x + y) := by
  rw [← infinitePos_neg, ← infinitePos_neg, ← @infiniteNeg_neg y, neg_add]
  exact infinitePos_add_not_infiniteNeg
#align hyperreal.infinite_neg_add_not_infinite_pos Hyperreal.infiniteNeg_add_not_infinitePos

theorem not_infinitePos_add_infiniteNeg {x y : ℝ*} :
    ¬InfinitePos x → InfiniteNeg y → InfiniteNeg (x + y) := fun hx hy =>
  add_comm y x ▸ infiniteNeg_add_not_infinitePos hy hx
#align hyperreal.not_infinite_pos_add_infinite_neg Hyperreal.not_infinitePos_add_infiniteNeg

theorem infinitePos_add_infinitePos {x y : ℝ*} :
    InfinitePos x → InfinitePos y → InfinitePos (x + y) := fun hx hy =>
  infinitePos_add_not_infiniteNeg hx hy.not_infiniteNeg
#align hyperreal.infinite_pos_add_infinite_pos Hyperreal.infinitePos_add_infinitePos

theorem infiniteNeg_add_infiniteNeg {x y : ℝ*} :
    InfiniteNeg x → InfiniteNeg y → InfiniteNeg (x + y) := fun hx hy =>
  infiniteNeg_add_not_infinitePos hx hy.not_infinitePos
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
  let ⟨i, hi⟩ := hf' (r + 1)
  have hi' : ∀ a : ℕ, f a < r + 1 → a < i := fun a => lt_imp_lt_of_le_imp_le (hi a)
  have hS : { a : ℕ | r < f a }ᶜ ⊆ { a : ℕ | a ≤ i } := by
    simp only [Set.compl_setOf, not_lt]
    exact fun a har => le_of_lt (hi' a (lt_of_le_of_lt har (lt_add_one _)))
  Germ.coe_lt.2 <| mem_hyperfilter_of_finite_compl <| (Set.finite_le_nat _).subset hS
#align hyperreal.infinite_pos_of_tendsto_top Hyperreal.infinitePos_of_tendsto_top

theorem infiniteNeg_of_tendsto_bot {f : ℕ → ℝ} (hf : Tendsto f atTop atBot) :
    InfiniteNeg (ofSeq f) := fun r =>
  have hf' := tendsto_atTop_atBot.mp hf
  let ⟨i, hi⟩ := hf' (r - 1)
  have hi' : ∀ a : ℕ, r - 1 < f a → a < i := fun a => lt_imp_lt_of_le_imp_le (hi a)
  have hS : { a : ℕ | f a < r }ᶜ ⊆ { a : ℕ | a ≤ i } := by
    simp only [Set.compl_setOf, not_lt]
    exact fun a har => le_of_lt (hi' a (lt_of_lt_of_le (sub_one_lt _) har))
  Germ.coe_lt.2 <| mem_hyperfilter_of_finite_compl <| (Set.finite_le_nat _).subset hS
#align hyperreal.infinite_neg_of_tendsto_bot Hyperreal.infiniteNeg_of_tendsto_bot

theorem not_infinite_neg {x : ℝ*} : ¬Infinite x → ¬Infinite (-x) := mt infinite_neg.mp
#align hyperreal.not_infinite_neg Hyperreal.not_infinite_neg

theorem not_infinite_add {x y : ℝ*} (hx : ¬Infinite x) (hy : ¬Infinite y) : ¬Infinite (x + y) :=
  have ⟨r, hr⟩ := exists_st_of_not_infinite hx
  have ⟨s, hs⟩ := exists_st_of_not_infinite hy
  not_infinite_of_exists_st <| ⟨r + s, hr.add hs⟩
#align hyperreal.not_infinite_add Hyperreal.not_infinite_add

theorem not_infinite_iff_exist_lt_gt {x : ℝ*} : ¬Infinite x ↔ ∃ r s : ℝ, (r : ℝ*) < x ∧ x < s :=
  ⟨fun hni ↦ let ⟨r, hr⟩ := exists_st_of_not_infinite hni; ⟨r - 1, r + 1, hr 1 one_pos⟩,
    fun ⟨r, s, hr, hs⟩ hi ↦ hi.elim (fun hp ↦ (hp s).not_lt hs) (fun hn ↦ (hn r).not_lt hr)⟩
#align hyperreal.not_infinite_iff_exist_lt_gt Hyperreal.not_infinite_iff_exist_lt_gt

theorem not_infinite_real (r : ℝ) : ¬Infinite r := by
  rw [not_infinite_iff_exist_lt_gt]
  exact ⟨r - 1, r + 1, coe_lt_coe.2 <| sub_one_lt r, coe_lt_coe.2 <| lt_add_one r⟩
#align hyperreal.not_infinite_real Hyperreal.not_infinite_real

theorem Infinite.ne_real {x : ℝ*} : Infinite x → ∀ r : ℝ, x ≠ r := fun hi r hr =>
  not_infinite_real r <| @Eq.subst _ Infinite _ _ hr hi
#align hyperreal.not_real_of_infinite Hyperreal.Infinite.ne_real

/-!
### Facts about `st` that require some infinite machinery
-/

theorem IsSt.mul {x y : ℝ*} {r s : ℝ} (hxr : IsSt x r) (hys : IsSt y s) : IsSt (x * y) (r * s) :=
  hxr.map₂ hys continuous_mul.continuousAt
#align hyperreal.is_st_mul Hyperreal.IsSt.mul

--AN INFINITE LEMMA THAT REQUIRES SOME MORE ST MACHINERY
theorem not_infinite_mul {x y : ℝ*} (hx : ¬Infinite x) (hy : ¬Infinite y) : ¬Infinite (x * y) :=
  have ⟨_r, hr⟩ := exists_st_of_not_infinite hx
  have ⟨_s, hs⟩ := exists_st_of_not_infinite hy
  (hr.mul hs).not_infinite
#align hyperreal.not_infinite_mul Hyperreal.not_infinite_mul

---
theorem st_add {x y : ℝ*} (hx : ¬Infinite x) (hy : ¬Infinite y) : st (x + y) = st x + st y :=
  (isSt_st' (not_infinite_add hx hy)).unique ((isSt_st' hx).add (isSt_st' hy))
#align hyperreal.st_add Hyperreal.st_add

theorem st_neg (x : ℝ*) : st (-x) = -st x :=
  if h : Infinite x then by
    rw [h.st_eq, (infinite_neg.2 h).st_eq, neg_zero]
  else (isSt_st' (not_infinite_neg h)).unique (isSt_st' h).neg
#align hyperreal.st_neg Hyperreal.st_neg

theorem st_mul {x y : ℝ*} (hx : ¬Infinite x) (hy : ¬Infinite y) : st (x * y) = st x * st y :=
  have hx' := isSt_st' hx
  have hy' := isSt_st' hy
  have hxy := isSt_st' (not_infinite_mul hx hy)
  hxy.unique (hx'.mul hy')
#align hyperreal.st_mul Hyperreal.st_mul

/-!
### Basic lemmas about infinitesimal
-/

theorem infinitesimal_def {x : ℝ*} : Infinitesimal x ↔ ∀ r : ℝ, 0 < r → -(r : ℝ*) < x ∧ x < r := by
  simp [Infinitesimal, IsSt]
#align hyperreal.infinitesimal_def Hyperreal.infinitesimal_def

theorem lt_of_pos_of_infinitesimal {x : ℝ*} : Infinitesimal x → ∀ r : ℝ, 0 < r → x < r :=
  fun hi r hr => ((infinitesimal_def.mp hi) r hr).2
#align hyperreal.lt_of_pos_of_infinitesimal Hyperreal.lt_of_pos_of_infinitesimal

theorem lt_neg_of_pos_of_infinitesimal {x : ℝ*} : Infinitesimal x → ∀ r : ℝ, 0 < r → -↑r < x :=
  fun hi r hr => ((infinitesimal_def.mp hi) r hr).1
#align hyperreal.lt_neg_of_pos_of_infinitesimal Hyperreal.lt_neg_of_pos_of_infinitesimal

theorem gt_of_neg_of_infinitesimal {x : ℝ*} (hi : Infinitesimal x) (r : ℝ) (hr : r < 0) : ↑r < x :=
  neg_neg r ▸ (infinitesimal_def.1 hi (-r) (neg_pos.2 hr)).1
#align hyperreal.gt_of_neg_of_infinitesimal Hyperreal.gt_of_neg_of_infinitesimal

theorem abs_lt_real_iff_infinitesimal {x : ℝ*} : Infinitesimal x ↔ ∀ r : ℝ, r ≠ 0 → |x| < |↑r| :=
  ⟨fun hi r hr ↦ abs_lt.mpr (coe_abs r ▸ infinitesimal_def.mp hi |r| (abs_pos.2 hr)), fun hR ↦
    infinitesimal_def.mpr fun r hr => abs_lt.mp <| (abs_of_pos <| coe_pos.2 hr) ▸ hR r <| hr.ne'⟩
#align hyperreal.abs_lt_real_iff_infinitesimal Hyperreal.abs_lt_real_iff_infinitesimal

theorem infinitesimal_zero : Infinitesimal 0 := isSt_refl_real 0
#align hyperreal.infinitesimal_zero Hyperreal.infinitesimal_zero

theorem Infinitesimal.eq_zero {r : ℝ} : Infinitesimal r → r = 0 := eq_of_isSt_real
#align hyperreal.zero_of_infinitesimal_real Hyperreal.Infinitesimal.eq_zero

-- Porting note: swapped LHS with RHS; added `@[simp]`
@[simp] theorem infinitesimal_real_iff {r : ℝ} : Infinitesimal r ↔ r = 0 :=
  isSt_real_iff_eq
#align hyperreal.zero_iff_infinitesimal_real Hyperreal.infinitesimal_real_iff

nonrec theorem Infinitesimal.add {x y : ℝ*} (hx : Infinitesimal x) (hy : Infinitesimal y) :
    Infinitesimal (x + y) := by simpa only [add_zero] using hx.add hy
#align hyperreal.infinitesimal_add Hyperreal.Infinitesimal.add

nonrec theorem Infinitesimal.neg {x : ℝ*} (hx : Infinitesimal x) : Infinitesimal (-x) := by
  simpa only [neg_zero] using hx.neg
#align hyperreal.infinitesimal_neg Hyperreal.Infinitesimal.neg

-- Porting note: swapped LHS and RHS, added `@[simp]`
@[simp] theorem infinitesimal_neg {x : ℝ*} : Infinitesimal (-x) ↔ Infinitesimal x :=
  ⟨fun h => neg_neg x ▸ h.neg, Infinitesimal.neg⟩
#align hyperreal.infinitesimal_neg_iff Hyperreal.infinitesimal_negₓ

nonrec theorem Infinitesimal.mul {x y : ℝ*} (hx : Infinitesimal x) (hy : Infinitesimal y) :
    Infinitesimal (x * y) := by simpa only [mul_zero] using hx.mul hy
#align hyperreal.infinitesimal_mul Hyperreal.Infinitesimal.mul

theorem infinitesimal_of_tendsto_zero {f : ℕ → ℝ} (h : Tendsto f atTop (𝓝 0)) :
    Infinitesimal (ofSeq f) :=
  isSt_of_tendsto h
#align hyperreal.infinitesimal_of_tendsto_zero Hyperreal.infinitesimal_of_tendsto_zero

theorem infinitesimal_epsilon : Infinitesimal ε :=
  infinitesimal_of_tendsto_zero tendsto_inverse_atTop_nhds_zero_nat
#align hyperreal.infinitesimal_epsilon Hyperreal.infinitesimal_epsilon

theorem not_real_of_infinitesimal_ne_zero (x : ℝ*) : Infinitesimal x → x ≠ 0 → ∀ r : ℝ, x ≠ r :=
  fun hi hx r hr =>
  hx <| hr.trans <| coe_eq_zero.2 <| IsSt.unique (hr.symm ▸ isSt_refl_real r : IsSt x r) hi
#align hyperreal.not_real_of_infinitesimal_ne_zero Hyperreal.not_real_of_infinitesimal_ne_zero

theorem IsSt.infinitesimal_sub {x : ℝ*} {r : ℝ} (hxr : IsSt x r) : Infinitesimal (x - ↑r) := by
  simpa only [sub_self] using hxr.sub (isSt_refl_real r)
#align hyperreal.infinitesimal_sub_is_st Hyperreal.IsSt.infinitesimal_sub

theorem infinitesimal_sub_st {x : ℝ*} (hx : ¬Infinite x) : Infinitesimal (x - ↑(st x)) :=
  (isSt_st' hx).infinitesimal_sub
#align hyperreal.infinitesimal_sub_st Hyperreal.infinitesimal_sub_st

theorem infinitePos_iff_infinitesimal_inv_pos {x : ℝ*} :
    InfinitePos x ↔ Infinitesimal x⁻¹ ∧ 0 < x⁻¹ :=
  ⟨fun hip =>
    ⟨infinitesimal_def.mpr fun r hr =>
        ⟨lt_trans (coe_lt_coe.2 (neg_neg_of_pos hr)) (inv_pos.2 (hip 0)),
          (inv_lt (coe_lt_coe.2 hr) (hip 0)).mp (by convert hip r⁻¹)⟩,
      inv_pos.2 <| hip 0⟩,
    fun ⟨hi, hp⟩ r =>
    @_root_.by_cases (r = 0) (↑r < x) (fun h => Eq.substr h (inv_pos.mp hp)) fun h =>
      lt_of_le_of_lt (coe_le_coe.2 (le_abs_self r))
        ((inv_lt_inv (inv_pos.mp hp) (coe_lt_coe.2 (abs_pos.2 h))).mp
          ((infinitesimal_def.mp hi) |r|⁻¹ (inv_pos.2 (abs_pos.2 h))).2)⟩
#align hyperreal.infinite_pos_iff_infinitesimal_inv_pos Hyperreal.infinitePos_iff_infinitesimal_inv_pos

theorem infiniteNeg_iff_infinitesimal_inv_neg {x : ℝ*} :
    InfiniteNeg x ↔ Infinitesimal x⁻¹ ∧ x⁻¹ < 0 := by
  rw [← infinitePos_neg, infinitePos_iff_infinitesimal_inv_pos, inv_neg, neg_pos, infinitesimal_neg]
#align hyperreal.infinite_neg_iff_infinitesimal_inv_neg Hyperreal.infiniteNeg_iff_infinitesimal_inv_neg

theorem infinitesimal_inv_of_infinite {x : ℝ*} : Infinite x → Infinitesimal x⁻¹ := fun hi =>
  Or.casesOn hi (fun hip => (infinitePos_iff_infinitesimal_inv_pos.mp hip).1) fun hin =>
    (infiniteNeg_iff_infinitesimal_inv_neg.mp hin).1
#align hyperreal.infinitesimal_inv_of_infinite Hyperreal.infinitesimal_inv_of_infinite

theorem infinite_of_infinitesimal_inv {x : ℝ*} (h0 : x ≠ 0) (hi : Infinitesimal x⁻¹) :
    Infinite x := by
  cases' lt_or_gt_of_ne h0 with hn hp
  · exact Or.inr (infiniteNeg_iff_infinitesimal_inv_neg.mpr ⟨hi, inv_lt_zero.mpr hn⟩)
  · exact Or.inl (infinitePos_iff_infinitesimal_inv_pos.mpr ⟨hi, inv_pos.mpr hp⟩)
#align hyperreal.infinite_of_infinitesimal_inv Hyperreal.infinite_of_infinitesimal_inv

theorem infinite_iff_infinitesimal_inv {x : ℝ*} (h0 : x ≠ 0) : Infinite x ↔ Infinitesimal x⁻¹ :=
  ⟨infinitesimal_inv_of_infinite, infinite_of_infinitesimal_inv h0⟩
#align hyperreal.infinite_iff_infinitesimal_inv Hyperreal.infinite_iff_infinitesimal_inv

theorem infinitesimal_pos_iff_infinitePos_inv {x : ℝ*} :
    InfinitePos x⁻¹ ↔ Infinitesimal x ∧ 0 < x :=
  infinitePos_iff_infinitesimal_inv_pos.trans <| by rw [inv_inv]
#align hyperreal.infinitesimal_pos_iff_infinite_pos_inv Hyperreal.infinitesimal_pos_iff_infinitePos_inv

theorem infinitesimal_neg_iff_infiniteNeg_inv {x : ℝ*} :
    InfiniteNeg x⁻¹ ↔ Infinitesimal x ∧ x < 0 :=
  infiniteNeg_iff_infinitesimal_inv_neg.trans <| by rw [inv_inv]
#align hyperreal.infinitesimal_neg_iff_infinite_neg_inv Hyperreal.infinitesimal_neg_iff_infiniteNeg_inv

theorem infinitesimal_iff_infinite_inv {x : ℝ*} (h : x ≠ 0) : Infinitesimal x ↔ Infinite x⁻¹ :=
  Iff.trans (by rw [inv_inv]) (infinite_iff_infinitesimal_inv (inv_ne_zero h)).symm
#align hyperreal.infinitesimal_iff_infinite_inv Hyperreal.infinitesimal_iff_infinite_inv

/-!
### `Hyperreal.st` stuff that requires infinitesimal machinery
-/

theorem IsSt.inv {x : ℝ*} {r : ℝ} (hi : ¬Infinitesimal x) (hr : IsSt x r) : IsSt x⁻¹ r⁻¹ :=
  hr.map <| continuousAt_inv₀ <| by rintro rfl; exact hi hr
#align hyperreal.is_st_inv Hyperreal.IsSt.inv

theorem st_inv (x : ℝ*) : st x⁻¹ = (st x)⁻¹ := by
  by_cases h0 : x = 0
  · rw [h0, inv_zero, ← coe_zero, st_id_real, inv_zero]
  by_cases h1 : Infinitesimal x
  · rw [((infinitesimal_iff_infinite_inv h0).mp h1).st_eq, h1.st_eq, inv_zero]
  by_cases h2 : Infinite x
  · rw [(infinitesimal_inv_of_infinite h2).st_eq, h2.st_eq, inv_zero]
  exact ((isSt_st' h2).inv h1).st_eq
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
    InfinitePos x → ¬Infinitesimal y → 0 < y → InfinitePos (x * y) := fun hx hy₁ hy₂ r => by
  have hy₁' := not_forall.mp (mt infinitesimal_def.2 hy₁)
  let ⟨r₁, hy₁''⟩ := hy₁'
  have hyr : 0 < r₁ ∧ ↑r₁ ≤ y := by
    rwa [Classical.not_imp, ← abs_lt, not_lt, abs_of_pos hy₂] at hy₁''
  rw [← div_mul_cancel₀ r (ne_of_gt hyr.1), coe_mul]
  exact mul_lt_mul (hx (r / r₁)) hyr.2 (coe_lt_coe.2 hyr.1) (le_of_lt (hx 0))
#align hyperreal.infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos Hyperreal.infinitePos_mul_of_infinitePos_not_infinitesimal_pos

theorem infinitePos_mul_of_not_infinitesimal_pos_infinitePos {x y : ℝ*} :
    ¬Infinitesimal x → 0 < x → InfinitePos y → InfinitePos (x * y) := fun hx hp hy =>
  mul_comm y x ▸ infinitePos_mul_of_infinitePos_not_infinitesimal_pos hy hx hp
#align hyperreal.infinite_pos_mul_of_not_infinitesimal_pos_infinite_pos Hyperreal.infinitePos_mul_of_not_infinitesimal_pos_infinitePos

theorem infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg {x y : ℝ*} :
    InfiniteNeg x → ¬Infinitesimal y → y < 0 → InfinitePos (x * y) := by
  rw [← infinitePos_neg, ← neg_pos, ← neg_mul_neg, ← infinitesimal_neg]
  exact infinitePos_mul_of_infinitePos_not_infinitesimal_pos
#align hyperreal.infinite_pos_mul_of_infinite_neg_not_infinitesimal_neg Hyperreal.infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg

theorem infinitePos_mul_of_not_infinitesimal_neg_infiniteNeg {x y : ℝ*} :
    ¬Infinitesimal x → x < 0 → InfiniteNeg y → InfinitePos (x * y) := fun hx hp hy =>
  mul_comm y x ▸ infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg hy hx hp
#align hyperreal.infinite_pos_mul_of_not_infinitesimal_neg_infinite_neg Hyperreal.infinitePos_mul_of_not_infinitesimal_neg_infiniteNeg

theorem infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg {x y : ℝ*} :
    InfinitePos x → ¬Infinitesimal y → y < 0 → InfiniteNeg (x * y) := by
  rw [← infinitePos_neg, ← neg_pos, neg_mul_eq_mul_neg, ← infinitesimal_neg]
  exact infinitePos_mul_of_infinitePos_not_infinitesimal_pos
#align hyperreal.infinite_neg_mul_of_infinite_pos_not_infinitesimal_neg Hyperreal.infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg

theorem infiniteNeg_mul_of_not_infinitesimal_neg_infinitePos {x y : ℝ*} :
    ¬Infinitesimal x → x < 0 → InfinitePos y → InfiniteNeg (x * y) := fun hx hp hy =>
  mul_comm y x ▸ infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg hy hx hp
#align hyperreal.infinite_neg_mul_of_not_infinitesimal_neg_infinite_pos Hyperreal.infiniteNeg_mul_of_not_infinitesimal_neg_infinitePos

theorem infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos {x y : ℝ*} :
    InfiniteNeg x → ¬Infinitesimal y → 0 < y → InfiniteNeg (x * y) := by
  rw [← infinitePos_neg, ← infinitePos_neg, neg_mul_eq_neg_mul]
  exact infinitePos_mul_of_infinitePos_not_infinitesimal_pos
#align hyperreal.infinite_neg_mul_of_infinite_neg_not_infinitesimal_pos Hyperreal.infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos

theorem infiniteNeg_mul_of_not_infinitesimal_pos_infiniteNeg {x y : ℝ*} :
    ¬Infinitesimal x → 0 < x → InfiniteNeg y → InfiniteNeg (x * y) := fun hx hp hy => by
  rw [mul_comm]; exact infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos hy hx hp
#align hyperreal.infinite_neg_mul_of_not_infinitesimal_pos_infinite_neg Hyperreal.infiniteNeg_mul_of_not_infinitesimal_pos_infiniteNeg

theorem infinitePos_mul_infinitePos {x y : ℝ*} :
    InfinitePos x → InfinitePos y → InfinitePos (x * y) := fun hx hy =>
  infinitePos_mul_of_infinitePos_not_infinitesimal_pos hx hy.not_infinitesimal (hy 0)
#align hyperreal.infinite_pos_mul_infinite_pos Hyperreal.infinitePos_mul_infinitePos

theorem infiniteNeg_mul_infiniteNeg {x y : ℝ*} :
    InfiniteNeg x → InfiniteNeg y → InfinitePos (x * y) := fun hx hy =>
  infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg hx hy.not_infinitesimal (hy 0)
#align hyperreal.infinite_neg_mul_infinite_neg Hyperreal.infiniteNeg_mul_infiniteNeg

theorem infinitePos_mul_infiniteNeg {x y : ℝ*} :
    InfinitePos x → InfiniteNeg y → InfiniteNeg (x * y) := fun hx hy =>
  infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg hx hy.not_infinitesimal (hy 0)
#align hyperreal.infinite_pos_mul_infinite_neg Hyperreal.infinitePos_mul_infiniteNeg

theorem infiniteNeg_mul_infinitePos {x y : ℝ*} :
    InfiniteNeg x → InfinitePos y → InfiniteNeg (x * y) := fun hx hy =>
  infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos hx hy.not_infinitesimal (hy 0)
#align hyperreal.infinite_neg_mul_infinite_pos Hyperreal.infiniteNeg_mul_infinitePos

theorem infinite_mul_of_infinite_not_infinitesimal {x y : ℝ*} :
    Infinite x → ¬Infinitesimal y → Infinite (x * y) := fun hx hy =>
  have h0 : y < 0 ∨ 0 < y := lt_or_gt_of_ne fun H0 => hy (Eq.substr H0 (isSt_refl_real 0))
  hx.elim
    (h0.elim
      (fun H0 Hx => Or.inr (infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg Hx hy H0))
      fun H0 Hx => Or.inl (infinitePos_mul_of_infinitePos_not_infinitesimal_pos Hx hy H0))
    (h0.elim
      (fun H0 Hx => Or.inl (infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg Hx hy H0))
      fun H0 Hx => Or.inr (infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos Hx hy H0))
#align hyperreal.infinite_mul_of_infinite_not_infinitesimal Hyperreal.infinite_mul_of_infinite_not_infinitesimal

theorem infinite_mul_of_not_infinitesimal_infinite {x y : ℝ*} :
    ¬Infinitesimal x → Infinite y → Infinite (x * y) := fun hx hy => by
  rw [mul_comm]; exact infinite_mul_of_infinite_not_infinitesimal hy hx
#align hyperreal.infinite_mul_of_not_infinitesimal_infinite Hyperreal.infinite_mul_of_not_infinitesimal_infinite

theorem Infinite.mul {x y : ℝ*} : Infinite x → Infinite y → Infinite (x * y) := fun hx hy =>
  infinite_mul_of_infinite_not_infinitesimal hx hy.not_infinitesimal
#align hyperreal.infinite.mul Hyperreal.Infinite.mul

end Hyperreal

/-
Porting note (#11215): TODO: restore `positivity` plugin

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
-/
