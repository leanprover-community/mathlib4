/-
Copyright (c) 2019 Abhimanyu Pallavi Sudhir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhimanyu Pallavi Sudhir
-/
module

public import Mathlib.Algebra.Order.Ring.StandardPart
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.Filter.FilterProduct

/-!
# Construction of the hyperreal numbers as an ultraproduct of real sequences.
-/

@[expose] public section

open ArchimedeanClass Filter Germ Topology

/-- Hyperreal numbers on the ultrafilter extending the cofinite filter -/
def Hyperreal : Type :=
  Germ (hyperfilter ℕ : Filter ℕ) ℝ

noncomputable section

#adaptation_note
/-- After nightly-2025-05-07 we had to remove `deriving Inhabited` on `Hyperreal` above,
as there is a new error about this instance having to be noncomputable, and `deriving` doesn't allow
for adding this! -/
namespace Hyperreal

@[inherit_doc] notation "ℝ*" => Hyperreal

instance : Field ℝ* :=
  inferInstanceAs% (Field (Germ _ _))

instance : LinearOrder ℝ* :=
  inferInstanceAs% (LinearOrder (Germ _ _))

instance : IsStrictOrderedRing ℝ* :=
  inferInstanceAs% (IsStrictOrderedRing (Germ _ _))

/-- Natural embedding `ℝ → ℝ*`. -/
@[coe] def ofReal : ℝ → ℝ* := const

instance : CoeTC ℝ ℝ* := ⟨ofReal⟩

@[simp, norm_cast]
theorem coe_eq_coe {x y : ℝ} : (x : ℝ*) = y ↔ x = y :=
  Germ.const_inj

theorem coe_ne_coe {x y : ℝ} : (x : ℝ*) ≠ y ↔ x ≠ y :=
  coe_eq_coe.not

@[simp, norm_cast]
theorem coe_eq_zero {x : ℝ} : (x : ℝ*) = 0 ↔ x = 0 :=
  coe_eq_coe

@[simp, norm_cast]
theorem coe_eq_one {x : ℝ} : (x : ℝ*) = 1 ↔ x = 1 :=
  coe_eq_coe

@[norm_cast]
theorem coe_ne_zero {x : ℝ} : (x : ℝ*) ≠ 0 ↔ x ≠ 0 :=
  coe_ne_coe

@[norm_cast]
theorem coe_ne_one {x : ℝ} : (x : ℝ*) ≠ 1 ↔ x ≠ 1 :=
  coe_ne_coe

@[simp, norm_cast]
theorem coe_one : ↑(1 : ℝ) = (1 : ℝ*) :=
  rfl

@[simp, norm_cast]
theorem coe_zero : ↑(0 : ℝ) = (0 : ℝ*) :=
  rfl

@[simp, norm_cast]
theorem coe_inv (x : ℝ) : ↑x⁻¹ = (x⁻¹ : ℝ*) :=
  rfl

@[simp, norm_cast]
theorem coe_neg (x : ℝ) : ↑(-x) = (-x : ℝ*) :=
  rfl

@[simp, norm_cast]
theorem coe_add (x y : ℝ) : ↑(x + y) = (x + y : ℝ*) :=
  rfl

@[simp, norm_cast]
theorem coe_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((ofNat(n) : ℝ) : ℝ*) = OfNat.ofNat n :=
  rfl

@[simp, norm_cast]
theorem coe_mul (x y : ℝ) : ↑(x * y) = (x * y : ℝ*) :=
  rfl

@[simp, norm_cast]
theorem coe_div (x y : ℝ) : ↑(x / y) = (x / y : ℝ*) :=
  rfl

@[simp, norm_cast]
theorem coe_sub (x y : ℝ) : ↑(x - y) = (x - y : ℝ*) :=
  rfl

@[simp, norm_cast]
theorem coe_le_coe {x y : ℝ} : (x : ℝ*) ≤ y ↔ x ≤ y :=
  Germ.const_le_iff

@[simp, norm_cast]
theorem coe_lt_coe {x y : ℝ} : (x : ℝ*) < y ↔ x < y :=
  Germ.const_lt_iff

@[simp, norm_cast]
theorem coe_nonneg {x : ℝ} : 0 ≤ (x : ℝ*) ↔ 0 ≤ x :=
  coe_le_coe

@[simp, norm_cast]
theorem coe_pos {x : ℝ} : 0 < (x : ℝ*) ↔ 0 < x :=
  coe_lt_coe

@[simp, norm_cast]
theorem coe_abs (x : ℝ) : ((|x| : ℝ) : ℝ*) = |↑x| :=
  const_abs x

@[simp, norm_cast]
theorem coe_max (x y : ℝ) : ((max x y : ℝ) : ℝ*) = max ↑x ↑y :=
  Germ.const_max _ _

@[simp, norm_cast]
theorem coe_min (x y : ℝ) : ((min x y : ℝ) : ℝ*) = min ↑x ↑y :=
  Germ.const_min _ _

/-- The canonical map `ℝ → ℝ*` as an `OrderRingHom`. -/
@[simps]
def coeRingHom : ℝ →+*o ℝ* where
  toFun x := x
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  monotone' _ _ := coe_le_coe.2

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem archimedeanClassMk_coe_nonneg (x : ℝ) : 0 ≤ mk (x : ℝ*) :=
  mk_map_nonneg_of_archimedean coeRingHom x

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem archimdeanClassMk_coe {x : ℝ} (hx : x ≠ 0) : mk (x : ℝ*) = 0 :=
  mk_map_of_archimedean' coeRingHom hx

@[simp]
theorem stdPart_coe (x : ℝ) : stdPart (x : ℝ*) = x :=
  stdPart_map_real coeRingHom x

/-! ### Basic constants -/

/-- Construct a hyperreal number from a sequence of real numbers. -/
def ofSeq (f : ℕ → ℝ) : ℝ* := (↑f : Germ (hyperfilter ℕ : Filter ℕ) ℝ)

theorem ofSeq_surjective : Function.Surjective ofSeq := Quot.exists_rep

theorem ofSeq_lt_ofSeq {f g : ℕ → ℝ} : ofSeq f < ofSeq g ↔ ∀ᶠ n in hyperfilter ℕ, f n < g n :=
  Germ.coe_lt

theorem ofSeq_le_ofSeq {f g : ℕ → ℝ} : ofSeq f ≤ ofSeq g ↔ ∀ᶠ n in hyperfilter ℕ, f n ≤ g n :=
  Germ.coe_le

/-! #### ω -/

/-- A sample infinite hyperreal ω = ⟦(0, 1, 2, 3, ⋯)⟧. -/
def omega : ℝ* := ofSeq Nat.cast

@[inherit_doc] scoped notation "ω" => Hyperreal.omega
recommended_spelling "omega" for "ω" in [omega, «termω»]

theorem coe_lt_omega (r : ℝ) : r < ω := by
  apply ofSeq_lt_ofSeq.2 <| Filter.Eventually.filter_mono Nat.hyperfilter_le_atTop _
  obtain ⟨n, hn⟩ := exists_nat_gt r
  rw [eventually_atTop]
  exact ⟨n, fun m hm ↦ hn.trans_le (mod_cast hm)⟩

theorem omega_pos : 0 < ω :=
  coe_lt_omega 0

@[simp]
theorem omega_ne_zero : ω ≠ 0 :=
  omega_pos.ne'

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem abs_omega : |ω| = ω :=
  abs_of_pos omega_pos

set_option backward.isDefEq.respectTransparency false in
theorem archimedeanClassMk_omega_neg : mk ω < 0 :=
  fun n ↦ by simpa using coe_lt_omega n

@[simp]
theorem stdPart_omega : stdPart ω = 0 := by
  rw [stdPart_eq_zero]
  exact archimedeanClassMk_omega_neg.ne

/-! #### ε -/

/-- A sample infinitesimal hyperreal ε = ⟦(0, 1, 1/2, 1/3, ⋯)⟧. -/
def epsilon : ℝ* :=
  ofSeq fun n => n⁻¹

@[inherit_doc] scoped notation "ε" => Hyperreal.epsilon
recommended_spelling "epsilon" for "ε" in [epsilon, «termε»]

@[simp]
theorem inv_omega : ω⁻¹ = ε :=
  rfl

@[simp]
theorem inv_epsilon : ε⁻¹ = ω :=
  @inv_inv _ _ ω

@[simp]
theorem epsilon_pos : 0 < ε :=
  inv_pos_of_pos omega_pos

@[simp]
theorem epsilon_ne_zero : ε ≠ 0 :=
  epsilon_pos.ne'

@[simp]
theorem epsilon_mul_omega : ε * ω = 1 :=
  @inv_mul_cancel₀ _ _ ω omega_ne_zero

set_option backward.isDefEq.respectTransparency false in
theorem archimedeanClassMk_epsilon_pos : 0 < mk ε := by
  simpa [← inv_omega] using archimedeanClassMk_omega_neg

/-!
### Some facts about `Tendsto`
-/

@[simp]
theorem tendsto_ofSeq {f : ℕ → ℝ} {lb : Filter ℝ} :
    (ofSeq f).Tendsto lb ↔ Tendsto f (hyperfilter ℕ) lb :=
  .rfl

theorem tendsto_iff_forall {x : ℝ*} {r : ℝ} :
    x.Tendsto (𝓝 r) ↔ (∀ s < r, s ≤ x) ∧ (∀ s > r, x ≤ s) := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rw [tendsto_ofSeq, (nhds_basis_Ioo _).tendsto_right_iff]
  simp_rw [Set.mem_Ioo, eventually_and, ← ofSeq_lt_ofSeq]
  refine ⟨fun H ↦ ⟨fun s hs ↦ ?_, fun s hs ↦ ?_⟩, fun H ⟨s, t⟩ ⟨hs, ht⟩ ↦ ⟨?_, ?_⟩⟩
  · obtain ⟨t, ht⟩ := exists_gt r
    exact (H ⟨s, t⟩ ⟨hs, ht⟩).1.le
  · obtain ⟨t, ht⟩ := exists_lt r
    exact (H ⟨t, s⟩ ⟨ht, hs⟩).2.le
  · obtain ⟨u, hu, hu'⟩ := exists_between hs
    exact (coe_lt_coe.2 hu).trans_le (H.1 _ hu')
  · obtain ⟨u, hu, hu'⟩ := exists_between ht
    exact (H.2 _ hu).trans_lt (coe_lt_coe.2 hu')

set_option backward.isDefEq.respectTransparency false in
theorem archimedeanClassMk_nonneg_of_tendsto {x : ℝ*} {r : ℝ} (hx : x.Tendsto (𝓝 r)) :
    0 ≤ mk x := by
  rw [tendsto_iff_forall] at hx
  obtain ⟨s, hs⟩ := exists_lt r
  obtain ⟨t, ht⟩ := exists_gt r
  exact mk_nonneg_of_le_of_le_of_archimedean coeRingHom (hx.1 s hs) (hx.2 t ht)

theorem stdPart_of_tendsto {x : ℝ*} {r : ℝ} (hx : x.Tendsto (𝓝 r)) : stdPart x = r := by
  rw [tendsto_iff_forall] at hx
  exact stdPart_eq coeRingHom hx.1 hx.2

set_option backward.isDefEq.respectTransparency false in
theorem archimedeanClassMk_pos_of_tendsto {x : ℝ*} (hx : x.Tendsto (𝓝 0)) : 0 < mk x := by
  apply (archimedeanClassMk_nonneg_of_tendsto hx).lt_of_ne'
  rw [← stdPart_eq_zero, stdPart_of_tendsto hx]

@[simp]
theorem stdPart_epsilon : stdPart ε = 0 :=
  stdPart_eq_zero.2 <| archimedeanClassMk_epsilon_pos.ne'

theorem epsilon_lt_of_pos {r : ℝ} : 0 < r → ε < r :=
  lt_of_pos_of_archimedean coeRingHom archimedeanClassMk_epsilon_pos

theorem epsilon_lt_of_neg {r : ℝ} : r < 0 → r < ε :=
  lt_of_neg_of_archimedean coeRingHom archimedeanClassMk_epsilon_pos

@[deprecated (since := "2026-01-05")]
alias epsilon_lt_pos := epsilon_lt_of_pos

@[deprecated archimedeanClassMk_pos_of_tendsto (since := "2026-01-05")]
theorem lt_of_tendsto_zero_of_pos {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0)) :
    ∀ {r : ℝ}, 0 < r → ofSeq f < (r : ℝ*) := fun hr ↦
  ofSeq_lt_ofSeq.2 <| (hf.eventually <| gt_mem_nhds hr).filter_mono Nat.hyperfilter_le_atTop

set_option backward.isDefEq.respectTransparency false in
set_option linter.deprecated false in
@[deprecated archimedeanClassMk_pos_of_tendsto (since := "2026-01-05")]
theorem neg_lt_of_tendsto_zero_of_pos {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0)) :
    ∀ {r : ℝ}, 0 < r → (-r : ℝ*) < ofSeq f := fun hr =>
  have hg := hf.neg
  neg_lt_of_neg_lt (by rw [neg_zero] at hg; exact lt_of_tendsto_zero_of_pos hg hr)

set_option linter.deprecated false in
@[deprecated archimedeanClassMk_pos_of_tendsto (since := "2026-01-05")]
theorem gt_of_tendsto_zero_of_neg {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0)) :
    ∀ {r : ℝ}, r < 0 → (r : ℝ*) < ofSeq f := fun {r} hr => by
  rw [← neg_neg r, coe_neg]; exact neg_lt_of_tendsto_zero_of_pos hf (neg_pos.mpr hr)

theorem lt_of_tendsto_atTop {x : ℝ*} (r : ℝ) (hx : x.Tendsto atTop) : r < x := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rw [tendsto_ofSeq] at hx
  exact ofSeq_lt_ofSeq.2 <| hx.eventually_mem (Ioi_mem_atTop r)

theorem lt_of_tendsto_atBot {x : ℝ*} (r : ℝ) (hx : x.Tendsto atBot) : x < r := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rw [tendsto_ofSeq] at hx
  exact ofSeq_lt_ofSeq.2 <| hx.eventually_mem (Iio_mem_atBot r)

set_option backward.isDefEq.respectTransparency false in
theorem archimedeanClassMk_neg_of_tendsto_atTop {x : ℝ*} (hx : x.Tendsto atTop) : mk x < 0 := by
  have : 0 < x := lt_of_tendsto_atTop 0 hx
  intro n
  simpa [abs_of_pos this] using lt_of_tendsto_atTop n hx

set_option backward.isDefEq.respectTransparency false in
theorem archimedeanClassMk_neg_of_tendsto_atBot {x : ℝ*} (hx : x.Tendsto atBot) : mk x < 0 := by
  have : x < 0 := lt_of_tendsto_atBot 0 hx
  intro n
  simpa [abs_of_neg this, lt_neg] using lt_of_tendsto_atBot (-n) hx

set_option backward.isDefEq.respectTransparency false in
theorem tendsto_atTop_iff {x : ℝ*} : x.Tendsto atTop ↔ 0 < x ∧ mk x < 0 where
  mp h := ⟨lt_of_tendsto_atTop 0 h, archimedeanClassMk_neg_of_tendsto_atTop h⟩
  mpr h := by
    rcases ofSeq_surjective x with ⟨f, rfl⟩
    rw [tendsto_ofSeq, tendsto_atTop]
    exact fun r ↦ ofSeq_le_ofSeq.1 <|
      (lt_of_mk_lt_mk_of_nonneg (h.2.trans_le <| archimedeanClassMk_coe_nonneg r) h.1.le).le

set_option backward.isDefEq.respectTransparency false in
theorem tendsto_atBot_iff {x : ℝ*} : x.Tendsto atBot ↔ x < 0 ∧ mk x < 0 where
  mp h := ⟨lt_of_tendsto_atBot 0 h, archimedeanClassMk_neg_of_tendsto_atBot h⟩
  mpr h := by
    rcases ofSeq_surjective x with ⟨f, rfl⟩
    rw [tendsto_ofSeq, tendsto_atBot]
    exact fun r ↦ ofSeq_le_ofSeq.1 <|
      (lt_of_mk_lt_mk_of_nonpos (h.2.trans_le <| archimedeanClassMk_coe_nonneg r) h.1.le).le

/-!
### Some facts about standard parts
-/

/-- Standard part predicate -/
def IsSt (x : ℝ*) (r : ℝ) :=
  ∀ δ : ℝ, 0 < δ → (r - δ : ℝ*) < x ∧ x < r + δ

open scoped Classical in
/-- Standard part function: like a "round" to ℝ instead of ℤ -/
def st : ℝ* → ℝ := fun x => if h : ∃ r, IsSt x r then Classical.choose h else 0

/-- A hyperreal number is infinitesimal if its standard part is 0 -/
def Infinitesimal (x : ℝ*) :=
  IsSt x 0

/-- A hyperreal number is positive infinite if it is larger than all real numbers -/
def InfinitePos (x : ℝ*) :=
  ∀ r : ℝ, ↑r < x

/-- A hyperreal number is negative infinite if it is smaller than all real numbers -/
def InfiniteNeg (x : ℝ*) :=
  ∀ r : ℝ, x < r

/-- A hyperreal number is infinite if it is infinite positive or infinite negative -/
def Infinite (x : ℝ*) :=
  InfinitePos x ∨ InfiniteNeg x

theorem isSt_ofSeq_iff_tendsto {f : ℕ → ℝ} {r : ℝ} :
    IsSt (ofSeq f) r ↔ Tendsto f (hyperfilter ℕ) (𝓝 r) :=
  Iff.trans (forall₂_congr fun _ _ ↦ (ofSeq_lt_ofSeq.and ofSeq_lt_ofSeq).trans eventually_and.symm)
    (nhds_basis_Ioo_pos _).tendsto_right_iff.symm

theorem isSt_iff_tendsto {x : ℝ*} {r : ℝ} : IsSt x r ↔ x.Tendsto (𝓝 r) := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  exact isSt_ofSeq_iff_tendsto

theorem isSt_of_tendsto {f : ℕ → ℝ} {r : ℝ} (hf : Tendsto f atTop (𝓝 r)) : IsSt (ofSeq f) r :=
  isSt_ofSeq_iff_tendsto.2 <| hf.mono_left Nat.hyperfilter_le_atTop

protected theorem IsSt.lt {x y : ℝ*} {r s : ℝ} (hxr : IsSt x r) (hys : IsSt y s) (hrs : r < s) :
    x < y := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rcases ofSeq_surjective y with ⟨g, rfl⟩
  rw [isSt_ofSeq_iff_tendsto] at hxr hys
  exact ofSeq_lt_ofSeq.2 <| hxr.eventually_lt hys hrs

theorem IsSt.unique {x : ℝ*} {r s : ℝ} (hr : IsSt x r) (hs : IsSt x s) : r = s := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rw [isSt_ofSeq_iff_tendsto] at hr hs
  exact tendsto_nhds_unique hr hs

theorem IsSt.st_eq {x : ℝ*} {r : ℝ} (hxr : IsSt x r) : st x = r := by
  have h : ∃ r, IsSt x r := ⟨r, hxr⟩
  rw [st, dif_pos h]
  exact (Classical.choose_spec h).unique hxr

theorem IsSt.not_infinite {x : ℝ*} {r : ℝ} (h : IsSt x r) : ¬Infinite x := fun hi ↦
  hi.elim (fun hp ↦ lt_asymm (h 1 one_pos).2 (hp (r + 1))) fun hn ↦
    lt_asymm (h 1 one_pos).1 (hn (r - 1))

theorem not_infinite_of_exists_st {x : ℝ*} : (∃ r : ℝ, IsSt x r) → ¬Infinite x := fun ⟨_r, hr⟩ =>
  hr.not_infinite

theorem Infinite.st_eq {x : ℝ*} (hi : Infinite x) : st x = 0 :=
  dif_neg fun ⟨_r, hr⟩ ↦ hr.not_infinite hi

theorem isSt_sSup {x : ℝ*} (hni : ¬Infinite x) : IsSt x (sSup { y : ℝ | (y : ℝ*) < x }) := by
  set S : Set ℝ := { y : ℝ | (y : ℝ*) < x }
  set R : ℝ := sSup S
  have hS₀ : S.Nonempty := by
    obtain ⟨r₁, hr₁⟩ := not_forall.mp (not_or.mp hni).2
    exact ⟨r₁ - 1, (coe_lt_coe.2 <| sub_one_lt _).trans_le (not_lt.mp hr₁)⟩
  have hS : BddAbove S := by
    obtain ⟨r₂, hr₂⟩ := not_forall.mp (not_or.mp hni).1
    exact ⟨r₂, fun _y hy => coe_le_coe.1 <| hy.le.trans <| not_lt.mp hr₂⟩
  intro δ hδ
  constructor <;> refine lt_of_not_ge fun hx => ?_
  · exact (sub_lt_self R hδ).not_ge <| csSup_le hS₀ fun _y hy => coe_le_coe.1 <| hy.le.trans hx
  · replace hx : ↑(R + δ / 2) < x := by grw [← hx]; norm_cast; linarith
    exact (le_csSup hS hx).not_gt <| by simpa [R]

theorem exists_st_of_not_infinite {x : ℝ*} (hni : ¬Infinite x) : ∃ r : ℝ, IsSt x r :=
  ⟨sSup { y : ℝ | (y : ℝ*) < x }, isSt_sSup hni⟩

theorem st_eq_sSup {x : ℝ*} : st x = sSup { y : ℝ | (y : ℝ*) < x } := by
  rcases _root_.em (Infinite x) with (hx | hx)
  · rw [hx.st_eq]
    cases hx with
    | inl hx =>
      convert Real.sSup_univ.symm
      exact Set.eq_univ_of_forall hx
    | inr hx =>
      convert Real.sSup_empty.symm
      exact Set.eq_empty_of_forall_notMem fun y hy ↦ hy.out.not_gt (hx _)
  · exact (isSt_sSup hx).st_eq

theorem exists_st_iff_not_infinite {x : ℝ*} : (∃ r : ℝ, IsSt x r) ↔ ¬Infinite x :=
  ⟨not_infinite_of_exists_st, exists_st_of_not_infinite⟩

theorem infinite_iff_not_exists_st {x : ℝ*} : Infinite x ↔ ¬∃ r : ℝ, IsSt x r :=
  iff_not_comm.mp exists_st_iff_not_infinite

theorem IsSt.isSt_st {x : ℝ*} {r : ℝ} (hxr : IsSt x r) : IsSt x (st x) := by
  rwa [hxr.st_eq]

theorem isSt_st_of_exists_st {x : ℝ*} (hx : ∃ r : ℝ, IsSt x r) : IsSt x (st x) :=
  let ⟨_r, hr⟩ := hx; hr.isSt_st

theorem isSt_st' {x : ℝ*} (hx : ¬Infinite x) : IsSt x (st x) :=
  (isSt_sSup hx).isSt_st

theorem isSt_st {x : ℝ*} (hx : st x ≠ 0) : IsSt x (st x) :=
  isSt_st' <| mt Infinite.st_eq hx

theorem isSt_refl_real (r : ℝ) : IsSt r r := isSt_ofSeq_iff_tendsto.2 tendsto_const_nhds

theorem st_id_real (r : ℝ) : st r = r := (isSt_refl_real r).st_eq

theorem eq_of_isSt_real {r s : ℝ} : IsSt r s → r = s :=
  (isSt_refl_real r).unique

theorem isSt_real_iff_eq {r s : ℝ} : IsSt r s ↔ r = s :=
  ⟨eq_of_isSt_real, fun hrs => hrs ▸ isSt_refl_real r⟩

theorem isSt_symm_real {r s : ℝ} : IsSt r s ↔ IsSt s r := by
  rw [isSt_real_iff_eq, isSt_real_iff_eq, eq_comm]

theorem isSt_trans_real {r s t : ℝ} : IsSt r s → IsSt s t → IsSt r t := by
  rw [isSt_real_iff_eq, isSt_real_iff_eq, isSt_real_iff_eq]; exact Eq.trans

theorem isSt_inj_real {r₁ r₂ s : ℝ} (h1 : IsSt r₁ s) (h2 : IsSt r₂ s) : r₁ = r₂ :=
  Eq.trans (eq_of_isSt_real h1) (eq_of_isSt_real h2).symm

set_option backward.isDefEq.respectTransparency false in
theorem isSt_iff_abs_sub_lt_delta {x : ℝ*} {r : ℝ} : IsSt x r ↔ ∀ δ : ℝ, 0 < δ → |x - ↑r| < δ := by
  simp only [abs_sub_lt_iff, sub_lt_iff_lt_add, IsSt, and_comm, add_comm]

theorem IsSt.map {x : ℝ*} {r : ℝ} (hxr : IsSt x r) {f : ℝ → ℝ} (hf : ContinuousAt f r) :
    IsSt (x.map f) (f r) := by
  rcases ofSeq_surjective x with ⟨g, rfl⟩
  exact isSt_ofSeq_iff_tendsto.2 <| hf.tendsto.comp (isSt_ofSeq_iff_tendsto.1 hxr)

theorem IsSt.map₂ {x y : ℝ*} {r s : ℝ} (hxr : IsSt x r) (hys : IsSt y s) {f : ℝ → ℝ → ℝ}
    (hf : ContinuousAt (Function.uncurry f) (r, s)) : IsSt (x.map₂ f y) (f r s) := by
  rcases ofSeq_surjective x with ⟨x, rfl⟩
  rcases ofSeq_surjective y with ⟨y, rfl⟩
  rw [isSt_ofSeq_iff_tendsto] at hxr hys
  exact isSt_ofSeq_iff_tendsto.2 <| hf.tendsto.comp (hxr.prodMk_nhds hys)

theorem IsSt.add {x y : ℝ*} {r s : ℝ} (hxr : IsSt x r) (hys : IsSt y s) :
    IsSt (x + y) (r + s) := hxr.map₂ hys continuous_add.continuousAt

theorem IsSt.neg {x : ℝ*} {r : ℝ} (hxr : IsSt x r) : IsSt (-x) (-r) :=
  hxr.map continuous_neg.continuousAt

theorem IsSt.sub {x y : ℝ*} {r s : ℝ} (hxr : IsSt x r) (hys : IsSt y s) : IsSt (x - y) (r - s) :=
  hxr.map₂ hys continuous_sub.continuousAt

theorem IsSt.le {x y : ℝ*} {r s : ℝ} (hrx : IsSt x r) (hsy : IsSt y s) (hxy : x ≤ y) : r ≤ s :=
  not_lt.1 fun h ↦ hxy.not_gt <| hsy.lt hrx h

theorem st_le_of_le {x y : ℝ*} (hix : ¬Infinite x) (hiy : ¬Infinite y) : x ≤ y → st x ≤ st y :=
  (isSt_st' hix).le (isSt_st' hiy)

theorem lt_of_st_lt {x y : ℝ*} (hix : ¬Infinite x) (hiy : ¬Infinite y) : st x < st y → x < y :=
  (isSt_st' hix).lt (isSt_st' hiy)

/-!
### Basic lemmas about infinite
-/

theorem infinitePos_def {x : ℝ*} : InfinitePos x ↔ ∀ r : ℝ, ↑r < x := Iff.rfl

theorem infiniteNeg_def {x : ℝ*} : InfiniteNeg x ↔ ∀ r : ℝ, x < r := Iff.rfl

theorem InfinitePos.pos {x : ℝ*} (hip : InfinitePos x) : 0 < x := hip 0

theorem InfiniteNeg.lt_zero {x : ℝ*} : InfiniteNeg x → x < 0 := fun hin => hin 0

theorem Infinite.ne_zero {x : ℝ*} (hI : Infinite x) : x ≠ 0 :=
  hI.elim (fun hip => hip.pos.ne') fun hin => hin.lt_zero.ne

theorem not_infinite_zero : ¬Infinite 0 := fun hI => hI.ne_zero rfl

theorem InfiniteNeg.not_infinitePos {x : ℝ*} : InfiniteNeg x → ¬InfinitePos x := fun hn hp =>
  (hn 0).not_gt (hp 0)

theorem InfinitePos.not_infiniteNeg {x : ℝ*} (hp : InfinitePos x) : ¬InfiniteNeg x := fun hn ↦
  hn.not_infinitePos hp

set_option backward.isDefEq.respectTransparency false in
theorem InfinitePos.neg {x : ℝ*} : InfinitePos x → InfiniteNeg (-x) := fun hp r =>
  neg_lt.mp (hp (-r))

set_option backward.isDefEq.respectTransparency false in
theorem InfiniteNeg.neg {x : ℝ*} : InfiniteNeg x → InfinitePos (-x) := fun hp r =>
  lt_neg.mp (hp (-r))

@[simp] theorem infiniteNeg_neg {x : ℝ*} : InfiniteNeg (-x) ↔ InfinitePos x :=
  ⟨fun hin => neg_neg x ▸ hin.neg, InfinitePos.neg⟩

@[simp] theorem infinitePos_neg {x : ℝ*} : InfinitePos (-x) ↔ InfiniteNeg x :=
  ⟨fun hin => neg_neg x ▸ hin.neg, InfiniteNeg.neg⟩

@[simp] theorem infinite_neg {x : ℝ*} : Infinite (-x) ↔ Infinite x :=
  or_comm.trans <| infiniteNeg_neg.or infinitePos_neg

nonrec theorem Infinitesimal.not_infinite {x : ℝ*} (h : Infinitesimal x) : ¬Infinite x :=
  h.not_infinite

theorem Infinite.not_infinitesimal {x : ℝ*} (h : Infinite x) : ¬Infinitesimal x := fun h' ↦
  h'.not_infinite h

theorem InfinitePos.not_infinitesimal {x : ℝ*} (h : InfinitePos x) : ¬Infinitesimal x :=
  Infinite.not_infinitesimal (Or.inl h)

theorem InfiniteNeg.not_infinitesimal {x : ℝ*} (h : InfiniteNeg x) : ¬Infinitesimal x :=
  Infinite.not_infinitesimal (Or.inr h)

theorem infinitePos_iff_infinite_and_pos {x : ℝ*} : InfinitePos x ↔ Infinite x ∧ 0 < x :=
  ⟨fun hip => ⟨Or.inl hip, hip 0⟩, fun ⟨hi, hp⟩ =>
    hi.casesOn id fun hin => False.elim (not_lt_of_gt hp (hin 0))⟩

theorem infiniteNeg_iff_infinite_and_neg {x : ℝ*} : InfiniteNeg x ↔ Infinite x ∧ x < 0 :=
  ⟨fun hip => ⟨Or.inr hip, hip 0⟩, fun ⟨hi, hp⟩ =>
    hi.casesOn (fun hin => False.elim (not_lt_of_gt hp (hin 0))) fun hip => hip⟩

theorem infinitePos_iff_infinite_of_nonneg {x : ℝ*} (hp : 0 ≤ x) : InfinitePos x ↔ Infinite x :=
  .symm <| or_iff_left fun h ↦ h.lt_zero.not_ge hp

theorem infinitePos_iff_infinite_of_pos {x : ℝ*} (hp : 0 < x) : InfinitePos x ↔ Infinite x :=
  infinitePos_iff_infinite_of_nonneg hp.le

theorem infiniteNeg_iff_infinite_of_neg {x : ℝ*} (hn : x < 0) : InfiniteNeg x ↔ Infinite x :=
  .symm <| or_iff_right fun h ↦ h.pos.not_gt hn

set_option backward.isDefEq.respectTransparency false in
theorem infinitePos_abs_iff_infinite_abs {x : ℝ*} : InfinitePos |x| ↔ Infinite |x| :=
  infinitePos_iff_infinite_of_nonneg (abs_nonneg _)

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem infinite_abs_iff {x : ℝ*} : Infinite |x| ↔ Infinite x := by
  cases le_total 0 x <;> simp [*, abs_of_nonneg, abs_of_nonpos, infinite_neg]

@[simp] theorem infinitePos_abs_iff_infinite {x : ℝ*} : InfinitePos |x| ↔ Infinite x :=
  infinitePos_abs_iff_infinite_abs.trans infinite_abs_iff

theorem infinite_iff_abs_lt_abs {x : ℝ*} : Infinite x ↔ ∀ r : ℝ, (|r| : ℝ*) < |x| :=
  infinitePos_abs_iff_infinite.symm.trans ⟨fun hI r => coe_abs r ▸ hI |r|, fun hR r =>
    (le_abs_self _).trans_lt (hR r)⟩

set_option backward.isDefEq.respectTransparency false in
theorem infinitePos_add_not_infiniteNeg {x y : ℝ*} :
    InfinitePos x → ¬InfiniteNeg y → InfinitePos (x + y) := by
  intro hip hnin r
  obtain ⟨r₂, hr₂⟩ := not_forall.mp hnin
  convert add_lt_add_of_lt_of_le (hip (r + -r₂)) (not_lt.mp hr₂) using 1
  simp

theorem not_infiniteNeg_add_infinitePos {x y : ℝ*} :
    ¬InfiniteNeg x → InfinitePos y → InfinitePos (x + y) := fun hx hy =>
  add_comm y x ▸ infinitePos_add_not_infiniteNeg hy hx

theorem infiniteNeg_add_not_infinitePos {x y : ℝ*} :
    InfiniteNeg x → ¬InfinitePos y → InfiniteNeg (x + y) := by
  rw [← infinitePos_neg, ← infinitePos_neg, ← @infiniteNeg_neg y, neg_add]
  exact infinitePos_add_not_infiniteNeg

theorem not_infinitePos_add_infiniteNeg {x y : ℝ*} :
    ¬InfinitePos x → InfiniteNeg y → InfiniteNeg (x + y) := fun hx hy =>
  add_comm y x ▸ infiniteNeg_add_not_infinitePos hy hx

theorem infinitePos_add_infinitePos {x y : ℝ*} :
    InfinitePos x → InfinitePos y → InfinitePos (x + y) := fun hx hy =>
  infinitePos_add_not_infiniteNeg hx hy.not_infiniteNeg

theorem infiniteNeg_add_infiniteNeg {x y : ℝ*} :
    InfiniteNeg x → InfiniteNeg y → InfiniteNeg (x + y) := fun hx hy =>
  infiniteNeg_add_not_infinitePos hx hy.not_infinitePos

theorem infinitePos_add_not_infinite {x y : ℝ*} :
    InfinitePos x → ¬Infinite y → InfinitePos (x + y) := fun hx hy =>
  infinitePos_add_not_infiniteNeg hx (not_or.mp hy).2

theorem infiniteNeg_add_not_infinite {x y : ℝ*} :
    InfiniteNeg x → ¬Infinite y → InfiniteNeg (x + y) := fun hx hy =>
  infiniteNeg_add_not_infinitePos hx (not_or.mp hy).1

theorem infinitePos_of_tendsto_top {f : ℕ → ℝ} (hf : Tendsto f atTop atTop) :
    InfinitePos (ofSeq f) := fun r =>
  have hf' := tendsto_atTop_atTop.mp hf
  let ⟨i, hi⟩ := hf' (r + 1)
  have hi' : ∀ a : ℕ, f a < r + 1 → a < i := fun a => lt_imp_lt_of_le_imp_le (hi a)
  have hS : { a : ℕ | r < f a }ᶜ ⊆ { a : ℕ | a ≤ i } := by
    simp only [Set.compl_setOf, not_lt]
    exact fun a har => le_of_lt (hi' a (lt_of_le_of_lt har (lt_add_one _)))
  Germ.coe_lt.2 <| mem_hyperfilter_of_finite_compl <| (Set.finite_le_nat _).subset hS

theorem infiniteNeg_of_tendsto_bot {f : ℕ → ℝ} (hf : Tendsto f atTop atBot) :
    InfiniteNeg (ofSeq f) := fun r =>
  have hf' := tendsto_atTop_atBot.mp hf
  let ⟨i, hi⟩ := hf' (r - 1)
  have hi' : ∀ a : ℕ, r - 1 < f a → a < i := fun a => lt_imp_lt_of_le_imp_le (hi a)
  have hS : { a : ℕ | f a < r }ᶜ ⊆ { a : ℕ | a ≤ i } := by
    simp only [Set.compl_setOf, not_lt]
    exact fun a har => le_of_lt (hi' a (lt_of_lt_of_le (sub_one_lt _) har))
  Germ.coe_lt.2 <| mem_hyperfilter_of_finite_compl <| (Set.finite_le_nat _).subset hS

theorem not_infinite_neg {x : ℝ*} : ¬Infinite x → ¬Infinite (-x) := mt infinite_neg.mp

theorem not_infinite_add {x y : ℝ*} (hx : ¬Infinite x) (hy : ¬Infinite y) : ¬Infinite (x + y) :=
  have ⟨r, hr⟩ := exists_st_of_not_infinite hx
  have ⟨s, hs⟩ := exists_st_of_not_infinite hy
  not_infinite_of_exists_st <| ⟨r + s, hr.add hs⟩

theorem not_infinite_iff_exist_lt_gt {x : ℝ*} : ¬Infinite x ↔ ∃ r s : ℝ, (r : ℝ*) < x ∧ x < s :=
  ⟨fun hni ↦ let ⟨r, hr⟩ := exists_st_of_not_infinite hni; ⟨r - 1, r + 1, hr 1 one_pos⟩,
    fun ⟨r, s, hr, hs⟩ hi ↦ hi.elim (fun hp ↦ (hp s).not_gt hs) (fun hn ↦ (hn r).not_gt hr)⟩

theorem not_infinite_real (r : ℝ) : ¬Infinite r := by
  rw [not_infinite_iff_exist_lt_gt]
  exact ⟨r - 1, r + 1, coe_lt_coe.2 <| sub_one_lt r, coe_lt_coe.2 <| lt_add_one r⟩

theorem Infinite.ne_real {x : ℝ*} : Infinite x → ∀ r : ℝ, x ≠ r := fun hi r hr =>
  not_infinite_real r <| @Eq.subst _ Infinite _ _ hr hi

/-!
### Facts about `st` that require some infinite machinery
-/

theorem IsSt.mul {x y : ℝ*} {r s : ℝ} (hxr : IsSt x r) (hys : IsSt y s) : IsSt (x * y) (r * s) :=
  hxr.map₂ hys continuous_mul.continuousAt

--AN INFINITE LEMMA THAT REQUIRES SOME MORE ST MACHINERY
theorem not_infinite_mul {x y : ℝ*} (hx : ¬Infinite x) (hy : ¬Infinite y) : ¬Infinite (x * y) :=
  have ⟨_r, hr⟩ := exists_st_of_not_infinite hx
  have ⟨_s, hs⟩ := exists_st_of_not_infinite hy
  (hr.mul hs).not_infinite

---
theorem st_add {x y : ℝ*} (hx : ¬Infinite x) (hy : ¬Infinite y) : st (x + y) = st x + st y :=
  (isSt_st' (not_infinite_add hx hy)).unique ((isSt_st' hx).add (isSt_st' hy))

theorem st_neg (x : ℝ*) : st (-x) = -st x := by
  classical
  by_cases h : Infinite x
  · rw [h.st_eq, (infinite_neg.2 h).st_eq, neg_zero]
  · exact (isSt_st' (not_infinite_neg h)).unique (isSt_st' h).neg

theorem st_mul {x y : ℝ*} (hx : ¬Infinite x) (hy : ¬Infinite y) : st (x * y) = st x * st y :=
  have hx' := isSt_st' hx
  have hy' := isSt_st' hy
  have hxy := isSt_st' (not_infinite_mul hx hy)
  hxy.unique (hx'.mul hy')

/-!
### Basic lemmas about infinitesimal
-/

theorem infinitesimal_def {x : ℝ*} : Infinitesimal x ↔ ∀ r : ℝ, 0 < r → -(r : ℝ*) < x ∧ x < r := by
  simp [Infinitesimal, IsSt]

theorem lt_of_pos_of_infinitesimal {x : ℝ*} : Infinitesimal x → ∀ r : ℝ, 0 < r → x < r :=
  fun hi r hr => ((infinitesimal_def.mp hi) r hr).2

theorem lt_neg_of_pos_of_infinitesimal {x : ℝ*} : Infinitesimal x → ∀ r : ℝ, 0 < r → -↑r < x :=
  fun hi r hr => ((infinitesimal_def.mp hi) r hr).1

theorem gt_of_neg_of_infinitesimal {x : ℝ*} (hi : Infinitesimal x) (r : ℝ) (hr : r < 0) : ↑r < x :=
  neg_neg r ▸ (infinitesimal_def.1 hi (-r) (neg_pos.2 hr)).1

set_option backward.isDefEq.respectTransparency false in
theorem abs_lt_real_iff_infinitesimal {x : ℝ*} : Infinitesimal x ↔ ∀ r : ℝ, r ≠ 0 → |x| < |↑r| :=
  ⟨fun hi r hr ↦ abs_lt.mpr (coe_abs r ▸ infinitesimal_def.mp hi |r| (abs_pos.2 hr)), fun hR ↦
    infinitesimal_def.mpr fun r hr => abs_lt.mp <| (abs_of_pos <| coe_pos.2 hr) ▸ hR r <| hr.ne'⟩

theorem infinitesimal_zero : Infinitesimal 0 := isSt_refl_real 0

theorem Infinitesimal.eq_zero {r : ℝ} : Infinitesimal r → r = 0 := eq_of_isSt_real

@[simp] theorem infinitesimal_real_iff {r : ℝ} : Infinitesimal r ↔ r = 0 :=
  isSt_real_iff_eq

nonrec theorem Infinitesimal.add {x y : ℝ*} (hx : Infinitesimal x) (hy : Infinitesimal y) :
    Infinitesimal (x + y) := by simpa only [add_zero] using hx.add hy

nonrec theorem Infinitesimal.neg {x : ℝ*} (hx : Infinitesimal x) : Infinitesimal (-x) := by
  simpa only [neg_zero] using hx.neg

@[simp] theorem infinitesimal_neg {x : ℝ*} : Infinitesimal (-x) ↔ Infinitesimal x :=
  ⟨fun h => neg_neg x ▸ h.neg, Infinitesimal.neg⟩

nonrec theorem Infinitesimal.mul {x y : ℝ*} (hx : Infinitesimal x) (hy : Infinitesimal y) :
    Infinitesimal (x * y) := by simpa only [mul_zero] using hx.mul hy

theorem infinitesimal_of_tendsto_zero {f : ℕ → ℝ} (h : Tendsto f atTop (𝓝 0)) :
    Infinitesimal (ofSeq f) :=
  isSt_of_tendsto h

theorem infinitesimal_epsilon : Infinitesimal ε :=
  infinitesimal_of_tendsto_zero tendsto_inv_atTop_nhds_zero_nat

theorem not_real_of_infinitesimal_ne_zero (x : ℝ*) : Infinitesimal x → x ≠ 0 → ∀ r : ℝ, x ≠ r :=
  fun hi hx r hr =>
  hx <| hr.trans <| coe_eq_zero.2 <| IsSt.unique (hr.symm ▸ isSt_refl_real r : IsSt x r) hi

theorem IsSt.infinitesimal_sub {x : ℝ*} {r : ℝ} (hxr : IsSt x r) : Infinitesimal (x - ↑r) := by
  simpa only [sub_self] using hxr.sub (isSt_refl_real r)

theorem infinitesimal_sub_st {x : ℝ*} (hx : ¬Infinite x) : Infinitesimal (x - ↑(st x)) :=
  (isSt_st' hx).infinitesimal_sub

theorem infinitePos_iff_infinitesimal_inv_pos {x : ℝ*} :
    InfinitePos x ↔ Infinitesimal x⁻¹ ∧ 0 < x⁻¹ :=
  ⟨fun hip =>
    ⟨infinitesimal_def.mpr fun r hr =>
        ⟨lt_trans (coe_lt_coe.2 (neg_neg_of_pos hr)) (inv_pos.2 (hip 0)),
          inv_lt_of_inv_lt₀ (coe_lt_coe.2 hr) (by convert hip r⁻¹)⟩,
      inv_pos.2 <| hip 0⟩,
    fun ⟨hi, hp⟩ r =>
    @_root_.by_cases (r = 0) (↑r < x) (fun h => Eq.substr h (inv_pos.mp hp)) fun h =>
      lt_of_le_of_lt (coe_le_coe.2 (le_abs_self r))
        ((inv_lt_inv₀ (inv_pos.mp hp) (coe_lt_coe.2 (abs_pos.2 h))).mp
          ((infinitesimal_def.mp hi) |r|⁻¹ (inv_pos.2 (abs_pos.2 h))).2)⟩

set_option backward.isDefEq.respectTransparency false in
theorem infiniteNeg_iff_infinitesimal_inv_neg {x : ℝ*} :
    InfiniteNeg x ↔ Infinitesimal x⁻¹ ∧ x⁻¹ < 0 := by
  rw [← infinitePos_neg, infinitePos_iff_infinitesimal_inv_pos, inv_neg, neg_pos, infinitesimal_neg]

theorem infinitesimal_inv_of_infinite {x : ℝ*} : Infinite x → Infinitesimal x⁻¹ := fun hi =>
  Or.casesOn hi (fun hip => (infinitePos_iff_infinitesimal_inv_pos.mp hip).1) fun hin =>
    (infiniteNeg_iff_infinitesimal_inv_neg.mp hin).1

theorem infinite_of_infinitesimal_inv {x : ℝ*} (h0 : x ≠ 0) (hi : Infinitesimal x⁻¹) :
    Infinite x := by
  rcases lt_or_gt_of_ne h0 with hn | hp
  · exact Or.inr (infiniteNeg_iff_infinitesimal_inv_neg.mpr ⟨hi, inv_lt_zero.mpr hn⟩)
  · exact Or.inl (infinitePos_iff_infinitesimal_inv_pos.mpr ⟨hi, inv_pos.mpr hp⟩)

theorem infinite_iff_infinitesimal_inv {x : ℝ*} (h0 : x ≠ 0) : Infinite x ↔ Infinitesimal x⁻¹ :=
  ⟨infinitesimal_inv_of_infinite, infinite_of_infinitesimal_inv h0⟩

theorem infinitesimal_pos_iff_infinitePos_inv {x : ℝ*} :
    InfinitePos x⁻¹ ↔ Infinitesimal x ∧ 0 < x :=
  infinitePos_iff_infinitesimal_inv_pos.trans <| by rw [inv_inv]

theorem infinitesimal_neg_iff_infiniteNeg_inv {x : ℝ*} :
    InfiniteNeg x⁻¹ ↔ Infinitesimal x ∧ x < 0 :=
  infiniteNeg_iff_infinitesimal_inv_neg.trans <| by rw [inv_inv]

theorem infinitesimal_iff_infinite_inv {x : ℝ*} (h : x ≠ 0) : Infinitesimal x ↔ Infinite x⁻¹ :=
  Iff.trans (by rw [inv_inv]) (infinite_iff_infinitesimal_inv (inv_ne_zero h)).symm

/-!
### `Hyperreal.st` stuff that requires infinitesimal machinery
-/

theorem IsSt.inv {x : ℝ*} {r : ℝ} (hi : ¬Infinitesimal x) (hr : IsSt x r) : IsSt x⁻¹ r⁻¹ :=
  hr.map <| continuousAt_inv₀ <| by rintro rfl; exact hi hr

theorem st_inv (x : ℝ*) : st x⁻¹ = (st x)⁻¹ := by
  by_cases h0 : x = 0
  · rw [h0, inv_zero, ← coe_zero, st_id_real, inv_zero]
  by_cases h1 : Infinitesimal x
  · rw [((infinitesimal_iff_infinite_inv h0).mp h1).st_eq, h1.st_eq, inv_zero]
  by_cases h2 : Infinite x
  · rw [(infinitesimal_inv_of_infinite h2).st_eq, h2.st_eq, inv_zero]
  exact ((isSt_st' h2).inv h1).st_eq

/-!
### Infinite stuff that requires infinitesimal machinery
-/

theorem infinitePos_omega : InfinitePos ω :=
  infinitePos_iff_infinitesimal_inv_pos.mpr ⟨infinitesimal_epsilon, epsilon_pos⟩

theorem infinite_omega : Infinite ω :=
  (infinite_iff_infinitesimal_inv omega_ne_zero).mpr infinitesimal_epsilon

set_option backward.isDefEq.respectTransparency false in
theorem infinitePos_mul_of_infinitePos_not_infinitesimal_pos {x y : ℝ*} :
    InfinitePos x → ¬Infinitesimal y → 0 < y → InfinitePos (x * y) := fun hx hy₁ hy₂ r => by
  have hy₁' := not_forall.mp (mt infinitesimal_def.2 hy₁)
  let ⟨r₁, hy₁''⟩ := hy₁'
  have hyr : 0 < r₁ ∧ ↑r₁ ≤ y := by
    rwa [Classical.not_imp, ← abs_lt, not_lt, abs_of_pos hy₂] at hy₁''
  rw [← div_mul_cancel₀ r (ne_of_gt hyr.1), coe_mul]
  exact mul_lt_mul (hx (r / r₁)) hyr.2 (coe_lt_coe.2 hyr.1) (le_of_lt (hx 0))

theorem infinitePos_mul_of_not_infinitesimal_pos_infinitePos {x y : ℝ*} :
    ¬Infinitesimal x → 0 < x → InfinitePos y → InfinitePos (x * y) := fun hx hp hy =>
  mul_comm y x ▸ infinitePos_mul_of_infinitePos_not_infinitesimal_pos hy hx hp

set_option backward.isDefEq.respectTransparency false in
theorem infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg {x y : ℝ*} :
    InfiniteNeg x → ¬Infinitesimal y → y < 0 → InfinitePos (x * y) := by
  rw [← infinitePos_neg, ← neg_pos, ← neg_mul_neg, ← infinitesimal_neg]
  exact infinitePos_mul_of_infinitePos_not_infinitesimal_pos

theorem infinitePos_mul_of_not_infinitesimal_neg_infiniteNeg {x y : ℝ*} :
    ¬Infinitesimal x → x < 0 → InfiniteNeg y → InfinitePos (x * y) := fun hx hp hy =>
  mul_comm y x ▸ infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg hy hx hp

set_option backward.isDefEq.respectTransparency false in
theorem infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg {x y : ℝ*} :
    InfinitePos x → ¬Infinitesimal y → y < 0 → InfiniteNeg (x * y) := by
  rw [← infinitePos_neg, ← neg_pos, neg_mul_eq_mul_neg, ← infinitesimal_neg]
  exact infinitePos_mul_of_infinitePos_not_infinitesimal_pos

theorem infiniteNeg_mul_of_not_infinitesimal_neg_infinitePos {x y : ℝ*} :
    ¬Infinitesimal x → x < 0 → InfinitePos y → InfiniteNeg (x * y) := fun hx hp hy =>
  mul_comm y x ▸ infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg hy hx hp

theorem infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos {x y : ℝ*} :
    InfiniteNeg x → ¬Infinitesimal y → 0 < y → InfiniteNeg (x * y) := by
  rw [← infinitePos_neg, ← infinitePos_neg, neg_mul_eq_neg_mul]
  exact infinitePos_mul_of_infinitePos_not_infinitesimal_pos

theorem infiniteNeg_mul_of_not_infinitesimal_pos_infiniteNeg {x y : ℝ*} :
    ¬Infinitesimal x → 0 < x → InfiniteNeg y → InfiniteNeg (x * y) := fun hx hp hy => by
  rw [mul_comm]; exact infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos hy hx hp

theorem infinitePos_mul_infinitePos {x y : ℝ*} :
    InfinitePos x → InfinitePos y → InfinitePos (x * y) := fun hx hy =>
  infinitePos_mul_of_infinitePos_not_infinitesimal_pos hx hy.not_infinitesimal (hy 0)

theorem infiniteNeg_mul_infiniteNeg {x y : ℝ*} :
    InfiniteNeg x → InfiniteNeg y → InfinitePos (x * y) := fun hx hy =>
  infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg hx hy.not_infinitesimal (hy 0)

theorem infinitePos_mul_infiniteNeg {x y : ℝ*} :
    InfinitePos x → InfiniteNeg y → InfiniteNeg (x * y) := fun hx hy =>
  infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg hx hy.not_infinitesimal (hy 0)

theorem infiniteNeg_mul_infinitePos {x y : ℝ*} :
    InfiniteNeg x → InfinitePos y → InfiniteNeg (x * y) := fun hx hy =>
  infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos hx hy.not_infinitesimal (hy 0)

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

theorem infinite_mul_of_not_infinitesimal_infinite {x y : ℝ*} :
    ¬Infinitesimal x → Infinite y → Infinite (x * y) := fun hx hy => by
  rw [mul_comm]; exact infinite_mul_of_infinite_not_infinitesimal hy hx

theorem Infinite.mul {x y : ℝ*} : Infinite x → Infinite y → Infinite (x * y) := fun hx hy =>
  infinite_mul_of_infinite_not_infinitesimal hx hy.not_infinitesimal

end Hyperreal
end

/-
Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: restore `positivity` plugin

namespace Tactic

open Positivity

private theorem hyperreal_coe_ne_zero {r : ℝ} : r ≠ 0 → (r : ℝ*) ≠ 0 :=
  Hyperreal.coe_ne_zero.2

private theorem hyperreal_coe_nonneg {r : ℝ} : 0 ≤ r → 0 ≤ (r : ℝ*) :=
  Hyperreal.coe_nonneg.2

private theorem hyperreal_coe_pos {r : ℝ} : 0 < r → 0 < (r : ℝ*) :=
  Hyperreal.coe_pos.2

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

end Tactic
-/
