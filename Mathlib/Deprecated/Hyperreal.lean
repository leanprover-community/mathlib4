/-
Copyright (c) 2019 Abhimanyu Pallavi Sudhir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhimanyu Pallavi Sudhir
-/
module

public import Mathlib.Analysis.Real.Hyperreal

deprecated_module (since := "2026-01-05")

/-!
# Deprecated predicates on `Hyperreal`
-/

@[expose] public section

open ArchimedeanClass Filter Germ Topology

namespace Hyperreal

/-- Standard part predicate.

**Do not use.** This is equivalent to the conjunction of `0 ≤ ArchimedeanClass.mk x` and
`ArchimedeanClass.stdPart x = r`. -/
@[deprecated stdPart (since := "2026-01-05")]
def IsSt (x : ℝ*) (r : ℝ) :=
  ∀ δ : ℝ, 0 < δ → (r - δ : ℝ*) < x ∧ x < r + δ

set_option linter.deprecated false in
@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
theorem isSt_iff {x r} : IsSt x r ↔ 0 ≤ mk x ∧ stdPart x = r where
  mp h := by
    refine ⟨?_, stdPart_eq coeRingHom (fun s hs ↦ ?_) (fun s hs ↦ ?_)⟩
    · have h := h 1 zero_lt_one
      exact mk_nonneg_of_le_of_le_of_archimedean coeRingHom h.1.le h.2.le
    · simpa using (h _ (sub_pos_of_lt hs)).1.le
    · simpa using (h _ (sub_pos_of_lt hs)).2.le
  mpr h := by
    obtain ⟨h, rfl⟩ := h
    refine fun y hy ↦ ⟨?_, ?_⟩
    · apply lt_of_lt_stdPart coeRingHom h; simpa
    · apply lt_of_stdPart_lt coeRingHom h; simpa

set_option linter.deprecated false in
open scoped Classical in
/-- Standard part function: like a "round" to ℝ instead of ℤ -/
@[deprecated stdPart (since := "2026-01-05")]
noncomputable def st : ℝ* → ℝ := fun x => if h : ∃ r, IsSt x r then Classical.choose h else 0

set_option linter.deprecated false in
@[deprecated "`st` is deprecated" (since := "2026-01-05")]
theorem st_eq (x : ℝ*) : st x = stdPart x := by
  rw [st]
  split_ifs with h
  · exact (isSt_iff.1 (Classical.choose_spec h)).2.symm
  · simp_rw [isSt_iff] at h
    push_neg at h
    rw [eq_comm, stdPart_eq_zero]
    apply ne_of_lt
    by_contra! hx
    exact h _ hx rfl

set_option linter.deprecated false in
/-- A hyperreal number is infinitesimal if its standard part is 0.

**Do not use.** Write `0 < ArchimedeanClass.mk x` instead. -/
@[deprecated ArchimedeanClass.mk (since := "2026-01-05")]
def Infinitesimal (x : ℝ*) :=
  IsSt x 0

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem infinitesimal_iff {x : ℝ*} : Infinitesimal x ↔ 0 < mk x := by
  rw [Infinitesimal, isSt_iff, stdPart_eq_zero, lt_iff_le_and_ne']

/-- A hyperreal number is positive infinite if it is larger than all real numbers.

**Do not use.** Write `0 < x ∧ ArchimedeanClass.mk x < 0` instead. -/
@[deprecated ArchimedeanClass.mk (since := "2026-01-05")]
def InfinitePos (x : ℝ*) :=
  ∀ r : ℝ, ↑r < x

set_option linter.deprecated false in
@[deprecated "`InfinitePos` is deprecated" (since := "2026-01-05")]
theorem infinitePos_iff {x : ℝ*} : InfinitePos x ↔ 0 < x ∧ mk x < 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨hx, hx'⟩ r ↦ ?_⟩
  · have hx : 0 < x := h 0
    refine ⟨h 0, fun n ↦ ?_⟩
    simpa [abs_of_pos hx] using h n
  · exact lt_of_mk_lt_mk_of_nonneg (hx'.trans_le <| mk_map_nonneg_of_archimedean coeRingHom _) hx.le

/-- A hyperreal number is negative infinite if it is smaller than all real numbers.

**Do not use.** Write `x < 0 ∧ ArchimedeanClass.mk x < 0` instead. -/
@[deprecated ArchimedeanClass.mk (since := "2026-01-05")]
def InfiniteNeg (x : ℝ*) :=
  ∀ r : ℝ, x < r

set_option linter.deprecated false in
@[deprecated "`InfiniteNeg` is deprecated" (since := "2026-01-05")]
theorem infiniteNeg_iff {x : ℝ*} : InfiniteNeg x ↔ x < 0 ∧ mk x < 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨hx, hx'⟩ r ↦ ?_⟩
  · have hx : x < 0 := h 0
    refine ⟨h 0, fun n ↦ ?_⟩
    simpa [abs_of_neg hx, lt_neg] using h (-n)
  · exact lt_of_mk_lt_mk_of_nonpos (hx'.trans_le <| mk_map_nonneg_of_archimedean coeRingHom _) hx.le

set_option linter.deprecated false in
/-- A hyperreal number is infinite if it is infinite positive or infinite negative.

**Do not use.** Write `ArchimedeanClass.mk x < 0` instead. -/
@[deprecated ArchimedeanClass.mk (since := "2026-01-05")]
def Infinite (x : ℝ*) :=
  InfinitePos x ∨ InfiniteNeg x

set_option linter.deprecated false in
@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
theorem infinite_iff {x : ℝ*} : Infinite x ↔ mk x < 0 := by
  rw [Infinite, infinitePos_iff, infiniteNeg_iff]
  aesop

set_option linter.deprecated false in
@[deprecated tendsto_iff_forall (since := "2026-01-05")]
theorem isSt_ofSeq_iff_tendsto {f : ℕ → ℝ} {r : ℝ} :
    IsSt (ofSeq f) r ↔ Tendsto f (hyperfilter ℕ) (𝓝 r) :=
  Iff.trans (forall₂_congr fun _ _ ↦ (ofSeq_lt_ofSeq.and ofSeq_lt_ofSeq).trans eventually_and.symm)
    (nhds_basis_Ioo_pos _).tendsto_right_iff.symm

set_option linter.deprecated false in
@[deprecated tendsto_iff_forall (since := "2026-01-05")]
theorem isSt_iff_tendsto {x : ℝ*} {r : ℝ} : IsSt x r ↔ x.Tendsto (𝓝 r) := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  exact isSt_ofSeq_iff_tendsto

set_option linter.deprecated false in
@[deprecated stdPart_of_tendsto (since := "2026-01-05")]
theorem isSt_of_tendsto {f : ℕ → ℝ} {r : ℝ} (hf : Tendsto f atTop (𝓝 r)) : IsSt (ofSeq f) r :=
  isSt_ofSeq_iff_tendsto.2 <| hf.mono_left Nat.hyperfilter_le_atTop

set_option linter.deprecated false in
@[deprecated stdPart_monotoneOn (since := "2026-01-05")]
protected theorem IsSt.lt {x y : ℝ*} {r s : ℝ} (hxr : IsSt x r) (hys : IsSt y s) (hrs : r < s) :
    x < y := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rcases ofSeq_surjective y with ⟨g, rfl⟩
  rw [isSt_ofSeq_iff_tendsto] at hxr hys
  exact ofSeq_lt_ofSeq.2 <| hxr.eventually_lt hys hrs

set_option linter.deprecated false in
@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
theorem IsSt.unique {x : ℝ*} {r s : ℝ} (hr : IsSt x r) (hs : IsSt x s) : r = s := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rw [isSt_ofSeq_iff_tendsto] at hr hs
  exact tendsto_nhds_unique hr hs

set_option linter.deprecated false in
@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
theorem IsSt.st_eq {x : ℝ*} {r : ℝ} (hxr : IsSt x r) : st x = r := by
  have h : ∃ r, IsSt x r := ⟨r, hxr⟩
  rw [st, dif_pos h]
  exact (Classical.choose_spec h).unique hxr

set_option linter.deprecated false in
@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
theorem IsSt.not_infinite {x : ℝ*} {r : ℝ} (h : IsSt x r) : ¬Infinite x := fun hi ↦
  hi.elim (fun hp ↦ lt_asymm (h 1 one_pos).2 (hp (r + 1))) fun hn ↦
    lt_asymm (h 1 one_pos).1 (hn (r - 1))

set_option linter.deprecated false in
@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
theorem not_infinite_of_exists_st {x : ℝ*} : (∃ r : ℝ, IsSt x r) → ¬Infinite x := fun ⟨_r, hr⟩ =>
  hr.not_infinite

set_option linter.deprecated false in
@[deprecated stdPart_eq_zero (since := "2026-01-05")]
theorem Infinite.st_eq {x : ℝ*} (hi : Infinite x) : st x = 0 :=
  dif_neg fun ⟨_r, hr⟩ ↦ hr.not_infinite hi

set_option linter.deprecated false in
@[deprecated stdPart_eq_sSup (since := "2026-01-05")]
theorem isSt_sSup {x : ℝ*} (hni : ¬Infinite x) : IsSt x (sSup { y : ℝ | (y : ℝ*) < x }) := by
  rw [infinite_iff, not_lt] at hni
  rw [isSt_iff]
  exact ⟨hni, stdPart_eq_sSup coeRingHom x⟩

set_option linter.deprecated false in
@[deprecated stdPart_eq_sSup (since := "2026-01-05")]
theorem exists_st_of_not_infinite {x : ℝ*} (hni : ¬Infinite x) : ∃ r : ℝ, IsSt x r :=
  ⟨sSup { y : ℝ | (y : ℝ*) < x }, isSt_sSup hni⟩

set_option linter.deprecated false in
@[deprecated stdPart_eq_sSup (since := "2026-01-05")]
theorem st_eq_sSup {x : ℝ*} : st x = sSup { y : ℝ | (y : ℝ*) < x } := by
  rw [st_eq]
  exact stdPart_eq_sSup coeRingHom x

set_option linter.deprecated false in
@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
theorem exists_st_iff_not_infinite {x : ℝ*} : (∃ r : ℝ, IsSt x r) ↔ ¬Infinite x :=
  ⟨not_infinite_of_exists_st, exists_st_of_not_infinite⟩

set_option linter.deprecated false in
@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
theorem infinite_iff_not_exists_st {x : ℝ*} : Infinite x ↔ ¬∃ r : ℝ, IsSt x r :=
  iff_not_comm.mp exists_st_iff_not_infinite

set_option linter.deprecated false in
@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
theorem IsSt.isSt_st {x : ℝ*} {r : ℝ} (hxr : IsSt x r) : IsSt x (st x) := by
  rwa [hxr.st_eq]

set_option linter.deprecated false in
@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
theorem isSt_st_of_exists_st {x : ℝ*} (hx : ∃ r : ℝ, IsSt x r) : IsSt x (st x) :=
  let ⟨_r, hr⟩ := hx; hr.isSt_st

set_option linter.deprecated false in
@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
theorem isSt_st' {x : ℝ*} (hx : ¬Infinite x) : IsSt x (st x) :=
  (isSt_sSup hx).isSt_st

set_option linter.deprecated false in
@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
theorem isSt_st {x : ℝ*} (hx : st x ≠ 0) : IsSt x (st x) :=
  isSt_st' <| mt Infinite.st_eq hx

set_option linter.deprecated false in
@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
theorem isSt_refl_real (r : ℝ) : IsSt r r := isSt_ofSeq_iff_tendsto.2 tendsto_const_nhds

set_option linter.deprecated false in
@[deprecated stdPart_coe (since := "2026-01-05")]
theorem st_id_real (r : ℝ) : st r = r := (isSt_refl_real r).st_eq

set_option linter.deprecated false in
@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
theorem eq_of_isSt_real {r s : ℝ} : IsSt r s → r = s :=
  (isSt_refl_real r).unique

set_option linter.deprecated false in
@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
theorem isSt_real_iff_eq {r s : ℝ} : IsSt r s ↔ r = s :=
  ⟨eq_of_isSt_real, fun hrs => hrs ▸ isSt_refl_real r⟩

set_option linter.deprecated false in
@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
theorem isSt_symm_real {r s : ℝ} : IsSt r s ↔ IsSt s r := by
  rw [isSt_real_iff_eq, isSt_real_iff_eq, eq_comm]

set_option linter.deprecated false in
@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
theorem isSt_trans_real {r s t : ℝ} : IsSt r s → IsSt s t → IsSt r t := by
  rw [isSt_real_iff_eq, isSt_real_iff_eq, isSt_real_iff_eq]; exact Eq.trans

set_option linter.deprecated false in
@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
theorem isSt_inj_real {r₁ r₂ s : ℝ} (h1 : IsSt r₁ s) (h2 : IsSt r₂ s) : r₁ = r₂ :=
  Eq.trans (eq_of_isSt_real h1) (eq_of_isSt_real h2).symm

set_option linter.deprecated false in
@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
theorem isSt_iff_abs_sub_lt_delta {x : ℝ*} {r : ℝ} : IsSt x r ↔ ∀ δ : ℝ, 0 < δ → |x - ↑r| < δ := by
  simp only [abs_sub_lt_iff, sub_lt_iff_lt_add, IsSt, and_comm, add_comm]

set_option linter.deprecated false in
@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
theorem IsSt.map {x : ℝ*} {r : ℝ} (hxr : IsSt x r) {f : ℝ → ℝ} (hf : ContinuousAt f r) :
    IsSt (x.map f) (f r) := by
  rcases ofSeq_surjective x with ⟨g, rfl⟩
  exact isSt_ofSeq_iff_tendsto.2 <| hf.tendsto.comp (isSt_ofSeq_iff_tendsto.1 hxr)

set_option linter.deprecated false in
@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
theorem IsSt.map₂ {x y : ℝ*} {r s : ℝ} (hxr : IsSt x r) (hys : IsSt y s) {f : ℝ → ℝ → ℝ}
    (hf : ContinuousAt (Function.uncurry f) (r, s)) : IsSt (x.map₂ f y) (f r s) := by
  rcases ofSeq_surjective x with ⟨x, rfl⟩
  rcases ofSeq_surjective y with ⟨y, rfl⟩
  rw [isSt_ofSeq_iff_tendsto] at hxr hys
  exact isSt_ofSeq_iff_tendsto.2 <| hf.tendsto.comp (hxr.prodMk_nhds hys)

set_option linter.deprecated false in
@[deprecated stdPart_add (since := "2026-01-05")]
theorem IsSt.add {x y : ℝ*} {r s : ℝ} (hxr : IsSt x r) (hys : IsSt y s) :
    IsSt (x + y) (r + s) := hxr.map₂ hys continuous_add.continuousAt

set_option linter.deprecated false in
@[deprecated stdPart_neg (since := "2026-01-05")]
theorem IsSt.neg {x : ℝ*} {r : ℝ} (hxr : IsSt x r) : IsSt (-x) (-r) :=
  hxr.map continuous_neg.continuousAt

set_option linter.deprecated false in
@[deprecated stdPart_sub (since := "2026-01-05")]
theorem IsSt.sub {x y : ℝ*} {r s : ℝ} (hxr : IsSt x r) (hys : IsSt y s) : IsSt (x - y) (r - s) :=
  hxr.map₂ hys continuous_sub.continuousAt

set_option linter.deprecated false in
@[deprecated stdPart_monotoneOn (since := "2026-01-05")]
theorem IsSt.le {x y : ℝ*} {r s : ℝ} (hrx : IsSt x r) (hsy : IsSt y s) (hxy : x ≤ y) : r ≤ s :=
  not_lt.1 fun h ↦ hxy.not_gt <| hsy.lt hrx h

set_option linter.deprecated false in
@[deprecated stdPart_monotoneOn (since := "2026-01-05")]
theorem st_le_of_le {x y : ℝ*} (hix : ¬Infinite x) (hiy : ¬Infinite y) : x ≤ y → st x ≤ st y :=
  (isSt_st' hix).le (isSt_st' hiy)

set_option linter.deprecated false in
@[deprecated stdPart_monotoneOn (since := "2026-01-05")]
theorem lt_of_st_lt {x y : ℝ*} (hix : ¬Infinite x) (hiy : ¬Infinite y) : st x < st y → x < y :=
  (isSt_st' hix).lt (isSt_st' hiy)

set_option linter.deprecated false in
@[deprecated "`InfinitePos` is deprecated" (since := "2026-01-05")]
theorem infinitePos_def {x : ℝ*} : InfinitePos x ↔ ∀ r : ℝ, ↑r < x := Iff.rfl

set_option linter.deprecated false in
@[deprecated "`InfiniteNeg` is deprecated" (since := "2026-01-05")]
theorem infiniteNeg_def {x : ℝ*} : InfiniteNeg x ↔ ∀ r : ℝ, x < r := Iff.rfl

set_option linter.deprecated false in
@[deprecated "`InfinitePos` is deprecated" (since := "2026-01-05")]
theorem InfinitePos.pos {x : ℝ*} (hip : InfinitePos x) : 0 < x := hip 0

set_option linter.deprecated false in
@[deprecated "`InfiniteNeg` is deprecated" (since := "2026-01-05")]
theorem InfiniteNeg.lt_zero {x : ℝ*} : InfiniteNeg x → x < 0 := fun hin => hin 0

set_option linter.deprecated false in
@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
theorem Infinite.ne_zero {x : ℝ*} (hI : Infinite x) : x ≠ 0 :=
  hI.elim (fun hip => hip.pos.ne') fun hin => hin.lt_zero.ne

set_option linter.deprecated false in
@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
theorem not_infinite_zero : ¬Infinite 0 := fun hI => hI.ne_zero rfl

set_option linter.deprecated false in
@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
theorem InfiniteNeg.not_infinitePos {x : ℝ*} : InfiniteNeg x → ¬InfinitePos x := fun hn hp =>
  (hn 0).not_gt (hp 0)

set_option linter.deprecated false in
@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
theorem InfinitePos.not_infiniteNeg {x : ℝ*} (hp : InfinitePos x) : ¬InfiniteNeg x := fun hn ↦
  hn.not_infinitePos hp

set_option linter.deprecated false in
@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
theorem InfinitePos.neg {x : ℝ*} : InfinitePos x → InfiniteNeg (-x) := fun hp r =>
  neg_lt.mp (hp (-r))

set_option linter.deprecated false in
@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
theorem InfiniteNeg.neg {x : ℝ*} : InfiniteNeg x → InfinitePos (-x) := fun hp r =>
  lt_neg.mp (hp (-r))

set_option linter.deprecated false in
@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
theorem infiniteNeg_neg {x : ℝ*} : InfiniteNeg (-x) ↔ InfinitePos x :=
  ⟨fun hin => neg_neg x ▸ hin.neg, InfinitePos.neg⟩

set_option linter.deprecated false in
@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
theorem infinitePos_neg {x : ℝ*} : InfinitePos (-x) ↔ InfiniteNeg x :=
  ⟨fun hin => neg_neg x ▸ hin.neg, InfiniteNeg.neg⟩

set_option linter.deprecated false in
@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
theorem infinite_neg {x : ℝ*} : Infinite (-x) ↔ Infinite x :=
  or_comm.trans <| infiniteNeg_neg.or infinitePos_neg

set_option linter.deprecated false in
@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
nonrec theorem Infinitesimal.not_infinite {x : ℝ*} (h : Infinitesimal x) : ¬Infinite x :=
  h.not_infinite

set_option linter.deprecated false in
@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
theorem Infinite.not_infinitesimal {x : ℝ*} (h : Infinite x) : ¬Infinitesimal x := fun h' ↦
  h'.not_infinite h

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem InfinitePos.not_infinitesimal {x : ℝ*} (h : InfinitePos x) : ¬Infinitesimal x :=
  Infinite.not_infinitesimal (Or.inl h)

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem InfiniteNeg.not_infinitesimal {x : ℝ*} (h : InfiniteNeg x) : ¬Infinitesimal x :=
  Infinite.not_infinitesimal (Or.inr h)

set_option linter.deprecated false in
@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
theorem infinitePos_iff_infinite_and_pos {x : ℝ*} : InfinitePos x ↔ Infinite x ∧ 0 < x :=
  ⟨fun hip => ⟨Or.inl hip, hip 0⟩, fun ⟨hi, hp⟩ =>
    hi.casesOn id fun hin => False.elim (not_lt_of_gt hp (hin 0))⟩

set_option linter.deprecated false in
@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
theorem infiniteNeg_iff_infinite_and_neg {x : ℝ*} : InfiniteNeg x ↔ Infinite x ∧ x < 0 :=
  ⟨fun hip => ⟨Or.inr hip, hip 0⟩, fun ⟨hi, hp⟩ =>
    hi.casesOn (fun hin => False.elim (not_lt_of_gt hp (hin 0))) fun hip => hip⟩

set_option linter.deprecated false in
@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
theorem infinitePos_iff_infinite_of_nonneg {x : ℝ*} (hp : 0 ≤ x) : InfinitePos x ↔ Infinite x :=
  .symm <| or_iff_left fun h ↦ h.lt_zero.not_ge hp

set_option linter.deprecated false in
@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
theorem infinitePos_iff_infinite_of_pos {x : ℝ*} (hp : 0 < x) : InfinitePos x ↔ Infinite x :=
  infinitePos_iff_infinite_of_nonneg hp.le

set_option linter.deprecated false in
@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
theorem infiniteNeg_iff_infinite_of_neg {x : ℝ*} (hn : x < 0) : InfiniteNeg x ↔ Infinite x :=
  .symm <| or_iff_right fun h ↦ h.pos.not_gt hn

set_option linter.deprecated false in
@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
theorem infinitePos_abs_iff_infinite_abs {x : ℝ*} : InfinitePos |x| ↔ Infinite |x| :=
  infinitePos_iff_infinite_of_nonneg (abs_nonneg _)

set_option linter.deprecated false in
@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
theorem infinite_abs_iff {x : ℝ*} : Infinite |x| ↔ Infinite x := by
  cases le_total 0 x <;> simp [*, abs_of_nonneg, abs_of_nonpos, infinite_neg]

set_option linter.deprecated false in
@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
theorem infinitePos_abs_iff_infinite {x : ℝ*} : InfinitePos |x| ↔ Infinite x :=
  infinitePos_abs_iff_infinite_abs.trans infinite_abs_iff

set_option linter.deprecated false in
@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
theorem infinite_iff_abs_lt_abs {x : ℝ*} : Infinite x ↔ ∀ r : ℝ, (|r| : ℝ*) < |x| :=
  infinitePos_abs_iff_infinite.symm.trans ⟨fun hI r => coe_abs r ▸ hI |r|, fun hR r =>
    (le_abs_self _).trans_lt (hR r)⟩

set_option linter.deprecated false in
@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
theorem infinitePos_add_not_infiniteNeg {x y : ℝ*} :
    InfinitePos x → ¬InfiniteNeg y → InfinitePos (x + y) := by
  intro hip hnin r
  obtain ⟨r₂, hr₂⟩ := not_forall.mp hnin
  convert add_lt_add_of_lt_of_le (hip (r + -r₂)) (not_lt.mp hr₂) using 1
  simp

set_option linter.deprecated false in
@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
theorem not_infiniteNeg_add_infinitePos {x y : ℝ*} :
    ¬InfiniteNeg x → InfinitePos y → InfinitePos (x + y) := fun hx hy =>
  add_comm y x ▸ infinitePos_add_not_infiniteNeg hy hx

set_option linter.deprecated false in
@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
theorem infiniteNeg_add_not_infinitePos {x y : ℝ*} :
    InfiniteNeg x → ¬InfinitePos y → InfiniteNeg (x + y) := by
  rw [← infinitePos_neg, ← infinitePos_neg, ← @infiniteNeg_neg y, neg_add]
  exact infinitePos_add_not_infiniteNeg

set_option linter.deprecated false in
@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
theorem not_infinitePos_add_infiniteNeg {x y : ℝ*} :
    ¬InfinitePos x → InfiniteNeg y → InfiniteNeg (x + y) := fun hx hy =>
  add_comm y x ▸ infiniteNeg_add_not_infinitePos hy hx

set_option linter.deprecated false in
@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
theorem infinitePos_add_infinitePos {x y : ℝ*} :
    InfinitePos x → InfinitePos y → InfinitePos (x + y) := fun hx hy =>
  infinitePos_add_not_infiniteNeg hx hy.not_infiniteNeg

set_option linter.deprecated false in
@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
theorem infiniteNeg_add_infiniteNeg {x y : ℝ*} :
    InfiniteNeg x → InfiniteNeg y → InfiniteNeg (x + y) := fun hx hy =>
  infiniteNeg_add_not_infinitePos hx hy.not_infinitePos

set_option linter.deprecated false in
@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
theorem infinitePos_add_not_infinite {x y : ℝ*} :
    InfinitePos x → ¬Infinite y → InfinitePos (x + y) := fun hx hy =>
  infinitePos_add_not_infiniteNeg hx (not_or.mp hy).2

set_option linter.deprecated false in
@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
theorem infiniteNeg_add_not_infinite {x y : ℝ*} :
    InfiniteNeg x → ¬Infinite y → InfiniteNeg (x + y) := fun hx hy =>
  infiniteNeg_add_not_infinitePos hx (not_or.mp hy).1

set_option linter.deprecated false in
@[deprecated "`InfinitePos` is deprecated" (since := "2026-01-05")]
theorem infinitePos_of_tendsto_top {f : ℕ → ℝ} (hf : Tendsto f atTop atTop) :
    InfinitePos (ofSeq f) := by
  replace hf := hf.mono_left Nat.hyperfilter_le_atTop
  rw [infinitePos_iff]
  exact ⟨lt_of_tendsto_atTop 0 hf, archimedeanClassMk_neg_of_tendsto_atTop hf⟩

set_option linter.deprecated false in
@[deprecated "`InfiniteNeg` is deprecated" (since := "2026-01-05")]
theorem infiniteNeg_of_tendsto_bot {f : ℕ → ℝ} (hf : Tendsto f atTop atBot) :
    InfiniteNeg (ofSeq f) := by
  replace hf := hf.mono_left Nat.hyperfilter_le_atTop
  rw [infiniteNeg_iff]
  exact ⟨lt_of_tendsto_atBot 0 hf, archimedeanClassMk_neg_of_tendsto_atBot hf⟩

set_option linter.deprecated false in
@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
theorem not_infinite_neg {x : ℝ*} : ¬Infinite x → ¬Infinite (-x) := mt infinite_neg.mp

set_option linter.deprecated false in
@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
theorem not_infinite_add {x y : ℝ*} (hx : ¬Infinite x) (hy : ¬Infinite y) : ¬Infinite (x + y) :=
  have ⟨r, hr⟩ := exists_st_of_not_infinite hx
  have ⟨s, hs⟩ := exists_st_of_not_infinite hy
  not_infinite_of_exists_st <| ⟨r + s, hr.add hs⟩

set_option linter.deprecated false in
@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
theorem not_infinite_iff_exist_lt_gt {x : ℝ*} : ¬Infinite x ↔ ∃ r s : ℝ, (r : ℝ*) < x ∧ x < s :=
  ⟨fun hni ↦ let ⟨r, hr⟩ := exists_st_of_not_infinite hni; ⟨r - 1, r + 1, hr 1 one_pos⟩,
    fun ⟨r, s, hr, hs⟩ hi ↦ hi.elim (fun hp ↦ (hp s).not_gt hs) (fun hn ↦ (hn r).not_gt hr)⟩

set_option linter.deprecated false in
@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
theorem not_infinite_real (r : ℝ) : ¬Infinite r := by
  rw [not_infinite_iff_exist_lt_gt]
  exact ⟨r - 1, r + 1, coe_lt_coe.2 <| sub_one_lt r, coe_lt_coe.2 <| lt_add_one r⟩

set_option linter.deprecated false in
@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
theorem Infinite.ne_real {x : ℝ*} : Infinite x → ∀ r : ℝ, x ≠ r := fun hi r hr =>
  not_infinite_real r <| @Eq.subst _ Infinite _ _ hr hi

/-!
### Facts about `st` that require some infinite machinery
-/

set_option linter.deprecated false in
@[deprecated stdPart_mul (since := "2026-01-05")]
theorem IsSt.mul {x y : ℝ*} {r s : ℝ} (hxr : IsSt x r) (hys : IsSt y s) : IsSt (x * y) (r * s) :=
  hxr.map₂ hys continuous_mul.continuousAt

set_option linter.deprecated false in
@[deprecated mk_mul (since := "2026-01-05")]
theorem not_infinite_mul {x y : ℝ*} (hx : ¬Infinite x) (hy : ¬Infinite y) : ¬Infinite (x * y) :=
  have ⟨_r, hr⟩ := exists_st_of_not_infinite hx
  have ⟨_s, hs⟩ := exists_st_of_not_infinite hy
  (hr.mul hs).not_infinite

set_option linter.deprecated false in
@[deprecated stdPart_add (since := "2026-01-05")]
theorem st_add {x y : ℝ*} (hx : ¬Infinite x) (hy : ¬Infinite y) : st (x + y) = st x + st y :=
  (isSt_st' (not_infinite_add hx hy)).unique ((isSt_st' hx).add (isSt_st' hy))

set_option linter.deprecated false in
@[deprecated stdPart_neg (since := "2026-01-05")]
theorem st_neg (x : ℝ*) : st (-x) = -st x := by
  classical
  by_cases h : Infinite x
  · rw [h.st_eq, (infinite_neg.2 h).st_eq, neg_zero]
  · exact (isSt_st' (not_infinite_neg h)).unique (isSt_st' h).neg

set_option linter.deprecated false in
@[deprecated stdPart_mul (since := "2026-01-05")]
theorem st_mul {x y : ℝ*} (hx : ¬Infinite x) (hy : ¬Infinite y) : st (x * y) = st x * st y :=
  have hx' := isSt_st' hx
  have hy' := isSt_st' hy
  have hxy := isSt_st' (not_infinite_mul hx hy)
  hxy.unique (hx'.mul hy')

/-!
### Basic lemmas about infinitesimal
-/

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem infinitesimal_def {x : ℝ*} : Infinitesimal x ↔ ∀ r : ℝ, 0 < r → -(r : ℝ*) < x ∧ x < r := by
  simp [Infinitesimal, IsSt]

set_option linter.deprecated false in
@[deprecated lt_of_pos_of_archimedean (since := "2026-01-05")]
theorem lt_of_pos_of_infinitesimal {x : ℝ*} : Infinitesimal x → ∀ r : ℝ, 0 < r → x < r :=
  fun hi r hr => ((infinitesimal_def.mp hi) r hr).2

set_option linter.deprecated false in
@[deprecated lt_of_neg_of_archimedean (since := "2026-01-05")]
theorem lt_neg_of_pos_of_infinitesimal {x : ℝ*} : Infinitesimal x → ∀ r : ℝ, 0 < r → -↑r < x :=
  fun hi r hr => ((infinitesimal_def.mp hi) r hr).1

set_option linter.deprecated false in
@[deprecated lt_of_neg_of_archimedean (since := "2026-01-05")]
theorem gt_of_neg_of_infinitesimal {x : ℝ*} (hi : Infinitesimal x) (r : ℝ) (hr : r < 0) : ↑r < x :=
  neg_neg r ▸ (infinitesimal_def.1 hi (-r) (neg_pos.2 hr)).1

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem abs_lt_real_iff_infinitesimal {x : ℝ*} : Infinitesimal x ↔ ∀ r : ℝ, r ≠ 0 → |x| < |↑r| :=
  ⟨fun hi r hr ↦ abs_lt.mpr (coe_abs r ▸ infinitesimal_def.mp hi |r| (abs_pos.2 hr)), fun hR ↦
    infinitesimal_def.mpr fun r hr => abs_lt.mp <| (abs_of_pos <| coe_pos.2 hr) ▸ hR r <| hr.ne'⟩

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem infinitesimal_zero : Infinitesimal 0 := isSt_refl_real 0

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem Infinitesimal.eq_zero {r : ℝ} : Infinitesimal r → r = 0 := eq_of_isSt_real

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem infinitesimal_real_iff {r : ℝ} : Infinitesimal r ↔ r = 0 :=
  isSt_real_iff_eq

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
nonrec theorem Infinitesimal.add {x y : ℝ*} (hx : Infinitesimal x) (hy : Infinitesimal y) :
    Infinitesimal (x + y) := by simpa only [add_zero] using hx.add hy

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
nonrec theorem Infinitesimal.neg {x : ℝ*} (hx : Infinitesimal x) : Infinitesimal (-x) := by
  simpa only [neg_zero] using hx.neg

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem infinitesimal_neg {x : ℝ*} : Infinitesimal (-x) ↔ Infinitesimal x :=
  ⟨fun h => neg_neg x ▸ h.neg, Infinitesimal.neg⟩

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
nonrec theorem Infinitesimal.mul {x y : ℝ*} (hx : Infinitesimal x) (hy : Infinitesimal y) :
    Infinitesimal (x * y) := by simpa only [mul_zero] using hx.mul hy

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem infinitesimal_of_tendsto_zero {f : ℕ → ℝ} (h : Tendsto f atTop (𝓝 0)) :
    Infinitesimal (ofSeq f) :=
  isSt_of_tendsto h

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem infinitesimal_epsilon : Infinitesimal ε :=
  infinitesimal_of_tendsto_zero tendsto_inv_atTop_nhds_zero_nat

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem not_real_of_infinitesimal_ne_zero (x : ℝ*) : Infinitesimal x → x ≠ 0 → ∀ r : ℝ, x ≠ r :=
  fun hi hx r hr =>
  hx <| hr.trans <| coe_eq_zero.2 <| IsSt.unique (hr.symm ▸ isSt_refl_real r : IsSt x r) hi

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem IsSt.infinitesimal_sub {x : ℝ*} {r : ℝ} (hxr : IsSt x r) : Infinitesimal (x - ↑r) := by
  simpa only [sub_self] using hxr.sub (isSt_refl_real r)

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem infinitesimal_sub_st {x : ℝ*} (hx : ¬Infinite x) : Infinitesimal (x - ↑(st x)) :=
  (isSt_st' hx).infinitesimal_sub

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem infinitePos_iff_infinitesimal_inv_pos {x : ℝ*} :
    InfinitePos x ↔ Infinitesimal x⁻¹ ∧ 0 < x⁻¹ := by
  rw [infinitePos_iff, infinitesimal_iff]
  aesop

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem infiniteNeg_iff_infinitesimal_inv_neg {x : ℝ*} :
    InfiniteNeg x ↔ Infinitesimal x⁻¹ ∧ x⁻¹ < 0 := by
  rw [← infinitePos_neg, infinitePos_iff_infinitesimal_inv_pos, inv_neg, neg_pos, infinitesimal_neg]

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem infinitesimal_inv_of_infinite {x : ℝ*} : Infinite x → Infinitesimal x⁻¹ := fun hi =>
  Or.casesOn hi (fun hip => (infinitePos_iff_infinitesimal_inv_pos.mp hip).1) fun hin =>
    (infiniteNeg_iff_infinitesimal_inv_neg.mp hin).1

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem infinite_of_infinitesimal_inv {x : ℝ*} (h0 : x ≠ 0) (hi : Infinitesimal x⁻¹) :
    Infinite x := by
  rcases lt_or_gt_of_ne h0 with hn | hp
  · exact Or.inr (infiniteNeg_iff_infinitesimal_inv_neg.mpr ⟨hi, inv_lt_zero.mpr hn⟩)
  · exact Or.inl (infinitePos_iff_infinitesimal_inv_pos.mpr ⟨hi, inv_pos.mpr hp⟩)

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem infinite_iff_infinitesimal_inv {x : ℝ*} (h0 : x ≠ 0) : Infinite x ↔ Infinitesimal x⁻¹ :=
  ⟨infinitesimal_inv_of_infinite, infinite_of_infinitesimal_inv h0⟩

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem infinitesimal_pos_iff_infinitePos_inv {x : ℝ*} :
    InfinitePos x⁻¹ ↔ Infinitesimal x ∧ 0 < x :=
  infinitePos_iff_infinitesimal_inv_pos.trans <| by rw [inv_inv]

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem infinitesimal_neg_iff_infiniteNeg_inv {x : ℝ*} :
    InfiniteNeg x⁻¹ ↔ Infinitesimal x ∧ x < 0 :=
  infiniteNeg_iff_infinitesimal_inv_neg.trans <| by rw [inv_inv]

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem infinitesimal_iff_infinite_inv {x : ℝ*} (h : x ≠ 0) : Infinitesimal x ↔ Infinite x⁻¹ :=
  Iff.trans (by rw [inv_inv]) (infinite_iff_infinitesimal_inv (inv_ne_zero h)).symm

set_option linter.deprecated false in
@[deprecated stdPart_inv (since := "2026-01-05")]
theorem IsSt.inv {x : ℝ*} {r : ℝ} (hi : ¬Infinitesimal x) (hr : IsSt x r) : IsSt x⁻¹ r⁻¹ :=
  hr.map <| continuousAt_inv₀ <| by rintro rfl; exact hi hr

set_option linter.deprecated false in
@[deprecated stdPart_inv (since := "2026-01-05")]
theorem st_inv (x : ℝ*) : st x⁻¹ = (st x)⁻¹ := by
  simp [st_eq]

set_option linter.deprecated false in
@[deprecated archimedeanClassMk_omega_neg (since := "2026-01-05")]
theorem infinitePos_omega : InfinitePos ω :=
  infinitePos_iff_infinitesimal_inv_pos.mpr ⟨infinitesimal_epsilon, epsilon_pos⟩

set_option linter.deprecated false in
@[deprecated archimedeanClassMk_omega_neg (since := "2026-01-05")]
theorem infinite_omega : Infinite ω :=
  (infinite_iff_infinitesimal_inv omega_ne_zero).mpr infinitesimal_epsilon

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem infinitePos_mul_of_infinitePos_not_infinitesimal_pos {x y : ℝ*} :
    InfinitePos x → ¬Infinitesimal y → 0 < y → InfinitePos (x * y) := fun hx hy₁ hy₂ r => by
  have hy₁' := not_forall.mp (mt infinitesimal_def.2 hy₁)
  let ⟨r₁, hy₁''⟩ := hy₁'
  have hyr : 0 < r₁ ∧ ↑r₁ ≤ y := by
    rwa [Classical.not_imp, ← abs_lt, not_lt, abs_of_pos hy₂] at hy₁''
  rw [← div_mul_cancel₀ r (ne_of_gt hyr.1), coe_mul]
  exact mul_lt_mul (hx (r / r₁)) hyr.2 (coe_lt_coe.2 hyr.1) (le_of_lt (hx 0))

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem infinitePos_mul_of_not_infinitesimal_pos_infinitePos {x y : ℝ*} :
    ¬Infinitesimal x → 0 < x → InfinitePos y → InfinitePos (x * y) := fun hx hp hy =>
  mul_comm y x ▸ infinitePos_mul_of_infinitePos_not_infinitesimal_pos hy hx hp

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg {x y : ℝ*} :
    InfiniteNeg x → ¬Infinitesimal y → y < 0 → InfinitePos (x * y) := by
  rw [← infinitePos_neg, ← neg_pos, ← neg_mul_neg, ← infinitesimal_neg]
  exact infinitePos_mul_of_infinitePos_not_infinitesimal_pos

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem infinitePos_mul_of_not_infinitesimal_neg_infiniteNeg {x y : ℝ*} :
    ¬Infinitesimal x → x < 0 → InfiniteNeg y → InfinitePos (x * y) := fun hx hp hy =>
  mul_comm y x ▸ infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg hy hx hp

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg {x y : ℝ*} :
    InfinitePos x → ¬Infinitesimal y → y < 0 → InfiniteNeg (x * y) := by
  rw [← infinitePos_neg, ← neg_pos, neg_mul_eq_mul_neg, ← infinitesimal_neg]
  exact infinitePos_mul_of_infinitePos_not_infinitesimal_pos

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem infiniteNeg_mul_of_not_infinitesimal_neg_infinitePos {x y : ℝ*} :
    ¬Infinitesimal x → x < 0 → InfinitePos y → InfiniteNeg (x * y) := fun hx hp hy =>
  mul_comm y x ▸ infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg hy hx hp

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos {x y : ℝ*} :
    InfiniteNeg x → ¬Infinitesimal y → 0 < y → InfiniteNeg (x * y) := by
  rw [← infinitePos_neg, ← infinitePos_neg, neg_mul_eq_neg_mul]
  exact infinitePos_mul_of_infinitePos_not_infinitesimal_pos

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem infiniteNeg_mul_of_not_infinitesimal_pos_infiniteNeg {x y : ℝ*} :
    ¬Infinitesimal x → 0 < x → InfiniteNeg y → InfiniteNeg (x * y) := fun hx hp hy => by
  rw [mul_comm]; exact infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos hy hx hp

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem infinitePos_mul_infinitePos {x y : ℝ*} :
    InfinitePos x → InfinitePos y → InfinitePos (x * y) := fun hx hy =>
  infinitePos_mul_of_infinitePos_not_infinitesimal_pos hx hy.not_infinitesimal (hy 0)

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem infiniteNeg_mul_infiniteNeg {x y : ℝ*} :
    InfiniteNeg x → InfiniteNeg y → InfinitePos (x * y) := fun hx hy =>
  infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg hx hy.not_infinitesimal (hy 0)

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem infinitePos_mul_infiniteNeg {x y : ℝ*} :
    InfinitePos x → InfiniteNeg y → InfiniteNeg (x * y) := fun hx hy =>
  infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg hx hy.not_infinitesimal (hy 0)

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem infiniteNeg_mul_infinitePos {x y : ℝ*} :
    InfiniteNeg x → InfinitePos y → InfiniteNeg (x * y) := fun hx hy =>
  infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos hx hy.not_infinitesimal (hy 0)

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
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

set_option linter.deprecated false in
@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
theorem infinite_mul_of_not_infinitesimal_infinite {x y : ℝ*} :
    ¬Infinitesimal x → Infinite y → Infinite (x * y) := fun hx hy => by
  rw [mul_comm]; exact infinite_mul_of_infinite_not_infinitesimal hy hx

set_option linter.deprecated false in
@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
theorem Infinite.mul {x y : ℝ*} : Infinite x → Infinite y → Infinite (x * y) := fun hx hy =>
  infinite_mul_of_infinite_not_infinitesimal hx hy.not_infinitesimal

end Hyperreal
