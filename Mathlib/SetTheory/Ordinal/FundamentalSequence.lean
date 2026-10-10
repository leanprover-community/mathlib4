/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Mario Carneiro
-/
module

public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal

/-!
# Fundamental sequences

A fundamental sequence for a countable limit ordinal `o` is a strictly monotone function `ℕ → Iio o`
with cofinal range. We can generalize this notion to arbitrary ordinals by setting the domain as
`Iio o.cof.card`. Note that for a countable limit ordinal, one has `o.cof.card = ω`.

## Main results

- `Ordinal.exists_isFundamentalSeq`: every ordinal has a fundamental sequence.
-/

@[expose] public section

universe u

open Cardinal Order Set

namespace Ordinal

variable {a b o : Ordinal}

/-- A fundamental sequence for `o` is a strictly monotonic function `Iio o.cof.ord → Iio o` with
cofinal range. We provide `a = o.cof.ord` explicitly to avoid type rewrites. -/
structure IsFundamentalSeq (f : Iio a → Iio o) : Prop where
  /-- This condition alongside the others is enough to conclude `o.cof.ord = a`, see
  `IsFundamentalSeq.ord_cof`. -/
  le_ord_cof : a ≤ o.cof.ord
  /-- A fundamental sequence is strictly monotonic. -/
  strictMono : StrictMono f
  /-- A fundamental sequence for `o` has cofinal range, i.e. its least strict upper bound equals the
  ordinal `o`. See `IsFundamentalSeq.iSup_add_one_eq` and `IsFundamentalSeq.iSup_eq`. -/
  isCofinal_range : IsCofinal (range f)

namespace IsFundamentalSeq
variable {f : Iio a → Iio o} {g : Iio b → Iio a}

theorem iSup_add_one_eq (hf : IsFundamentalSeq f) : ⨆ i, (f i).1 + 1 = o := by
  apply le_antisymm
  · simp_rw [Ordinal.iSup_le_iff, add_one_le_iff]
    exact fun i ↦ (f i).2
  · refine le_of_forall_lt fun b hb ↦ ?_
    obtain ⟨_, ⟨c, rfl⟩, hc : b ≤ _⟩ := hf.isCofinal_range ⟨b, hb⟩
    apply hc.trans_lt
    rw [← add_one_le_iff]
    apply Ordinal.le_iSup

theorem ord_cof (hf : IsFundamentalSeq f) : o.cof.ord = a := by
  apply hf.le_ord_cof.antisymm'
  rw [← hf.iSup_add_one_eq, cof_iSup_Iio_add_one hf.strictMono]
  exact ord_cof_le a

theorem iSup_eq (hf : IsFundamentalSeq f) (ha : 1 < a) : ⨆ i, (f i).1 = o := by
  rw [← iSup_Iio_add_one hf.strictMono, hf.iSup_add_one_eq]
  rw [← hf.ord_cof]
  apply (isSuccLimit_ord _).isSuccPrelimit
  rwa [aleph0_le_cof_iff, ← ord_lt_ord, hf.ord_cof, ord_one]

/-- A regular ordinal `o` has a fundamental sequence given by all smaller ordinals. -/
protected theorem id (ho : o ≤ o.cof.ord) : IsFundamentalSeq (o := o) id where
  strictMono := strictMono_id
  isCofinal_range := by simp
  le_ord_cof := ho

/-- The empty function is a fundamental sequence for 0. -/
protected theorem zero (f : Iio 0 → Iio 0) : IsFundamentalSeq f where
  strictMono _ := by simp
  le_ord_cof := by simp
  isCofinal_range := .of_isEmpty

set_option backward.isDefEq.respectTransparency false in
/-- The length one sequence `(o)` is a fundamental sequence for `o + 1`. -/
protected theorem add_one (o : Ordinal) :
    @IsFundamentalSeq 1 (o + 1) fun _ ↦ ⟨o, lt_add_one o⟩ where
  strictMono _ := by simp
  le_ord_cof := by simp
  isCofinal_range := by simp [IsTop]

protected theorem comp (hf : IsFundamentalSeq f) (hg : IsFundamentalSeq g) :
    IsFundamentalSeq (f ∘ g) where
  strictMono := hf.strictMono.comp hg.strictMono
  le_ord_cof := by rw [hf.ord_cof, ← hg.ord_cof]; exact a.ord_cof_le
  isCofinal_range := by
    rw [range_comp]
    exact hg.isCofinal_range.image hf.strictMono.monotone hf.isCofinal_range

/-- If `f` is a fundamental sequence for a limit ordinal `o` and `g` is normal, then `g ∘ f` is a
fundamental sequence for `g o`. -/
theorem comp_isNormal {g : Ordinal → Ordinal} (hg : IsNormal g) (hf : IsFundamentalSeq f)
    (ho : IsSuccLimit o) : IsFundamentalSeq fun i ↦ ⟨g (f i), hg.strictMono (f i).2⟩ where
  strictMono := hg.strictMono.comp hf.strictMono
  le_ord_cof := by rw [cof_map_of_isNormal hg ho, hf.ord_cof]
  isCofinal_range := by
    rintro ⟨b, hb⟩
    rw [mem_Iio, hg.lt_iff_exists_lt ho] at hb
    obtain ⟨c, hc, hc'⟩ := hb
    obtain ⟨_, ⟨d, rfl⟩, hd⟩ := hf.isCofinal_range ⟨c, hc⟩
    refine ⟨⟨_, hg.strictMono (f d).2⟩, ?_, hc'.le.trans (hg.monotone hd)⟩
    simp

end IsFundamentalSeq

/-- Every ordinal has a fundamental sequence. -/
theorem exists_isFundamentalSeq (ha : o.cof.ord = a) : ∃ f : Iio a → Iio o, IsFundamentalSeq f := by
  subst ha
  obtain ⟨s, hs, hs'⟩ := exists_ord_cof_eq o.ToType
  rw [cof_toType] at hs'
  let g := (Set.orderIsoOfEq _ _ (congrArg _ hs'.symm)).trans <|
    .ofRelIsoLT (enum (α := s) (· < ·))
  refine ⟨fun i ↦ g i, le_rfl, fun _ ↦ by simp, ?_⟩
  rw [range_comp', OrderIso.map_isCofinal_iff, range_comp', g.range_eq]
  simpa

end Ordinal
