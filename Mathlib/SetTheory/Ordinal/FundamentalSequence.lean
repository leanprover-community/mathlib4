/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Mario Carneiro
-/
module

public import Mathlib.SetTheory.Cardinal.Cofinality

/-!
# Fundamental sequences

A fundamental sequence for a countable limit ordinal `o` is a strictly monotone function `ℕ → Iio o`
with cofinal range. We can generalize this notion to arbitrary ordinals by setting the domain as
`Iio o.cof.card`. Note that for a countable limit ordinal, one has `o.cof.card = ω`.

## Main results

- `Ordinal.exists_isFundamentalSeq`: every ordinal has a fundamental sequence.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe u

open Cardinal Order Set

namespace Ordinal

variable {a b o : Ordinal}

/-- A fundamental sequence for `o` is a strictly monotonic function `Iio o.cof.ord → Iio o` with
cofinal range. We provide `a = o.cof.ord` explicitly to avoid type rewrites. -/
structure IsFundamentalSeq (f : Iio a → Iio o) : Prop where
  /-- This condition alongside the others is enough to conclude `o.cof.ord = a`, see
  `IsFundamentalSeq.ord_cof_eq`. -/
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
  isCofinal_range := by rw [range_eq_empty, isCofinal_empty_iff]; infer_instance

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
  obtain ⟨s, hs, hs'⟩ := ord_cof_eq o.ToType
  rw [cof_toType] at hs'
  let g := (OrderIso.setCongr _ _ (congrArg _ hs'.symm)).trans <|
    .ofRelIsoLT (enum (α := s) (· < ·))
  refine ⟨fun i ↦ g i, le_rfl, fun _ ↦ by simp, ?_⟩
  rw [range_comp', OrderIso.map_isCofinal_iff, range_comp', g.range_eq]
  simpa

/-! ### Deprecated material -/

set_option linter.deprecated false in
/-- A fundamental sequence for `a` is an increasing sequence of length `o = cof a` that converges at
    `a`. We provide `o` explicitly in order to avoid type rewrites. -/
@[deprecated IsFundamentalSeq (since := "2026-03-23")]
def IsFundamentalSequence (a o : Ordinal.{u}) (f : ∀ b < o, Ordinal.{u}) : Prop :=
  o ≤ a.cof.ord ∧ (∀ {i j} (hi hj), i < j → f i hi < f j hj) ∧ blsub.{u, u} o f = a

namespace IsFundamentalSequence

variable {a o : Ordinal.{u}} {f : ∀ b < o, Ordinal.{u}}

set_option linter.deprecated false in
@[deprecated IsFundamentalSeq.ord_cof (since := "2026-03-23")]
protected theorem cof_eq (hf : IsFundamentalSequence a o f) : a.cof.ord = o :=
  hf.1.antisymm' <| by
    rw [← hf.2.2]
    exact (ord_le_ord.2 (cof_blsub_le f)).trans (ord_card_le o)

set_option linter.deprecated false in
@[deprecated IsFundamentalSeq.strictMono (since := "2026-03-23")]
protected theorem strict_mono (hf : IsFundamentalSequence a o f) {i j} :
    ∀ hi hj, i < j → f i hi < f j hj :=
  hf.2.1

set_option linter.deprecated false in
@[deprecated IsFundamentalSeq.iSup_add_one_eq (since := "2026-03-23")]
theorem blsub_eq (hf : IsFundamentalSequence a o f) : blsub.{u, u} o f = a :=
  hf.2.2

set_option linter.deprecated false in
@[deprecated IsFundamentalSeq (since := "2026-03-23")]
theorem ord_cof (hf : IsFundamentalSequence a o f) :
    IsFundamentalSequence a a.cof.ord fun i hi => f i (hi.trans_le (by rw [hf.cof_eq])) := by
  have H := hf.cof_eq
  subst H
  exact hf

set_option linter.deprecated false in
@[deprecated IsFundamentalSeq.id (since := "2026-03-23")]
theorem id_of_le_cof (h : o ≤ o.cof.ord) : IsFundamentalSequence o o fun a _ => a :=
  ⟨h, @fun _ _ _ _ => id, blsub_id o⟩

set_option linter.deprecated false in
@[deprecated IsFundamentalSeq.zero (since := "2026-03-23")]
protected theorem zero {f : ∀ b < (0 : Ordinal), Ordinal} : IsFundamentalSequence 0 0 f :=
  ⟨by rw [cof_zero, ord_zero], @fun i _ hi => (not_lt_zero hi).elim, blsub_zero f⟩

set_option linter.deprecated false in
@[deprecated IsFundamentalSeq.add_one (since := "2026-03-23")]
protected theorem succ : IsFundamentalSequence (succ o) 1 fun _ _ => o := by
  refine ⟨?_, @fun i j hi hj h => ?_, blsub_const Ordinal.one_ne_zero o⟩
  · rw [cof_succ, ord_one]
  · rw [lt_one_iff_zero] at hi hj
    rw [hi, hj] at h
    exact h.false.elim

set_option linter.deprecated false in
@[deprecated IsFundamentalSeq.strictMono (since := "2026-03-23")]
protected theorem monotone (hf : IsFundamentalSequence a o f) {i j : Ordinal} (hi : i < o)
    (hj : j < o) (hij : i ≤ j) : f i hi ≤ f j hj := by
  rcases lt_or_eq_of_le hij with (hij | rfl)
  · exact (hf.2.1 hi hj hij).le
  · rfl

set_option linter.deprecated false in
@[deprecated IsFundamentalSeq.comp (since := "2026-03-23")]
theorem trans {a o o' : Ordinal.{u}} {f : ∀ b < o, Ordinal.{u}} (hf : IsFundamentalSequence a o f)
    {g : ∀ b < o', Ordinal.{u}} (hg : IsFundamentalSequence o o' g) :
    IsFundamentalSequence a o' fun i hi =>
      f (g i hi) (by rw [← hg.2.2]; apply lt_blsub) := by
  refine ⟨?_, @fun i j _ _ h => hf.2.1 _ _ (hg.2.1 _ _ h), ?_⟩
  · rw [hf.cof_eq]
    exact hg.1.trans (ord_cof_le o)
  · rw [@blsub_comp.{u, u, u} o _ f (@IsFundamentalSequence.monotone _ _ f hf)]
    · exact hf.2.2
    · exact hg.2.2

set_option linter.deprecated false in
@[deprecated IsFundamentalSeq (since := "2026-03-23")]
protected theorem lt {a o : Ordinal} {s : Π p < o, Ordinal}
    (h : IsFundamentalSequence a o s) {p : Ordinal} (hp : p < o) : s p hp < a :=
  h.blsub_eq ▸ lt_blsub s p hp

end IsFundamentalSequence

set_option linter.deprecated false in
/-- Every ordinal has a fundamental sequence. -/
@[deprecated exists_isFundamentalSeq (since := "2026-03-23")]
theorem exists_fundamental_sequence (a : Ordinal.{u}) :
    ∃ f, IsFundamentalSequence a a.cof.ord f := by
  suffices h : ∃ o f, IsFundamentalSequence a o f by
    rcases h with ⟨o, f, hf⟩
    exact ⟨_, hf.ord_cof⟩
  rcases exists_lsub_cof a with ⟨ι, f, hf, hι⟩
  rcases ord_eq ι with ⟨r, wo, hr⟩
  let r' := Subrel r fun i ↦ ∀ j, r j i → f j < f i
  let hrr' : r' ↪r r := Subrel.relEmbedding _ _
  haveI := hrr'.isWellOrder
  refine
    ⟨_, _, hrr'.ordinal_type_le.trans ?_, @fun i j _ h _ => (enum r' ⟨j, h⟩).prop _ ?_,
      le_antisymm (blsub_le fun i hi => lsub_le_iff.1 hf.le _) ?_⟩
  · rw [← hι, hr]
  · change r (hrr'.1 _) (hrr'.1 _)
    rwa [hrr'.2, @enum_lt_enum _ r']
  · rw [← hf, lsub_le_iff]
    intro i
    suffices h : ∃ i' hi', f i ≤ bfamilyOfFamily' r' (fun i => f i) i' hi' by
      rcases h with ⟨i', hi', hfg⟩
      exact hfg.trans_lt (lt_blsub _ _ _)
    by_cases! h : ∀ j, r j i → f j < f i
    · refine ⟨typein r' ⟨i, h⟩, typein_lt_type _ _, ?_⟩
      rw [bfamilyOfFamily'_typein]
    · obtain ⟨hji, hij⟩ := wo.wf.min_mem _ h
      refine ⟨typein r' ⟨_, fun k hkj => lt_of_lt_of_le ?_ hij⟩, typein_lt_type _ _, ?_⟩
      · by_contra! H
        exact (wo.wf.not_lt_min {j | r j i ∧ f i ≤ f j} ⟨IsTrans.trans _ _ _ hkj hji, H⟩) hkj
      · rwa [bfamilyOfFamily'_typein]

set_option linter.deprecated false in
@[deprecated IsFundamentalSeq.comp_isNormal (since := "2026-03-23")]
theorem IsFundamentalSequence.of_isNormal {f : Ordinal.{u} → Ordinal.{u}} (hf : IsNormal f)
    {a o} (ha : IsSuccLimit a) {g} (hg : IsFundamentalSequence a o g) :
    IsFundamentalSequence (f a) o fun b hb => f (g b hb) := by
  refine ⟨?_, @fun i j _ _ h => hf.strictMono (hg.2.1 _ _ h), ?_⟩
  · grind [Ordinal.IsFundamentalSequence, cof_map_of_isNormal]
  · rw [@blsub_comp.{u, u, u} a _ (fun b _ => f b) (@fun i j _ _ h => hf.strictMono.monotone h) g
        hg.2.2]
    exact IsNormal.blsub_eq.{u, u} hf ha

@[deprecated (since := "2025-12-25")]
alias IsNormal.isFundamentalSequence := IsFundamentalSequence.of_isNormal

end Ordinal
