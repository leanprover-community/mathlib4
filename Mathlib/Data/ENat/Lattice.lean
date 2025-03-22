/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.ENat.Basic
import Mathlib.Algebra.Group.Action.Defs

/-!
# Extended natural numbers form a complete linear order

This instance is not in `Data.ENat.Basic` to avoid dependency on `Finset`s.

We also restate some lemmas about `WithTop` for `ENat` to have versions that use `Nat.cast` instead
of `WithTop.some`.

## TODO

Currently (2024-Nov-12), `shake` does not check `proof_wanted` and insist that
`Mathlib.Algebra.Group.Action.Defs` should not be imported. Once `shake` is fixed, please remove the
corresponding `noshake.json` entry.

-/

assert_not_exists Field

open Set

-- The `CompleteLinearOrder` instance should be constructed by a deriving handler.
-- https://github.com/leanprover-community/mathlib4/issues/380

-- `noncomputable` through 'Nat.instConditionallyCompleteLinearOrderBotNat'
noncomputable instance : CompleteLinearOrder ENat :=
  inferInstanceAs (CompleteLinearOrder (WithTop ℕ))

noncomputable instance : CompleteLinearOrder (WithBot ENat) :=
  inferInstanceAs (CompleteLinearOrder (WithBot (WithTop ℕ)))

namespace ENat
variable {ι : Sort*} {f : ι → ℕ} {s : Set ℕ}

lemma iSup_coe_eq_top : ⨆ i, (f i : ℕ∞) = ⊤ ↔ ¬ BddAbove (range f) := WithTop.iSup_coe_eq_top
lemma iSup_coe_ne_top : ⨆ i, (f i : ℕ∞) ≠ ⊤ ↔ BddAbove (range f) := iSup_coe_eq_top.not_left
lemma iSup_coe_lt_top : ⨆ i, (f i : ℕ∞) < ⊤ ↔ BddAbove (range f) := WithTop.iSup_coe_lt_top
lemma iInf_coe_eq_top : ⨅ i, (f i : ℕ∞) = ⊤ ↔ IsEmpty ι := WithTop.iInf_coe_eq_top
lemma iInf_coe_ne_top : ⨅ i, (f i : ℕ∞) ≠ ⊤ ↔ Nonempty ι := by
  rw [Ne, iInf_coe_eq_top, not_isEmpty_iff]
lemma iInf_coe_lt_top : ⨅ i, (f i : ℕ∞) < ⊤ ↔ Nonempty ι := WithTop.iInf_coe_lt_top

lemma coe_sSup : BddAbove s → ↑(sSup s) = ⨆ a ∈ s, (a : ℕ∞) := WithTop.coe_sSup

lemma coe_sInf (hs : s.Nonempty) : ↑(sInf s) = ⨅ a ∈ s, (a : ℕ∞) :=
  WithTop.coe_sInf hs (OrderBot.bddBelow s)

lemma coe_iSup : BddAbove (range f) → ↑(⨆ i, f i) = ⨆ i, (f i : ℕ∞) := WithTop.coe_iSup _

@[norm_cast] lemma coe_iInf [Nonempty ι] : ↑(⨅ i, f i) = ⨅ i, (f i : ℕ∞) :=
  WithTop.coe_iInf (OrderBot.bddBelow _)

@[simp]
lemma iInf_eq_top_of_isEmpty [IsEmpty ι] : ⨅ i, (f i : ℕ∞) = ⊤ :=
  iInf_coe_eq_top.mpr ‹_›

lemma iInf_toNat : (⨅ i, (f i : ℕ∞)).toNat = ⨅ i, f i := by
  cases isEmpty_or_nonempty ι
  · simp
  · norm_cast

@[simp] lemma iInf_eq_zero {f : ι → ℕ∞} : ⨅ i, f i = 0 ↔ ∃ i, f i = 0 := by
  simpa [lt_one_iff_eq_zero] using iInf_lt_iff (α := ℕ∞) (a := 1)

variable {f : ι → ℕ∞} {s : Set ℕ∞}

lemma sSup_eq_zero : sSup s = 0 ↔ ∀ a ∈ s, a = 0 :=
  sSup_eq_bot

lemma sInf_eq_zero : sInf s = 0 ↔ 0 ∈ s := by
  rw [← lt_one_iff_eq_zero]
  simp only [sInf_lt_iff, lt_one_iff_eq_zero, exists_eq_right]

lemma sSup_eq_zero' : sSup s = 0 ↔ s = ∅ ∨ s = {0} :=
  sSup_eq_bot'

@[simp] lemma iSup_eq_zero : iSup f = 0 ↔ ∀ i, f i = 0 := iSup_eq_bot
@[simp] lemma iSup_zero : ⨆ _ : ι, (0 : ℕ∞) = 0 := by simp

lemma sSup_eq_top_of_infinite (h : s.Infinite) : sSup s = ⊤ := by
  apply (sSup_eq_top ..).mpr
  intro x hx
  cases x with
  | top => simp at hx
  | coe x =>
    contrapose! h
    simp only [not_infinite]
    apply Finite.subset <| Finite.Set.finite_image {n : ℕ | n ≤ x} (fun (n : ℕ) => (n : ℕ∞))
    intro y hy
    specialize h y hy
    have hxt : y < ⊤ := lt_of_le_of_lt h hx
    use y.toNat
    simp [toNat_le_of_le_coe h, LT.lt.ne_top hxt]

lemma finite_of_sSup_lt_top (h : sSup s < ⊤) : s.Finite := by
  contrapose! h
  simp only [top_le_iff]
  exact sSup_eq_top_of_infinite h

lemma sSup_mem_of_nonempty_of_lt_top [Nonempty s] (hs' : sSup s < ⊤) : sSup s ∈ s :=
  Nonempty.csSup_mem .of_subtype (finite_of_sSup_lt_top hs')

lemma exists_eq_iSup_of_lt_top [Nonempty ι] (h : ⨆ i, f i < ⊤) :
    ∃ i, f i = ⨆ i, f i :=
  sSup_mem_of_nonempty_of_lt_top h

lemma exists_eq_iSup₂_of_lt_top {ι₁ ι₂ : Type*} {f : ι₁ → ι₂ → ℕ∞} [Nonempty ι₁] [Nonempty ι₂]
    (h : ⨆ i, ⨆ j, f i j < ⊤) : ∃ i j, f i j = ⨆ i, ⨆ j, f i j := by
  rw [iSup_prod'] at h ⊢
  exact Prod.exists'.mp (exists_eq_iSup_of_lt_top h)

variable {ι κ : Sort*} {f g : ι → ℕ∞} {s : Set ℕ∞} {a : ℕ∞}

lemma iSup_natCast : ⨆ n : ℕ, (n : ℕ∞) = ⊤ :=
  (iSup_eq_top _).2 fun _b hb ↦ ENat.exists_nat_gt (lt_top_iff_ne_top.1 hb)

proof_wanted mul_iSup (a : ℕ∞) (f : ι → ℕ∞) : a * ⨆ i, f i = ⨆ i, a * f i
proof_wanted iSup_mul (f : ι → ℕ∞) (a : ℕ∞) : (⨆ i, f i) * a = ⨆ i, f i * a
proof_wanted mul_sSup : a * sSup s = ⨆ b ∈ s, a * b
proof_wanted sSup_mul : sSup s * a = ⨆ b ∈ s, b * a

proof_wanted mul_iInf' (_h₀ : a = 0 → Nonempty ι) :
    a * ⨅ i, f i = ⨅ i, a * f i

proof_wanted iInf_mul' (_h₀ : a = 0 → Nonempty ι) : (⨅ i, f i) * a = ⨅ i, f i * a

/-- If `a ≠ 0` and `a ≠ ⊤`, then right multiplication by `a` maps infimum to infimum.
See also `ENNReal.iInf_mul` that assumes `[Nonempty ι]` but does not require `a ≠ 0`. -/
proof_wanted mul_iInf_of_ne (_ha₀ : a ≠ 0) (_ha : a ≠ ⊤) : a * ⨅ i, f i = ⨅ i, a * f i

/-- If `a ≠ 0` and `a ≠ ⊤`, then right multiplication by `a` maps infimum to infimum.
See also `ENNReal.iInf_mul` that assumes `[Nonempty ι]` but does not require `a ≠ 0`. -/
proof_wanted iInf_mul_of_ne (_ha₀ : a ≠ 0) (_ha : a ≠ ⊤) : (⨅ i, f i) * a = ⨅ i, f i * a

proof_wanted mul_iInf [Nonempty ι] : a * ⨅ i, f i = ⨅ i, a * f i
proof_wanted iInf_mul [Nonempty ι] : (⨅ i, f i) * a = ⨅ i, f i * a

lemma add_iSup [Nonempty ι] (f : ι → ℕ∞) : a + ⨆ i, f i = ⨆ i, a + f i := by
  obtain rfl | ha := eq_or_ne a ⊤
  · simp
  refine le_antisymm ?_ <| iSup_le fun i ↦ add_le_add_left (le_iSup ..) _
  refine add_le_of_le_tsub_left_of_le (le_iSup_of_le (Classical.arbitrary _) le_self_add) ?_
  exact iSup_le fun i ↦ ENat.le_sub_of_add_le_left ha <| le_iSup (a + f ·) i

lemma iSup_add [Nonempty ι] (f : ι → ℕ∞) : (⨆ i, f i) + a = ⨆ i, f i + a := by
  simp [add_comm, add_iSup]

lemma add_biSup' {p : ι → Prop} (h : ∃ i, p i) (f : ι → ℕ∞) :
    a + ⨆ i, ⨆ _ : p i, f i = ⨆ i, ⨆ _ : p i, a + f i := by
  haveI : Nonempty {i // p i} := nonempty_subtype.2 h
  simp only [iSup_subtype', add_iSup]

lemma biSup_add' {p : ι → Prop} (h : ∃ i, p i) (f : ι → ℕ∞) :
    (⨆ i, ⨆ _ : p i, f i) + a = ⨆ i, ⨆ _ : p i, f i + a := by simp only [add_comm, add_biSup' h]

lemma add_biSup {ι : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι → ℕ∞) :
    a + ⨆ i ∈ s, f i = ⨆ i ∈ s, a + f i := add_biSup' hs _

lemma biSup_add {ι : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι → ℕ∞) :
    (⨆ i ∈ s, f i) + a = ⨆ i ∈ s, f i + a := biSup_add' hs _

lemma add_sSup (hs : s.Nonempty) : a + sSup s = ⨆ b ∈ s, a + b := by
  rw [sSup_eq_iSup, add_biSup hs]

lemma sSup_add (hs : s.Nonempty) : sSup s + a = ⨆ b ∈ s, b + a := by
  rw [sSup_eq_iSup, biSup_add hs]

lemma iSup_add_iSup_le [Nonempty ι] [Nonempty κ] {g : κ → ℕ∞} (h : ∀ i j, f i + g j ≤ a) :
    iSup f + iSup g ≤ a := by simp_rw [iSup_add, add_iSup]; exact iSup₂_le h

lemma biSup_add_biSup_le' {p : ι → Prop} {q : κ → Prop} (hp : ∃ i, p i) (hq : ∃ j, q j)
    {g : κ → ℕ∞} (h : ∀ i, p i → ∀ j, q j → f i + g j ≤ a) :
    (⨆ i, ⨆ _ : p i, f i) + ⨆ j, ⨆ _ : q j, g j ≤ a := by
  simp_rw [biSup_add' hp, add_biSup' hq]
  exact iSup₂_le fun i hi => iSup₂_le (h i hi)

lemma biSup_add_biSup_le {ι κ : Type*} {s : Set ι} {t : Set κ} (hs : s.Nonempty) (ht : t.Nonempty)
    {f : ι → ℕ∞} {g : κ → ℕ∞} {a : ℕ∞} (h : ∀ i ∈ s, ∀ j ∈ t, f i + g j ≤ a) :
    (⨆ i ∈ s, f i) + ⨆ j ∈ t, g j ≤ a := biSup_add_biSup_le' hs ht h

lemma iSup_add_iSup (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) : iSup f + iSup g = ⨆ i, f i + g i := by
  cases isEmpty_or_nonempty ι
  · simp only [iSup_of_empty, bot_eq_zero, zero_add]
  · refine le_antisymm ?_ (iSup_le fun a => add_le_add (le_iSup _ _) (le_iSup _ _))
    refine iSup_add_iSup_le fun i j => ?_
    rcases h i j with ⟨k, hk⟩
    exact le_iSup_of_le k hk

lemma iSup_add_iSup_of_monotone {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] {f g : ι → ℕ∞}
    (hf : Monotone f) (hg : Monotone g) : iSup f + iSup g = ⨆ a, f a + g a :=
  iSup_add_iSup fun i j ↦ (exists_ge_ge i j).imp fun _k ⟨hi, hj⟩ ↦ by gcongr <;> apply_rules

proof_wanted smul_iSup {R} [SMul R ℕ∞] [IsScalarTower R ℕ∞ ℕ∞] (f : ι → ℕ∞) (c : R) :
    c • ⨆ i, f i = ⨆ i, c • f i

proof_wanted smul_sSup {R} [SMul R ℕ∞] [IsScalarTower R ℕ∞ ℕ∞] (s : Set ℕ∞) (c : R) :
    c • sSup s = ⨆ a ∈ s, c • a

lemma sub_iSup [Nonempty ι] (ha : a ≠ ⊤) : a - ⨆ i, f i = ⨅ i, a - f i := by
  obtain ⟨i, hi⟩ | h := em (∃ i, a < f i)
  · rw [tsub_eq_zero_iff_le.2 <| le_iSup_of_le _ hi.le, (iInf_eq_bot _).2, bot_eq_zero]
    exact fun x hx ↦ ⟨i, by simpa [hi.le, tsub_eq_zero_of_le]⟩
  simp_rw [not_exists, not_lt] at h
  refine le_antisymm (le_iInf fun i ↦ tsub_le_tsub_left (le_iSup ..) _) <|
    ENat.le_sub_of_add_le_left (ne_top_of_le_ne_top ha <| iSup_le h) <|
    add_le_of_le_tsub_right_of_le (iInf_le_of_le (Classical.arbitrary _) tsub_le_self) <|
    iSup_le fun i ↦ ?_
  rw [← ENat.sub_sub_cancel ha (h _)]
  exact tsub_le_tsub_left (iInf_le (a - f ·) i) _
end ENat

namespace WithBot

lemma coe_unbotD_iSup {ι : Sort*} [Nonempty ι] {f : ι → WithBot ℕ∞} (ex : ∃ i, f i ≠ ⊥) :
    ⨆ i, f i = ⨆ i, (WithBot.unbotD 0 (f i) : ℕ∞) := by
  rw[WithBot.coe_iSup]
  · rw[iSup_eq_of_forall_le_of_forall_lt_exists_gt]
    · intro i
      by_cases o : (f i = ⊥)
      · rw[o]; simp
      · have : ↑(WithBot.unbotD 0 (f i)) = f i := by
          cases k : (f i)
          · contradiction
          · exact rfl
        rw[← this]
        exact le_iSup_iff.mpr fun b a ↦ a i
    · intro w hw
      obtain ⟨i, hi⟩ := lt_iSup_iff.mp hw
      by_cases o : (f i = ⊥)
      · obtain ⟨j, hj⟩ := ex
        use j
        have : f j ≥ 0 := by
          cases k : (f j)
          · contradiction
          · simp
        apply lt_of_lt_of_le (b := 0)
        · simp[o] at hi
          assumption
        · exact this
      · use i
        simp_all
        have : ↑(WithBot.unbotD 0 (f i)) = f i := by
          cases k : (f i)
          · contradiction
          · rename_i a
            exact rfl
        rw[←this]
        exact hi
  · exact OrderTop.bddAbove (Set.range fun i ↦ WithBot.unbotD 0 (f i))

lemma add_iSup {ι : Sort*} [Nonempty ι] {a : WithBot ℕ∞} (f : ι → WithBot ℕ∞) :
    a + ⨆ i, f i = ⨆ i, a + f i := by
  refine le_antisymm ?_ <| iSup_le fun i ↦ add_le_add_left (le_iSup ..) _
  obtain m | hf := eq_or_ne (⨆ i, f i) ⊥
  · simp[m]
  cases a
  · simp
  · rename_i a
    let g : ι → ℕ∞ := fun i ↦ WithBot.unbotD 0 (f i)
    have h1 : ∀ i, unbotD 0 (f i) = f i ∨ f i = ⊥ := by
      intro i
      cases (f i)
      · exact add_eq_bot.mp rfl
      · exact unbotD_eq_self_iff.mp rfl
    have enatStat := ENat.add_iSup (fun i ↦ WithBot.unbotD 0 (f i)) (a := a)
    simp at hf
    rw[coe_unbotD_iSup hf]
    obtain ⟨x, hx⟩ := hf
    simp[WithBot.ne_bot_iff_exists] at hx
    obtain ⟨fx, hfx⟩ := hx

    rw[← WithBot.coe_add, enatStat, WithBot.coe_iSup]
    · simp only [coe_add, iSup_le_iff]
      intro i
      obtain h | h := h1 i
      · rw[h]
        exact le_iSup_iff.mpr fun b a ↦ a i
      · simp[h]
        refine le_iSup_iff.mpr ?_
        intro b j
        specialize j x
        have : unbotD 0 (f x) = f x := by
          nth_rw 2 [←(WithBot.unbotD_coe 0 (f x))]
          rw[←hfx]
          rfl
        have : f x ≥ 0 := by
          rw[←hfx]
          simp[zero_le fx]
        exact le_trans (b := (↑a + f x)) (le_add_of_nonneg_right this) j
    · exact OrderTop.bddAbove (Set.range fun i ↦ a + unbotD 0 (f i))


lemma iSup_add {ι : Sort*} [Nonempty ι] {a : WithBot ℕ∞} (f : ι → WithBot ℕ∞) :
    (⨆ i, f i) + a = ⨆ i, f i + a := by simp [add_comm, WithBot.add_iSup]

theorem iSup_le_add {ι ι': Sort*} [Nonempty ι] [Nonempty ι']
  {f : ι → WithBot ℕ∞} {g : ι' → WithBot ℕ∞} {a : WithBot ℕ∞} :
iSup f + iSup g ≤ a ↔ ∀ (i: ι) (j : ι'), f i + g j ≤ a := by
  simp_rw [WithBot.iSup_add, WithBot.add_iSup]
  exact iSup₂_le_iff

end WithBot
