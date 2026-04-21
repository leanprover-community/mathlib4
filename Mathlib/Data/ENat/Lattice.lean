/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Nat.Lattice
public import Mathlib.Data.ENat.Basic

/-!
# Extended natural numbers form a complete linear order

This instance is not in `Data.ENat.Basic` to avoid dependency on `Finset`s.

We also restate some lemmas about `WithTop` for `ENat` to have versions that use `Nat.cast` instead
of `WithTop.some`.

-/
set_option backward.defeqAttrib.useBackward true

public section

assert_not_exists Field

open Set

noncomputable section
deriving instance CompleteLinearOrder for ℕ∞
end

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

lemma iInf_eq_coe_iff {f : ι → ℕ∞} {n : ℕ} :
    ⨅ i, f i = n ↔ (∃ i, f i = n) ∧ ∀ i, n ≤ f i := by
  by_cases! hι : IsEmpty ι
  · simp [iInf_of_isEmpty]
  apply ciInf_eq_iff

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

lemma exists_eq_iInf [Nonempty ι] (f : ι → ℕ∞) : ∃ a, f a = ⨅ x, f x :=
  csInf_mem (range_nonempty fun i ↦ f i)

lemma exists_eq_iSup₂_of_lt_top {ι₁ ι₂ : Type*} {f : ι₁ → ι₂ → ℕ∞} [Nonempty ι₁] [Nonempty ι₂]
    (h : ⨆ i, ⨆ j, f i j < ⊤) : ∃ i j, f i j = ⨆ i, ⨆ j, f i j := by
  rw [iSup_prod'] at h ⊢
  exact Prod.exists'.mp (exists_eq_iSup_of_lt_top h)

variable {ι κ : Sort*} {f g : ι → ℕ∞} {s : Set ℕ∞} {a : ℕ∞}

lemma iSup_natCast : ⨆ n : ℕ, (n : ℕ∞) = ⊤ :=
  (iSup_eq_top _).2 fun _b hb ↦ ENat.exists_nat_gt (lt_top_iff_ne_top.1 hb)

lemma mul_iSup (a : ℕ∞) (f : ι → ℕ∞) : a * ⨆ i, f i = ⨆ i, a * f i := by
  refine (iSup_le fun i ↦ mul_le_mul' rfl.le <| le_iSup_iff.2 fun _ a ↦ a i).antisymm' <|
    le_iSup_iff.2 fun d h ↦ ?_
  obtain rfl | hne := eq_or_ne a 0
  · simp
  obtain hι | hι := isEmpty_or_nonempty ι
  · simp
  cases d with
  | top => simp
  | coe d =>
  have hlt : ⨆ i, f i < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    obtain ⟨i, hi : d < f i⟩ := (iSup_eq_top ..).1 htop d (by simp)
    exact (((h i).trans_lt hi).trans_le (ENat.self_le_mul_left _ hne)).false
  obtain ⟨j, hj⟩ := exists_eq_iSup_of_lt_top hlt
  rw [← hj]
  apply h

lemma iSup_mul (f : ι → ℕ∞) (a : ℕ∞) : (⨆ i, f i) * a = ⨆ i, f i * a := by
  simp_rw [mul_comm, ENat.mul_iSup]

lemma mul_sSup : a * sSup s = ⨆ b ∈ s, a * b := by
  simp_rw [sSup_eq_iSup, mul_iSup]

lemma sSup_mul : sSup s * a = ⨆ b ∈ s, b * a := by
  simp_rw [mul_comm, mul_sSup]

lemma mul_iInf [Nonempty ι] : a * ⨅ i, f i = ⨅ i, a * f i := by
  refine (le_iInf fun x ↦ by grw [iInf_le]).antisymm ?_
  obtain ⟨b, hb⟩ := ENat.exists_eq_iInf f
  rw [← hb, iInf_le_iff]
  exact fun x h ↦ h _

lemma iInf_mul [Nonempty ι] : (⨅ i, f i) * a = ⨅ i, f i * a := by
  simp_rw [mul_comm, mul_iInf]

/-- A version of `mul_iInf` with a slightly more general hypothesis. -/
lemma mul_iInf' (h₀ : a = 0 → Nonempty ι) : a * ⨅ i, f i = ⨅ i, a * f i := by
  obtain hι | hι := isEmpty_or_nonempty ι
  · suffices a ≠ 0 by simpa [iInf_of_empty, ite_eq_right_iff, mul_top']
    aesop
  rw [mul_iInf]

/-- A version of `iInf_mul` with a slightly more general hypothesis. -/
lemma iInf_mul' (h₀ : a = 0 → Nonempty ι) : (⨅ i, f i) * a = ⨅ i, f i * a := by
  simp_rw [mul_comm, mul_iInf' h₀]

/-- If `a ≠ 0`, then right multiplication by `a` maps infimum to infimum.
See also `ENat.iInf_mul` that assumes `[Nonempty ι]` but does not require `a ≠ 0`. -/
lemma mul_iInf_of_ne (ha₀ : a ≠ 0) : a * ⨅ i, f i = ⨅ i, a * f i :=
  mul_iInf' <| by simp [ha₀]

/-- If `a ≠ 0`, then right multiplication by `a` maps infimum to infimum.
See also `ENat.iInf_mul` that assumes `[Nonempty ι]` but does not require `a ≠ 0`. -/
lemma iInf_mul_of_ne (ha₀ : a ≠ 0) : (⨅ i, f i) * a = ⨅ i, f i * a :=
  iInf_mul' <| by simp [ha₀]

lemma add_iSup [Nonempty ι] (f : ι → ℕ∞) : a + ⨆ i, f i = ⨆ i, a + f i := by
  obtain rfl | ha := eq_or_ne a ⊤
  · simp
  refine le_antisymm ?_ <| iSup_le fun i ↦ by grw [← le_iSup]
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

lemma iSup_add_iSup_of_monotone {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {f g : ι → ℕ∞}
    (hf : Monotone f) (hg : Monotone g) : iSup f + iSup g = ⨆ a, f a + g a :=
  iSup_add_iSup fun i j ↦ (exists_ge_ge i j).imp fun _k ⟨hi, hj⟩ ↦ by gcongr <;> apply_rules

lemma smul_iSup {R} [SMul R ℕ∞] [IsScalarTower R ℕ∞ ℕ∞] (f : ι → ℕ∞) (c : R) :
    c • ⨆ i, f i = ⨆ i, c • f i := by
  simpa using mul_iSup (c • 1) f

lemma smul_sSup {R} [SMul R ℕ∞] [IsScalarTower R ℕ∞ ℕ∞] (s : Set ℕ∞) (c : R) :
    c • sSup s = ⨆ a ∈ s, c • a := by
  simp_rw [sSup_eq_iSup, smul_iSup]

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

lemma iInf_add : iInf f + a = ⨅ i, f i + a :=
  le_antisymm (le_iInf fun _ ↦ add_le_add (iInf_le _ _) le_rfl) <|
    (tsub_le_iff_right.1 <| le_iInf fun _ ↦ tsub_le_iff_right.2 <| iInf_le _ _)

theorem sub_iInf : (a - ⨅ i, f i) = ⨆ i, a - f i := by
  refine eq_of_forall_ge_iff fun c => ?_
  rw [tsub_le_iff_right, add_comm, iInf_add]
  simp [tsub_le_iff_right, add_comm]

theorem sInf_add {s : Set ℕ∞} : sInf s + a = ⨅ b ∈ s, b + a := by simp [sInf_eq_iInf, iInf_add]

theorem add_iInf {a : ℕ∞} : a + iInf f = ⨅ b, a + f b := by
  rw [add_comm, iInf_add]; simp [add_comm]

theorem iInf_add_iInf (h : ∀ i j, ∃ k, f k + g k ≤ f i + g j) : iInf f + iInf g = ⨅ a, f a + g a :=
  suffices ⨅ a, f a + g a ≤ iInf f + iInf g from
    le_antisymm (le_iInf fun _ => add_le_add (iInf_le _ _) (iInf_le _ _)) this
  calc
    ⨅ a, f a + g a ≤ ⨅ (a) (a'), f a + g a' :=
      le_iInf₂ fun a a' => let ⟨k, h⟩ := h a a'; iInf_le_of_le k h
    _ = iInf f + iInf g := by simp_rw [iInf_add, add_iInf]

lemma iInf_add_iInf_of_monotone {ι : Type*} [Preorder ι] [IsCodirectedOrder ι] {f g : ι → ℕ∞}
    (hf : Monotone f) (hg : Monotone g) : iInf f + iInf g = ⨅ a, f a + g a :=
  iInf_add_iInf fun i j ↦ (exists_le_le i j).imp fun _k ⟨hi, hj⟩ ↦ by gcongr <;> apply_rules

lemma add_iInf₂ {κ : ι → Sort*} (f : (i : ι) → κ i → ℕ∞) :
    a + ⨅ (i) (j), f i j = ⨅ (i) (j), a + f i j := by
  simp [add_iInf]

lemma iInf₂_add {κ : ι → Sort*} (f : (i : ι) → κ i → ℕ∞) :
    (⨅ (i) (j), f i j) + a = ⨅ (i) (j), f i j + a := by
  simp only [add_comm, add_iInf₂]

lemma add_sInf {s : Set ℕ∞} : a + sInf s = ⨅ b ∈ s, a + b := by
  rw [sInf_eq_iInf, add_iInf₂]

variable {κ : Sort*}

lemma le_iInf_add_iInf {g : κ → ℕ∞} (h : ∀ i j, a ≤ f i + g j) :
    a ≤ iInf f + iInf g := by
  simp_rw [iInf_add, add_iInf]; exact le_iInf₂ h

lemma le_iInf₂_add_iInf₂ {q₁ : ι → Sort*} {q₂ : κ → Sort*}
    {f : (i : ι) → q₁ i → ℕ∞} {g : (k : κ) → q₂ k → ℕ∞}
    (h : ∀ i pi k qk, a ≤ f i pi + g k qk) :
    a ≤ (⨅ (i) (qi), f i qi) + ⨅ (k) (qk), g k qk := by
  simp_rw [iInf₂_add, add_iInf₂]
  exact le_iInf₂ fun i hi => le_iInf₂ (h i hi)

end ENat
