/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite

#align_import combinatorics.configuration from "leanprover-community/mathlib"@"d2d8742b0c21426362a9dacebc6005db895ca963"

/-!
# Configurations of Points and lines
This file introduces abstract configurations of points and lines, and proves some basic properties.

## Main definitions
* `Configuration.Nondegenerate`: Excludes certain degenerate configurations,
  and imposes uniqueness of intersection points.
* `Configuration.HasPoints`: A nondegenerate configuration in which
  every pair of lines has an intersection point.
* `Configuration.HasLines`:  A nondegenerate configuration in which
  every pair of points has a line through them.
* `Configuration.lineCount`: The number of lines through a given point.
* `Configuration.pointCount`: The number of lines through a given line.

## Main statements
* `Configuration.HasLines.card_le`: `HasLines` implies `|P| ≤ |L|`.
* `Configuration.HasPoints.card_le`: `HasPoints` implies `|L| ≤ |P|`.
* `Configuration.HasLines.hasPoints`: `HasLines` and `|P| = |L|` implies `HasPoints`.
* `Configuration.HasPoints.hasLines`: `HasPoints` and `|P| = |L|` implies `HasLines`.
Together, these four statements say that any two of the following properties imply the third:
(a) `HasLines`, (b) `HasPoints`, (c) `|P| = |L|`.

-/


open BigOperators

namespace Configuration

variable (P L : Type*) [Membership P L]

/-- A type synonym. -/
def Dual :=
  P
#align configuration.dual Configuration.Dual

-- porting note: was `this` instead of `h`
instance [h : Inhabited P] : Inhabited (Dual P) :=
  h

instance [Finite P] : Finite (Dual P) :=
  ‹Finite P›

-- porting note: was `this` instead of `h`
instance [h : Fintype P] : Fintype (Dual P) :=
  h

-- porting note: TODO: figure out if this is needed.
set_option synthInstance.checkSynthOrder false in
instance : Membership (Dual L) (Dual P) :=
  ⟨Function.swap (Membership.mem : P → L → Prop)⟩

/-- A configuration is nondegenerate if:
  1) there does not exist a line that passes through all of the points,
  2) there does not exist a point that is on all of the lines,
  3) there is at most one line through any two points,
  4) any two lines have at most one intersection point.
  Conditions 3 and 4 are equivalent. -/
class Nondegenerate : Prop where
  exists_point : ∀ l : L, ∃ p, p ∉ l
  exists_line : ∀ p, ∃ l : L, p ∉ l
  eq_or_eq : ∀ {p₁ p₂ : P} {l₁ l₂ : L}, p₁ ∈ l₁ → p₂ ∈ l₁ → p₁ ∈ l₂ → p₂ ∈ l₂ → p₁ = p₂ ∨ l₁ = l₂
#align configuration.nondegenerate Configuration.Nondegenerate

/-- A nondegenerate configuration in which every pair of lines has an intersection point. -/
class HasPoints extends Nondegenerate P L where
  mkPoint : ∀ {l₁ l₂ : L} (_ : l₁ ≠ l₂), P
  mkPoint_ax : ∀ {l₁ l₂ : L} (h : l₁ ≠ l₂), mkPoint h ∈ l₁ ∧ mkPoint h ∈ l₂
#align configuration.has_points Configuration.HasPoints

/-- A nondegenerate configuration in which every pair of points has a line through them. -/
class HasLines extends Nondegenerate P L where
  mkLine : ∀ {p₁ p₂ : P} (_ : p₁ ≠ p₂), L
  mkLine_ax : ∀ {p₁ p₂ : P} (h : p₁ ≠ p₂), p₁ ∈ mkLine h ∧ p₂ ∈ mkLine h
#align configuration.has_lines Configuration.HasLines

open Nondegenerate

open HasPoints (mkPoint mkPoint_ax)

open HasLines (mkLine mkLine_ax)

instance Dual.Nondegenerate [Nondegenerate P L] : Nondegenerate (Dual L) (Dual P) where
  exists_point := @exists_line P L _ _
  exists_line := @exists_point P L _ _
  eq_or_eq := @fun l₁ l₂ p₁ p₂ h₁ h₂ h₃ h₄ => (@eq_or_eq P L _ _ p₁ p₂ l₁ l₂ h₁ h₃ h₂ h₄).symm

instance Dual.hasLines [HasPoints P L] : HasLines (Dual L) (Dual P) :=
  { Dual.Nondegenerate _ _ with
    mkLine := @mkPoint P L _ _
    mkLine_ax := @mkPoint_ax P L _ _ }

instance Dual.hasPoints [HasLines P L] : HasPoints (Dual L) (Dual P) :=
  { Dual.Nondegenerate _ _ with
    mkPoint := @mkLine P L _ _
    mkPoint_ax := @mkLine_ax P L _ _ }

theorem HasPoints.existsUnique_point [HasPoints P L] (l₁ l₂ : L) (hl : l₁ ≠ l₂) :
    ∃! p, p ∈ l₁ ∧ p ∈ l₂ :=
  ⟨mkPoint hl, mkPoint_ax hl, fun _ hp =>
    (eq_or_eq hp.1 (mkPoint_ax hl).1 hp.2 (mkPoint_ax hl).2).resolve_right hl⟩
#align configuration.has_points.exists_unique_point Configuration.HasPoints.existsUnique_point

theorem HasLines.existsUnique_line [HasLines P L] (p₁ p₂ : P) (hp : p₁ ≠ p₂) :
    ∃! l : L, p₁ ∈ l ∧ p₂ ∈ l :=
  HasPoints.existsUnique_point (Dual L) (Dual P) p₁ p₂ hp
#align configuration.has_lines.exists_unique_line Configuration.HasLines.existsUnique_line

variable {P L}

/-- If a nondegenerate configuration has at least as many points as lines, then there exists
  an injective function `f` from lines to points, such that `f l` does not lie on `l`. -/
theorem Nondegenerate.exists_injective_of_card_le [Nondegenerate P L] [Fintype P] [Fintype L]
    (h : Fintype.card L ≤ Fintype.card P) : ∃ f : L → P, Function.Injective f ∧ ∀ l, f l ∉ l := by
  classical
    let t : L → Finset P := fun l => Set.toFinset { p | p ∉ l }
    suffices ∀ s : Finset L, s.card ≤ (s.biUnion t).card by
      -- Hall's marriage theorem
      obtain ⟨f, hf1, hf2⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp this
      exact ⟨f, hf1, fun l => Set.mem_toFinset.mp (hf2 l)⟩
    intro s
    by_cases hs₀ : s.card = 0
    -- If `s = ∅`, then `s.card = 0 ≤ (s.bUnion t).card`
    · simp_rw [hs₀, zero_le]
    by_cases hs₁ : s.card = 1
    -- If `s = {l}`, then pick a point `p ∉ l`
    · obtain ⟨l, rfl⟩ := Finset.card_eq_one.mp hs₁
      obtain ⟨p, hl⟩ := exists_point l
      rw [Finset.card_singleton, Finset.singleton_biUnion, Nat.one_le_iff_ne_zero]
      exact Finset.card_ne_zero_of_mem (Set.mem_toFinset.mpr hl)
    suffices (s.biUnion t)ᶜ.card ≤ sᶜ.card by
      -- Rephrase in terms of complements (uses `h`)
      rw [Finset.card_compl, Finset.card_compl, tsub_le_iff_left] at this
      replace := h.trans this
      rwa [← add_tsub_assoc_of_le s.card_le_univ, le_tsub_iff_left (le_add_left s.card_le_univ),
        add_le_add_iff_right] at this
    have hs₂ : (s.biUnion t)ᶜ.card ≤ 1 := by
      -- At most one line through two points of `s`
      refine' Finset.card_le_one_iff.mpr @fun p₁ p₂ hp₁ hp₂ => _
      simp_rw [Finset.mem_compl, Finset.mem_biUnion, not_exists, not_and,
        Set.mem_toFinset, Set.mem_setOf_eq, Classical.not_not] at hp₁ hp₂
      obtain ⟨l₁, l₂, hl₁, hl₂, hl₃⟩ :=
        Finset.one_lt_card_iff.mp (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hs₀, hs₁⟩)
      exact (eq_or_eq (hp₁ l₁ hl₁) (hp₂ l₁ hl₁) (hp₁ l₂ hl₂) (hp₂ l₂ hl₂)).resolve_right hl₃
    by_cases hs₃ : sᶜ.card = 0
    · rw [hs₃, le_zero_iff]
      rw [Finset.card_compl, tsub_eq_zero_iff_le, LE.le.le_iff_eq (Finset.card_le_univ _), eq_comm,
        Finset.card_eq_iff_eq_univ] at hs₃ ⊢
      rw [hs₃]
      rw [Finset.eq_univ_iff_forall] at hs₃ ⊢
      exact fun p =>
        Exists.elim (exists_line p)-- If `s = univ`, then show `s.bUnion t = univ`
        fun l hl => Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ l, Set.mem_toFinset.mpr hl⟩
    · exact hs₂.trans (Nat.one_le_iff_ne_zero.mpr hs₃)
#align configuration.nondegenerate.exists_injective_of_card_le Configuration.Nondegenerate.exists_injective_of_card_le

-- If `s < univ`, then consequence of `hs₂`
-- porting note: left out {P} to avoid redundant binder annotation
variable (L)

/-- Number of points on a given line. -/
noncomputable def lineCount (p : P) : ℕ :=
  Nat.card { l : L // p ∈ l }
#align configuration.line_count Configuration.lineCount

variable (P) {L}

/-- Number of lines through a given point. -/
noncomputable def pointCount (l : L) : ℕ :=
  Nat.card { p : P // p ∈ l }
#align configuration.point_count Configuration.pointCount

-- porting note: left out (P) to avoid redundant binder annotation
variable (L)

theorem sum_lineCount_eq_sum_pointCount [Fintype P] [Fintype L] :
    ∑ p : P, lineCount L p = ∑ l : L, pointCount P l := by
  classical
    simp only [lineCount, pointCount, Nat.card_eq_fintype_card, ← Fintype.card_sigma]
    apply Fintype.card_congr
    calc
      (Σp, { l : L // p ∈ l }) ≃ { x : P × L // x.1 ∈ x.2 } :=
        (Equiv.subtypeProdEquivSigmaSubtype (· ∈ ·)).symm
      _ ≃ { x : L × P // x.2 ∈ x.1 } := ((Equiv.prodComm P L).subtypeEquiv fun x => Iff.rfl)
      _ ≃ Σl, { p // p ∈ l } := Equiv.subtypeProdEquivSigmaSubtype fun (l : L) (p : P) => p ∈ l
#align configuration.sum_line_count_eq_sum_point_count Configuration.sum_lineCount_eq_sum_pointCount

variable {P L}

theorem HasLines.pointCount_le_lineCount [HasLines P L] {p : P} {l : L} (h : p ∉ l)
    [Finite { l : L // p ∈ l }] : pointCount P l ≤ lineCount L p := by
  by_cases hf : Infinite { p : P // p ∈ l }
  -- ⊢ pointCount P l ≤ lineCount L p
  · exact (le_of_eq Nat.card_eq_zero_of_infinite).trans (zero_le (lineCount L p))
    -- 🎉 no goals
  haveI := fintypeOfNotInfinite hf
  -- ⊢ pointCount P l ≤ lineCount L p
  cases nonempty_fintype { l : L // p ∈ l }
  -- ⊢ pointCount P l ≤ lineCount L p
  rw [lineCount, pointCount, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  -- ⊢ Fintype.card { p // p ∈ l } ≤ Fintype.card { l // p ∈ l }
  have : ∀ p' : { p // p ∈ l }, p ≠ p' := fun p' hp' => h ((congr_arg (· ∈ l) hp').mpr p'.2)
  -- ⊢ Fintype.card { p // p ∈ l } ≤ Fintype.card { l // p ∈ l }
  exact
    Fintype.card_le_of_injective (fun p' => ⟨mkLine (this p'), (mkLine_ax (this p')).1⟩)
      fun p₁ p₂ hp =>
      Subtype.ext
        ((eq_or_eq p₁.2 p₂.2 (mkLine_ax (this p₁)).2
              ((congr_arg _ (Subtype.ext_iff.mp hp)).mpr (mkLine_ax (this p₂)).2)).resolve_right
          fun h' => (congr_arg (¬p ∈ ·) h').mp h (mkLine_ax (this p₁)).1)
#align configuration.has_lines.point_count_le_line_count Configuration.HasLines.pointCount_le_lineCount

theorem HasPoints.lineCount_le_pointCount [HasPoints P L] {p : P} {l : L} (h : p ∉ l)
    [hf : Finite { p : P // p ∈ l }] : lineCount L p ≤ pointCount P l :=
  @HasLines.pointCount_le_lineCount (Dual L) (Dual P) _ _ l p h hf
#align configuration.has_points.line_count_le_point_count Configuration.HasPoints.lineCount_le_pointCount

variable (P L)

/-- If a nondegenerate configuration has a unique line through any two points, then `|P| ≤ |L|`. -/
theorem HasLines.card_le [HasLines P L] [Fintype P] [Fintype L] :
    Fintype.card P ≤ Fintype.card L := by
  classical
  by_contra hc₂
  obtain ⟨f, hf₁, hf₂⟩ := Nondegenerate.exists_injective_of_card_le (le_of_not_le hc₂)
  have :=
    calc
      ∑ p, lineCount L p = ∑ l, pointCount P l := sum_lineCount_eq_sum_pointCount P L
      _ ≤ ∑ l, lineCount L (f l) :=
        (Finset.sum_le_sum fun l _ => HasLines.pointCount_le_lineCount (hf₂ l))
      _ = ∑ p in Finset.univ.image f, lineCount L p :=
        (Finset.sum_bij (fun l _ => f l) (fun l hl => Finset.mem_image_of_mem f hl)
          (fun l _ => rfl) (fun l₁ l₂ hl₁ hl₂ hl₃ => hf₁ hl₃) fun p => by
          rw [Finset.mem_image]
          exact fun ⟨a, ⟨h, h'⟩⟩ => ⟨a, ⟨h, h'.symm⟩⟩)
      _ < ∑ p, lineCount L p := by
        obtain ⟨p, hp⟩ := not_forall.mp (mt (Fintype.card_le_of_surjective f) hc₂)
        refine'
          Finset.sum_lt_sum_of_subset (Finset.univ.image f).subset_univ (Finset.mem_univ p) _ _
            fun p _ _ => zero_le (lineCount L p)
        · simpa only [Finset.mem_image, exists_prop, Finset.mem_univ, true_and_iff]
        · rw [lineCount, Nat.card_eq_fintype_card, Fintype.card_pos_iff]
          obtain ⟨l, _⟩ := @exists_line P L _ _ p
          exact
            let this := not_exists.mp hp l
            ⟨⟨mkLine this, (mkLine_ax this).2⟩⟩
  exact lt_irrefl _ this
#align configuration.has_lines.card_le Configuration.HasLines.card_le

/-- If a nondegenerate configuration has a unique point on any two lines, then `|L| ≤ |P|`. -/
theorem HasPoints.card_le [HasPoints P L] [Fintype P] [Fintype L] :
    Fintype.card L ≤ Fintype.card P :=
  @HasLines.card_le (Dual L) (Dual P) _ _ _ _
#align configuration.has_points.card_le Configuration.HasPoints.card_le

variable {P L}

theorem HasLines.exists_bijective_of_card_eq [HasLines P L] [Fintype P] [Fintype L]
    (h : Fintype.card P = Fintype.card L) :
    ∃ f : L → P, Function.Bijective f ∧ ∀ l, pointCount P l = lineCount L (f l) := by
  classical
    obtain ⟨f, hf1, hf2⟩ := Nondegenerate.exists_injective_of_card_le (ge_of_eq h)
    have hf3 := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf1, h.symm⟩
    refine'
      ⟨f, hf3, fun l =>
        (Finset.sum_eq_sum_iff_of_le fun l _ => HasLines.pointCount_le_lineCount (hf2 l)).mp
          ((sum_lineCount_eq_sum_pointCount P L).symm.trans
            (Finset.sum_bij (fun l _ => f l) (fun l _ => Finset.mem_univ (f l))
                (fun l _ => refl (lineCount L (f l))) (fun l₁ l₂ hl₁ hl₂ hl => hf1 hl) fun p hp =>
                _).symm)
          l (Finset.mem_univ l)⟩
    obtain ⟨l, rfl⟩ := hf3.2 p
    exact ⟨l, Finset.mem_univ l, rfl⟩
#align configuration.has_lines.exists_bijective_of_card_eq Configuration.HasLines.exists_bijective_of_card_eq

theorem HasLines.lineCount_eq_pointCount [HasLines P L] [Fintype P] [Fintype L]
    (hPL : Fintype.card P = Fintype.card L) {p : P} {l : L} (hpl : p ∉ l) :
    lineCount L p = pointCount P l := by
  classical
    obtain ⟨f, hf1, hf2⟩ := HasLines.exists_bijective_of_card_eq hPL
    let s : Finset (P × L) := Set.toFinset { i | i.1 ∈ i.2 }
    have step1 : ∑ i : P × L, lineCount L i.1 = ∑ i : P × L, pointCount P i.2 := by
      rw [← Finset.univ_product_univ, Finset.sum_product_right, Finset.sum_product]
      simp_rw [Finset.sum_const, Finset.card_univ, hPL, sum_lineCount_eq_sum_pointCount]
    have step2 : ∑ i in s, lineCount L i.1 = ∑ i in s, pointCount P i.2 := by
      rw [s.sum_finset_product Finset.univ fun p => Set.toFinset { l | p ∈ l }]
      rw [s.sum_finset_product_right Finset.univ fun l => Set.toFinset { p | p ∈ l }]
      refine'
        (Finset.sum_bij (fun l _ => f l) (fun l _ => Finset.mem_univ (f l)) (fun l hl => _)
            (fun _ _ _ _ h => hf1.1 h) fun p _ => _).symm
      · simp_rw [Finset.sum_const, Set.toFinset_card, ← Nat.card_eq_fintype_card]
        change pointCount P l • pointCount P l = lineCount L (f l) • lineCount L (f l)
        rw [hf2]
      · obtain ⟨l, hl⟩ := hf1.2 p
        exact ⟨l, Finset.mem_univ l, hl.symm⟩
      all_goals simp_rw [Finset.mem_univ, true_and_iff, Set.mem_toFinset]; exact fun p => Iff.rfl
    have step3 : ∑ i in sᶜ, lineCount L i.1 = ∑ i in sᶜ, pointCount P i.2 := by
      rwa [← s.sum_add_sum_compl, ← s.sum_add_sum_compl, step2, add_left_cancel_iff] at step1
    rw [← Set.toFinset_compl] at step3
    exact
      ((Finset.sum_eq_sum_iff_of_le fun i hi =>
              HasLines.pointCount_le_lineCount (by exact Set.mem_toFinset.mp hi)).mp
          step3.symm (p, l) (Set.mem_toFinset.mpr hpl)).symm
#align configuration.has_lines.line_count_eq_point_count Configuration.HasLines.lineCount_eq_pointCount

theorem HasPoints.lineCount_eq_pointCount [HasPoints P L] [Fintype P] [Fintype L]
    (hPL : Fintype.card P = Fintype.card L) {p : P} {l : L} (hpl : p ∉ l) :
    lineCount L p = pointCount P l :=
  (@HasLines.lineCount_eq_pointCount (Dual L) (Dual P) _ _ _ _ hPL.symm l p hpl).symm
#align configuration.has_points.line_count_eq_point_count Configuration.HasPoints.lineCount_eq_pointCount

/-- If a nondegenerate configuration has a unique line through any two points, and if `|P| = |L|`,
  then there is a unique point on any two lines. -/
noncomputable def HasLines.hasPoints [HasLines P L] [Fintype P] [Fintype L]
    (h : Fintype.card P = Fintype.card L) : HasPoints P L :=
  let this : ∀ l₁ l₂ : L, l₁ ≠ l₂ → ∃ p : P, p ∈ l₁ ∧ p ∈ l₂ := fun l₁ l₂ hl => by
    classical
      obtain ⟨f, _, hf2⟩ := HasLines.exists_bijective_of_card_eq h
      haveI : Nontrivial L := ⟨⟨l₁, l₂, hl⟩⟩
      haveI := Fintype.one_lt_card_iff_nontrivial.mp ((congr_arg _ h).mpr Fintype.one_lt_card)
      have h₁ : ∀ p : P, 0 < lineCount L p := fun p =>
        Exists.elim (exists_ne p) fun q hq =>
          (congr_arg _ Nat.card_eq_fintype_card).mpr
            (Fintype.card_pos_iff.mpr ⟨⟨mkLine hq, (mkLine_ax hq).2⟩⟩)
      have h₂ : ∀ l : L, 0 < pointCount P l := fun l => (congr_arg _ (hf2 l)).mpr (h₁ (f l))
      obtain ⟨p, hl₁⟩ := Fintype.card_pos_iff.mp ((congr_arg _ Nat.card_eq_fintype_card).mp (h₂ l₁))
      by_cases hl₂ : p ∈ l₂
      exact ⟨p, hl₁, hl₂⟩
      have key' : Fintype.card { q : P // q ∈ l₂ } = Fintype.card { l : L // p ∈ l } :=
        ((HasLines.lineCount_eq_pointCount h hl₂).trans Nat.card_eq_fintype_card).symm.trans
          Nat.card_eq_fintype_card
      have : ∀ q : { q // q ∈ l₂ }, p ≠ q := fun q hq => hl₂ ((congr_arg (· ∈ l₂) hq).mpr q.2)
      let f : { q : P // q ∈ l₂ } → { l : L // p ∈ l } := fun q =>
        ⟨mkLine (this q), (mkLine_ax (this q)).1⟩
      have hf : Function.Injective f := fun q₁ q₂ hq =>
        Subtype.ext
          ((eq_or_eq q₁.2 q₂.2 (mkLine_ax (this q₁)).2
                ((congr_arg _ (Subtype.ext_iff.mp hq)).mpr (mkLine_ax (this q₂)).2)).resolve_right
            fun h => (congr_arg (¬p ∈ ·) h).mp hl₂ (mkLine_ax (this q₁)).1)
      have key' := ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, key'⟩).2
      obtain ⟨q, hq⟩ := key' ⟨l₁, hl₁⟩
      exact ⟨q, (congr_arg _ (Subtype.ext_iff.mp hq)).mp (mkLine_ax (this q)).2, q.2⟩
  { ‹HasLines P L› with
    mkPoint := fun {l₁ l₂} hl => Classical.choose (this l₁ l₂ hl)
    mkPoint_ax := fun {l₁ l₂} hl => Classical.choose_spec (this l₁ l₂ hl) }
#align configuration.has_lines.has_points Configuration.HasLines.hasPoints

/-- If a nondegenerate configuration has a unique point on any two lines, and if `|P| = |L|`,
  then there is a unique line through any two points. -/
noncomputable def HasPoints.hasLines [HasPoints P L] [Fintype P] [Fintype L]
    (h : Fintype.card P = Fintype.card L) : HasLines P L :=
  let this := @HasLines.hasPoints (Dual L) (Dual P) _ _ _ _ h.symm
  { ‹HasPoints P L› with
    mkLine := @fun _ _ => this.mkPoint
    mkLine_ax := @fun _ _ => this.mkPoint_ax }
#align configuration.has_points.has_lines Configuration.HasPoints.hasLines

variable (P L)

/-- A projective plane is a nondegenerate configuration in which every pair of lines has
  an intersection point, every pair of points has a line through them,
  and which has three points in general position. -/
class ProjectivePlane extends HasPoints P L, HasLines P L where
  exists_config :
    ∃ (p₁ p₂ p₃ : P) (l₁ l₂ l₃ : L),
      p₁ ∉ l₂ ∧ p₁ ∉ l₃ ∧ p₂ ∉ l₁ ∧ p₂ ∈ l₂ ∧ p₂ ∈ l₃ ∧ p₃ ∉ l₁ ∧ p₃ ∈ l₂ ∧ p₃ ∉ l₃
#align configuration.projective_plane Configuration.ProjectivePlane

namespace ProjectivePlane

variable [ProjectivePlane P L]

instance : ProjectivePlane (Dual L) (Dual P) :=
  { Dual.hasPoints _ _, Dual.hasLines _ _ with
    exists_config :=
      let ⟨p₁, p₂, p₃, l₁, l₂, l₃, h₁₂, h₁₃, h₂₁, h₂₂, h₂₃, h₃₁, h₃₂, h₃₃⟩ := @exists_config P L _ _
      ⟨l₁, l₂, l₃, p₁, p₂, p₃, h₂₁, h₃₁, h₁₂, h₂₂, h₃₂, h₁₃, h₂₃, h₃₃⟩ }

/-- The order of a projective plane is one less than the number of lines through an arbitrary point.
Equivalently, it is one less than the number of points on an arbitrary line. -/
noncomputable def order : ℕ :=
  lineCount L (Classical.choose (@exists_config P L _ _)) - 1
#align configuration.projective_plane.order Configuration.ProjectivePlane.order

theorem card_points_eq_card_lines [Fintype P] [Fintype L] : Fintype.card P = Fintype.card L :=
  le_antisymm (HasLines.card_le P L) (HasPoints.card_le P L)
#align configuration.projective_plane.card_points_eq_card_lines Configuration.ProjectivePlane.card_points_eq_card_lines

-- porting note: left out (L) to avoid redundant binder annotation
variable {P}

theorem lineCount_eq_lineCount [Finite P] [Finite L] (p q : P) : lineCount L p = lineCount L q := by
  cases nonempty_fintype P
  -- ⊢ lineCount L p = lineCount L q
  cases nonempty_fintype L
  -- ⊢ lineCount L p = lineCount L q
  obtain ⟨p₁, p₂, p₃, l₁, l₂, l₃, h₁₂, h₁₃, h₂₁, h₂₂, h₂₃, h₃₁, h₃₂, h₃₃⟩ := @exists_config P L _ _
  -- ⊢ lineCount L p = lineCount L q
  have h := card_points_eq_card_lines P L
  -- ⊢ lineCount L p = lineCount L q
  let n := lineCount L p₂
  -- ⊢ lineCount L p = lineCount L q
  have hp₂ : lineCount L p₂ = n := rfl
  -- ⊢ lineCount L p = lineCount L q
  have hl₁ : pointCount P l₁ = n := (HasLines.lineCount_eq_pointCount h h₂₁).symm.trans hp₂
  -- ⊢ lineCount L p = lineCount L q
  have hp₃ : lineCount L p₃ = n := (HasLines.lineCount_eq_pointCount h h₃₁).trans hl₁
  -- ⊢ lineCount L p = lineCount L q
  have hl₃ : pointCount P l₃ = n := (HasLines.lineCount_eq_pointCount h h₃₃).symm.trans hp₃
  -- ⊢ lineCount L p = lineCount L q
  have hp₁ : lineCount L p₁ = n := (HasLines.lineCount_eq_pointCount h h₁₃).trans hl₃
  -- ⊢ lineCount L p = lineCount L q
  have hl₂ : pointCount P l₂ = n := (HasLines.lineCount_eq_pointCount h h₁₂).symm.trans hp₁
  -- ⊢ lineCount L p = lineCount L q
  suffices ∀ p : P, lineCount L p = n by exact (this p).trans (this q).symm
  -- ⊢ ∀ (p : P), lineCount L p = n
  refine' fun p =>
    or_not.elim (fun h₂ => _) fun h₂ => (HasLines.lineCount_eq_pointCount h h₂).trans hl₂
  refine' or_not.elim (fun h₃ => _) fun h₃ => (HasLines.lineCount_eq_pointCount h h₃).trans hl₃
  -- ⊢ lineCount L p = n
  rw [(eq_or_eq h₂ h₂₂ h₃ h₂₃).resolve_right fun h =>
      h₃₃ ((congr_arg (Membership.mem p₃) h).mp h₃₂)]
#align configuration.projective_plane.line_count_eq_line_count Configuration.ProjectivePlane.lineCount_eq_lineCount

variable (P) {L}

theorem pointCount_eq_pointCount [Finite P] [Finite L] (l m : L) :
    pointCount P l = pointCount P m := by
  apply lineCount_eq_lineCount (Dual P)
  -- 🎉 no goals
#align configuration.projective_plane.point_count_eq_point_count Configuration.ProjectivePlane.pointCount_eq_pointCount

-- porting note: left out {L} to avoid redundant binder annotation
variable {P}

theorem lineCount_eq_pointCount [Finite P] [Finite L] (p : P) (l : L) :
    lineCount L p = pointCount P l :=
  Exists.elim (exists_point l) fun q hq =>
    (lineCount_eq_lineCount L p q).trans <| by
      cases nonempty_fintype P
      -- ⊢ lineCount L q = pointCount P l
      cases nonempty_fintype L
      -- ⊢ lineCount L q = pointCount P l
      exact HasLines.lineCount_eq_pointCount (card_points_eq_card_lines P L) hq
      -- 🎉 no goals
#align configuration.projective_plane.line_count_eq_point_count Configuration.ProjectivePlane.lineCount_eq_pointCount

variable (P L)

theorem Dual.order [Finite P] [Finite L] : order (Dual L) (Dual P) = order P L :=
  congr_arg (fun n => n - 1) (lineCount_eq_pointCount _ _)
#align configuration.projective_plane.dual.order Configuration.ProjectivePlane.Dual.order

-- porting note: left out (L) to avoid redundant binder annotation
variable {P}

theorem lineCount_eq [Finite P] [Finite L] (p : P) : lineCount L p = order P L + 1 := by
  classical
    obtain ⟨q, -, -, l, -, -, -, -, h, -⟩ := Classical.choose_spec (@exists_config P L _ _)
    cases nonempty_fintype { l : L // q ∈ l }
    rw [order, lineCount_eq_lineCount L p q, lineCount_eq_lineCount L (Classical.choose _) q,
      lineCount, Nat.card_eq_fintype_card, Nat.sub_add_cancel]
    exact Fintype.card_pos_iff.mpr ⟨⟨l, h⟩⟩
#align configuration.projective_plane.line_count_eq Configuration.ProjectivePlane.lineCount_eq

variable (P) {L}

theorem pointCount_eq [Finite P] [Finite L] (l : L) : pointCount P l = order P L + 1 :=
  (lineCount_eq (Dual P) _).trans (congr_arg (fun n => n + 1) (Dual.order P L))
#align configuration.projective_plane.point_count_eq Configuration.ProjectivePlane.pointCount_eq

variable (L)

theorem one_lt_order [Finite P] [Finite L] : 1 < order P L := by
  obtain ⟨p₁, p₂, p₃, l₁, l₂, l₃, -, -, h₂₁, h₂₂, h₂₃, h₃₁, h₃₂, h₃₃⟩ := @exists_config P L _ _
  -- ⊢ 1 < order P L
  cases nonempty_fintype { p : P // p ∈ l₂ }
  -- ⊢ 1 < order P L
  rw [← add_lt_add_iff_right 1, ← pointCount_eq _ l₂, pointCount, Nat.card_eq_fintype_card,
    Fintype.two_lt_card_iff]
  simp_rw [Ne, Subtype.ext_iff]
  -- ⊢ ∃ a b c, ¬↑a = ↑b ∧ ¬↑a = ↑c ∧ ¬↑b = ↑c
  have h := mkPoint_ax fun h => h₂₁ ((congr_arg _ h).mpr h₂₂)
  -- ⊢ ∃ a b c, ¬↑a = ↑b ∧ ¬↑a = ↑c ∧ ¬↑b = ↑c
  exact
    ⟨⟨mkPoint _, h.2⟩, ⟨p₂, h₂₂⟩, ⟨p₃, h₃₂⟩, ne_of_mem_of_not_mem h.1 h₂₁,
      ne_of_mem_of_not_mem h.1 h₃₁, ne_of_mem_of_not_mem h₂₃ h₃₃⟩
#align configuration.projective_plane.one_lt_order Configuration.ProjectivePlane.one_lt_order

variable {P}

theorem two_lt_lineCount [Finite P] [Finite L] (p : P) : 2 < lineCount L p := by
  simpa only [lineCount_eq L p, Nat.succ_lt_succ_iff] using one_lt_order P L
  -- 🎉 no goals
#align configuration.projective_plane.two_lt_line_count Configuration.ProjectivePlane.two_lt_lineCount

variable (P) {L}

theorem two_lt_pointCount [Finite P] [Finite L] (l : L) : 2 < pointCount P l := by
  simpa only [pointCount_eq P l, Nat.succ_lt_succ_iff] using one_lt_order P L
  -- 🎉 no goals
#align configuration.projective_plane.two_lt_point_count Configuration.ProjectivePlane.two_lt_pointCount

-- porting note: left out (P) to avoid redundant binder annotation
variable (L)

theorem card_points [Fintype P] [Finite L] : Fintype.card P = order P L ^ 2 + order P L + 1 := by
  cases nonempty_fintype L
  -- ⊢ Fintype.card P = order P L ^ 2 + order P L + 1
  obtain ⟨p, -⟩ := @exists_config P L _ _
  -- ⊢ Fintype.card P = order P L ^ 2 + order P L + 1
  let ϕ : { q // q ≠ p } ≃ Σl : { l : L // p ∈ l }, { q // q ∈ l.1 ∧ q ≠ p } :=
    { toFun := fun q => ⟨⟨mkLine q.2, (mkLine_ax q.2).2⟩, q, (mkLine_ax q.2).1, q.2⟩
      invFun := fun lq => ⟨lq.2, lq.2.2.2⟩
      left_inv := fun q => Subtype.ext rfl
      right_inv := fun lq =>
        Sigma.subtype_ext
          (Subtype.ext
            ((eq_or_eq (mkLine_ax lq.2.2.2).1 (mkLine_ax lq.2.2.2).2 lq.2.2.1 lq.1.2).resolve_left
              lq.2.2.2))
          rfl }
  classical
    have h1 : Fintype.card { q // q ≠ p } + 1 = Fintype.card P := by
      apply (eq_tsub_iff_add_eq_of_le (Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr ⟨p⟩))).mp
      convert(Fintype.card_subtype_compl _).trans (congr_arg _ (Fintype.card_subtype_eq p))
    have h2 : ∀ l : { l : L // p ∈ l }, Fintype.card { q // q ∈ l.1 ∧ q ≠ p } = order P L := by
      intro l
      rw [← Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ l.val) (· ≠ p)),
        Fintype.card_subtype_compl fun x : Subtype (· ∈ l.val) => x.val = p, ←
        Nat.card_eq_fintype_card]
      refine' tsub_eq_of_eq_add ((pointCount_eq P l.1).trans _)
      rw [← Fintype.card_subtype_eq (⟨p, l.2⟩ : { q : P // q ∈ l.1 })]
      simp_rw [Subtype.ext_iff_val]
    simp_rw [← h1, Fintype.card_congr ϕ, Fintype.card_sigma, h2, Finset.sum_const, Finset.card_univ]
    rw [← Nat.card_eq_fintype_card, ← lineCount, lineCount_eq, smul_eq_mul, Nat.succ_mul, sq]
#align configuration.projective_plane.card_points Configuration.ProjectivePlane.card_points

theorem card_lines [Finite P] [Fintype L] : Fintype.card L = order P L ^ 2 + order P L + 1 :=
  (card_points (Dual L) (Dual P)).trans (congr_arg (fun n => n ^ 2 + n + 1) (Dual.order P L))
#align configuration.projective_plane.card_lines Configuration.ProjectivePlane.card_lines

end ProjectivePlane

end Configuration
