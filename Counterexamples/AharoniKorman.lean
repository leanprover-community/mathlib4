/-
Copyright (c) 2024 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Order.Chain
import Mathlib.Order.WellFoundedSet
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Data.Setoid.Partition
import Mathlib.Topology.Filter

/-!
# Disproof of the Aharoni–Korman conjecture

The Aharoni–Korman conjecture (sometimes called the fishbone conjecture) says that every partial
order satisfies at least one of the following:
- It contains an infinite antichain
- It contains a chain C, together with a partition into antichains such that every part meets C.

In November 2024, Hollom disproved this conjecture. In this file, we construct Hollom's
counterexample P_5 and show it satisfies neither of the above, and thus disprove the conjecture.
See https://arxiv.org/abs/2411.16844 for further details.
-/

def Hollom : Type := ℕ × ℕ × ℕ

def ofHollom : Hollom ≃ ℕ × ℕ × ℕ := Equiv.refl _
def toHollom : ℕ × ℕ × ℕ ≃ Hollom := Equiv.refl _

@[simp] lemma ofHollom_symm_eq : ofHollom.symm = toHollom := rfl
@[simp] lemma toHollom_symm_eq : toHollom.symm = ofHollom := rfl

@[simp] lemma ofHollom_toHollom (x) : ofHollom (toHollom x) = x := rfl
@[simp] lemma toHollom_ofHollom (x) : toHollom (ofHollom x) = x := rfl

@[simp] lemma Hollom.«forall» {p : Hollom → Prop} : (∀ x, p x) ↔ ∀ x, p (toHollom x) := Iff.rfl
@[simp] lemma Hollom.«exists» {p : Hollom → Prop} : (∃ x, p x) ↔ ∃ x, p (toHollom x) := Iff.rfl

namespace Hollom

@[elab_as_elim, induction_eliminator, cases_eliminator]
lemma induction {p : Hollom → Prop} (h : ∀ x, p (toHollom x)) : ∀ x, p x := h

@[mk_iff]
inductive HollomOrder : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ → Prop
  | twice {x y n u v m : ℕ} : m + 2 ≤ n →
      HollomOrder (x, y, n) (u, v, m)
  | within {x y u v m : ℕ} : x ≤ u → y ≤ v →
      HollomOrder (x, y, m) (u, v, m)
  | next_min {x y u v m : ℕ} : min x y + 1 ≤ min u v →
      HollomOrder (x, y, m + 1) (u, v, m)
  | next_add {x y u v m : ℕ} : x + y ≤ 2 * (u + v) →
      HollomOrder (x, y, m + 1) (u, v, m)

instance : LE Hollom := ⟨fun x y ↦ HollomOrder (ofHollom x) (ofHollom y)⟩

private theorem antisymms : (x y : Hollom) → x ≤ y → y ≤ x → x = y
  | _, _, .twice _, .twice _ => by omega
  | _, (_, _, _), .twice _, .within _ _ => by omega
  | _, _, .twice _, .next_min _ => by omega
  | _, _, .twice _, .next_add _ => by omega
  | _, _, .within _ _, .twice _ => by omega
  | _, _, .within _ _, .within _ _ => by
      rw [Prod.ext_iff, Prod.ext_iff]
      simp only [and_true]
      omega
  | _, _, .next_min _, .twice _ => by omega
  | _, _, .next_add _, .twice _ => by omega

instance : PartialOrder Hollom where
  le_refl x := .within le_rfl le_rfl
  le_trans
  | _, _, _, .twice _, .twice _ => .twice (by omega)
  | _, _, _, .twice _, .within _ _ => .twice (by omega)
  | _, _, _, .twice _, .next_min _ => .twice (by omega)
  | _, _, _, .twice _, .next_add _ => .twice (by omega)
  | _, _, _, .within _ _, .twice _ => .twice (by omega)
  | _, _, _, .within _ _, .within _ _ => .within (by omega) (by omega)
  | _, _, _, .within _ _, .next_min _ => .next_min (by omega)
  | _, _, _, .within _ _, .next_add _ => .next_add (by omega)
  | _, _, _, .next_min _, .twice _ => .twice (by omega)
  | _, _, _, .next_min _, .within _ _ => .next_min (by omega)
  | _, _, _, .next_min _, .next_min _ => .twice (by omega)
  | _, _, _, .next_min _, .next_add _ => .twice (by omega)
  | _, _, _, .next_add _, .twice _ => .twice (by omega)
  | _, _, _, .next_add _, .within _ _ => .next_add (by omega)
  | _, _, _, .next_add _, .next_min _ => .twice (by omega)
  | _, _, _, .next_add _, .next_add _ => .twice (by omega)
  le_antisymm := antisymms

@[simp] lemma toHollom_le_toHollom_iff_fixed_right {a b c d n : ℕ} :
    toHollom (a, b, n) ≤ toHollom (c, d, n) ↔ a ≤ c ∧ b ≤ d := by
  refine ⟨?_, ?_⟩
  · rintro (_ | _)
    · omega
    · omega
  · rintro ⟨h₁, h₂⟩
    exact .within h₁ h₂

lemma le_of_toHollom_le_toHollom {a b c d e f : ℕ} :
    toHollom (a, b, c) ≤ toHollom (d, e, f) → f ≤ c
  | .twice _ => by omega
  | .within _ _ => by omega
  | .next_add _ => by omega
  | .next_min _ => by omega

lemma toHollom_le_toHollom {a b c d e f : ℕ} (h : (a, b) ≤ (d, e)) (hcf : f ≤ c) :
    toHollom (a, b, c) ≤ toHollom (d, e, f) := by
  simp only [Prod.mk_le_mk] at h
  obtain rfl | rfl | hc : f = c ∨ f + 1 = c ∨ f + 2 ≤ c := by omega
  · simpa using h
  · exact .next_add (by omega)
  · exact .twice hc

-- written L_n in the paper
def level (n : ℕ) : Set Hollom := {toHollom (x, y, n) | (x : ℕ) (y : ℕ)}

lemma level_eq (n : ℕ) : level n = {x | (ofHollom x).2.2 = n} := by
  simp [Set.ext_iff, level, eq_comm]

def embed (n : ℕ) : ℕ × ℕ → Hollom := fun x ↦ toHollom (x.1, x.2, n)

lemma embed_monotone {n : ℕ} : Monotone (embed n) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simpa [embed] using h

lemma embed_strictMono {n : ℕ} : StrictMono (embed n) :=
  embed_monotone.strictMono_of_injective <| by rintro ⟨_, _⟩ _ ⟨⟩; rfl

lemma embed_le_embed_iff {n : ℕ} {x y} : embed n x ≤ embed n y ↔ x ≤ y := by
  rw [embed, embed, toHollom_le_toHollom_iff_fixed_right]
  rfl

lemma embed_lt_embed_iff {n : ℕ} {x y} : embed n x < embed n y ↔ x < y :=
  lt_iff_lt_of_le_iff_le' embed_le_embed_iff embed_le_embed_iff

lemma level_eq_range (n : ℕ) : level n = Set.range (embed n) := by
  simp [level, Set.range, embed]

lemma univ_isPWO {α : Type*} [LinearOrder α] [WellFoundedLT α] : (Set.univ : Set α).IsPWO := by
  rw [← Set.isWF_iff_isPWO, Set.isWF_univ_iff]
  exact wellFounded_lt

lemma level_isPWO {n : ℕ} : (level n).IsPWO := by
  rw [level_eq_range, ← Set.image_univ]
  refine Set.IsPWO.image_of_monotone ?_ embed_monotone
  rw [← Set.univ_prod_univ]
  exact Set.IsPWO.prod univ_isPWO univ_isPWO

lemma no_infinite_antichain_level {n : ℕ} {A : Set Hollom} (hA : A ⊆ level n)
    (hA' : IsAntichain (· ≤ ·) A) : A.Finite :=
  hA'.finite_of_partiallyWellOrderedOn ((level_isPWO).mono hA)

@[simp] lemma toHollom_mem_level_iff {n : ℕ} {x} : toHollom x ∈ level n ↔ x.2.2 = n := by
  simp [level_eq]

-- 5.8.i
lemma ordConnected_level {n : ℕ} : (level n).OrdConnected := by
  rw [Set.ordConnected_iff]
  simp only [level_eq, Set.mem_setOf_eq, Set.subset_def, Set.mem_Icc, and_imp, Hollom.forall,
    ofHollom_toHollom, Prod.forall, forall_eq, toHollom_le_toHollom_iff_fixed_right]
  intro a b c d ac bd e f g h1 h2
  exact le_antisymm (le_of_toHollom_le_toHollom h1) (le_of_toHollom_le_toHollom h2)

-- written K_{n,s} in the paper
def levelLine (n s : ℕ) : Set Hollom :=
  { toHollom (x, y, n) | (x : ℕ) (y : ℕ) (_ : x + y = s) }

@[simp] lemma toHollom_mem_levelLine_iff {n s x y z : ℕ} :
    toHollom (x, y, z) ∈ levelLine n s ↔ x + y = s ∧ z = n := by
  aesop (add simp levelLine)

-- implicit in 5.8.ii
lemma levelLine_le_level {n s : ℕ} : levelLine n s ⊆ level n := by simp [Set.subset_def]

-- 5.8.ii
lemma isAntichain_levelLine {n s : ℕ} : IsAntichain (· ≤ ·) (levelLine n s) := by
  rw [IsAntichain, Set.Pairwise]
  simp
  omega

lemma Set.finite_of_finite_fibers {α β : Type*} (f : α → β) {s : Set α}
    (himage : (f '' s).Finite)
    (hfibers : ∀ x ∈ f '' s, (s ∩ f ⁻¹' {x}).Finite) : s.Finite :=
  (himage.biUnion hfibers).subset <| fun x ↦ by aesop

-- Lemma 5.9
lemma no_infinite_antichain {A : Set Hollom} (hC : IsAntichain (· ≤ ·) A) : A.Finite := by
  let f (x : Hollom) : ℕ := (ofHollom x).2.2
  have (n : ℕ) : A ∩ f ⁻¹' {n} ⊆ level n := fun x ↦ by induction x with | h x => simp [f]
  apply Set.finite_of_finite_fibers f
  case hfibers =>
    intro x hx
    exact no_infinite_antichain_level (this _) (hC.subset Set.inter_subset_left)
  case himage =>
    rw [← Set.not_infinite]
    intro h
    obtain ⟨n, hn⟩ := h.nonempty
    suffices f '' A ⊆ Set.Iio (n + 2) from h ((Set.finite_Iio _).subset this)
    intro m
    simp only [Set.mem_image, «exists», ofHollom_toHollom, Prod.exists, exists_eq_right,
      Set.mem_Iio, forall_exists_index, f]
    simp only [Set.mem_image, «exists», ofHollom_toHollom, Prod.exists, exists_eq_right, f] at hn
    obtain ⟨a, b, hab⟩ := hn
    intro c d hcd
    by_contra!
    exact hC hcd hab (by simp; omega) (HollomOrder.twice this)

variable {C : Set Hollom}

lemma test {f : ℕ → ℕ} {n₀ : ℕ} (hf : ∀ n ≥ n₀, f (n + 1) < f n) : False := by
  let g (n : ℕ) : ℕ := f (n₀ + n)
  have hg : StrictAnti g := strictAnti_nat_of_succ_lt fun n ↦ hf (n₀ + n) (by simp)
  obtain ⟨m, n, h₁, h₂⟩ := univ_isPWO g (by simp)
  exact (hg h₁).not_le h₂

-- Lemma 5.10
-- every chain has a finite intersection with infinitely many levels
lemma exists_finite_intersection (hC : IsChain (· ≤ ·) C) {n₀ : ℕ} :
    ∃ n ≥ n₀, (C ∩ level n).Finite := by
  by_contra! hC'
  simp only [← Set.not_infinite, not_not] at hC'
  let m (n : ℕ) : ℕ := sInf {min (ofHollom x).1 (ofHollom x).2.1 | x ∈ C ∩ level n}
  have nonempty_mins (n : ℕ) (hn : n₀ ≤ n) :
      {min (ofHollom x).1 (ofHollom x).2.1 | x ∈ C ∩ level n}.Nonempty :=
    (hC' n hn).nonempty.image _
  have hm (n : ℕ) (hn : n ≥ n₀) : ∃ u v : ℕ, toHollom (u, v, n) ∈ C ∧ min u v = m n := by
    simpa [m] using Nat.sInf_mem (nonempty_mins n hn)
  suffices ∀ n ≥ n₀, m (n + 1) < m n by
    exact test this
  intro n hn
  obtain ⟨u, v, huv, hmn⟩ := hm n hn
  rw [← hmn]
  let D := {x | (ofHollom x).1 + (ofHollom x).2.1 ≤ 2 * (u + v)}
  have : ((C ∩ level (n + 1)) \ D).Infinite := by
    have : (C ∩ level (n + 1) ∩ D).Finite := by
      have : C ∩ level (n + 1) ∩ D ⊆
          (fun t ↦ toHollom (t.1, t.2, n + 1)) '' {x : ℕ × ℕ | x.1 + x.2 ≤ 2 * (u + v)} := by
        intro x
        induction x
        case h x =>
        rcases x with ⟨a, b, c⟩
        simp +contextual [D]
      refine .subset (.image _ ?_) this
      have : {x : ℕ × ℕ | x.1 + x.2 ≤ 2 * (u + v)} ⊆ Set.Iic (2 * (u + v), 2 * (u + v)) := by
        rintro ⟨x, y⟩ h
        simp only [Set.mem_setOf_eq] at h
        simp only [Set.mem_Iic, Prod.mk_le_mk]
        omega
      exact .subset (Set.finite_Iic _) this
    specialize hC' (n + 1) (by omega)
    rw [← (C ∩ level (n + 1)).inter_union_diff D, Set.infinite_union] at hC'
    refine hC'.resolve_left ?_
    simpa using this
  obtain ⟨⟨x, y, z⟩, hxyz⟩ := this.nonempty.image ofHollom
  simp only [Set.mem_image_equiv, ofHollom_symm_eq, Set.mem_diff, Set.mem_inter_iff,
    toHollom_mem_level_iff, Set.mem_setOf_eq, ofHollom_toHollom, not_le, D] at hxyz
  obtain ⟨⟨h1, rfl⟩, h2⟩ := hxyz
  obtain h3 | h3 := hC huv h1 (by simp)
  · have := le_of_toHollom_le_toHollom h3
    omega
  · cases h3
    case twice => omega
    case next_add => omega
    case next_min h3 =>
      rw [← Nat.add_one_le_iff]
      refine h3.trans' ?_
      simp only [add_le_add_iff_right]
      exact Nat.sInf_le ⟨_, ⟨h1, by simp⟩, by simp⟩

lemma partition_iff_function {α : Type*} [PartialOrder α] {C : Set α} (hC : IsChain (· ≤ ·) C) :
    (∃ S, Setoid.IsPartition S ∧ ∀ A ∈ S, IsAntichain (· ≤ ·) A ∧ (A ∩ C).Nonempty) ↔
    (∃ f, Set.range f ⊆ C ∧ (∀ x ∈ C, f x = x) ∧ ∀ x, IsAntichain (· ≤ ·) (f ⁻¹' {x})) := by
  constructor
  · simp only [forall_exists_index, and_imp]
    intro S hS hSA
    choose hS f hf hf' using hS
    simp only at hf
    simp only [and_imp] at hf'
    choose hA g hg using hSA
    refine ⟨fun x ↦ g (f x) (hf _).1, ?_, ?_, ?_⟩
    · simp only [Set.subset_def, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
      intro a
      exact (hg _ _).2
    · intro a ha
      simp only
      have hfa : f a ∈ S := (hf _).1
      have : g (f a) hfa ∈ f a ∩ C := hg _ _
      have : a ∈ f a := (hf _).2
      by_contra!
      obtain h₁ | h₁ := hC (hg _ hfa).2 ha this
      · exact this ((hA _ hfa).eq (hg _ _).1 (hf _).2 h₁)
      · exact this ((hA _ hfa).eq' (hg _ _).1 (hf _).2 h₁)
    · intro x
      have : ∀ a b : α, a ∈ f b → f b = f a := by
        intro a b
        exact hf' a _ (hf b).1
      have : ((fun x ↦ g (f x) (hf _).1) ⁻¹' {x}) ⊆ f x := by
        intro y hy
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy
        have h := hg (f y) (hf _).1
        have := this _ _ h.1
        rw [hy] at this
        rw [← this]
        exact (hf _).2
      apply IsAntichain.subset _ this
      exact hA _ (hf _).1
  · simp only [forall_exists_index, and_imp]
    intro f hf hf' hfA
    refine ⟨{{y | f y = f x} | (x : α)}, ⟨?_, ?_⟩, ?_⟩
    · simp only [Set.mem_setOf_eq, not_exists, ← Set.nonempty_iff_ne_empty]
      intro x
      exact ⟨x, rfl⟩
    · intro x
      simp only [Set.mem_setOf_eq]
      refine ⟨_, ⟨⟨x, rfl⟩, rfl⟩, ?_⟩
      aesop
    · simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff]
      intro x
      refine ⟨?_, ?_⟩
      · exact hfA _
      · obtain hx := hf (by simp : f x ∈ Set.range f)
        refine ⟨f x, ?_, hx⟩
        simp only [Set.mem_setOf_eq]
        rw [hf' _ hx]

variable {n : ℕ} {f : Hollom → Hollom}
  (hn : (C ∩ level n).Finite)
  (hfC : ∀ x, f x ∈ C) (hfCid : ∀ x ∈ C, f x = x) (hf : ∀ x, IsAntichain (· ≤ ·) (f ⁻¹' {x}))

include hf in
lemma not_le_of_eq {x y : Hollom} (hfxy : f x = f y) (hxy : x ≠ y) : ¬ x ≤ y :=
  hf (f y) (by simp [hfxy]) (by simp) hxy

include hf in
lemma incomp_of_eq {x y : Hollom} (hfxy : f x = f y) (hxy : x ≠ y) : ¬ (x ≤ y ∨ y ≤ x) := by
  simp only [not_or]
  exact ⟨not_le_of_eq hf hfxy hxy, not_le_of_eq hf hfxy.symm hxy.symm⟩

include hfC hfCid hf in
lemma incomp_apply {x : Hollom} (hx : f x ≠ x) : ¬ (f x ≤ x ∨ x ≤ f x) :=
  incomp_of_eq hf (hfCid _ (hfC _)) hx

def R (n : ℕ) (C : Set Hollom) : Set Hollom := {x ∈ level n | ∀ y ∈ C ∩ level n, x ≤ y ∨ y ≤ x}

lemma R_subset_level : R n C ⊆ level n := Set.sep_subset (level n) _

lemma mem_R {n : ℕ} {C : Set Hollom} {x} :
  x ∈ R n C ↔ x ∈ level n ∧ ∀ y ∈ C ∩ level n, x ≤ y ∨ y ≤ x := Iff.rfl

lemma square_subset_above (h : (C ∩ level n).Finite) :
    ∃ a, embed n '' Set.Ici (a, a) ⊆ {x | ∀ y ∈ C ∩ level n, y ≤ x} := by
  obtain h | hne := (C ∩ level n).eq_empty_or_nonempty
  · refine ⟨0, ?_⟩
    intro x
    induction x
    rw [h]
    aesop

  obtain ⟨a, b, hab⟩ : ∃ a b, ∀ c d, toHollom (c, d, n) ∈ C → c ≤ a ∧ d ≤ b := by
    obtain ⟨⟨a, b⟩, hab⟩ := (h.image (fun t ↦ ((ofHollom t).1, (ofHollom t).2.1))).bddAbove
    use a, b
    intro c d hcd
    simpa using hab ⟨toHollom (_, _, _), ⟨hcd, by simp⟩, rfl⟩

  refine ⟨max a b, ?_⟩
  rw [Set.subset_def]
  simp +contextual only [Set.mem_image, Set.mem_Ici, Prod.exists, Prod.mk_le_mk, sup_le_iff, R,
    Set.mem_inter_iff, and_imp, «forall», toHollom_mem_level_iff, Prod.forall, Set.mem_setOf_eq,
    forall_exists_index, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq,
    toHollom_le_toHollom_iff_fixed_right, true_and, embed]

  rintro _ _ _ c d haf hbf hag hbg rfl rfl rfl e f n hef rfl
  specialize hab e f hef
  omega

lemma square_subset_R (h : (C ∩ level n).Finite) :
    ∃ a, embed n '' Set.Ici (a, a) ⊆ R n C := by
  obtain ⟨a, ha⟩ := square_subset_above h
  refine ⟨a, ?_⟩
  rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
  exact ⟨by simp [embed], fun b hb ↦ .inr (ha ⟨_, hxy, rfl⟩ _ hb)⟩

lemma R_infinite (h : (C ∩ level n).Finite) : (R n C).Infinite := by
  obtain ⟨a, ha⟩ := square_subset_R h
  refine ((Set.Ici_infinite _).image ?_).mono ha
  aesop (add norm unfold [Set.InjOn, embed])

lemma R_diff_infinite (h : (C ∩ level n).Finite) : (R n C \ (C ∩ level n)).Infinite :=
  (R_infinite h).diff h

-- we could state this as Disjoint (f '' (R n C)) (C ∩ level n), but this is more
-- annoying than helpful
include hfC hfCid hf in
lemma R_maps {x : Hollom} (hx : x ∈ R n C) (hx' : x ∉ C ∩ level n) : f x ∉ C ∩ level n := by
  intro hfx
  apply incomp_apply hfC hfCid hf _ (hx.2 _ hfx).symm
  exact ne_of_mem_of_not_mem hfx hx'

open Classical in
noncomputable def x0y0 (n : ℕ) (C : Set Hollom) : ℕ × ℕ :=
  if h : (C ∩ level (n + 1)).Nonempty
    then WellFounded.min wellFounded_lt {x | embed (n + 1) x ∈ C} <| by
      rw [level_eq_range] at h
      obtain ⟨_, h, y, rfl⟩ := h
      exact ⟨y, h⟩
    else 0

lemma x0y0_mem (h : (C ∩ level (n + 1)).Nonempty) :
    embed (n + 1) (x0y0 n C) ∈ C := by
  rw [x0y0, dif_pos h]
  exact WellFounded.min_mem _ {x | embed (n + 1) x ∈ C} _

lemma _root_.IsChain.le_of_not_lt {α : Type*} [Preorder α] {s : Set α} (hs : IsChain (· ≤ ·) s)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) (h : ¬ x < y) : y ≤ x := by
  cases hs.total hx hy with
  | inr h' => exact h'
  | inl h' => rw [lt_iff_le_not_le, not_and, not_not] at h; exact h h'

lemma x0y0_min (z : ℕ × ℕ) (hC : IsChain (· ≤ ·) C) (h : embed (n + 1) z ∈ C) :
    embed (n + 1) (x0y0 n C) ≤ embed (n + 1) z := by
  have : (C ∩ level (n + 1)).Nonempty := ⟨_, h, by simp [level_eq_range]⟩
  refine hC.le_of_not_lt h (x0y0_mem this) ?_
  rw [x0y0, dif_pos this, embed_lt_embed_iff]
  exact WellFounded.not_lt_min wellFounded_lt {x | embed (n + 1) x ∈ C} ?_ h

noncomputable def x0 (n : ℕ) (C : Set Hollom) : ℕ := (x0y0 n C).1
noncomputable def y0 (n : ℕ) (C : Set Hollom) : ℕ := (x0y0 n C).2

lemma x0_y0_mem (h : (C ∩ level (n + 1)).Nonempty) : toHollom (x0 n C, y0 n C, n + 1) ∈ C :=
  x0y0_mem h

lemma x0_y0_min (hC : IsChain (· ≤ ·) C) {a b : ℕ} (h : (a, b, n + 1) ∈ C) :
    toHollom (x0 n C, y0 n C, n + 1) ≤ toHollom (a, b, n + 1) :=
  x0y0_min (a, b) hC h

open Classical in
noncomputable def S (n : ℕ) (C : Set Hollom) : Set Hollom :=
  if (C ∩ level (n + 1)).Finite
    then {x ∈ R n C | ∀ y ∈ C ∩ level (n + 1), x ≤ y ∨ y ≤ x}
    else {x ∈ R n C | max (x0 n C) (y0 n C) + 1 ≤ min (ofHollom x).1 (ofHollom x).2.1}

lemma S_subset_R : S n C ⊆ R n C := by
  rw [S]
  split <;>
  exact Set.sep_subset _ _

lemma S_subset_level : S n C ⊆ level n := S_subset_R.trans R_subset_level

lemma square_subset_S_case_1 (h : (C ∩ level n).Finite) (h' : (C ∩ level (n + 1)).Finite) :
    ∃ a, embed n '' Set.Ici (a, a) ⊆ S n C := by
  rw [S, if_pos h']
  obtain ⟨a, ha⟩ := square_subset_R h

  obtain ⟨b, c, hab⟩ : ∃ b c, ∀ d e, toHollom (d, e, n + 1) ∈ C → (d, e) ≤ (b, c) := by
    obtain ⟨⟨b, c⟩, hbc⟩ := (h'.image (fun t ↦ ((ofHollom t).1, (ofHollom t).2.1))).bddAbove
    use b, c
    intro d e hde
    simpa using hbc ⟨toHollom (_, _, _), ⟨hde, by simp⟩, rfl⟩

  refine ⟨max a (max b c), ?_⟩
  rintro x hx
  have : x ∈ embed n '' Set.Ici (a, a) := by
    obtain ⟨z, hz, rfl⟩ := hx
    refine ⟨z, ?_, rfl⟩
    simp only [Set.mem_Ici] at hz ⊢
    exact hz.trans' (by simp)
  refine ⟨ha this, ?_⟩
  simp only [Set.mem_inter_iff, and_imp, «forall», toHollom_mem_level_iff, Prod.forall]
  rintro d e _ hde rfl
  simp only [Set.mem_image, Set.mem_Ici, Prod.exists, Prod.mk_le_mk, sup_le_iff] at hx
  obtain ⟨f, g, hfg, rfl⟩ := hx
  right
  apply toHollom_le_toHollom
  · have : d ≤ b ∧ e ≤ c := hab _ _ hde
    simp
    omega
  · simp

lemma square_subset_S_case_2 (h : (C ∩ level n).Finite) (h' : (C ∩ level (n + 1)).Infinite) :
    ∃ a, embed n '' Set.Ici (a, a) ⊆ S n C := by
  rw [S, if_neg h']
  obtain ⟨a, ha⟩ := square_subset_R h
  use max (max (x0 n C) (y0 n C) + 1) a
  sorry





-- lemma S_infinite : (S n C).Infinite := by
--   rw [S]
--   split
--   · sorry
--   · sorry

end Hollom

/--
The Aharoni–Korman conjecture (sometimes called the fishbone conjecture) says that every partial
order satisfies one of the following:
- It contains an infinite antichain
- It contains a chain C, and has a partition into antichains such that every part meets C.

In November 2024, Hollom disproved this conjecture.
-/
theorem aharoni_korman_false :
    ¬ ∀ (α : Type) (_ : PartialOrder α),
        (∃ A : Set α, IsAntichain (· ≤ ·) A ∧ A.Infinite) ∨
        (∃ C : Set α, IsChain (· ≤ ·) C ∧
         ∃ S : Set (Set α), Setoid.IsPartition S ∧
          ∀ A ∈ S, IsAntichain (· ≤ ·) A ∧ (A ∩ C).Nonempty) := by
  sorry
