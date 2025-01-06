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

section to_move

/--
If the image of `s` under `f` is finite, and each fiber of `f` has a finite intersection
with `s`, then `s` is itself finite.
-/
lemma Set.Finite.of_finite_fibers {α β : Type*} (f : α → β) {s : Set α}
    (himage : (f '' s).Finite)
    (hfibers : ∀ x ∈ f '' s, (s ∩ f ⁻¹' {x}).Finite) : s.Finite :=
  (himage.biUnion hfibers).subset <| fun x ↦ by aesop

/--
If `α` is a linear order with well-founded `<`, then the universe is a partially well-ordered set.
Note this does not hold without the linearity assumption.
-/
lemma univ_isPWO_of_linearOrder {α : Type*} [LinearOrder α] [WellFoundedLT α] :
    (Set.univ : Set α).IsPWO := by
  rw [← Set.isWF_iff_isPWO, Set.isWF_univ_iff]
  exact wellFounded_lt

open Finset

variable {α β : Type*}

section sectL

variable [Preorder α] [PartialOrder β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]
  [DecidableRel (α := α × β) (· ≤ ·)] (a b : α) (c : β)

lemma Prod.Icc_map_sectL : (Icc a b).map (.sectL _ c) = Icc (a, c) (b, c) := by
  aesop (add safe forward [le_antisymm, not_lt_of_le, le_of_lt])

lemma Prod.Ioc_map_sectL : (Ioc a b).map (.sectL _ c) = Ioc (a, c) (b, c) := by
  aesop (add safe forward [le_antisymm, not_lt_of_le, le_of_lt])

lemma Prod.Ico_map_sectL : (Ico a b).map (.sectL _ c) = Ico (a, c) (b, c) := by
  aesop (add safe forward [le_antisymm, not_lt_of_le, le_of_lt])

lemma Prod.Ioo_map_sectL : (Ioo a b).map (.sectL _ c) = Ioo (a, c) (b, c) := by
  aesop (add safe forward [le_antisymm, not_lt_of_le, le_of_lt])

end sectL

section sectR

variable [PartialOrder α] [Preorder β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]
  [DecidableRel (α := α × β) (· ≤ ·)] (c : α) (a b : β)

lemma Prod.Icc_map_sectR : (Icc a b).map (.sectR c _) = Icc (c, a) (c, b) := by
  aesop (add safe forward [le_antisymm, not_lt_of_le, le_of_lt])

lemma Prod.Ioc_map_sectR : (Ioc a b).map (.sectR c _) = Ioc (c, a) (c, b) := by
  aesop (add safe forward [le_antisymm, not_lt_of_le, le_of_lt])

lemma Prod.Ico_map_sectR : (Ico a b).map (.sectR c _) = Ico (c, a) (c, b) := by
  aesop (add safe forward [le_antisymm, not_lt_of_le, le_of_lt])

lemma Prod.Ioo_map_sectR : (Ioo a b).map (.sectR c _) = Ioo (c, a) (c, b) := by
  aesop (add safe forward [le_antisymm, not_lt_of_le, le_of_lt])

end sectR

end to_move

def Hollom : Type := ℕ × ℕ × ℕ
  deriving DecidableEq

def ofHollom : Hollom ≃ ℕ × ℕ × ℕ := Equiv.refl _
def toHollom : ℕ × ℕ × ℕ ≃ Hollom := Equiv.refl _

@[simp] lemma ofHollom_symm_eq : ofHollom.symm = toHollom := rfl
@[simp] lemma toHollom_symm_eq : toHollom.symm = ofHollom := rfl

@[simp] lemma ofHollom_toHollom (x) : ofHollom (toHollom x) = x := rfl
@[simp] lemma toHollom_ofHollom (x) : toHollom (ofHollom x) = x := rfl

namespace Hollom

@[simp] lemma «forall» {p : Hollom → Prop} : (∀ x, p x) ↔ ∀ x, p (toHollom x) := Iff.rfl
@[simp] lemma «exists» {p : Hollom → Prop} : (∃ x, p x) ↔ ∃ x, p (toHollom x) := Iff.rfl

@[elab_as_elim, induction_eliminator, cases_eliminator]
lemma induction {p : Hollom → Prop} (h : ∀ x y z, p (toHollom (x, y, z))) : ∀ x, p x := by simpa

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

private lemma antisymm : (x y : Hollom) → x ≤ y → y ≤ x → x = y
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
  le_antisymm := antisymm

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

/--
The Hollom partial order is divided into "levels", indexed by the natural numbers. These correspond
to the third coordinate of the tuple.
This is written L_n in the paper.
-/
def level (n : ℕ) : Set Hollom := {toHollom (x, y, n) | (x : ℕ) (y : ℕ)}

lemma level_eq (n : ℕ) : level n = {x | (ofHollom x).2.2 = n} := by
  simp [Set.ext_iff, level, eq_comm]

@[simp] lemma toHollom_mem_level_iff {n : ℕ} {x} : toHollom x ∈ level n ↔ x.2.2 = n := by
  simp [level_eq]

/--
For each `n`, there is an order embedding from ℕ × ℕ (which has the product order) to the Hollom
partial order.
-/
@[simps]
def embed (n : ℕ) : ℕ × ℕ ↪o Hollom where
  toFun x := toHollom (x.1, x.2, n)
  inj' x := by aesop
  map_rel_iff' := by simp

lemma embed_monotone {n : ℕ} : Monotone (embed n) := (embed n).monotone

lemma embed_strictMono {n : ℕ} : StrictMono (embed n) := (embed n).strictMono

@[simp] lemma embed_le_embed_iff {n : ℕ} {x y} : embed n x ≤ embed n y ↔ x ≤ y :=
  (embed n).le_iff_le

@[simp] lemma embed_lt_embed_iff {n : ℕ} {x y} : embed n x < embed n y ↔ x < y :=
  (embed n).lt_iff_lt

lemma level_eq_range (n : ℕ) : level n = Set.range (embed n) := by
  simp [level, Set.range, embed]

lemma pairwise_disjoint_level : Pairwise (Disjoint on level) := by
  simp [Pairwise, Function.onFun, level_eq, Set.disjoint_left]

lemma pairwiseDisjoint_level : Set.PairwiseDisjoint .univ level :=
  pairwise_disjoint_level.pairwiseDisjoint _

lemma level_isPWO {n : ℕ} : (level n).IsPWO := by
  rw [level_eq_range, ← Set.image_univ]
  refine Set.IsPWO.image_of_monotone ?_ embed_monotone
  rw [← Set.univ_prod_univ]
  exact Set.IsPWO.prod univ_isPWO_of_linearOrder univ_isPWO_of_linearOrder

/--
If `A` is a subset of `level n` and is an antichain, then `A` is finite.
This is a special case of the fact that any antichain in the Hollom order is finite, but is a useful
lemma to prove that fact later: `no_infinite_antichain`.
-/
lemma no_infinite_antichain_level {n : ℕ} {A : Set Hollom} (hA : A ⊆ level n)
    (hA' : IsAntichain (· ≤ ·) A) : A.Finite :=
  hA'.finite_of_partiallyWellOrderedOn ((level_isPWO).mono hA)

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

@[simp] lemma toHollom_mem_levelLine_iff {n s : ℕ} {x : ℕ × ℕ × ℕ}:
    toHollom x ∈ levelLine n s ↔ x.1 + x.2.1 = s ∧ x.2.2 = n := by
  aesop (add simp levelLine)

-- implicit in 5.8.ii
lemma levelLine_subset_level {n s : ℕ} : levelLine n s ⊆ level n := by simp [Set.subset_def]

-- 5.8.ii
lemma isAntichain_levelLine {n s : ℕ} : IsAntichain (· ≤ ·) (levelLine n s) := by
  rw [IsAntichain, Set.Pairwise]
  simp
  omega

lemma iUnion_levelLine {n : ℕ} : ⋃ s, levelLine n s = level n := by
  simp [Set.ext_iff]

-- Lemma 5.9
lemma no_infinite_antichain {A : Set Hollom} (hC : IsAntichain (· ≤ ·) A) : A.Finite := by
  let f (x : Hollom) : ℕ := (ofHollom x).2.2
  have (n : ℕ) : A ∩ f ⁻¹' {n} ⊆ level n := fun x ↦ by induction x with | h x => simp [f]
  apply Set.Finite.of_finite_fibers f
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
  obtain ⟨m, n, h₁, h₂⟩ := univ_isPWO_of_linearOrder g (by simp)
  exact (hg h₁).not_le h₂

lemma triangle_finite (n : ℕ) : {x : ℕ × ℕ | x.1 + x.2 ≤ n}.Finite :=
  (Set.finite_Iic (n, n)).subset <| by
    aesop (add simp Set.subset_def) (add norm tactic Lean.Elab.Tactic.Omega.omegaDefault)

open Filter

-- Lemma 5.10
-- every chain has a finite intersection with infinitely many levels
lemma exists_finite_intersection (hC : IsChain (· ≤ ·) C) :
    ∃ᶠ n in atTop, (C ∩ level n).Finite := by
  rw [frequently_atTop]
  intro n₀
  by_contra! hC'
  simp only [← Set.not_infinite, not_not] at hC'
  let m (n : ℕ) : ℕ := sInf {min (ofHollom x).1 (ofHollom x).2.1 | x ∈ C ∩ level n}
  have nonempty_mins (n : ℕ) (hn : n₀ ≤ n) :
      {min (ofHollom x).1 (ofHollom x).2.1 | x ∈ C ∩ level n}.Nonempty :=
    (hC' n hn).nonempty.image _
  have hm (n : ℕ) (hn : n ≥ n₀) : ∃ u v : ℕ, toHollom (u, v, n) ∈ C ∧ min u v = m n := by
    simpa [m] using Nat.sInf_mem (nonempty_mins n hn)
  suffices ∀ n ≥ n₀, m (n + 1) < m n from test this
  intro n hn
  obtain ⟨u, v, huv, hmn⟩ := hm n hn
  rw [← hmn]
  let D : Set Hollom := {x | (ofHollom x).1 + (ofHollom x).2.1 ≤ 2 * (u + v)}
  have : ((C ∩ level (n + 1)) \ D).Infinite := by
    have : (C ∩ level (n + 1) ∩ D).Finite := by
      refine .subset (.image (embed (n + 1)) (triangle_finite (2 * (u + v)))) ?_
      simp +contextual [Set.subset_def, D]
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

/--
Given a chain `C` in a partial order `α`, the existence of the following are equivalent:
* a partition of `α` into antichains, each which meets `C`
* a function `f : α → C` which is the identity on `C` and for which each fiber is an antichain

In fact, these two are in bijection, but we only need the weaker version that their existence
is equivalent.
-/
lemma partition_iff_function {α : Type*} [PartialOrder α] {C : Set α} (hC : IsChain (· ≤ ·) C) :
    (∃ S, Setoid.IsPartition S ∧ ∀ A ∈ S, IsAntichain (· ≤ ·) A ∧ (A ∩ C).Nonempty) ↔
    (∃ f : α → α, (∀ x, f x ∈ C) ∧ (∀ x ∈ C, f x = x) ∧ ∀ x, IsAntichain (· ≤ ·) (f ⁻¹' {x})) := by
  constructor
  · rintro ⟨S, hS, hSA⟩
    choose hS f hf hf' using hS
    simp only [and_imp] at hf'
    choose hA g hg using hSA
    refine ⟨fun x ↦ g (f x) (hf _).1, fun a ↦ (hg _ _).2, ?_, ?_⟩
    · intro a ha
      have hfa : f a ∈ S := (hf _).1
      by_contra!
      obtain h₁ | h₁ := hC (hg _ hfa).2 ha this
      · exact this ((hA _ hfa).eq (hg _ _).1 (hf _).2 h₁)
      · exact this ((hA _ hfa).eq' (hg _ _).1 (hf _).2 h₁)
    · intro x
      refine (hA (f x) (hf x).1).subset ?_
      have (a b : α) : a ∈ f b → f b = f a := hf' a _ (hf b).1
      intro y hy
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy
      have := this _ _ (hg (f y) (hf _).1).1
      rw [hy] at this
      rw [← this]
      exact (hf _).2
  · rintro ⟨f, hf, hf', hfA⟩
    refine ⟨{{y | f y = f x} | (x : α)}, ⟨?_, ?_⟩, ?_⟩
    · simp only [Set.mem_setOf_eq, not_exists, ← Set.nonempty_iff_ne_empty]
      intro x
      exact ⟨x, rfl⟩
    · intro x
      exact ⟨_, ⟨⟨x, rfl⟩, rfl⟩, by aesop⟩
    · rintro A ⟨x, rfl⟩
      exact ⟨hfA _, f x, hf' _ (hf x), hf x⟩

variable
  (hC : IsChain (· ≤ ·) C)
  {f : Hollom → Hollom}
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

include hC hfC hfCid hf in
lemma le_apply_of_le {x y : Hollom} (hy : y ∈ C) (hx : y ≤ x) : y ≤ f x := by
  obtain h₁ | h₁ := eq_or_ne (f x) x
  · rwa [h₁]
  refine (hC.total hy (hfC x)).resolve_right ?_
  intro hxy
  exact incomp_apply hfC hfCid hf h₁ (.inl (hxy.trans hx))

include hC hfC hfCid hf in
lemma apply_le_of_le {x y : Hollom} (hy : y ∈ C) (hx : x ≤ y) : f x ≤ y := by
  obtain h₁ | h₁ := eq_or_ne (f x) x
  · rwa [h₁]
  refine (hC.total hy (hfC x)).resolve_left ?_
  intro hxy
  exact incomp_apply hfC hfCid hf h₁ (.inr (hx.trans hxy))

include hC hfC hfCid hf in
lemma apply_mem_interval {x y z : Hollom} (hy : y ∈ C) (hz : z ∈ C) (hx : x ∈ Set.Icc y z) :
    f x ∈ Set.Icc y z :=
  ⟨le_apply_of_le hC hfC hfCid hf hy hx.1, apply_le_of_le hC hfC hfCid hf hz hx.2⟩

include hf in
lemma injOn_chain {D : Set Hollom} (hD : IsChain (· ≤ ·) D) : D.InjOn f := by
  intro x hx y hy h
  by_contra! h'
  exact incomp_of_eq hf h h' (hD.total hx hy)

/-!  In this section we construct explicit chains in ℕ × ℕ that will be useful later.  -/
section make_chains

open Finset

def chainBetween (a b c d : ℕ) : Finset (ℕ × ℕ) :=
  if a ≤ c ∧ b ≤ d
    then Icc (a, b) (a, d) ∪ Ioc (a, d) (c, d)
    else ∅

lemma chainBetween_isChain {a b c d : ℕ} : IsChain (· ≤ ·) (chainBetween a b c d).toSet := by
  rw [chainBetween]
  split_ifs
  · rintro ⟨v, w⟩ hvw ⟨x, y⟩ hxy
    simp_all [chainBetween]
    omega
  · simp

lemma image_chainBetween_isChain {a b c d n : ℕ} :
    IsChain (· ≤ ·) ((chainBetween a b c d).image (embed n)).toSet := by
  rw [coe_image]
  apply chainBetween_isChain.image
  simp

lemma left_mem_chainBetween {a b c d : ℕ} (hac : a ≤ c) (hbd : b ≤ d) :
    (a, b) ∈ chainBetween a b c d := by
  rw [chainBetween, if_pos ⟨hac, hbd⟩]
  simp
  omega

lemma right_mem_chainBetween {a b c d : ℕ} (hac : a ≤ c) (hbd : b ≤ d) :
    (c, d) ∈ chainBetween a b c d := by
  rw [chainBetween, if_pos ⟨hac, hbd⟩]
  simp
  omega

open Finset in
lemma card_chainBetween {a b c d : ℕ} (hac : a ≤ c) (hbd : b ≤ d) :
    #(chainBetween a b c d) = c + d + 1 - (a + b) := by
  rw [chainBetween, if_pos ⟨hac, hbd⟩, card_union_of_disjoint, Finset.card_Icc_prod]
  · simp only [Icc_self, card_singleton, Nat.card_Icc, one_mul]
    rw [← Prod.Ioc_map_sectL, card_map, Nat.card_Ioc]
    omega
  · rw [disjoint_left]
    simp
    omega

open Finset in
lemma chainBetween_subset {a b c d : ℕ} (hac : a ≤ c) (hbd : b ≤ d) :
    chainBetween a b c d ⊆ Finset.Icc (a, b) (c, d) := by
  rw [chainBetween]
  split_ifs
  · rw [union_subset_iff]
    constructor
    · simp only [subset_iff, mem_Icc, and_imp, Prod.forall, Prod.mk_le_mk]
      omega
    · simp only [subset_iff, mem_Ioc, mem_Icc, and_imp, Prod.forall, Prod.mk_lt_mk, Prod.mk_le_mk]
      omega
  · simp

lemma chainBetween_inter {a b c d e f : ℕ}
    (hac : a ≤ c) (hbd : b ≤ d) (hce : c ≤ e) (hdf : d ≤ f) :
    chainBetween a b c d ∩ chainBetween c d e f = {(c, d)} := by
  ext ⟨x, y⟩
  simp [chainBetween, if_pos, *]
  omega

-- The chain between (a,b) and (e,f) that contains (c,d)
def chainBetweenMem (a b c d e f : ℕ) : Finset (ℕ × ℕ) :=
    chainBetween a b c d ∪ chainBetween c d e f

lemma chainBetweenMem_isChain {a b c d e f : ℕ} :
    IsChain (· ≤ ·) (chainBetweenMem a b c d e f).toSet := by
  rw [chainBetweenMem, IsChain, Finset.coe_union, Set.pairwise_union_of_symmetric]
  · refine ⟨chainBetween_isChain, chainBetween_isChain, ?_⟩
    rw [chainBetween]
    split_ifs
    case neg => simp
    case pos h₁ =>
      rw [chainBetween]
      split_ifs
      case neg => simp
      case pos h₂ =>
        simp only [Finset.coe_union, Finset.coe_Icc, Finset.coe_Ioc, Set.mem_union, Set.mem_Icc,
          Set.mem_Ioc, ne_eq, Prod.forall, Prod.mk_le_mk, Prod.mk_lt_mk, Prod.mk.injEq, not_and]
        omega
  · intro x y h
    exact h.symm

lemma image_chainBetweenMem_isChain {a b c d e f n : ℕ} :
    IsChain (· ≤ ·) ((chainBetweenMem a b c d e f).image (embed n)).toSet := by
  rw [Finset.coe_image]
  apply chainBetweenMem_isChain.image
  simp

open Finset in
lemma card_chainBetweenMem {a b c d e f : ℕ}
    (hac : a ≤ c) (hbd : b ≤ d) (hce : c ≤ e) (hdf : d ≤ f) :
    #(chainBetweenMem a b c d e f) = e + f + 1 - (a + b) := by
  rw [chainBetweenMem, card_union, chainBetween_inter hac hbd hce hdf]
  simp [card_chainBetween, *]
  omega

lemma middle_mem_chainBetweenMem {a b c d e f : ℕ}
    (hac : a ≤ c) (hbd : b ≤ d) :
    (c, d) ∈ chainBetweenMem a b c d e f := by
  rw [chainBetweenMem, Finset.mem_union]
  left
  exact right_mem_chainBetween hac hbd

lemma chainBetweenMem_subset {a b c d e f : ℕ}
    (hac : a ≤ c) (hbd : b ≤ d) (hce : c ≤ e) (hdf : d ≤ f) :
    chainBetweenMem a b c d e f ⊆ Finset.Icc (a, b) (e, f) := by
  rw [chainBetweenMem, Finset.union_subset_iff]
  refine ⟨(chainBetween_subset hac hbd).trans ?_, (chainBetween_subset hce hdf).trans ?_⟩
  · exact Finset.Icc_subset_Icc_right (by simp [*])
  · exact Finset.Icc_subset_Icc_left (by simp [*])

end make_chains

/--
If `C ∩ level n` is infinite, then infinitely many `C ∩ levelLine n s` are nonempty.
We later show that in the full context, cofinitely many are nonempty, but this is a useful
helper lemma.
-/
lemma levelLine_nonempty_of_infinite {n s : ℕ}
    (hCn : (C ∩ level n).Infinite) :
    ∃ s' > s, (C ∩ levelLine n s').Nonempty := by
  by_contra!
  have h₁ : C ∩ level n ⊆ embed n '' {(a, b) | a + b ≤ s} := by
    simp only [gt_iff_lt, Set.eq_empty_iff_forall_not_mem, Set.mem_inter_iff, not_and, «forall»,
      Prod.forall, toHollom_mem_levelLine_iff] at this
    simp only [Set.subset_def, Set.mem_inter_iff, Set.mem_image, Set.mem_setOf_eq, Prod.exists,
      and_imp, «forall», toHollom_mem_level_iff, Prod.forall]
    rintro a b n hab rfl
    refine ⟨a, b, ?_, rfl⟩
    by_contra! hsab
    exact this _ hsab _ _ _ hab rfl rfl
  have h₂ : Set.Finite {(a, b) | a + b ≤ s} := by
    refine (Set.finite_Iic (s, s)).subset ?_
    rintro ⟨a, b⟩
    simp only [Set.mem_setOf_eq, Set.mem_Iic, Prod.mk_le_mk]
    omega
  exact hCn ((h₂.image _).subset h₁)

lemma embed_image_Icc {a b c d n : ℕ} :
    embed n '' Set.Icc (a, b) (c, d) = Set.Icc (embed n (a, b)) (embed n (c, d)) := by
  rw [OrderEmbedding.image_Icc]
  rw [← level_eq_range]
  exact ordConnected_level

open Finset in
include hC hfC hfCid hf in
lemma C_touches_levelLine {n s x₀ y₀ : ℕ}
    (hCn : (C ∩ level n).Infinite)
    (hxy : toHollom (x₀, y₀, n) ∈ C) (hs : x₀ + y₀ ≤ s) :
    (C ∩ levelLine n s).Nonempty := by
  -- obtain rfl | lt := eq_or_lt_of_le hs
  -- · exact ⟨_, hxy, by simp⟩
  classical
  by_contra! hns
  obtain ⟨s₁, hs₁, hs₁n⟩ : ∃ s' > s, (C ∩ levelLine n s').Nonempty :=
    levelLine_nonempty_of_infinite hCn
  simp only [Set.Nonempty, Set.mem_inter_iff, «exists», Prod.exists, toHollom_mem_levelLine_iff,
    exists_eq_right_right] at hs₁n
  obtain ⟨x₁, y₁, hx₁y₁C, hx₁y₁s₁⟩ := hs₁n
  have h₁ : toHollom (x₀, y₀, n) ≤ toHollom (x₁, y₁, n) := by
    refine (hC.total hxy hx₁y₁C).resolve_right ?_
    simp only [toHollom_le_toHollom_iff_fixed_right, not_and, not_le]
    omega
  let int : Finset Hollom := (Finset.Icc (x₀, y₀) (x₁, y₁)).image (embed n)
  have int_eq : int = Set.Icc (toHollom (x₀, y₀, n)) (toHollom (x₁, y₁, n)) := by
    rw [Finset.coe_image, Finset.coe_Icc, embed_image_Icc]
    rfl
  have : #{x ∈ int | x ∈ C} ≤ (x₁ + y₁) - (x₀ + y₀) := by
    rw [filter_image]
    refine card_image_le.trans ?_
    have : {a ∈ Icc (x₀, y₀) (x₁, y₁) | embed n a ∈ C}.toSet.InjOn (fun x ↦ x.1 + x.2) := by
      rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd h
      simp only [coe_filter, mem_Icc, Set.mem_setOf_eq, Prod.mk_le_mk] at hab hcd h
      have := hC.total hab.2 hcd.2
      simp only [embed_le_embed_iff, Prod.mk_le_mk] at this
      simp
      omega
    rw [← card_image_of_injOn this]
    have h₁ : {a ∈ Icc (x₀, y₀) (x₁, y₁) | embed n a ∈ C}.image (fun x ↦ x.1 + x.2) ⊆
        Icc (x₀ + y₀) (x₁ + y₁) := by
      simp [Finset.subset_iff]
      omega
    have h₂ : {a ∈ Icc (x₀, y₀) (x₁, y₁) | embed n a ∈ C}.image (fun x ↦ x.1 + x.2) ⊆
        (Icc (x₀ + y₀) (x₁ + y₁)).erase s := by
      simp only [subset_erase, h₁, mem_image, mem_filter, mem_Icc, Prod.exists, Prod.mk_le_mk,
        not_exists, not_and, and_imp, true_and]
      intro a b ha₀ hb₀ ha₁ hb₁ hab habs
      exact Set.eq_empty_iff_forall_not_mem.1 hns _ ⟨hab, by simp [embed, habs]⟩
    refine (card_le_card h₂).trans ?_
    rw [card_erase_of_mem, Nat.card_Icc]
    · omega
    simp
    omega
  let D : Finset Hollom := (chainBetween x₀ y₀ x₁ y₁).image (embed n)
  have hD : D ⊆ int := by
    apply image_subset_image
    simp only [toHollom_le_toHollom_iff_fixed_right] at h₁
    exact chainBetween_subset h₁.1 h₁.2
  have hD' : ∀ x ∈ D, f x ∈ {x ∈ int | x ∈ C} := by
    intro x hx
    simp only [mem_filter]
    have hfx : f x ∈ C := hfC _
    refine ⟨?_, hfx⟩
    rw [← Finset.mem_coe, int_eq]
    apply apply_mem_interval hC hfC hfCid hf hxy hx₁y₁C
    rw [← int_eq, Finset.mem_coe]
    exact hD hx
  have h₂ : #{x ∈ int | x ∈ C} < #D := calc
    _ ≤ _ := this
    _ < #(chainBetween x₀ y₀ x₁ y₁) := by
      simp only [toHollom_le_toHollom_iff_fixed_right] at h₁
      rw [card_chainBetween h₁.1 h₁.2]
      omega
    _ = #D := by
      rw [card_image_of_injective]
      exact (embed n).injective
  obtain ⟨x, hx, y, hy, hxy, hfxy⟩ := exists_ne_map_eq_of_card_lt_of_maps_to h₂ hD'
  exact incomp_of_eq hf hfxy hxy (image_chainBetween_isChain.total hx hy)

def R (n : ℕ) (C : Set Hollom) : Set Hollom := {x ∈ level n | ∀ y ∈ C ∩ level n, x ≤ y ∨ y ≤ x}

variable {n : ℕ}
lemma R_subset_level : R n C ⊆ level n := Set.sep_subset (level n) _

lemma mem_R {n : ℕ} {C : Set Hollom} {x} :
  x ∈ R n C ↔ x ∈ level n ∧ ∀ y ∈ C ∩ level n, x ≤ y ∨ y ≤ x := Iff.rfl

lemma square_subset_above (h : (C ∩ level n).Finite) :
    ∀ᶠ a in atTop, embed n '' Set.Ici (a, a) ⊆ {x | ∀ y ∈ C ∩ level n, y ≤ x} := by
  obtain h | hne := (C ∩ level n).eq_empty_or_nonempty
  · simp [h]

  obtain ⟨a, b, hab⟩ : ∃ a b, ∀ c d, toHollom (c, d, n) ∈ C → c ≤ a ∧ d ≤ b := by
    obtain ⟨⟨a, b⟩, hab⟩ := (h.image (fun t ↦ ((ofHollom t).1, (ofHollom t).2.1))).bddAbove
    use a, b
    intro c d hcd
    simpa using hab ⟨toHollom (_, _, _), ⟨hcd, by simp⟩, rfl⟩

  rw [eventually_atTop]

  refine ⟨max a b, ?_⟩
  simp +contextual only [ge_iff_le, sup_le_iff, embed, RelEmbedding.coe_mk,
    Function.Embedding.coeFn_mk, Set.mem_inter_iff, and_imp, «forall», toHollom_mem_level_iff,
    Prod.forall, Set.subset_def, Set.mem_image, Set.mem_Ici, Prod.exists, Prod.mk_le_mk,
    Set.mem_setOf_eq, forall_exists_index, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq,
    toHollom_le_toHollom_iff_fixed_right]

  rintro k hak hbk _ _ _ f g hkf hkg rfl rfl rfl c d n hcd rfl
  specialize hab c d hcd
  omega

lemma square_subset_R (h : (C ∩ level n).Finite) :
    ∀ᶠ a in atTop, embed n '' Set.Ici (a, a) ⊆ R n C := by
  filter_upwards [square_subset_above h] with a ha
  rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
  exact ⟨by simp [embed], fun b hb ↦ .inr (ha ⟨_, hxy, rfl⟩ _ hb)⟩

lemma R_infinite (h : (C ∩ level n).Finite) : (R n C).Infinite := by
  obtain ⟨a, ha⟩ := (square_subset_R h).exists
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
    ∀ᶠ a in atTop, embed n '' Set.Ici (a, a) ⊆ S n C := by
  rw [S, if_pos h']

  obtain ⟨b, c, hab⟩ : ∃ b c, ∀ d e, toHollom (d, e, n + 1) ∈ C → (d, e) ≤ (b, c) := by
    obtain ⟨⟨b, c⟩, hbc⟩ := (h'.image (fun t ↦ ((ofHollom t).1, (ofHollom t).2.1))).bddAbove
    use b, c
    intro d e hde
    simpa using hbc ⟨toHollom (_, _, _), ⟨hde, by simp⟩, rfl⟩

  have : ∀ᶠ a in atTop, embed n '' .Ici (a, a) ⊆ {x | ∀ y ∈ C ∩ level (n + 1), x ≤ y ∨ y ≤ x} := by
    rw [eventually_atTop, level_eq]
    refine ⟨max b c, ?_⟩
    simp only [ge_iff_le, sup_le_iff, embed, RelEmbedding.coe_mk, Function.Embedding.coeFn_mk,
      Set.mem_inter_iff, Set.mem_setOf_eq, and_imp, «forall», ofHollom_toHollom, Prod.forall,
      Set.subset_def, Set.mem_image, Set.mem_Ici, Prod.exists, Prod.mk_le_mk, forall_exists_index,
      EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
    rintro d hbd hcd _ _ _ e f hde hdf rfl rfl rfl g h _ hgh rfl
    right
    apply toHollom_le_toHollom _ (by simp)
    have := hab _ _ hgh
    simp only [Prod.mk_le_mk] at this ⊢
    omega

  filter_upwards [square_subset_R h, this] with a h₁ h₂
  exact Set.subset_inter h₁ h₂

lemma square_subset_S_case_2 (h : (C ∩ level n).Finite) (h' : (C ∩ level (n + 1)).Infinite) :
    ∀ᶠ a in atTop, embed n '' Set.Ici (a, a) ⊆ S n C := by
  rw [S, if_neg h']
  change ∀ᶠ a : ℕ in atTop, _ ⊆ R n C ∩ {x | _ + 1 ≤ _}
  filter_upwards [eventually_ge_atTop (x0 n C + 1), eventually_ge_atTop (y0 n C + 1),
    square_subset_R h] with a hax hay haR
  refine Set.subset_inter haR ?_
  simp only [embed, RelEmbedding.coe_mk, Function.Embedding.coeFn_mk, le_inf_iff, Set.subset_def,
    Set.mem_image, Set.mem_Ici, Prod.exists, Prod.mk_le_mk, Set.mem_setOf_eq, forall_exists_index,
    and_imp, «forall», EmbeddingLike.apply_eq_iff_eq, ofHollom_toHollom, Prod.forall, Prod.mk.injEq]
  rintro _ _ _ b c hae haf rfl rfl rfl
  omega

lemma square_subset_S (h : (C ∩ level n).Finite) :
    ∀ᶠ a in atTop, embed n '' Set.Ici (a, a) ⊆ S n C := by
  cases (C ∩ level (n + 1)).finite_or_infinite with
  | inl h' => exact square_subset_S_case_1 h h'
  | inr h' => exact square_subset_S_case_2 h h'

lemma S_infinite (h : (C ∩ level n).Finite) : (S n C).Infinite := by
  obtain ⟨a, ha⟩ := (square_subset_S h).exists
  refine ((Set.Ici_infinite _).image ?_).mono ha
  aesop (add norm unfold [Set.InjOn, embed])



-- include hC hfC hfCid hf in
-- lemma C_touches_levelLine {n s x₀ y₀ : ℕ}
--     (hCn : (C ∩ level n).Infinite)
--     (hxy : toHollom (x₀, y₀, n) ∈ C) (hs : x₀ + y₀ ≤ s) :
--     (C ∩ levelLine n s).Nonempty := by

lemma left_or_right_bias {n : ℕ} (a b : ℕ)
    (hab : ∀ x ∈ C ∩ level n, toHollom (a, b, n) ≤ x)
    (hCn : (C ∩ level n).Infinite) :
    (∀ i : ℕ, ∃ j ∈ C ∩ level n, toHollom (a, i, n) ≤ j) ∨
    (∀ i : ℕ, ∃ j ∈ C ∩ level n, toHollom (i, b, n) ≤ j) := by
  by_contra! h
  obtain ⟨⟨c, hc⟩, d, hd⟩ := h

  have : C ∩ level n ⊆ embed n '' Set.Iic (d, c) := by
    simp only [Set.subset_def, Set.mem_inter_iff, Set.mem_image, Set.mem_Iic, Prod.exists,
      Prod.mk_le_mk, and_imp, «forall», toHollom_mem_level_iff, Prod.forall]
    rintro x y n hxy rfl
    specialize hab (toHollom (x, y, n)) (by simp [hxy])
    specialize hc (toHollom (x, y, n)) (by simp [hxy])
    specialize hd (toHollom (x, y, n)) (by simp [hxy])
    simp_all only [toHollom_le_toHollom_iff_fixed_right, true_and, not_le, and_true]
    exact ⟨_, _, ⟨hd.le, hc.le⟩, rfl⟩

  exact hCn (((Set.finite_Iic (d, c)).image _).subset this)

-- lemma left_or_right_strong_bias {n : ℕ} (a b : ℕ)
--     (hab : ∀ x ∈ C ∩ level n, toHollom (a, b, n) ≤ x)
--     (hCn : (C ∩ level n).Infinite) :
--     (∀ i : ℕ, ∀ᶠ j in atTop, j ∈ C ∩ level n ∧ toHollom (a, i, n) ≤ j) ∨
--     (∀ i : ℕ, ∀ᶠ j in atTop, j ∈ C ∩ level n ∧ toHollom (i, b, n) ≤ j) := by
--   sorry

lemma chain_intersect_antichain {α : Type*} [PartialOrder α] {s t : Set α}
    (hs : IsChain (· ≤ ·) s) (ht : IsAntichain (· ≤ ·) t) :
    (s ∩ t).Subsingleton := by
  simp only [Set.Subsingleton, Set.mem_inter_iff, and_imp]
  intro x hxs hxt y hys hyt
  by_contra! hne
  cases hs.total hxs hys
  case inl h => exact ht hxt hyt hne h
  case inr h => exact ht hyt hxt hne.symm h

open Classical in
noncomputable def p (n : ℕ) (C : Set Hollom) (f : Hollom → Hollom) (s : ℕ) : Hollom :=
  if h : IsChain (· ≤ ·) C ∧ (∀ x, f x ∈ C) ∧ (∀ x ∈ C, f x = x) ∧
        (∀ x, IsAntichain (fun x1 x2 ↦ x1 ≤ x2) (f ⁻¹' {x})) ∧ (C ∩ level (n + 1)).Infinite ∧
        x0 n C + y0 n C ≤ s
    then (C_touches_levelLine h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1
          (x0_y0_mem h.2.2.2.2.1.nonempty) h.2.2.2.2.2).choose
    else toHollom (0, 0, n + 1)

include hC hfC hfCid hf in
lemma p_mem_inter
    (hnC : (C ∩ level (n + 1)).Infinite)
    {s : ℕ} (hs : x0 n C + y0 n C ≤ s) :
    p n C f s ∈ C ∩ levelLine (n + 1) s := by
  rw [p, dif_pos ⟨hC, hfC, hfCid, hf, hnC, hs⟩]
  exact Exists.choose_spec (C_touches_levelLine hC hfC hfCid hf hnC (x0_y0_mem hnC.nonempty) hs)

include hC hfC hfCid hf in
lemma p_mem_C
    (hnC : (C ∩ level (n + 1)).Infinite) {s : ℕ} (hs : x0 n C + y0 n C ≤ s) :
    p n C f s ∈ C :=
  (p_mem_inter hC hfC hfCid hf hnC hs).1

include hC hfC hfCid hf in
lemma p_uniq
    (hnC : (C ∩ level (n + 1)).Infinite)
    {s : ℕ} (hs : x0 n C + y0 n C ≤ s)
    {x : Hollom} (hx : x ∈ C ∩ levelLine (n + 1) s) :
    p n C f s = x :=
  chain_intersect_antichain hC isAntichain_levelLine (p_mem_inter hC hfC hfCid hf hnC hs) hx

include hC hfC hfCid hf in
lemma singleton_p (hnC : (C ∩ level (n + 1)).Infinite) {s : ℕ} (hs : x0 n C + y0 n C ≤ s) :
    {p n C f s} = C ∩ levelLine (n + 1) s := by
  rw [eq_comm, Set.eq_singleton_iff_unique_mem]
  refine ⟨p_mem_inter hC hfC hfCid hf hnC hs, ?_⟩
  intro x hx
  exact (p_uniq hC hfC hfCid hf hnC hs hx).symm

include hC hfC hfCid hf in
lemma p_uniq'
    (hnC : (C ∩ level (n + 1)).Infinite)
    {s : ℕ} (hs : x0 n C + y0 n C ≤ s)
    {x y : ℕ} (hxy : x + y = s)
    (hxyC : toHollom (x, y, n + 1) ∈ C) :
    p n C f s = toHollom (x, y, n + 1) :=
  p_uniq hC hfC hfCid hf hnC hs (by simp [hxyC, hxy])

include hC hfC hfCid hf in
lemma p_zero
    (hnC : (C ∩ level (n + 1)).Infinite) :
    p n C f (x0 n C + y0 n C) = toHollom (x0 n C, y0 n C, n + 1) :=
  p_uniq' hC hfC hfCid hf hnC le_rfl rfl (x0_y0_mem hnC.nonempty)

include hC hfC hfCid hf in
lemma p_lt_p
    (hnC : (C ∩ level (n + 1)).Infinite)
     {s₁ s₂ : ℕ} (hs₁ : x0 n C + y0 n C ≤ s₁) (h : s₁ < s₂) :
    p n C f s₁ < p n C f s₂ := by
  have h₁ : p n C f s₁ ∈ C ∩ _ := p_mem_inter hC hfC hfCid hf hnC hs₁
  have h₂ : p n C f s₂ ∈ C ∩ _ := p_mem_inter hC hfC hfCid hf hnC (hs₁.trans h.le)
  set x₁ : Hollom := p n C f s₁ with hx₁
  set x₂ : Hollom := p n C f s₂ with hx₂
  clear_value x₁ x₂
  revert x₂ x₁
  simp only [Set.mem_inter_iff, gt_iff_lt, and_imp, «forall», Prod.forall,
    toHollom_mem_levelLine_iff]
  rintro x₂ y₂ _ h₂ rfl rfl h₂' x₁ y₁ _ h₁ rfl rfl h₁'
  apply lt_of_le_of_ne _ (by simp; omega)
  apply hC.le_of_not_lt h₂ h₁
  intro h'
  replace h' := h'.le
  simp only [toHollom_le_toHollom_iff_fixed_right] at h'
  omega

include hC hfC hfCid hf in
lemma p_le_p
    (hnC : (C ∩ level (n + 1)).Infinite)
     {s₁ s₂ : ℕ} (hs₁ : x0 n C + y0 n C ≤ s₁) (h : s₁ ≤ s₂) :
    p n C f s₁ ≤ p n C f s₂ := by
  obtain rfl | h := h.eq_or_lt
  case inl => simp
  case inr => exact (p_lt_p hC hfC hfCid hf hnC hs₁ h).le

include hC hfC hfCid hf in
lemma p_strictMonoOn (hnC : (C ∩ level (n + 1)).Infinite) :
    StrictMonoOn (p n C f) (Set.Ici (x0 n C + y0 n C)) :=
  fun _ hx _ _ h ↦ p_lt_p hC hfC hfCid hf hnC hx h

include hC hfC hfCid hf in
lemma p_injOn (hnC : (C ∩ level (n + 1)).Infinite) :
    Set.InjOn (p n C f) (Set.Ici (x0 n C + y0 n C)) :=
  (p_strictMonoOn hC hfC hfCid hf hnC).injOn

include hC hfC hfCid hf in
lemma p_image_Icc {l : ℕ}
    (hnC : (C ∩ level (n + 1)).Infinite) :
    p n C f '' Set.Icc (x0 n C + y0 n C) (x0 n C + y0 n C + l) =
      C ∩ Set.Icc (p n C f (x0 n C + y0 n C)) (p n C f (x0 n C + y0 n C + l)) := by
  refine subset_antisymm ?_ ?_
  · simp only [Set.image_subset_iff]
    simp only [Set.preimage_inter, Set.subset_def, Set.mem_Icc, Set.mem_inter_iff, Set.mem_preimage,
      and_imp]
    intro i hi hil
    exact ⟨p_mem_C hC hfC hfCid hf hnC hi, p_le_p hC hfC hfCid hf hnC le_rfl hi,
      p_le_p hC hfC hfCid hf hnC hi hil⟩
  · simp only [Set.subset_def, Set.mem_inter_iff, Set.mem_Icc, Set.mem_image, and_imp, «forall»,
      Prod.forall]
    rintro x y z hxyC hxyl hxyu
    obtain rfl : z = n + 1 := by
      have hl : p n C f (x0 n C + y0 n C) ∈ _ :=
        levelLine_subset_level (p_mem_inter hC hfC hfCid hf hnC le_rfl).2
      have hu : p n C f (x0 n C + y0 n C + l) ∈ _ :=
        levelLine_subset_level (p_mem_inter hC hfC hfCid hf hnC (by simp)).2
      simpa using ordConnected_level.out hl hu ⟨hxyl, hxyu⟩
    have : x0 n C + y0 n C ≤ x + y := by
      rw [p_zero hC hfC hfCid hf hnC, toHollom_le_toHollom_iff_fixed_right] at hxyl
      omega
    have' := p_uniq' hC hfC hfCid hf hnC this rfl hxyC
    refine ⟨x + y, ⟨‹_›, ?_⟩, this⟩
    by_contra! h
    rw [← this] at hxyu
    exact hxyu.not_lt (p_lt_p hC hfC hfCid hf hnC (by simp) h)

include hC hfC hfCid hf in
lemma p_image_Ici
    (hnC : (C ∩ level (n + 1)).Infinite) :
    p n C f '' Set.Ici (x0 n C + y0 n C) = C ∩ level (n + 1) := by
  rw [← iUnion_levelLine, Set.inter_iUnion]
  ext x
  simp only [Set.mem_image, Set.mem_Ici, Set.mem_iUnion, Set.mem_inter_iff, exists_and_left]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨p_mem_C hC hfC hfCid hf hnC hs, s, (p_mem_inter hC hfC hfCid hf hnC hs).2⟩
  · simp only [and_imp, forall_exists_index]
    intro hx s hx'
    have : x0 n C + y0 n C ≤ s := by
      revert x
      simp only [«forall», Prod.forall, toHollom_mem_levelLine_iff, and_imp]
      rintro x y _ hxy rfl rfl
      have' := x0_y0_min hC  hxy
      simp only [toHollom_le_toHollom_iff_fixed_right] at this
      omega
    exact ⟨s, ‹_›, p_uniq hC hfC hfCid hf hnC this ⟨hx, hx'⟩⟩

open Finset in
lemma surjOn_of_injOn_of_card_le {α β : Type*} {s : Finset α} {t : Finset β}
    (f : α → β) (hf : Set.MapsTo f s t)
    (hinj : Set.InjOn f s) (hst : #t ≤ #s) :
    Set.SurjOn f s t := fun y hy ↦
  let ⟨x, hx, hy⟩ :=
    surj_on_of_inj_on_of_card_le (fun x _ ↦ f x) hf (fun _ _ h h' ↦ hinj h h') hst y hy
  ⟨x, hx, hy.symm⟩

open Finset in
include hC hfC hfCid hf in
lemma eqn_1_aux
    {n : ℕ}
    (hnC : (C ∩ level (n + 1)).Infinite)
    (h : ∀ i : ℕ, ∃ j ∈ C ∩ level (n + 1), toHollom (i, y0 n C, n + 1) ≤ j)
    (i : ℕ) :
    False := by
  classical
  have hp0 : p n C f (x0 n C + y0 n C) = toHollom (x0 n C, y0 n C, n + 1) := by
    rw [p_zero hC hfC hfCid hf hnC]

  have hlow : toHollom (x0 n C, y0 n C, n + 1) ≤ toHollom (x0 n C + i, y0 n C, n + 1) := by simp
  obtain ⟨l, hl, hl'⟩ :
      ∃ l, i ≤ l ∧ toHollom (x0 n C + i, y0 n C, n + 1) ≤ p n C f (x0 n C + y0 n C + l) := by
    specialize h (x0 n C + i)
    simp only [Set.mem_inter_iff, «exists», toHollom_mem_level_iff, Prod.exists] at h
    obtain ⟨a, b, _, ⟨hab, rfl⟩, habC⟩ := h
    have habC' := habC
    simp only [toHollom_le_toHollom_iff_fixed_right] at habC'
    have : p n C f (a + b) = toHollom (a, b, n + 1) :=
      p_uniq' hC hfC hfCid hf hnC (by omega) rfl hab
    refine ⟨a + b - (x0 n C + y0 n C), by omega, habC.trans_eq ?_⟩
    rw [← this]
    congr 1
    omega

  set top := p n C f (x0 n C + y0 n C + l) with htop
  clear_value top
  induction top with | h x y z =>
  have htop' : toHollom (x, y, z) ∈ C ∩ levelLine (n + 1) (x0 n C + y0 n C + l) := by
    rw [htop]
    exact p_mem_inter hC hfC hfCid hf hnC (by omega)
  simp only [Set.mem_inter_iff, toHollom_mem_levelLine_iff] at htop'
  obtain ⟨hxy, hxyC, rfl⟩ := htop'
  let E : Finset Hollom :=
    (chainBetweenMem (x0 n C) (y0 n C) (x0 n C + i) (y0 n C) x y).image (embed (n + 1))
  have card_E : #E = l + 1 := by
    simp only [toHollom_le_toHollom_iff_fixed_right] at hl'
    rw [card_image_of_injective _ (embed (n + 1)).injective,
      card_chainBetweenMem (by simp) (by simp) hl'.1 hl'.2]
    omega
  let int := (Finset.Icc (x0 n C, y0 n C) (x, y)).image (embed (n + 1))
  have int_eq : int = Set.Icc (toHollom (x0 n C, y0 n C, n + 1)) (toHollom (x, y, n + 1)) := by
    rw [Finset.coe_image, Finset.coe_Icc, embed_image_Icc]
    rfl
  have E_subset : E ⊆ int := by
    apply Finset.image_subset_image
    simp only [toHollom_le_toHollom_iff_fixed_right] at hl'
    exact chainBetweenMem_subset (by simp) (by simp) hl'.1 hl'.2
  have E_maps : ∀ z ∈ E, f z ∈ int := by
    intro z hz
    rw [← Finset.mem_coe, int_eq]
    refine apply_mem_interval hC hfC hfCid hf (x0_y0_mem hnC.nonempty) hxy ?_
    rw [← int_eq, Finset.mem_coe]
    exact E_subset hz
  replace E_maps : Set.MapsTo f E {z ∈ int | z ∈ C}.toSet := by
    intro z hz
    simp only [coe_filter, Set.mem_setOf_eq]
    exact ⟨E_maps _ hz, hfC _⟩
  have h₂ : {z ∈ int | z ∈ C} = (Icc (x0 n C + y0 n C) (x0 n C + y0 n C + l)).image (p n C f) := by
    apply Finset.coe_injective
    rw [coe_filter, coe_image, coe_Icc, p_image_Icc hC hfC hfCid hf hnC]
    change ↑int ∩ C = _
    rw [int_eq, Set.inter_comm, hp0, htop]
  have E_card : #{z ∈ int | z ∈ C} = l + 1 := by
    rw [h₂, card_image_of_injOn, Nat.card_Icc]
    · omega
    · simp only [coe_Icc]
      exact Set.InjOn.mono Set.Icc_subset_Ici_self (p_injOn hC hfC hfCid hf hnC)
  have hs : Set.SurjOn f E {z ∈ int | z ∈ C}.toSet := by
    refine surjOn_of_injOn_of_card_le f E_maps ?_ ?_
    · refine injOn_chain hf image_chainBetweenMem_isChain
    · rw [E_card, card_E]
  have : p n C f (x0 n C + y0 n C + i) ∈ {z ∈ int | z ∈ C}.toSet := by
    rw [h₂, coe_image, coe_Icc]
    refine ⟨_, ?_, rfl⟩
    simp only [Set.mem_Icc, le_add_iff_nonneg_right, zero_le, add_le_add_iff_left, true_and, hl]
  obtain ⟨z, hz, hz'⟩ := hs this
  simp only [coe_image, Set.mem_image, mem_coe, Prod.exists, E] at hz
  sorry


    -- rw [this]
    -- exact ⟨p_mem_inter hC hfC hfCid hf hnC (by omega), x + y, hxy, rfl⟩

include hC hfC hfCid hf in
lemma S_maps {x : Hollom} (hx : x ∈ S n C) (hx' : x ∉ C ∩ level n) : f x ∉ C ∩ level (n + 1) := by
  cases (C ∩ level (n + 1)).finite_or_infinite
  case inl h =>
    rw [S, if_pos h, Set.mem_setOf_eq] at hx
    intro hy
    refine incomp_apply hfC hfCid hf ?_ (hx.2 _ hy).symm
    have := R_subset_level hx.1
    simp only [level_eq, Set.mem_setOf_eq] at this
    intro h
    simp [level_eq, h, this] at hy

  case inr h =>
    induction x with | h x y n =>
    obtain rfl := by simpa using S_subset_level hx
    simp only [S, if_neg h, Set.mem_setOf_eq, ofHollom_toHollom] at hx
    have (i : ℕ) : toHollom (x0 n C + i, y0 n C, n + 1) ≤ toHollom (x, y, n) :=
      .next_min (hx.2.trans' (by simp))
    intro hp
    rw [← p_image_Ici hC hfC hfCid hf h] at hp
    sorry







  -- · simp only [Set.not_infinite] at h
  --   rw [S, if_pos h] at hx
  --   simp? at hx

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
