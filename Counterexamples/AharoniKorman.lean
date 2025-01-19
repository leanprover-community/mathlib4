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

The proof structure is as follows:
* Begin by defining the type `Hollom` as a synonym for `ℕ³` and giving it the partial order
  structure as required.
* Define the levels `level` of the partial order, corresponding to `L` in the informal proof.
* Show that this partial order has no infinite antichains (`Hollom.no_infinite_antichain`).
* Given a chain `C`, show that for infinitely many `n`, `C ∩ level n` must be finite
  (`exists_finite_intersection`).
* Given a chain `C`, the existence of a partition with the desired properties is equivalent to the
  existence of a "spinal map" (`exists_partition_iff_nonempty_spinalMap`). A spinal map is a
  function from the partial order to `C`, which is identity on `C` and for which each fiber is an
  antichain.

From this point forward, we assume `C` is a chain and that we have a spinal map to `C`, with the
aim of reaching a contradiction (as then, no such partition can exist). We may further assume that
`n ≠ 0` and `C ∩ level n` is finite.

* Define a subset `S` of `level n`, and we will aim to show a contradiction by considering
  the image of `S` under the spinal map. By construction, no element of `S` can be mapped into
  `level n`.
* The subset `S \ (C ∩ level n)` contains some "infinite square", i.e. a set of the form
  `{(x, y, n) | a ≤ x ∧ a ≤ y}` for some `a` (`square_subset_S`).
* For two points of `C` in the same level, the intersection of `C` with the interval between
  them is exactly the length of a maximal chain between them (`card_C_inter_Icc_eq`).
* For two points of `C` in the same level, and two points `(a, b, n)` and `(c, d, n)` between them,
  if `a + b = c + d` then `f (a, b, n) = f (c, d, n)` (`apply_eq_of_line_eq`).
* No element of `S ​\ (C ∩ level n)` can be mapped into `level (n + 1)` (`not_S_hits_next`). This
  step vitally uses the previous two facts.
* If all of `S \ (C ∩ level n)` is mapped into `level (n - 1)`, then we have a contradiction
  (`not_S_mapsTo_previous`).
* But as `f` maps each element of `S \ (C ∩ level n)` to `level (n - 1) ∪ level n ∪ level (n + 1)`,
  we have a contradiction (`no_spinalMap`), and therefore show that no spinal map exists.
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

lemma Set.IsWF.of_wellFoundedLT {α : Type*} {s : Set α} [LT α] [WellFoundedLT α] : Set.IsWF s :=
  (Set.isWF_univ_iff.2 wellFounded_lt).mono (Set.subset_univ _)

/--
If `α` is a linear order with well-founded `<`, then the universe is a partially well-ordered set.
Note this does not hold without the linearity assumption.
-/
lemma Set.IsPWO.of_linearOrder {α : Type*} {s : Set α} [LinearOrder α] [WellFoundedLT α] :
    s.IsPWO :=
  IsWF.of_wellFoundedLT.isPWO

open Finset

lemma Finset.surjOn_of_injOn_of_card_le {α β : Type*} {s : Finset α} {t : Finset β}
    (f : α → β) (hf : Set.MapsTo f s t) (hinj : Set.InjOn f s) (hst : #t ≤ #s) :
    Set.SurjOn f s t := by
  classical
  suffices s.image f = t by simp [← this, Set.SurjOn]
  have : s.image f ⊆ t := by aesop (add simp Finset.subset_iff)
  exact eq_of_subset_of_card_le this (hst.trans_eq (card_image_of_injOn hinj).symm)

lemma Finset.surj_on_of_inj_on_of_card_le_again {α β : Type*} {s : Finset α} {t : Finset β}
    (f : ∀ a ∈ s, β) (hf : ∀ a ha, f a ha ∈ t)
    (hinj : ∀ a₁ a₂ ha₁ ha₂, f a₁ ha₁ = f a₂ ha₂ → a₁ = a₂) (hst : #t ≤ #s) :
    ∀ b ∈ t, ∃ a ha, b = f a ha := by
  let f' : s → β := fun a ↦ f a a.property
  have hinj' : Set.InjOn f' s.attach := fun x hx y hy hxy => Subtype.ext (hinj _ _ x.2 y.2 hxy)
  have hmapsto' : Set.MapsTo f' s.attach t := fun x hx => hf _ _
  intro b hb
  obtain ⟨a, ha, rfl⟩ := surjOn_of_injOn_of_card_le f' hmapsto' hinj' (by rwa [card_attach]) hb
  exact ⟨a, a.2, rfl⟩

lemma Finset.injOn_of_surjOn_of_card_le {α β : Type*} {s : Finset α} {t : Finset β}
    (f : α → β) (hf : Set.MapsTo f s t) (hsurj : Set.SurjOn f s t) (hst : #s ≤ #t) :
    Set.InjOn f s := by
  classical
  rw [← card_image_iff]
  have : s.image f = t := Finset.coe_injective <| by simp [hsurj.image_eq_of_mapsTo hf]
  have : #(s.image f) = #t := by rw [this]
  have : #(s.image f) ≤ #s := card_image_le
  omega

lemma chain_intersect_antichain {α : Type*} [PartialOrder α] {s t : Set α}
    (hs : IsChain (· ≤ ·) s) (ht : IsAntichain (· ≤ ·) t) :
    (s ∩ t).Subsingleton := by
  simp only [Set.Subsingleton, Set.mem_inter_iff, and_imp]
  intro x hxs hxt y hys hyt
  by_contra! hne
  cases hs.total hxs hys
  case inl h => exact ht hxt hyt hne h
  case inr h => exact ht hyt hxt hne.symm h

lemma IsChain.le_of_not_lt {α : Type*} [Preorder α] {s : Set α} (hs : IsChain (· ≤ ·) s)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) (h : ¬ x < y) : y ≤ x := by
  cases hs.total hx hy with
  | inr h' => exact h'
  | inl h' => simpa [lt_iff_le_not_le, h'] using h

lemma IsChain.lt_of_not_le {α : Type*} [Preorder α] {s : Set α} (hs : IsChain (· ≤ ·) s)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) (h : ¬ x ≤ y) : y < x :=
  (hs.total hx hy).elim (h · |>.elim) (lt_of_le_not_le · h)

lemma Set.SurjOn.of_comp {α β γ : Type*}
    {r : Set α} {s : Set β} {t : Set γ} {f : α → β} {g : β → γ}
    (h : Set.SurjOn (g ∘ f) r t) (hr : Set.MapsTo f r s) : Set.SurjOn g s t := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := h hz
  exact ⟨f x, hr hx, rfl⟩

lemma isChain_union {α : Type*} [Preorder α] {s t : Set α} :
    IsChain (· ≤ ·) (s ∪ t) ↔
      IsChain (· ≤ ·) s ∧ IsChain (· ≤ ·) t ∧ ∀ a ∈ s, ∀ b ∈ t, a ≠ b → a ≤ b ∨ b ≤ a := by
  rw [IsChain, IsChain, IsChain, Set.pairwise_union_of_symmetric]
  intro x y
  exact Or.symm

namespace Finset

variable {α β : Type*}

section sectL

variable [Preorder α] [PartialOrder β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]
  [DecidableRel (α := α × β) (· ≤ ·)] (a b : α) (c : β)

lemma Icc_map_sectL : (Icc a b).map (.sectL _ c) = Icc (a, c) (b, c) := by
  aesop (add safe forward [le_antisymm, not_lt_of_le, le_of_lt])

lemma Ioc_map_sectL : (Ioc a b).map (.sectL _ c) = Ioc (a, c) (b, c) := by
  aesop (add safe forward [le_antisymm, not_lt_of_le, le_of_lt])

lemma Ico_map_sectL : (Ico a b).map (.sectL _ c) = Ico (a, c) (b, c) := by
  aesop (add safe forward [le_antisymm, not_lt_of_le, le_of_lt])

lemma Ioo_map_sectL : (Ioo a b).map (.sectL _ c) = Ioo (a, c) (b, c) := by
  aesop (add safe forward [le_antisymm, not_lt_of_le, le_of_lt])

end sectL

section sectR

variable [PartialOrder α] [Preorder β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]
  [DecidableRel (α := α × β) (· ≤ ·)] (c : α) (a b : β)

lemma Icc_map_sectR : (Icc a b).map (.sectR c _) = Icc (c, a) (c, b) := by
  aesop (add safe forward [le_antisymm, not_lt_of_le, le_of_lt])

lemma Ioc_map_sectR : (Ioc a b).map (.sectR c _) = Ioc (c, a) (c, b) := by
  aesop (add safe forward [le_antisymm, not_lt_of_le, le_of_lt])

lemma Ico_map_sectR : (Ico a b).map (.sectR c _) = Ico (c, a) (c, b) := by
  aesop (add safe forward [le_antisymm, not_lt_of_le, le_of_lt])

lemma Ioo_map_sectR : (Ioo a b).map (.sectR c _) = Ioo (c, a) (c, b) := by
  aesop (add safe forward [le_antisymm, not_lt_of_le, le_of_lt])

end sectR

end Finset

end to_move

attribute [aesop norm 10 tactic] Lean.Elab.Tactic.Omega.omegaDefault
attribute [aesop 2 simp] Set.subset_def Finset.subset_iff

/-- A type synonym on ℕ³ on which we will construct Hollom's partial order P_5. -/
def Hollom : Type := ℕ × ℕ × ℕ
  deriving DecidableEq

/--
The backward equivalence between ℕ³ and the underlying set in Hollom's partial order.
Note that this equivalence does not respect the partial order relation, and therefore should be used
explicitly to transfer between the two types, despite their being equal.
-/
def ofHollom : Hollom ≃ ℕ × ℕ × ℕ := Equiv.refl _
/--
The forward equivalence between ℕ³ and the underlying set in Hollom's partial order.
Note that this equivalence does not respect the partial order relation, and therefore should be used
explicitly to transfer between the two types, despite their being equal.
-/
def toHollom : ℕ × ℕ × ℕ ≃ Hollom := Equiv.refl _

@[simp] lemma ofHollom_symm_eq : ofHollom.symm = toHollom := rfl
@[simp] lemma toHollom_symm_eq : toHollom.symm = ofHollom := rfl

@[simp] lemma ofHollom_toHollom (x) : ofHollom (toHollom x) = x := rfl
@[simp] lemma toHollom_ofHollom (x) : toHollom (ofHollom x) = x := rfl

namespace Hollom

@[simp] lemma «forall» {p : Hollom → Prop} : (∀ x, p x) ↔ ∀ x, p (toHollom x) := Iff.rfl
@[simp] lemma «exists» {p : Hollom → Prop} : (∃ x, p x) ↔ ∃ x, p (toHollom x) := Iff.rfl

local notation3 "h(" x ", " y ", " z ")" => toHollom (x, y, z)

@[elab_as_elim, induction_eliminator, cases_eliminator]
lemma induction {p : Hollom → Prop} (h : ∀ x y z, p (h(x, y, z))) : ∀ x, p x := by simpa

/--
The ordering on ℕ³ which is used to define Hollom's example P₅
-/
@[mk_iff]
inductive HollomOrder : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ → Prop
  | twice {x y n u v m : ℕ} : m + 2 ≤ n → HollomOrder (x, y, n) (u, v, m)
  | within {x y u v m : ℕ} : x ≤ u → y ≤ v → HollomOrder (x, y, m) (u, v, m)
  | next_min {x y u v m : ℕ} : min x y + 1 ≤ min u v → HollomOrder (x, y, m + 1) (u, v, m)
  | next_add {x y u v m : ℕ} : x + y ≤ 2 * (u + v) → HollomOrder (x, y, m + 1) (u, v, m)

instance : PartialOrder Hollom where
  le x y := HollomOrder (ofHollom x) (ofHollom y)
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
  le_antisymm
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

@[simp] lemma toHollom_le_toHollom_iff_fixed_right {a b c d n : ℕ} :
    h(a, b, n) ≤ h(c, d, n) ↔ a ≤ c ∧ b ≤ d := by
  refine ⟨?_, ?_⟩
  · rintro (_ | _)
    · omega
    · omega
  · rintro ⟨h₁, h₂⟩
    exact .within h₁ h₂

lemma le_of_toHollom_le_toHollom {a b c d e f : ℕ} :
    h(a, b, c) ≤ h(d, e, f) → f ≤ c
  | .twice _ => by omega
  | .within _ _ => by omega
  | .next_add _ => by omega
  | .next_min _ => by omega

lemma toHollom_le_toHollom {a b c d e f : ℕ} (h : (a, b) ≤ (d, e)) (hcf : f ≤ c) :
    h(a, b, c) ≤ h(d, e, f) := by
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
def level (n : ℕ) : Set Hollom := {h(x, y, n) | (x : ℕ) (y : ℕ)}

lemma level_eq (n : ℕ) : level n = {x | (ofHollom x).2.2 = n} := by
  simp [Set.ext_iff, level, eq_comm]

@[simp] lemma toHollom_mem_level_iff {n : ℕ} {x} : toHollom x ∈ level n ↔ x.2.2 = n := by
  simp [level_eq]

@[elab_as_elim, induction_eliminator, cases_eliminator]
lemma induction_on_level {n : ℕ} {p : (x : Hollom) → x ∈ level n → Prop}
    (h : ∀ x y, p h(x, y, n) (by simp)) :
    ∀ {x : Hollom}, (h : x ∈ level n) → p x h := by
  simp +contextual only [«forall», toHollom_mem_level_iff, Prod.forall]
  rintro x y _ rfl
  exact h _ _

/--
For each `n`, there is an order embedding from ℕ × ℕ (which has the product order) to the Hollom
partial order.
-/
def embed (n : ℕ) : ℕ × ℕ ↪o Hollom where
  toFun x := h(x.1, x.2, n)
  inj' x := by aesop
  map_rel_iff' := by simp

lemma embed_apply (n : ℕ) (x y : ℕ) : embed n (x, y) = h(x, y, n) := rfl

lemma embed_strictMono {n : ℕ} : StrictMono (embed n) := (embed n).strictMono

lemma level_eq_range (n : ℕ) : level n = Set.range (embed n) := by
  simp [level, Set.range, embed]

lemma level_isPWO {n : ℕ} : (level n).IsPWO := by
  rw [level_eq_range, ← Set.image_univ]
  refine Set.IsPWO.image_of_monotone ?_ (embed n).monotone
  rw [← Set.univ_prod_univ]
  exact .prod .of_linearOrder .of_linearOrder

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

/-- The map from `(x, y, n)` to `x + y`. -/
@[pp_nodot] def line (x : Hollom) : ℕ := (ofHollom x).1 + (ofHollom x).2.1

@[simp] lemma line_toHollom (x : ℕ × ℕ × ℕ) : line (toHollom x) = x.1 + x.2.1 := rfl

lemma line_injOn {C : Set Hollom} (n : ℕ) (hC : IsChain (· ≤ ·) C) (hCn : C ⊆ level n) :
    C.InjOn line := by
  rw [Set.InjOn]
  intro x hx y hy h
  induction hCn hx using induction_on_level with | h a b =>
  induction hCn hy using induction_on_level with | h c d =>
  have := hC.total hx hy
  aesop

lemma add_lt_add_of_lt {a b c d n : ℕ} (h : h(a, b, n) < h(c, d, n)) : a + b < c + d := by
  change embed n (a, b) < embed n (c, d) at h
  aesop

/--
Any antichain in the Hollom partial order is finite. This corresponds to Lemma 5.9 in the paper.
-/
theorem no_infinite_antichain {A : Set Hollom} (hC : IsAntichain (· ≤ ·) A) : A.Finite := by
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

private lemma no_strictly_decreasing {f : ℕ → ℕ} {n₀ : ℕ} (hf : ∀ n ≥ n₀, f (n + 1) < f n) :
    False := by
  let g (n : ℕ) : ℕ := f (n₀ + n)
  have hg : StrictAnti g := strictAnti_nat_of_succ_lt fun n ↦ hf (n₀ + n) (by simp)
  obtain ⟨m, n, h₁, h₂⟩ := Set.IsPWO.of_linearOrder (s := Set.univ) g (by simp)
  exact (hg h₁).not_le h₂

private lemma triangle_finite (n : ℕ) : {x : ℕ × ℕ | x.1 + x.2 ≤ n}.Finite :=
  (Set.finite_Iic (n, n)).subset <| by aesop

open Filter

/--
Show that every chain in the Hollom partial order has a finite intersection with infinitely many
levels.
This corresponds to Lemma 5.10 from the paper.
-/
theorem exists_finite_intersection (hC : IsChain (· ≤ ·) C) :
    ∃ᶠ n in atTop, (C ∩ level n).Finite := by
  -- Begin by assuming `C ∩ level n` is infinite for all `n ≥ n₀`
  rw [frequently_atTop]
  intro n₀
  by_contra! hC'
  simp only [← Set.not_infinite, not_not] at hC'
  -- Define `m n` to be the smallest value of `min x y` as `(x, y, n)` ranges over `C`.
  let m (n : ℕ) : ℕ := sInf {min (ofHollom x).1 (ofHollom x).2.1 | x ∈ C ∩ level n}
  -- `m n` is well-defined above `n₀`, since the set in question is nonempty (it's infinite).
  have nonempty_mins (n : ℕ) (hn : n₀ ≤ n) :
      {min (ofHollom x).1 (ofHollom x).2.1 | x ∈ C ∩ level n}.Nonempty :=
    (hC' n hn).nonempty.image _
  -- We aim to show that `m n` is strictly decreasing above `n₀`, which is clearly a contradiction.
  suffices ∀ n ≥ n₀, m (n + 1) < m n from no_strictly_decreasing this
  intro n hn
  -- Take `n ≥ n₀`, and take `u, v` such that `min u v = m n` (which exists by definition).
  -- We aim to show `m (n + 1) < min u v`
  obtain ⟨u, v, huv, hmn⟩ : ∃ u v : ℕ, h(u, v, n) ∈ C ∧ min u v = m n := by
    simpa [m] using Nat.sInf_mem (nonempty_mins n hn)
  rw [← hmn]
  -- Consider the set of points `{(x, y, z) | x + y ≤ 2 * (u + v)}`.
  let D : Set Hollom := {x | (ofHollom x).1 + (ofHollom x).2.1 ≤ 2 * (u + v)}
  -- There are infinitely many points in `C ∩ level (n + 1)` that are not in `D`...
  have : ((C ∩ level (n + 1)) \ D).Infinite := by
    -- ...because there are finitely many points in `C ∩ level (n + 1) ∩ D`...
    have : (C ∩ level (n + 1) ∩ D).Finite := by
      -- (indeed, `level (n + 1) ∩ D` is finite)
      refine .subset (.image (embed (n + 1)) (triangle_finite (2 * (u + v)))) ?_
      simp +contextual [Set.subset_def, D, embed_apply]
    -- ...and `C ∩ level (n + 1)` is infinite (by assumption).
    specialize hC' (n + 1) (by omega)
    rw [← (C ∩ level (n + 1)).inter_union_diff D, Set.infinite_union] at hC'
    refine hC'.resolve_left ?_
    simpa using this
  -- In fact, we only need it to be nonempty, and find a point.
  obtain ⟨x, hxy⟩ := this.nonempty
  induction hxy.1.2 using induction_on_level with | h x y =>
  simp only [Set.mem_diff, Set.mem_inter_iff, toHollom_mem_level_iff, and_true, Set.mem_setOf_eq,
    ofHollom_toHollom, not_le, D, m] at hxy
  -- Take the point `(x, y, n + 1)` in `C` that avoids `D`. As `(u, v, n)` is also in the chain `C`,
  -- they must be comparable.
  obtain h3 | h3 := hC.total huv hxy.1
  -- We cannot have `(u, v, n) ≤ (x, y, n + 1)` by definition of the order.
  · simpa using le_of_toHollom_le_toHollom h3
  -- Whereas if `(x, y, n + 1) ≤ (u, v, n)`, as `2 * (u + v) < x + y`, we must have
  -- `min x y + 1 ≤ min u v`, which finishes the proof.
  · cases h3
    case twice => omega
    case next_add => omega
    case next_min h3 =>
      rw [← Nat.add_one_le_iff]
      refine h3.trans' ?_
      simp only [add_le_add_iff_right]
      exact Nat.sInf_le ⟨_, ⟨hxy.1, by simp⟩, by simp⟩

/-!  In this section we define spinal maps, and prove important properties about them.  -/
section SpinalMap

variable {α : Type*} [PartialOrder α] {C : Set α}

/--
A spinal map is a function `f : α → C` which is the identity on `C`, and for which each fiber is an
antichain.
Provided `C` is a chain, the existence of a spinal map is equivalent to the fact that `C` is a
spine.
-/
structure SpinalMap (C : Set α) where
  /-- The underlying function of a spinal map. -/
  toFun : α → α
  mem' : ∀ x, toFun x ∈ C
  eq_self_of_mem' : ∀ x ∈ C, toFun x = x
  fibre_antichain' : ∀ x, IsAntichain (· ≤ ·) (toFun ⁻¹' {x})

instance : FunLike (SpinalMap C) α α where
  coe := SpinalMap.toFun
  coe_injective' | ⟨f, _, _, _⟩, ⟨g, _, _, _⟩, h => by simp_all only

namespace SpinalMap

variable (f : SpinalMap C)

@[ext] lemma ext {f g : SpinalMap C} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h
@[simp] lemma toFun_eq_coe : f.toFun = f := rfl
@[simp] lemma mem (x : α) : f x ∈ C := f.mem' x
lemma eq_self_of_mem {x : α} (hx : x ∈ C) : f x = x := f.eq_self_of_mem' x hx
lemma fibre_antichain (x : α) : IsAntichain (· ≤ ·) (f ⁻¹' {x}) := f.fibre_antichain' x
lemma range_subset : Set.range f ⊆ C := by simp [Set.subset_def]

variable {x y z : α}

@[simp] lemma idempotent (x : α) : f (f x) = f x := f.eq_self_of_mem (f.mem x)

lemma not_le_of_eq (hfxy : f x = f y) (hxy : x ≠ y) : ¬ x ≤ y :=
  f.fibre_antichain (f y) hfxy rfl hxy

lemma eq_of_le (hfxy : f x = f y) (hxy : x ≤ y) : x = y := by_contra (f.not_le_of_eq hfxy · hxy)

lemma not_lt_of_eq (hfxy : f x = f y) : ¬ x < y := fun h ↦ h.ne (f.eq_of_le hfxy h.le)

lemma incomp_of_eq (hfxy : f x = f y) (hxy : x ≠ y) : ¬ (x ≤ y ∨ y ≤ x) :=
  not_or.2 ⟨f.not_le_of_eq hfxy hxy, f.not_le_of_eq hfxy.symm hxy.symm⟩

lemma incomp_apply (hx : f x ≠ x) : ¬ (f x ≤ x ∨ x ≤ f x) :=
  f.incomp_of_eq (f.idempotent x) hx

lemma not_apply_lt : ¬ f x < x := f.not_lt_of_eq (by simp)
lemma not_lt_apply : ¬ x < f x := f.not_lt_of_eq (by simp)

lemma le_apply_of_le (hC : IsChain (· ≤ ·) C) (hy : y ∈ C) (hx : y ≤ x) : y ≤ f x :=
  hC.le_of_not_lt (f.mem x) hy fun hxy ↦ f.not_apply_lt (hxy.trans_le hx)

lemma apply_le_of_le (hC : IsChain (· ≤ ·) C) (hy : y ∈ C) (hx : x ≤ y) : f x ≤ y :=
  hC.le_of_not_lt hy (f.mem x) fun hxy ↦ f.not_lt_apply (hx.trans_lt hxy)

lemma lt_apply_of_lt (hC : IsChain (· ≤ ·) C) (hy : y ∈ C) (hx : y < x) : y < f x :=
  hC.lt_of_not_le (f.mem x) hy fun hxy ↦ f.not_apply_lt (hxy.trans_lt hx)

lemma apply_lt_of_lt (hC : IsChain (· ≤ ·) C) (hy : y ∈ C) (hx : x < y) : f x < y :=
  hC.lt_of_not_le hy (f.mem x) fun hxy ↦ f.not_lt_apply (hx.trans_le hxy)

lemma apply_mem_Icc_of_mem_Icc (hC : IsChain (· ≤ ·) C) (hy : y ∈ C) (hz : z ∈ C)
    (hx : x ∈ Set.Icc y z) : f x ∈ Set.Icc y z :=
  ⟨f.le_apply_of_le hC hy hx.1, f.apply_le_of_le hC hz hx.2⟩

lemma mapsTo_Icc_self (hC : IsChain (· ≤ ·) C) (hy : y ∈ C) (hz : z ∈ C) :
    Set.MapsTo f (Set.Icc y z) (Set.Icc y z) := fun _ ↦ apply_mem_Icc_of_mem_Icc _ hC hy hz

lemma injOn_of_isChain {D : Set α} (hD : IsChain (· ≤ ·) D) : D.InjOn f := by
  intro x hx y hy h
  by_contra! h'
  exact f.incomp_of_eq h h' (hD.total hx hy)

end SpinalMap

end SpinalMap

/--
Given a chain `C` in a partial order `α`, the existence of the following are equivalent:
* a partition of `α` into antichains, each which meets `C`
* a function `f : α → C` which is the identity on `C` and for which each fiber is an antichain

In fact, these two are in bijection, but we only need the weaker version that their existence
is equivalent.
-/
theorem exists_partition_iff_nonempty_spinalMap
    {α : Type*} [PartialOrder α] {C : Set α} (hC : IsChain (· ≤ ·) C) :
    (∃ S, Setoid.IsPartition S ∧ ∀ A ∈ S, IsAntichain (· ≤ ·) A ∧ (A ∩ C).Nonempty) ↔
      Nonempty (SpinalMap C) := by
  constructor
  · rintro ⟨S, ⟨hSemp, hS⟩, hSA⟩
    simp only [ExistsUnique, and_imp, and_assoc] at hS
    simp only [Set.Nonempty, Set.mem_inter_iff] at hSA
    choose F hFS hFmem hFuniq using hS
    choose hA G hGA hGC using hSA
    let f (x : α) : α := G (F x) (hFS x)
    have hfCid (x : α) (hx : x ∈ C) : f x = x :=
      chain_intersect_antichain hC (hA (F x) (hFS _)) ⟨hGC _ _, hGA _ _⟩ ⟨hx, hFmem _⟩
    have hf (x : α) : IsAntichain (· ≤ ·) (f ⁻¹' {x}) := (hA (F x) (hFS _)).subset <| by
      rintro y rfl
      exact hFuniq (f y) (F y) (hFS y) (hGA _ _) ▸ hFmem _
    exact ⟨⟨f, fun x ↦ hGC _ _, hfCid, hf⟩⟩
  · rintro ⟨f⟩
    refine ⟨_, (Setoid.ker f).isPartition_classes, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact ⟨f.fibre_antichain _, f x, by simp [Setoid.ker, Function.onFun]⟩

variable {f : SpinalMap C}

/-!  In this section we construct explicit chains in ℕ × ℕ that will be useful later.  -/
section make_chains

open Finset

/--
An explicit contiguous chain between `(a, b)` and `(c, d)` in `ℕ × ℕ`. We implement this as the
union of two disjoint sets: the first is the chain from `(a, b)` to `(a, d)`, and the second is the
chain from `(a, d)` to `(c, d)`.
-/
def chainBetween (a b c d : ℕ) : Finset (ℕ × ℕ) :=
  if a ≤ c ∧ b ≤ d
    then Ico (a, b) (a, d) ∪ Icc (a, d) (c, d)
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

open Finset in
lemma card_chainBetween {a b c d : ℕ} (hac : a ≤ c) (hbd : b ≤ d) :
    #(chainBetween a b c d) = c + d + 1 - (a + b) := by
  rw [chainBetween, if_pos ⟨hac, hbd⟩, card_union_of_disjoint, Finset.card_Icc_prod]
  · simp only [Icc_self, card_singleton, Nat.card_Icc, one_mul]
    rw [← Finset.Ico_map_sectR, card_map, Nat.card_Ico]
    omega
  · rw [disjoint_left]
    simp
    omega

lemma chainBetween_subset {a b c d : ℕ} :
    chainBetween a b c d ⊆ Finset.Icc (a, b) (c, d) := by
  rw [chainBetween]
  aesop (add simp Finset.subset_iff)

end make_chains

lemma line_mapsTo {x y : Hollom} (hxy : (ofHollom x).2.2 = (ofHollom y).2.2) :
    Set.MapsTo line (Set.Icc x y) (Set.Icc (line x) (line y)) := by
  induction x with | h a b c =>
  induction y with | h d e f =>
  obtain rfl : c = f := by simpa using hxy
  rw [Set.mapsTo']
  intro n
  simp only [Set.mem_image, Set.mem_Icc, «exists», line_toHollom, Prod.exists, exists_and_right,
    forall_exists_index, and_imp]
  rintro p q r h₁ h₂ rfl
  obtain rfl := (le_of_toHollom_le_toHollom h₁).antisymm (le_of_toHollom_le_toHollom h₂)
  simp only [toHollom_le_toHollom_iff_fixed_right] at h₁ h₂
  omega

lemma embed_image_Icc {a b c d n : ℕ} :
    embed n '' Set.Icc (a, b) (c, d) = Set.Icc h(a, b, n) h(c, d, n) := by
  rw [OrderEmbedding.image_Icc, embed_apply, embed_apply]
  rw [← level_eq_range]
  exact ordConnected_level

lemma mapsTo_Icc_image (hC : IsChain (· ≤ ·) C) {a b c d n : ℕ}
    (hab : h(a, b, n) ∈ C) (hcd : h(c, d, n) ∈ C) :
    Set.MapsTo f
      ((Finset.Icc (a, b) (c, d)).image (embed n))
      ((Finset.Icc (a, b) (c, d)).image (embed n)) := by
  simp only [Finset.coe_image, Finset.coe_Icc, embed_image_Icc]
  exact f.mapsTo_Icc_self hC hab hcd

open Classical Finset in
/--
The collection of points between `(xl, yl, n)` and `(xh, yh, n)` that are also in `C` has at least
`xh + yh + 1 - (xl + yl)` elements.
In other words, this collection must be a maximal chain relative to the interval it is contained in.
Note `card_C_inter_Icc_eq` strengthens this to an equality.
-/
lemma C_inter_Icc_large (f : SpinalMap C) {n : ℕ} {xl yl xh yh : ℕ}
    (hC : IsChain (· ≤ ·) C)
    (hx : xl ≤ xh) (hy : yl ≤ yh)
    (hlo : h(xl, yl, n) ∈ C) (hhi : h(xh, yh, n) ∈ C) :
    xh + yh + 1 - (xl + yl) ≤ #{x ∈ (Icc (xl, yl) (xh, yh)).image (embed n) | x ∈ C} := by
  set int : Finset Hollom := (Icc (xl, yl) (xh, yh)).image (embed n)
  set I : Finset Hollom := {x ∈ int | x ∈ C}
  let D : Finset Hollom := (chainBetween xl yl xh yh).image (embed n)
  have hD : D ⊆ int := Finset.image_subset_image chainBetween_subset
  have D_maps : Set.MapsTo f D I := by
    simp only [I, Finset.coe_filter]
    exact ((mapsTo_Icc_image hC hlo hhi).mono_left hD).inter (by simp [Set.MapsTo])
  have f_inj : Set.InjOn f D := f.injOn_of_isChain image_chainBetween_isChain
  have : #D = xh + yh + 1 - (xl + yl) := by
    simp [D, Finset.card_image_of_injective, (embed n).injective, card_chainBetween hx hy]
  rw [← this]
  exact Finset.card_le_card_of_injOn f D_maps f_inj

open Classical Finset in
/--
The collection of points between `(xl, yl, n)` and `(xh, yh, n)` that are also in `C` has exactly
`xh + yh + 1 - (xl + yl)` elements.
In other words, this collection must be a maximal chain relative to the interval it is contained in.
Alternatively speaking, it has the same size as any maximal chain in that interval.
-/
theorem card_C_inter_Icc_eq (f : SpinalMap C) {n : ℕ} {xl yl xh yh : ℕ}
    (hC : IsChain (· ≤ ·) C)
    (hx : xl ≤ xh) (hy : yl ≤ yh)
    (hlo : h(xl, yl, n) ∈ C) (hhi : h(xh, yh, n) ∈ C) :
    #{x ∈ (Icc (xl, yl) (xh, yh)).image (embed n) | x ∈ C} = xh + yh + 1 - (xl + yl) := by
  set int : Finset Hollom := (Icc (xl, yl) (xh, yh)).image (embed n)
  set I : Finset Hollom := {x ∈ int | x ∈ C}
  have int_eq : int = Set.Icc h(xl, yl, n) h(xh, yh, n) := by
    simp only [coe_image, coe_Icc, int, embed_image_Icc]
  have hI : IsChain (· ≤ ·) I.toSet := hC.mono (by simp [Set.subset_def, I])
  have hIn : I.toSet ⊆ level n := by simp +contextual [Set.subset_def, I, int, embed_apply]
  have : Set.MapsTo line int (Icc (xl + yl) (xh + yh)) := by
    rw [int_eq, coe_Icc]
    exact line_mapsTo rfl
  replace this : Set.MapsTo line I (Icc (xl + yl) (xh + yh)) := this.mono_left (filter_subset _ _)
  refine le_antisymm ?_ (C_inter_Icc_large f hC hx hy hlo hhi)
  rw [← Nat.card_Icc]
  exact card_le_card_of_injOn _ this (line_injOn _ hI hIn)

open Finset in
lemma apply_eq_of_line_eq_step (f : SpinalMap C) {n xl yl xh yh : ℕ}
    (hC : IsChain (· ≤ ·) C)
    (hlo : h(xl, yl, n) ∈ C) (hhi : h(xh, yh, n) ∈ C) (hx : xl ≤ xh) (hy : yl ≤ yh)
    {x y : ℕ}
    (h₁l : h(xl, yl, n) ≤ h(x + 1, y, n)) (h₂l : h(xl, yl, n) ≤ h(x, y + 1, n))
    (h₁h : h(x + 1, y, n) ≤ h(xh, yh, n)) (h₂h : h(x, y + 1, n) ≤ h(xh, yh, n)) :
    f h(x + 1, y, n) = f h(x, y + 1, n) := by
  classical
  set int : Finset Hollom := (Icc (xl, yl) (xh, yh)).image (embed n)
  set I : Finset Hollom := {x ∈ int | x ∈ C}
  have cI : #I = xh + yh + 1 - (xl + yl) := card_C_inter_Icc_eq f hC hx hy hlo hhi
  have int_eq : int = Set.Icc h(xl, yl, n) h(xh, yh, n) := by
    simp only [coe_image, coe_Icc, int, embed_image_Icc]
  have : f h(x + 1, y, n) ∈ int ∧ f h(x, y + 1, n) ∈ int := by
    rw [← mem_coe, ← mem_coe, int_eq]
    exact ⟨f.mapsTo_Icc_self hC hlo hhi ⟨h₁l, h₁h⟩, f.mapsTo_Icc_self hC hlo hhi ⟨h₂l, h₂h⟩⟩
  simp only [toHollom_le_toHollom_iff_fixed_right] at h₁l h₂l h₁h h₂h
  let B : Finset Hollom :=
    (chainBetween xl yl x y ∪ chainBetween (x + 1) (y + 1) xh yh).image (embed n)
  have cB : #B = xh + yh - (xl + yl) := by
    rw [card_image_of_injective _ (embed n).injective, card_union_of_disjoint,
      card_chainBetween h₂l.1 h₁l.2, card_chainBetween h₁h.1 h₂h.2]
    · omega
    · simp [disjoint_left, chainBetween, *]
      omega
  have hB : B ⊆ int := by
    refine Finset.image_subset_image ?_
    rw [Finset.union_subset_iff]
    refine ⟨chainBetween_subset.trans ?_, chainBetween_subset.trans ?_⟩
    · exact Finset.Icc_subset_Icc_right (by simp [*])
    · exact Finset.Icc_subset_Icc_left (by simp [*])
  have f_maps : Set.MapsTo f B I := by
    simp only [I, Finset.coe_filter]
    exact ((mapsTo_Icc_image hC hlo hhi).mono_left hB).inter (by simp [Set.MapsTo])
  have f_inj : Set.InjOn f B := by
    refine f.injOn_of_isChain ?_
    simp only [B]
    rw [coe_image]
    refine IsChain.image (· ≤ ·) _ (embed n) (by simp) ?_
    rw [coe_union, isChain_union]
    refine ⟨chainBetween_isChain, chainBetween_isChain, ?_⟩
    simp [chainBetween, *]
    omega
  have hleft : f h(x + 1, y, n) ∉ B.image f := by
    simp +contextual only [mem_image, mem_union, embed_apply, Prod.exists, «exists»,
      EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq, not_exists, not_and, forall_exists_index,
      and_imp, or_imp, B, forall_and]
    constructor
    · rintro _ _ c a b hab rfl rfl rfl
      have : (a, b) ≤ (x, y) := (Finset.mem_Icc.1 (chainBetween_subset hab)).2
      have : embed n (a, b) < embed n (x + 1, y) := embed_strictMono (this.trans_lt (by simp))
      intro h
      exact f.not_lt_of_eq h this
    · rintro _ _ c a b hab rfl rfl rfl
      have : (x + 1, y + 1) ≤ (a, b) := (Finset.mem_Icc.1 (chainBetween_subset hab)).1
      have : embed n (x + 1, y) < embed n (a, b) := embed_strictMono (this.trans_lt' (by simp))
      intro h
      exact f.not_lt_of_eq h.symm this
  have hright : f h(x, y + 1, n) ∉ B.image f := by
    simp +contextual only [mem_image, mem_union, embed_apply, Prod.exists, «exists»,
      EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq, not_exists, not_and, forall_exists_index,
      and_imp, or_imp, B, forall_and]
    constructor
    · rintro _ _ c a b hab rfl rfl rfl
      have : (a, b) ≤ (x, y) := (Finset.mem_Icc.1 (chainBetween_subset hab)).2
      have : embed n (a, b) < embed n (x, y + 1) := embed_strictMono (this.trans_lt (by simp))
      intro h
      exact f.not_lt_of_eq h this
    · rintro _ _ c a b hab rfl rfl rfl
      have : (x + 1, y + 1) ≤ (a, b) := (Finset.mem_Icc.1 (chainBetween_subset hab)).1
      have : embed n (x, y + 1) < embed n (a, b) := embed_strictMono (this.trans_lt' (by simp))
      intro h
      exact f.not_lt_of_eq h.symm this
  have card_eq : (I \ B.image f).card = 1 := by
    rw [card_sdiff, cI, card_image_of_injOn f_inj, cB]
    · omega
    · rw [← coe_subset, coe_image]
      exact f_maps.image_subset
  replace hleft : f h(x + 1, y, n) ∈ I \ B.image f := by simpa [mem_sdiff, hleft, I] using this.1
  replace hright : f h(x, y + 1, n) ∈ I \ B.image f := by simpa [mem_sdiff, hright, I] using this.2
  exact Finset.card_le_one.1 card_eq.le _ hleft _ hright

lemma apply_eq_of_line_eq_aux (f : SpinalMap C) {n xl yl xh yh : ℕ}
    (hC : IsChain (· ≤ ·) C)
    (hlo : h(xl, yl, n) ∈ C) (hhi : h(xh, yh, n) ∈ C) (hx : xl ≤ xh) (hy : yl ≤ yh)
    {x y k : ℕ}
    (h₁l : h(xl, yl, n) ≤ h(x + k, y, n)) (h₂l : h(xl, yl, n) ≤ h(x, y + k, n))
    (h₁h : h(x + k, y, n) ≤ h(xh, yh, n)) (h₂h : h(x, y + k, n) ≤ h(xh, yh, n)) :
    f h(x + k, y, n) = f h(x, y + k, n) := by
  induction k generalizing x y with
  | zero => simp
  | succ k ih =>
      have : f h(x + (k + 1), y, n) = f h(x + k, y + 1, n) := by
        simp only [← add_assoc] at h₁l h₁h ⊢
        refine apply_eq_of_line_eq_step f hC hlo hhi hx hy h₁l ?_ h₁h ?_
        all_goals
          simp only [toHollom_le_toHollom_iff_fixed_right] at h₁l h₁h h₂l h₂h ⊢
          omega
      rw [this, ih, add_right_comm, add_assoc]
      all_goals
        simp only [toHollom_le_toHollom_iff_fixed_right] at h₁l h₁h h₂l h₂h ⊢
        omega

/--
For two points of `C` in the same level, and two points `(a, b, n)` and `(c, d, n)` between them,
if `a + b = c + d` then `f (a, b, n) = f (c, d, n)`.
-/
theorem apply_eq_of_line_eq (f : SpinalMap C) {n : ℕ} (hC : IsChain (· ≤ ·) C)
    {lo hi : Hollom} (hlo : lo ∈ C ∩ level n) (hhi : hi ∈ C ∩ level n) (hlohi : lo ≤ hi)
    {x y : Hollom} (h : line x = line y)
    (h₁l : lo ≤ x) (h₂l : lo ≤ y) (h₁h : x ≤ hi) (h₂h : y ≤ hi) :
    f x = f y := by
  wlog hxy : (ofHollom y).1 ≤ (ofHollom x).1 generalizing x y
  · exact (this h.symm h₂l h₁l h₂h h₁h (le_of_not_le hxy)).symm
  have hx : x ∈ level n := ordConnected_level.out hlo.2 hhi.2 ⟨h₁l, h₁h⟩
  have hy : y ∈ level n := ordConnected_level.out hlo.2 hhi.2 ⟨h₂l, h₂h⟩
  induction hx using induction_on_level with | h x₁ y₁ =>
  induction hy using induction_on_level with | h x₂ y₂ =>
  simp only [ofHollom_toHollom] at hxy
  simp only [line_toHollom] at h
  obtain ⟨k, rfl⟩ := exists_add_of_le hxy
  obtain rfl : y₂ = y₁ + k := by omega
  induction hlo.2 using induction_on_level with | h xlo ylo =>
  induction hhi.2 using induction_on_level with | h xhi yhi =>
  exact apply_eq_of_line_eq_aux f hC hlo.1 hhi.1 (by simp_all) (by simp_all) h₁l h₂l h₁h h₂h

/--
Construction of the set `R`, which has the following key properties:
* It is a subset of `level n`.
* Each of its elements is comparable to all of `C ∩ level n`.
* There exists an `a` such that `{(x, y, n) | x ≥ a ∧ y ≥ a} ⊆ R`.
-/
def R (n : ℕ) (C : Set Hollom) : Set Hollom := {x ∈ level n | ∀ y ∈ C ∩ level n, x ≤ y ∨ y ≤ x}

variable {n : ℕ}
lemma R_subset_level : R n C ⊆ level n := Set.sep_subset (level n) _

lemma square_subset_above (h : (C ∩ level n).Finite) :
    ∀ᶠ a in atTop, embed n '' Set.Ici (a, a) ⊆ {x | ∀ y ∈ C ∩ level n, y ≤ x} \ (C ∩ level n) := by
  obtain h | hne := (C ∩ level n).eq_empty_or_nonempty
  · simp [h]

  obtain ⟨a, b, hab⟩ : ∃ a b, ∀ c d, h(c, d, n) ∈ C → c ≤ a ∧ d ≤ b := by
    obtain ⟨⟨a, b⟩, hab⟩ := (h.image (fun t ↦ ((ofHollom t).1, (ofHollom t).2.1))).bddAbove
    use a, b
    intro c d hcd
    simpa using hab ⟨h(_, _, _), ⟨hcd, by simp⟩, rfl⟩

  rw [eventually_atTop]

  refine ⟨max a b + 1, ?_⟩
  simp +contextual only [ge_iff_le, sup_le_iff, embed, RelEmbedding.coe_mk,
    Function.Embedding.coeFn_mk, Set.mem_inter_iff, and_imp, «forall», toHollom_mem_level_iff,
    Prod.forall, Set.subset_def, Set.mem_image, Set.mem_Ici, Prod.exists, Prod.mk_le_mk,
    Set.mem_setOf_eq, forall_exists_index, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq,
    toHollom_le_toHollom_iff_fixed_right, Set.mem_diff, and_true, ← max_add_add_right]

  rintro k hak hbk _ _ _ f g hkf hkg rfl rfl rfl
  constructor
  · rintro c d n hcd rfl
    specialize hab c d hcd
    omega
  · intro hfg
    specialize hab _ _ hfg
    omega

lemma square_subset_R (h : (C ∩ level n).Finite) :
    ∀ᶠ a in atTop, embed n '' Set.Ici (a, a) ⊆ R n C \ (C ∩ level n) := by
  filter_upwards [square_subset_above h] with a ha
  rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
  exact ⟨⟨by simp [embed], fun b hb ↦ .inr ((ha ⟨_, hxy, rfl⟩).1 _ hb)⟩, (ha ⟨_, hxy, rfl⟩).2⟩

lemma R_diff_infinite (h : (C ∩ level n).Finite) : (R n C \ (C ∩ level n)).Infinite := by
  obtain ⟨a, ha⟩ := (square_subset_R h).exists
  refine ((Set.Ici_infinite _).image ?_).mono ha
  aesop (add safe unfold [Set.InjOn])

-- we could state this as Disjoint (f '' (R n C)) (C ∩ level n), but this is more
-- annoying than helpful
lemma not_R_hits_same {x : Hollom} (hx : x ∈ R n C) (hx' : x ∉ C ∩ level n) :
    f x ∉ C ∩ level n := by
  intro hfx
  apply f.incomp_apply _ (hx.2 _ hfx).symm
  exact ne_of_mem_of_not_mem hfx hx'

open Classical in
/--
Given a subset `C` of the Hollom partial order, and an index `n`, find the smallest element of
`C ∩ level (n + 1)`, expressed as `(x₀, y₀, n + 1)`.
This is only the global minimum provided `C` is a chain, which it is in context.
-/
noncomputable def x0y0 (n : ℕ) (C : Set Hollom) : ℕ × ℕ :=
  if h : (C ∩ level (n + 1)).Nonempty
    then wellFounded_lt.min {x | embed (n + 1) x ∈ C} <| by
      rw [level_eq_range] at h
      obtain ⟨_, h, y, rfl⟩ := h
      exact ⟨y, h⟩
    else 0

lemma x0y0_mem (h : (C ∩ level (n + 1)).Nonempty) :
    embed (n + 1) (x0y0 n C) ∈ C := by
  rw [x0y0, dif_pos h]
  exact WellFounded.min_mem _ {x | embed (n + 1) x ∈ C} _

lemma x0y0_min (z : ℕ × ℕ) (hC : IsChain (· ≤ ·) C) (h : embed (n + 1) z ∈ C) :
    embed (n + 1) (x0y0 n C) ≤ embed (n + 1) z := by
  have : (C ∩ level (n + 1)).Nonempty := ⟨_, h, by simp [level_eq_range]⟩
  refine hC.le_of_not_lt h (x0y0_mem this) ?_
  rw [x0y0, dif_pos this, OrderEmbedding.lt_iff_lt]
  exact wellFounded_lt.not_lt_min {x | embed (n + 1) x ∈ C} ?_ h

/--
Given a subset `C` of the Hollom partial order, and an index `n`, find the smallest element of
`C ∩ level (n + 1)`, and `x0 n C` will be the x-coordinate thereof.
-/
noncomputable def x0 (n : ℕ) (C : Set Hollom) : ℕ := (x0y0 n C).1
/--
Given a subset `C` of the Hollom partial order, and an index `n`, find the smallest element of
`C ∩ level (n + 1)`, and `y0 n C` will be the y-coordinate thereof.
-/
noncomputable def y0 (n : ℕ) (C : Set Hollom) : ℕ := (x0y0 n C).2

lemma x0_y0_mem (h : (C ∩ level (n + 1)).Nonempty) : h(x0 n C, y0 n C, n + 1) ∈ C := x0y0_mem h

lemma x0_y0_min (hC : IsChain (· ≤ ·) C) {a b : ℕ} (h : h(a, b, n + 1) ∈ C) :
    h(x0 n C, y0 n C, n + 1) ≤ h(a, b, n + 1) := x0y0_min (a, b) hC h

open Classical in
/--
Construction of the set `S`, which has the following key properties:
* It is a subset of `R`.
* No element of it can be mapped to an element of `C ∩ level (n + 1)` by `f`.
* There exists an `a` such that `{(x, y, n) | x ≥ a ∧ y ≥ a} ⊆ S`.
-/
noncomputable def S (n : ℕ) (C : Set Hollom) : Set Hollom :=
  if (C ∩ level (n + 1)).Finite
    then {x ∈ R n C | ∀ y ∈ C ∩ level (n + 1), x ≤ y ∨ y ≤ x}
    else {x ∈ R n C | max (x0 n C) (y0 n C) + 1 ≤ min (ofHollom x).1 (ofHollom x).2.1}

lemma S_subset_R : S n C ⊆ R n C := by
  rw [S]
  split <;> exact Set.sep_subset _ _

lemma S_subset_level : S n C ⊆ level n := S_subset_R.trans R_subset_level

lemma square_subset_S_case_1 (h : (C ∩ level n).Finite) (h' : (C ∩ level (n + 1)).Finite) :
    ∀ᶠ a in atTop, embed n '' Set.Ici (a, a) ⊆ S n C \ (C ∩ level n) := by
  rw [S, if_pos h']

  obtain ⟨b, c, hab⟩ : ∃ b c, ∀ d e, h(d, e, n + 1) ∈ C → (d, e) ≤ (b, c) := by
    obtain ⟨⟨b, c⟩, hbc⟩ := (h'.image (fun t ↦ ((ofHollom t).1, (ofHollom t).2.1))).bddAbove
    use b, c
    intro d e hde
    simpa using hbc ⟨h(_, _, _), ⟨hde, by simp⟩, rfl⟩

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
  exact fun x hx ↦ ⟨⟨(h₁ hx).1, h₂ hx⟩, (h₁ hx).2⟩

lemma square_subset_S_case_2 (h : (C ∩ level n).Finite) (h' : (C ∩ level (n + 1)).Infinite) :
    ∀ᶠ a in atTop, embed n '' Set.Ici (a, a) ⊆ S n C \ (C ∩ level n) := by
  rw [S, if_neg h']
  filter_upwards [eventually_ge_atTop (x0 n C + 1), eventually_ge_atTop (y0 n C + 1),
    square_subset_R h] with a hax hay haR
  aesop (add simp embed_apply)

theorem square_subset_S (h : (C ∩ level n).Finite) :
    ∀ᶠ a in atTop, embed n '' Set.Ici (a, a) ⊆ S n C \ (C ∩ level n) :=
  (C ∩ level (n + 1)).finite_or_infinite.elim (square_subset_S_case_1 h) (square_subset_S_case_2 h)

lemma S_infinite (h : (C ∩ level n).Finite) : (S n C \ (C ∩ level n)).Infinite := by
  obtain ⟨a, ha⟩ := (square_subset_S h).exists
  refine ((Set.Ici_infinite _).image ?_).mono ha
  aesop (add safe unfold Set.InjOn)

lemma left_or_right_bias {n : ℕ} (a b : ℕ)
    (hab : ∀ x y, h(x, y, n) ∈ C → h(a, b, n) ≤ h(x, y, n))
    (hCn : (C ∩ level n).Infinite) :
    (∀ i : ℕ, ∃ j ∈ C ∩ level n, h(a, i, n) ≤ j) ∨
    (∀ i : ℕ, ∃ j ∈ C ∩ level n, h(i, b, n) ≤ j) := by
  by_contra! h
  obtain ⟨⟨c, hc⟩, d, hd⟩ := h
  refine hCn (((Set.finite_Iic (d, c)).image (embed n)).subset ?_)
  simp only [Set.subset_def, Set.mem_inter_iff, Set.mem_image, Set.mem_Iic, Prod.exists,
    Prod.mk_le_mk, and_imp, «forall», toHollom_mem_level_iff, Prod.forall]
  rintro x y n hxy rfl
  specialize hab x y (by simp [hxy])
  specialize hc h(x, y, n) (by simp [hxy])
  specialize hd h(x, y, n) (by simp [hxy])
  simp_all only [toHollom_le_toHollom_iff_fixed_right, true_and, not_le, and_true]
  exact ⟨_, _, ⟨hd.le, hc.le⟩, rfl⟩

theorem not_S_hits_next (f : SpinalMap C) (hC : IsChain (· ≤ ·) C)
    {x : Hollom} (hx : x ∈ S n C) (hx' : x ∉ C ∩ level n) :
    f x ∉ C ∩ level (n + 1) := by
  cases (C ∩ level (n + 1)).finite_or_infinite
  case inl h =>
    rw [S, if_pos h, Set.mem_setOf_eq] at hx
    intro hy
    refine f.incomp_apply ?_ (hx.2 _ hy).symm
    have := R_subset_level hx.1
    simp only [level_eq, Set.mem_setOf_eq] at this
    intro h
    simp [level_eq, h, this] at hy

  case inr h =>
    induction x with | h x y n =>
    obtain rfl := by simpa using S_subset_level hx
    simp only [S, if_neg h, Set.mem_setOf_eq, ofHollom_toHollom] at hx
    intro hp
    set fp := f h(x, y, n) with hfp
    clear_value fp
    induction hp.2 using induction_on_level with | h a b =>
    clear fp
    obtain ⟨ha, hb⟩ : x0 n C ≤ a ∧ y0 n C ≤ b := by simpa using x0_y0_min hC hp.1
    obtain (rbias | lbias) := left_or_right_bias (x0 n C) (y0 n C) (fun x y ↦ x0_y0_min hC) h
    · obtain ⟨j, hjCn, hj⟩ := rbias (a + b - x0 n C)
      have hj' : h(a, b, n + 1) ≤ j := by
        induction hjCn.2 using induction_on_level with | h c d =>
        apply hC.le_of_not_lt hjCn.1 hp.1 ?_
        intro h
        have : c + d < a + b := add_lt_add_of_lt h
        simp only [toHollom_le_toHollom_iff_fixed_right] at hj
        omega
      have h0j : h(x0 n C, y0 n C, n + 1) ≤ j := hj'.trans' (by simp [ha, hb])
      have : line h(a, b, n + 1) = line h(x0 n C, a + b - x0 n C, n + 1) := by simp; omega
      have := apply_eq_of_line_eq f hC ⟨x0_y0_mem h.nonempty, by simp⟩ hjCn ‹_› this
        (x0_y0_min hC hp.1) (by simp; omega) hj' hj
      have : f h(x, y, n) = f h(x0 n C, a + b - x0 n C, n + 1) := by
        rw [← this, ← hfp, f.eq_self_of_mem hp.1]
      exact f.not_le_of_eq this.symm (by simp) (.next_min (hx.2.trans' (by simp)))
    · obtain ⟨j, hjCn, hj⟩ := lbias (a + b - y0 n C)
      have hj' : h(a, b, n + 1) ≤ j := by
        induction hjCn.2 using induction_on_level with | h c d =>
        apply hC.le_of_not_lt hjCn.1 hp.1 ?_
        intro h
        have : c + d < a + b := add_lt_add_of_lt h
        simp only [toHollom_le_toHollom_iff_fixed_right] at hj
        omega
      have h0j : h(x0 n C, y0 n C, n + 1) ≤ j := hj'.trans' (by simp [ha, hb])
      have : line h(a, b, n + 1) = line h(a + b - y0 n C, y0 n C, n + 1) := by simp; omega
      have := apply_eq_of_line_eq f hC ⟨x0_y0_mem h.nonempty, by simp⟩ hjCn ‹_› this
        (x0_y0_min hC hp.1) (by simp; omega) hj' hj
      have : f h(x, y, n) = f h(a + b - y0 n C, y0 n C, n + 1) := by
        rw [← this, ← hfp, f.eq_self_of_mem hp.1]
      exact f.not_le_of_eq this.symm (by simp) (.next_min (hx.2.trans' (by simp)))

lemma S_mapsTo_previous (f : SpinalMap C) (hC : IsChain (· ≤ ·) C) (hn : n ≠ 0) :
    ∀ x ∈ S n C \ (C ∩ level n), f x ∈ C ∩ level (n - 1) := by
  intro x hx
  refine ⟨f.mem _, ?_⟩
  set p := f x with hp
  clear_value p
  induction S_subset_level hx.1 using induction_on_level with | h x y =>
  induction p with | h a b m =>
  simp only [toHollom_mem_level_iff]
  have : m ≠ n := by
    rintro rfl
    have : f _ ∉ _ := not_R_hits_same (S_subset_R hx.1) hx.2
    simp only [Set.mem_inter_iff, SpinalMap.mem, true_and] at this
    simp [← hp] at this
  have : n + 1 ≠ m := by
    rintro rfl
    have : f _ ∉ _ := not_S_hits_next f hC hx.1 hx.2
    simp only [Set.mem_inter_iff, SpinalMap.mem, true_and] at this
    simp [← hp] at this
  have hp' : f h(a, b, m) = f h(x, y, n) := by
    rw [hp, f.idempotent]
  have : ¬ m + 2 ≤ n := by
    intro h
    have := f.eq_of_le hp'.symm (.twice h)
    simp only [EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq] at this
    omega
  have : ¬ n + 2 ≤ m := by
    intro h
    have := f.eq_of_le hp' (.twice h)
    simp only [EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq] at this
    omega
  omega

open Finset in
theorem not_S_mapsTo_previous (hC : IsChain (· ≤ ·) C)
    (hCn : (C ∩ level n).Finite) (hn : n ≠ 0)
    (h : ∀ x ∈ S n C \ (C ∩ level n), f x ∈ C ∩ level (n - 1)) :
    False := by
  obtain ⟨a, ha⟩ := (square_subset_S hCn).exists
  let F : Finset Hollom := (chainBetween a a (3 * a) a).image (embed n)
  have F_subs : F.toSet ⊆ S n C \ (C ∩ level n) := calc
    F.toSet = embed n '' chainBetween a a (3 * a) a := Finset.coe_image
    _ ⊆ embed n '' Finset.Icc (a, a) (3 * a, a) := Set.image_mono chainBetween_subset
    _ = embed n '' Set.Icc (a, a) (3 * a, a) := by simp
    _ ⊆ embed n '' Set.Ici (a, a) := Set.image_mono Set.Icc_subset_Ici_self
    _ ⊆ S n C \ (C ∩ level n) := ha
  have card_F : #F = 2 * a + 1 := by
    rw [Finset.card_image_of_injective _ (embed n).injective,
      card_chainBetween (by omega) (by simp)]
    omega
  have F_mapsTo : Set.MapsTo f F {x ∈ C ∩ level (n - 1) | line x < 2 * a} := by
    intro x hx
    refine ⟨h _ (F_subs hx), ?_⟩
    set c := f x with hc
    have hc' : c ∈ C ∩ level (n - 1) := h _ (F_subs hx)
    clear_value c
    rw [coe_image, chainBetween, Ico_self, if_pos (by omega), empty_union, ← Icc_map_sectL] at hx
    simp only [embed_apply, coe_map, Function.Embedding.sectL_apply, coe_Icc,
      Set.mem_image, Set.mem_Icc, exists_exists_and_eq_and] at hx
    obtain ⟨b, ⟨hab, hba⟩, rfl⟩ := hx
    induction hc'.2 using induction_on_level with | h u v =>
    simp only [line_toHollom]
    by_contra!
    have le : h(b, a, n) ≤ h(u, v, n - 1) := by
      match n, hn with
      | n + 1, _ =>
          simp only [add_tsub_cancel_right]
          apply HollomOrder.next_add (by omega)
    have : f h(u, v, n - 1) = f h(b, a, n) := by rw [f.eq_self_of_mem hc'.1, hc]
    have := le_of_toHollom_le_toHollom (f.eq_of_le this.symm le).ge
    omega
  have line_mapsTo :
      Set.MapsTo line {x ∈ C ∩ level (n - 1) | line x < 2 * a} (Finset.range (2 * a)) := by
    rintro x ⟨_, hx⟩
    simpa using hx
  have F_inj : Set.InjOn f F := f.injOn_of_isChain image_chainBetween_isChain
  have line_inj : Set.InjOn line {x ∈ C ∩ level (n - 1) | line x < 2 * a} :=
    line_injOn (n - 1)
      (hC.mono (by simp +contextual [Set.subset_def]))
      (by simp +contextual [Set.subset_def])
  have line_F_mapsTo := line_mapsTo.comp F_mapsTo
  have := card_le_card_of_injOn _ line_F_mapsTo (line_inj.comp F_inj F_mapsTo)
  simp only [Finset.card_range] at this
  omega

/-- The Hollom partial order has no spinal maps. -/
theorem no_spinalMap (hC : IsChain (· ≤ ·) C) (f : SpinalMap C) : False := by
  obtain ⟨n, hn, hn'⟩ : ∃ n, n ≠ 0 ∧ (C ∩ Hollom.level n).Finite := by
    obtain ⟨n, hn, hn'⟩ := Filter.frequently_atTop.1 (Hollom.exists_finite_intersection hC) 1
    exact ⟨n, by omega, hn'⟩
  exact Hollom.not_S_mapsTo_previous hC hn' hn (Hollom.S_mapsTo_previous f hC hn)

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
  simp only [not_forall, not_or, not_exists]
  refine ⟨Hollom, inferInstance, ?_, ?_⟩
  · intro A ⟨hA, hA'⟩
    exact hA' (Hollom.no_infinite_antichain hA)
  · rintro C ⟨hC, h⟩
    rw [Hollom.exists_partition_iff_nonempty_spinalMap hC] at h
    obtain ⟨f⟩ := h
    exact Hollom.no_spinalMap hC f
