/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Data.Bool.Set
import Mathlib.Data.Nat.Set
import Mathlib.Order.CompleteLattice.Basic

/-!
# Theory of complete lattices

This file contains results on complete lattices that need more theory to develop.

## Naming conventions

In lemma names,
* `sSup` is called `sSup`
* `sInf` is called `sInf`
* `⨆ i, s i` is called `iSup`
* `⨅ i, s i` is called `iInf`
* `⨆ i j, s i j` is called `iSup₂`. This is an `iSup` inside an `iSup`.
* `⨅ i j, s i j` is called `iInf₂`. This is an `iInf` inside an `iInf`.
* `⨆ i ∈ s, t i` is called `biSup` for "bounded `iSup`". This is the special case of `iSup₂`
  where `j : i ∈ s`.
* `⨅ i ∈ s, t i` is called `biInf` for "bounded `iInf`". This is the special case of `iInf₂`
  where `j : i ∈ s`.

## Notation

* `⨆ i, f i` : `iSup f`, the supremum of the range of `f`;
* `⨅ i, f i` : `iInf f`, the infimum of the range of `f`.
-/

open Function OrderDual Set

variable {α β γ : Type*} {ι ι' : Sort*} {κ : ι → Sort*} {κ' : ι' → Sort*}

open OrderDual

section

variable [CompleteLattice α] {f g s : ι → α} {a b : α}

/-!
### `iSup` and `iInf` under `Type`
-/

theorem iSup_bool_eq {f : Bool → α} : ⨆ b : Bool, f b = f true ⊔ f false := by
  rw [iSup, Bool.range_eq, sSup_pair, sup_comm]

theorem iInf_bool_eq {f : Bool → α} : ⨅ b : Bool, f b = f true ⊓ f false :=
  @iSup_bool_eq αᵒᵈ _ _

theorem sup_eq_iSup (x y : α) : x ⊔ y = ⨆ b : Bool, cond b x y := by
  rw [iSup_bool_eq, Bool.cond_true, Bool.cond_false]

theorem inf_eq_iInf (x y : α) : x ⊓ y = ⨅ b : Bool, cond b x y :=
  @sup_eq_iSup αᵒᵈ _ _ _

/-!
### `iSup` and `iInf` under `ℕ`
-/


theorem iSup_ge_eq_iSup_nat_add (u : ℕ → α) (n : ℕ) : ⨆ i ≥ n, u i = ⨆ i, u (i + n) := by
  apply le_antisymm <;> simp only [iSup_le_iff]
  · refine fun i hi => le_sSup ⟨i - n, ?_⟩
    dsimp only
    rw [Nat.sub_add_cancel hi]
  · exact fun i => le_sSup ⟨i + n, iSup_pos (Nat.le_add_left _ _)⟩

theorem iInf_ge_eq_iInf_nat_add (u : ℕ → α) (n : ℕ) : ⨅ i ≥ n, u i = ⨅ i, u (i + n) :=
  @iSup_ge_eq_iSup_nat_add αᵒᵈ _ _ _

theorem Monotone.iSup_nat_add {f : ℕ → α} (hf : Monotone f) (k : ℕ) : ⨆ n, f (n + k) = ⨆ n, f n :=
  le_antisymm (iSup_le fun i => le_iSup _ (i + k)) <| iSup_mono fun i => hf <| Nat.le_add_right i k

theorem Antitone.iInf_nat_add {f : ℕ → α} (hf : Antitone f) (k : ℕ) : ⨅ n, f (n + k) = ⨅ n, f n :=
  hf.dual_right.iSup_nat_add k

-- Porting note: the linter doesn't like this being marked as `@[simp]`,
-- saying that it doesn't work when called on its LHS.
-- Mysteriously, it *does* work. Nevertheless, per
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/complete_lattice.20and.20has_sup/near/316497982
-- "the subterm ?f (i + ?k) produces an ugly higher-order unification problem."
-- @[simp]
theorem iSup_iInf_ge_nat_add (f : ℕ → α) (k : ℕ) :
    ⨆ n, ⨅ i ≥ n, f (i + k) = ⨆ n, ⨅ i ≥ n, f i := by
  have hf : Monotone fun n => ⨅ i ≥ n, f i := fun n m h => biInf_mono fun i => h.trans
  rw [← Monotone.iSup_nat_add hf k]
  · simp_rw [iInf_ge_eq_iInf_nat_add, ← Nat.add_assoc]

-- Porting note: removing `@[simp]`, see discussion on `iSup_iInf_ge_nat_add`.
-- @[simp]
theorem iInf_iSup_ge_nat_add :
    ∀ (f : ℕ → α) (k : ℕ), ⨅ n, ⨆ i ≥ n, f (i + k) = ⨅ n, ⨆ i ≥ n, f i :=
  @iSup_iInf_ge_nat_add αᵒᵈ _

theorem sup_iSup_nat_succ (u : ℕ → α) : (u 0 ⊔ ⨆ i, u (i + 1)) = ⨆ i, u i :=
  calc
    (u 0 ⊔ ⨆ i, u (i + 1)) = ⨆ x ∈ {0} ∪ range Nat.succ, u x := by
      { rw [iSup_union, iSup_singleton, iSup_range] }
    _ = ⨆ i, u i := by rw [Nat.zero_union_range_succ, iSup_univ]

theorem inf_iInf_nat_succ (u : ℕ → α) : (u 0 ⊓ ⨅ i, u (i + 1)) = ⨅ i, u i :=
  @sup_iSup_nat_succ αᵒᵈ _ u

theorem iInf_nat_gt_zero_eq (f : ℕ → α) : ⨅ i > 0, f i = ⨅ i, f (i + 1) := by
  rw [← iInf_range, Nat.range_succ]
  simp

theorem iSup_nat_gt_zero_eq (f : ℕ → α) : ⨆ i > 0, f i = ⨆ i, f (i + 1) :=
  @iInf_nat_gt_zero_eq αᵒᵈ _ f

end

/-!
### Instances
-/

section CompleteLattice

variable [CompleteLattice α] {a : α} {s : Set α}

/-- This is a weaker version of `sup_sInf_eq` -/
theorem sup_sInf_le_iInf_sup : a ⊔ sInf s ≤ ⨅ b ∈ s, a ⊔ b :=
  le_iInf₂ fun _ h => sup_le_sup_left (sInf_le h) _

/-- This is a weaker version of `inf_sSup_eq` -/
theorem iSup_inf_le_inf_sSup : ⨆ b ∈ s, a ⊓ b ≤ a ⊓ sSup s :=
  @sup_sInf_le_iInf_sup αᵒᵈ _ _ _

/-- This is a weaker version of `sInf_sup_eq` -/
theorem sInf_sup_le_iInf_sup : sInf s ⊔ a ≤ ⨅ b ∈ s, b ⊔ a :=
  le_iInf₂ fun _ h => sup_le_sup_right (sInf_le h) _

/-- This is a weaker version of `sSup_inf_eq` -/
theorem iSup_inf_le_sSup_inf : ⨆ b ∈ s, b ⊓ a ≤ sSup s ⊓ a :=
  @sInf_sup_le_iInf_sup αᵒᵈ _ _ _

theorem le_iSup_inf_iSup (f g : ι → α) : ⨆ i, f i ⊓ g i ≤ (⨆ i, f i) ⊓ ⨆ i, g i :=
  le_inf (iSup_mono fun _ => inf_le_left) (iSup_mono fun _ => inf_le_right)

theorem iInf_sup_iInf_le (f g : ι → α) : (⨅ i, f i) ⊔ ⨅ i, g i ≤ ⨅ i, f i ⊔ g i :=
  @le_iSup_inf_iSup αᵒᵈ ι _ f g

theorem disjoint_sSup_left {a : Set α} {b : α} (d : Disjoint (sSup a) b) {i} (hi : i ∈ a) :
    Disjoint i b :=
  disjoint_iff_inf_le.mpr (iSup₂_le_iff.1 (iSup_inf_le_sSup_inf.trans d.le_bot) i hi :)

theorem disjoint_sSup_right {a : Set α} {b : α} (d : Disjoint b (sSup a)) {i} (hi : i ∈ a) :
    Disjoint b i :=
  disjoint_iff_inf_le.mpr (iSup₂_le_iff.mp (iSup_inf_le_inf_sSup.trans d.le_bot) i hi :)

lemma disjoint_of_sSup_disjoint_of_le_of_le {a b : α} {c d : Set α} (hs : ∀ e ∈ c, e ≤ a)
    (ht : ∀ e ∈ d, e ≤ b) (hd : Disjoint a b) (he : ⊥ ∉ c ∨ ⊥ ∉ d) : Disjoint c d := by
  rw [disjoint_iff_forall_ne]
  intros x hx y hy
  rw [Disjoint.ne_iff]
  · aesop
  · exact Disjoint.mono (hs x hx) (ht y hy) hd

lemma disjoint_of_sSup_disjoint {a b : Set α} (hd : Disjoint (sSup a) (sSup b))
    (he : ⊥ ∉ a ∨ ⊥ ∉ b) : Disjoint a b :=
  disjoint_of_sSup_disjoint_of_le_of_le (fun _ hc ↦ le_sSup hc) (fun _ hc ↦ le_sSup hc) hd he

end CompleteLattice

namespace ULift

universe v

instance supSet [SupSet α] : SupSet (ULift.{v} α) where sSup s := ULift.up (sSup <| ULift.up ⁻¹' s)

theorem down_sSup [SupSet α] (s : Set (ULift.{v} α)) : (sSup s).down = sSup (ULift.up ⁻¹' s) := rfl
theorem up_sSup [SupSet α] (s : Set α) : up (sSup s) = sSup (ULift.down ⁻¹' s) := rfl

instance infSet [InfSet α] : InfSet (ULift.{v} α) where sInf s := ULift.up (sInf <| ULift.up ⁻¹' s)

theorem down_sInf [InfSet α] (s : Set (ULift.{v} α)) : (sInf s).down = sInf (ULift.up ⁻¹' s) := rfl
theorem up_sInf [InfSet α] (s : Set α) : up (sInf s) = sInf (ULift.down ⁻¹' s) := rfl

theorem down_iSup [SupSet α] (f : ι → ULift.{v} α) : (⨆ i, f i).down = ⨆ i, (f i).down :=
  congr_arg sSup <| (preimage_eq_iff_eq_image ULift.up_bijective).mpr <|
    Eq.symm (range_comp _ _).symm
theorem up_iSup [SupSet α] (f : ι → α) : up (⨆ i, f i) = ⨆ i, up (f i) :=
  congr_arg ULift.up <| (down_iSup _).symm

theorem down_iInf [InfSet α] (f : ι → ULift.{v} α) : (⨅ i, f i).down = ⨅ i, (f i).down :=
  congr_arg sInf <| (preimage_eq_iff_eq_image ULift.up_bijective).mpr <|
    Eq.symm (range_comp _ _).symm
theorem up_iInf [InfSet α] (f : ι → α) : up (⨅ i, f i) = ⨅ i, up (f i) :=
  congr_arg ULift.up <| (down_iInf _).symm

instance instCompleteLattice [CompleteLattice α] : CompleteLattice (ULift.{v} α) :=
  ULift.down_injective.completeLattice _ down_sup down_inf
    (fun s => by rw [sSup_eq_iSup', down_iSup, iSup_subtype''])
    (fun s => by rw [sInf_eq_iInf', down_iInf, iInf_subtype'']) down_top down_bot

end ULift

namespace PUnit

instance instCompleteLinearOrder : CompleteLinearOrder PUnit where
  __ := instBooleanAlgebra
  __ := instLinearOrder
  sSup := fun _ => unit
  sInf := fun _ => unit
  le_sSup := by intros; trivial
  sSup_le := by intros; trivial
  sInf_le := by intros; trivial
  le_sInf := by intros; trivial
  le_himp_iff := by intros; trivial
  himp_bot := by intros; trivial
  sdiff_le_iff := by intros; trivial
  top_sdiff := by intros; trivial

end PUnit
