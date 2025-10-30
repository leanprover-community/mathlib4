/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yaël Dillies
-/

import Mathlib.Data.List.Iterate
import Mathlib.Data.Set.Pairwise.List
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.Tactic.Group

/-!
# Cycle factors of a permutation

Let `β` be a `Fintype` and `f : Equiv.Perm β`.

* `Equiv.Perm.cycleOf`: `f.cycleOf x` is the cycle of `f` that `x` belongs to.
* `Equiv.Perm.cycleFactors`: `f.cycleFactors` is a list of disjoint cyclic permutations
  that multiply to `f`.
-/

open Equiv Function Finset

variable {ι α β : Type*}

namespace Equiv.Perm

/-!
### `cycleOf`
-/

section CycleOf

variable {f g : Perm α} {x y : α}

/-- `f.cycleOf x` is the cycle of the permutation `f` to which `x` belongs. -/
def cycleOf (f : Perm α) [DecidableRel f.SameCycle] (x : α) : Perm α :=
  ofSubtype (subtypePerm f fun _ => sameCycle_apply_right : Perm { y // SameCycle f x y })

theorem cycleOf_apply (f : Perm α) [DecidableRel f.SameCycle] (x y : α) :
    cycleOf f x y = if SameCycle f x y then f y else y := by
  dsimp only [cycleOf]
  split_ifs with h
  · apply ofSubtype_apply_of_mem
    exact h
  · apply ofSubtype_apply_of_not_mem
    exact h

theorem cycleOf_inv (f : Perm α) [DecidableRel f.SameCycle] (x : α) :
    (cycleOf f x)⁻¹ = cycleOf f⁻¹ x :=
  Equiv.ext fun y => by
    rw [inv_eq_iff_eq, cycleOf_apply, cycleOf_apply]
    split_ifs <;> simp_all [sameCycle_inv, sameCycle_inv_apply_right]

@[simp]
theorem cycleOf_pow_apply_self (f : Perm α) [DecidableRel f.SameCycle] (x : α) :
    ∀ n : ℕ, (cycleOf f x ^ n) x = (f ^ n) x := by
  intro n
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [pow_succ', mul_apply, cycleOf_apply, hn, if_pos, pow_succ', mul_apply]
    exact ⟨n, rfl⟩

@[simp]
theorem cycleOf_zpow_apply_self (f : Perm α) [DecidableRel f.SameCycle] (x : α) :
    ∀ n : ℤ, (cycleOf f x ^ n) x = (f ^ n) x := by
  intro z
  cases z with
  | ofNat z => exact cycleOf_pow_apply_self f x z
  | negSucc z =>
    rw [zpow_negSucc, ← inv_pow, cycleOf_inv, zpow_negSucc, ← inv_pow, cycleOf_pow_apply_self]

theorem SameCycle.cycleOf_apply [DecidableRel f.SameCycle] :
    SameCycle f x y → cycleOf f x y = f y :=
  ofSubtype_apply_of_mem _

theorem cycleOf_apply_of_not_sameCycle [DecidableRel f.SameCycle] :
    ¬SameCycle f x y → cycleOf f x y = y :=
  ofSubtype_apply_of_not_mem _

theorem SameCycle.cycleOf_eq [DecidableRel f.SameCycle] (h : SameCycle f x y) :
    cycleOf f x = cycleOf f y := by
  ext z
  rw [Equiv.Perm.cycleOf_apply]
  split_ifs with hz
  · exact (h.symm.trans hz).cycleOf_apply.symm
  · exact (cycleOf_apply_of_not_sameCycle (mt h.trans hz)).symm

@[simp]
theorem cycleOf_apply_apply_zpow_self (f : Perm α) [DecidableRel f.SameCycle] (x : α) (k : ℤ) :
    cycleOf f x ((f ^ k) x) = (f ^ (k + 1) : Perm α) x := by
  rw [SameCycle.cycleOf_apply]
  · rw [add_comm, zpow_add, zpow_one, mul_apply]
  · exact ⟨k, rfl⟩

@[simp]
theorem cycleOf_apply_apply_pow_self (f : Perm α) [DecidableRel f.SameCycle] (x : α) (k : ℕ) :
    cycleOf f x ((f ^ k) x) = (f ^ (k + 1) : Perm α) x := by
  convert cycleOf_apply_apply_zpow_self f x k using 1

@[simp]
theorem cycleOf_apply_apply_self (f : Perm α) [DecidableRel f.SameCycle] (x : α) :
    cycleOf f x (f x) = f (f x) := by
  convert cycleOf_apply_apply_pow_self f x 1 using 1

@[simp]
theorem cycleOf_apply_self (f : Perm α) [DecidableRel f.SameCycle] (x : α) : cycleOf f x x = f x :=
  SameCycle.rfl.cycleOf_apply

theorem IsCycle.cycleOf_eq [DecidableRel f.SameCycle]
    (hf : IsCycle f) (hx : f x ≠ x) : cycleOf f x = f :=
  Equiv.ext fun y =>
    if h : SameCycle f x y then by rw [h.cycleOf_apply]
    else by
      rw [cycleOf_apply_of_not_sameCycle h,
        Classical.not_not.1 (mt ((isCycle_iff_sameCycle hx).1 hf).2 h)]

@[simp]
theorem cycleOf_eq_one_iff (f : Perm α) [DecidableRel f.SameCycle] : cycleOf f x = 1 ↔ f x = x := by
  simp_rw [Perm.ext_iff, cycleOf_apply, one_apply]
  refine ⟨fun h => (if_pos (SameCycle.refl f x)).symm.trans (h x), fun h y => ?_⟩
  by_cases hy : f y = y
  · rw [hy, ite_self]
  · exact if_neg (mt SameCycle.apply_eq_self_iff (by tauto))

@[simp]
theorem cycleOf_self_apply (f : Perm α) [DecidableRel f.SameCycle] (x : α) :
    cycleOf f (f x) = cycleOf f x :=
  (sameCycle_apply_right.2 SameCycle.rfl).symm.cycleOf_eq

@[simp]
theorem cycleOf_self_apply_pow (f : Perm α) [DecidableRel f.SameCycle] (n : ℕ) (x : α) :
    cycleOf f ((f ^ n) x) = cycleOf f x :=
  SameCycle.rfl.pow_left.cycleOf_eq

@[simp]
theorem cycleOf_self_apply_zpow (f : Perm α) [DecidableRel f.SameCycle] (n : ℤ) (x : α) :
    cycleOf f ((f ^ n) x) = cycleOf f x :=
  SameCycle.rfl.zpow_left.cycleOf_eq

protected theorem IsCycle.cycleOf [DecidableRel f.SameCycle] [DecidableEq α]
    (hf : IsCycle f) : cycleOf f x = if f x = x then 1 else f := by
  by_cases hx : f x = x
  · rwa [if_pos hx, cycleOf_eq_one_iff]
  · rwa [if_neg hx, hf.cycleOf_eq]

theorem cycleOf_one [DecidableRel (1 : Perm α).SameCycle] (x : α) :
    cycleOf 1 x = 1 := (cycleOf_eq_one_iff 1).mpr rfl

theorem isCycle_cycleOf (f : Perm α) [DecidableRel f.SameCycle] (hx : f x ≠ x) :
    IsCycle (cycleOf f x) :=
  have : cycleOf f x x ≠ x := by rwa [SameCycle.rfl.cycleOf_apply]
  (isCycle_iff_sameCycle this).2 @fun y =>
    ⟨fun h => mt h.apply_eq_self_iff.2 this, fun h =>
      if hxy : SameCycle f x y then
        let ⟨i, hi⟩ := hxy
        ⟨i, by rw [cycleOf_zpow_apply_self, hi]⟩
      else by
        rw [cycleOf_apply_of_not_sameCycle hxy] at h
        exact (h rfl).elim⟩

theorem pow_mod_orderOf_cycleOf_apply (f : Perm α) [DecidableRel f.SameCycle] (n : ℕ) (x : α) :
    (f ^ (n % orderOf (cycleOf f x))) x = (f ^ n) x := by
  rw [← cycleOf_pow_apply_self f, ← cycleOf_pow_apply_self f, pow_mod_orderOf]

theorem cycleOf_mul_of_apply_right_eq_self [DecidableRel f.SameCycle]
    [DecidableRel (f * g).SameCycle]
    (h : Commute f g) (x : α) (hx : g x = x) : (f * g).cycleOf x = f.cycleOf x := by
  ext y
  by_cases hxy : (f * g).SameCycle x y
  · obtain ⟨z, rfl⟩ := hxy
    rw [cycleOf_apply_apply_zpow_self]
    simp [h.mul_zpow, zpow_apply_eq_self_of_apply_eq_self hx]
  · rw [cycleOf_apply_of_not_sameCycle hxy, cycleOf_apply_of_not_sameCycle]
    contrapose! hxy
    obtain ⟨z, rfl⟩ := hxy
    refine ⟨z, ?_⟩
    simp [h.mul_zpow, zpow_apply_eq_self_of_apply_eq_self hx]

theorem Disjoint.cycleOf_mul_distrib [DecidableRel f.SameCycle] [DecidableRel g.SameCycle]
    [DecidableRel (f * g).SameCycle] [DecidableRel (g * f).SameCycle] (h : f.Disjoint g) (x : α) :
    (f * g).cycleOf x = f.cycleOf x * g.cycleOf x := by
  rcases (disjoint_iff_eq_or_eq.mp h) x with hfx | hgx
  · simp [h.commute.eq, cycleOf_mul_of_apply_right_eq_self h.symm.commute, hfx]
  · simp [cycleOf_mul_of_apply_right_eq_self h.commute, hgx]

private theorem mem_support_cycleOf_iff_aux [DecidableRel f.SameCycle] [DecidableEq α] [Fintype α] :
    y ∈ support (f.cycleOf x) ↔ SameCycle f x y ∧ x ∈ support f := by
  by_cases hx : f x = x
  · rw [(cycleOf_eq_one_iff _).mpr hx]
    simp [hx]
  · rw [mem_support, cycleOf_apply]
    split_ifs with hy
    · simp only [hx, hy, Ne, not_false_iff, and_self_iff, mem_support]
      rcases hy with ⟨k, rfl⟩
      rw [← notMem_support]
      simpa using hx
    · simpa [hx] using hy

private theorem mem_support_cycleOf_iff'_aux (hx : f x ≠ x)
    [DecidableRel f.SameCycle] [DecidableEq α] [Fintype α] :
    y ∈ support (f.cycleOf x) ↔ SameCycle f x y := by
  rw [mem_support_cycleOf_iff_aux, and_iff_left (mem_support.2 hx)]

/-- `x` is in the support of `f` iff `Equiv.Perm.cycle_of f x` is a cycle. -/
theorem isCycle_cycleOf_iff (f : Perm α) [DecidableRel f.SameCycle] :
    IsCycle (cycleOf f x) ↔ f x ≠ x := by
  refine ⟨fun hx => ?_, f.isCycle_cycleOf⟩
  rw [Ne, ← cycleOf_eq_one_iff f]
  exact hx.ne_one

private theorem isCycleOn_support_cycleOf_aux [DecidableEq α] [Fintype α] (f : Perm α)
    [DecidableRel f.SameCycle] (x : α) : f.IsCycleOn (f.cycleOf x).support :=
  ⟨f.bijOn <| by
    refine fun _ ↦
        ⟨fun h ↦ mem_support_cycleOf_iff_aux.2 ?_, fun h ↦ mem_support_cycleOf_iff_aux.2 ?_⟩
    · exact ⟨sameCycle_apply_right.1 (mem_support_cycleOf_iff_aux.1 h).1,
      (mem_support_cycleOf_iff_aux.1 h).2⟩
    · exact ⟨sameCycle_apply_right.2 (mem_support_cycleOf_iff_aux.1 h).1,
      (mem_support_cycleOf_iff_aux.1 h).2⟩,
    fun a ha b hb ↦ by
      rw [mem_coe, mem_support_cycleOf_iff_aux] at ha hb
      exact ha.1.symm.trans hb.1⟩

private theorem SameCycle.exists_pow_eq_of_mem_support_aux {f} [DecidableEq α] [Fintype α]
    [DecidableRel f.SameCycle] (h : SameCycle f x y) (hx : x ∈ f.support) :
    ∃ i < #(f.cycleOf x).support, (f ^ i) x = y := by
  rw [mem_support] at hx
  exact Equiv.Perm.IsCycleOn.exists_pow_eq (b := y) (f.isCycleOn_support_cycleOf_aux x)
    (by rw [mem_support_cycleOf_iff'_aux hx]) (by rwa [mem_support_cycleOf_iff'_aux hx])

instance instDecidableRelSameCycle [DecidableEq α] [Fintype α] (f : Perm α) :
    DecidableRel (SameCycle f) := fun x y =>
  decidable_of_iff (y ∈ List.iterate f x (Fintype.card α)) <| by
    simp only [List.mem_iterate, iterate_eq_pow, eq_comm (a := y)]
    constructor
    · rintro ⟨n, _, hn⟩
      exact ⟨n, hn⟩
    · intro hxy
      by_cases hx : x ∈ f.support
      case pos =>
        -- we can't invoke the aux lemmas above without obtaining the decidable instance we are
        -- already building; but now we've left the data, so we can do this non-constructively
        -- without sacrificing computability.
        let _inst (f : Perm α) : DecidableRel (SameCycle f) := Classical.decRel _
        rcases hxy.exists_pow_eq_of_mem_support_aux hx with ⟨i, hixy, hi⟩
        refine ⟨i, lt_of_lt_of_le hixy (card_le_univ _), hi⟩
      case neg =>
        haveI : Nonempty α := ⟨x⟩
        rw [notMem_support] at hx
        exact ⟨0, Fintype.card_pos, hxy.eq_of_left hx⟩

@[simp]
theorem two_le_card_support_cycleOf_iff [DecidableEq α] [Fintype α] :
    2 ≤ #(cycleOf f x).support ↔ f x ≠ x := by
  refine ⟨fun h => ?_, fun h => by simpa using (isCycle_cycleOf _ h).two_le_card_support⟩
  contrapose! h
  rw [← cycleOf_eq_one_iff] at h
  simp [h]

@[simp] lemma support_cycleOf_nonempty [DecidableEq α] [Fintype α] :
    (cycleOf f x).support.Nonempty ↔ f x ≠ x := by
  rw [← two_le_card_support_cycleOf_iff, ← card_pos, ← Nat.succ_le_iff]
  exact ⟨fun h => Or.resolve_left h.eq_or_lt (card_support_ne_one _).symm, zero_lt_two.trans_le⟩

theorem mem_support_cycleOf_iff [DecidableEq α] [Fintype α] :
    y ∈ support (f.cycleOf x) ↔ SameCycle f x y ∧ x ∈ support f :=
  mem_support_cycleOf_iff_aux

theorem mem_support_cycleOf_iff' (hx : f x ≠ x) [DecidableEq α] [Fintype α] :
    y ∈ support (f.cycleOf x) ↔ SameCycle f x y :=
  mem_support_cycleOf_iff'_aux hx

theorem sameCycle_iff_cycleOf_eq_of_mem_support [DecidableEq α] [Fintype α]
    {g : Perm α} {x y : α} (hx : x ∈ g.support) (hy : y ∈ g.support) :
    g.SameCycle x y ↔ g.cycleOf x = g.cycleOf y := by
  refine ⟨SameCycle.cycleOf_eq, fun h ↦ ?_⟩
  rw [← mem_support_cycleOf_iff' (mem_support.mp hx), h,
    mem_support_cycleOf_iff' (mem_support.mp hy)]

theorem support_cycleOf_eq_nil_iff [DecidableEq α] [Fintype α] :
    (f.cycleOf x).support = ∅ ↔ x ∉ f.support := by simp

theorem isCycleOn_support_cycleOf [DecidableEq α] [Fintype α] (f : Perm α) (x : α) :
    f.IsCycleOn (f.cycleOf x).support :=
  isCycleOn_support_cycleOf_aux f x

theorem SameCycle.exists_pow_eq_of_mem_support {f} [DecidableEq α] [Fintype α] (h : SameCycle f x y)
    (hx : x ∈ f.support) : ∃ i < #(f.cycleOf x).support, (f ^ i) x = y :=
  h.exists_pow_eq_of_mem_support_aux hx

theorem support_cycleOf_le [DecidableEq α] [Fintype α] (f : Perm α) (x : α) :
    support (f.cycleOf x) ≤ support f := by
  intro y hy
  rw [mem_support, cycleOf_apply] at hy
  split_ifs at hy
  · exact mem_support.mpr hy
  · exact absurd rfl hy

theorem SameCycle.mem_support_iff {f} [DecidableEq α] [Fintype α] (h : SameCycle f x y) :
    x ∈ support f ↔ y ∈ support f :=
  ⟨fun hx => support_cycleOf_le f x (mem_support_cycleOf_iff.mpr ⟨h, hx⟩), fun hy =>
    support_cycleOf_le f y (mem_support_cycleOf_iff.mpr ⟨h.symm, hy⟩)⟩

theorem pow_mod_card_support_cycleOf_self_apply [DecidableEq α] [Fintype α]
    (f : Perm α) (n : ℕ) (x : α) : (f ^ (n % #(f.cycleOf x).support)) x = (f ^ n) x := by
  by_cases hx : f x = x
  · rw [pow_apply_eq_self_of_apply_eq_self hx, pow_apply_eq_self_of_apply_eq_self hx]
  · rw [← cycleOf_pow_apply_self, ← cycleOf_pow_apply_self f, ← (isCycle_cycleOf f hx).orderOf,
      pow_mod_orderOf]

theorem SameCycle.exists_pow_eq [DecidableEq α] [Fintype α] (f : Perm α) (h : SameCycle f x y) :
    ∃ i : ℕ, 0 < i ∧ i ≤ #(f.cycleOf x).support + 1 ∧ (f ^ i) x = y := by
  by_cases hx : x ∈ f.support
  · obtain ⟨k, hk, hk'⟩ := h.exists_pow_eq_of_mem_support hx
    rcases k with - | k
    · refine ⟨#(f.cycleOf x).support, hk, self_le_add_right _ _, ?_⟩
      simp only [pow_zero, coe_one, id_eq] at hk'
      subst hk'
      rw [← (isCycle_cycleOf _ <| mem_support.1 hx).orderOf, ← cycleOf_pow_apply_self,
        pow_orderOf_eq_one, one_apply]
    · exact ⟨k + 1, by simp, Nat.le_succ_of_le hk.le, hk'⟩
  · refine ⟨1, zero_lt_one, by simp, ?_⟩
    obtain ⟨k, rfl⟩ := h
    rw [notMem_support] at hx
    rw [pow_apply_eq_self_of_apply_eq_self hx, zpow_apply_eq_self_of_apply_eq_self hx]

theorem zpow_eq_zpow_on_iff [DecidableEq α] [Fintype α]
    (g : Perm α) {m n : ℤ} {x : α} (hx : g x ≠ x) :
    (g ^ m) x = (g ^ n) x ↔ m % #(g.cycleOf x).support = n % #(g.cycleOf x).support := by
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
  conv_lhs => rw [← Int.sub_add_cancel m n, Int.add_comm, zpow_add]
  simp only [coe_mul, Function.comp_apply, EmbeddingLike.apply_eq_iff_eq]
  rw [← Int.dvd_iff_emod_eq_zero]
  rw [← cycleOf_zpow_apply_self g x, cycle_zpow_mem_support_iff]
  · rw [← Int.dvd_iff_emod_eq_zero]
  · exact isCycle_cycleOf g hx
  · simp only [cycleOf_apply_self]; exact hx

end CycleOf


/-!
### `cycleFactors`
-/

section cycleFactors

open scoped List in
/-- Given a list `l : List α` and a permutation `f : Perm α` whose nonfixed points are all in `l`,
  recursively factors `f` into cycles. -/
def cycleFactorsAux [DecidableEq α] [Fintype α]
    (l : List α) (f : Perm α) (h : ∀ {x}, f x ≠ x → x ∈ l) :
    { pl : List (Perm α) // pl.prod = f ∧ (∀ g ∈ pl, IsCycle g) ∧ pl.Pairwise Disjoint } :=
  go l f h (fun _ => rfl)
where
  /-- The auxiliary of `cycleFactorsAux`. This functions separates cycles from `f` instead of `g`
  to prevent the process of a cycle gets complex. -/
  go (l : List α) (g : Perm α) (hg : ∀ {x}, g x ≠ x → x ∈ l)
    (hfg : ∀ {x}, g x ≠ x → cycleOf f x = cycleOf g x) :
    { pl : List (Perm α) // pl.prod = g ∧ (∀ g' ∈ pl, IsCycle g') ∧ pl.Pairwise Disjoint } :=
  match l with
  | [] => ⟨[], by
      { simp only [imp_false, List.Pairwise.nil, List.not_mem_nil, forall_const, and_true,
          forall_prop_of_false, Classical.not_not, not_false_iff, List.prod_nil] at *
        ext
        simp [*]}⟩
  | x :: l =>
    if hx : g x = x then go l g (by
        intro y hy; exact List.mem_of_ne_of_mem (fun h => hy (by rwa [h])) (hg hy)) hfg
    else
      let ⟨m, hm⟩ :=
        go l ((cycleOf f x)⁻¹ * g) (by
            rw [hfg hx]
            intro y hy
            exact List.mem_of_ne_of_mem
              (fun h : y = x => by
                rw [h, mul_apply, Ne, inv_eq_iff_eq, cycleOf_apply_self] at hy
                exact hy rfl)
              (hg fun h : g y = y => by
                rw [mul_apply, h, Ne, inv_eq_iff_eq, cycleOf_apply] at hy
                split_ifs at hy <;> tauto))
          (by
            rw [hfg hx]
            intro y hy
            simp [inv_eq_iff_eq, cycleOf_apply, eq_comm (a := g y)] at hy
            rw [hfg (Ne.symm hy.right), ← mul_inv_eq_one (a := g.cycleOf y), cycleOf_inv]
            simp_rw [mul_inv_rev]
            rw [inv_inv, cycleOf_mul_of_apply_right_eq_self, ← cycleOf_inv, mul_inv_eq_one]
            · rw [Commute.inv_left_iff, commute_iff_eq]
              ext z; by_cases hz : SameCycle g x z
              · simp [cycleOf_apply, hz]
              · simp [cycleOf_apply_of_not_sameCycle, hz]
            · exact cycleOf_apply_of_not_sameCycle hy.left)
      ⟨cycleOf f x :: m, by
        obtain ⟨hm₁, hm₂, hm₃⟩ := hm
        rw [hfg hx] at hm₁ ⊢
        constructor
        · rw [List.prod_cons, hm₁]
          simp
        · exact
            ⟨fun g' hg' =>
              ((List.mem_cons).1 hg').elim (fun hg' => hg'.symm ▸ isCycle_cycleOf _ hx) (hm₂ g'),
              List.pairwise_cons.2
                ⟨fun g' hg' y =>
                  or_iff_not_imp_left.2 fun hgy =>
                    have hxy : SameCycle g x y :=
                      Classical.not_not.1 (mt cycleOf_apply_of_not_sameCycle hgy)
                    have hg'm : (g' :: m.erase g') ~ m :=
                      List.cons_perm_iff_perm_erase.2 ⟨hg', List.Perm.refl _⟩
                    have : ∀ h ∈ m.erase g', Disjoint g' h :=
                      (List.pairwise_cons.1 ((hg'm.pairwise_iff Disjoint.symm).2 hm₃)).1
                    by_cases id fun hg'y : g' y ≠ y =>
                      (disjoint_prod_right _ this y).resolve_right <| by
                        have hsc : SameCycle g⁻¹ x (g y) := by
                          rwa [sameCycle_inv, sameCycle_apply_right]
                        rw [disjoint_prod_perm hm₃ hg'm.symm, List.prod_cons,
                            ← eq_inv_mul_iff_mul_eq] at hm₁
                        rwa [hm₁, mul_apply, mul_apply, cycleOf_inv, hsc.cycleOf_apply,
                          inv_apply_self, inv_eq_iff_eq, eq_comm],
                  hm₃⟩⟩⟩

theorem mem_list_cycles_iff {α : Type*} [Finite α] {l : List (Perm α)}
    (h1 : ∀ σ : Perm α, σ ∈ l → σ.IsCycle) (h2 : l.Pairwise Disjoint) {σ : Perm α} :
    σ ∈ l ↔ σ.IsCycle ∧ ∀ a, σ a ≠ a → σ a = l.prod a := by
  suffices σ.IsCycle → (σ ∈ l ↔ ∀ a, σ a ≠ a → σ a = l.prod a) by
    exact ⟨fun hσ => ⟨h1 σ hσ, (this (h1 σ hσ)).mp hσ⟩, fun hσ => (this hσ.1).mpr hσ.2⟩
  intro h3
  classical
    cases nonempty_fintype α
    constructor
    · intro h a ha
      exact eq_on_support_mem_disjoint h h2 _ (mem_support.mpr ha)
    · intro h
      have hσl : σ.support ⊆ l.prod.support := by
        intro x hx
        rw [mem_support] at hx
        rwa [mem_support, ← h _ hx]
      obtain ⟨a, ha, -⟩ := id h3
      rw [← mem_support] at ha
      obtain ⟨τ, hτ, hτa⟩ := exists_mem_support_of_mem_support_prod (hσl ha)
      have hτl : ∀ x ∈ τ.support, τ x = l.prod x := eq_on_support_mem_disjoint hτ h2
      have key : ∀ x ∈ σ.support ∩ τ.support, σ x = τ x := by
        intro x hx
        rw [h x (mem_support.mp (mem_of_mem_inter_left hx)), hτl x (mem_of_mem_inter_right hx)]
      convert hτ
      refine h3.eq_on_support_inter_nonempty_congr (h1 _ hτ) key ?_ ha
      exact key a (mem_inter_of_mem ha hτa)

open scoped List in
theorem list_cycles_perm_list_cycles {α : Type*} [Finite α] {l₁ l₂ : List (Perm α)}
    (h₀ : l₁.prod = l₂.prod) (h₁l₁ : ∀ σ : Perm α, σ ∈ l₁ → σ.IsCycle)
    (h₁l₂ : ∀ σ : Perm α, σ ∈ l₂ → σ.IsCycle) (h₂l₁ : l₁.Pairwise Disjoint)
    (h₂l₂ : l₂.Pairwise Disjoint) : l₁ ~ l₂ := by
  classical
    refine
      (List.perm_ext_iff_of_nodup (nodup_of_pairwise_disjoint_cycles h₁l₁ h₂l₁)
            (nodup_of_pairwise_disjoint_cycles h₁l₂ h₂l₂)).mpr
        fun σ => ?_
    by_cases hσ : σ.IsCycle
    · obtain _ := not_forall.mp (mt ext hσ.ne_one)
      rw [mem_list_cycles_iff h₁l₁ h₂l₁, mem_list_cycles_iff h₁l₂ h₂l₂, h₀]
    · exact iff_of_false (mt (h₁l₁ σ) hσ) (mt (h₁l₂ σ) hσ)

/-- Factors a permutation `f` into a list of disjoint cyclic permutations that multiply to `f`. -/
def cycleFactors [Fintype α] [LinearOrder α] (f : Perm α) :
    { l : List (Perm α) // l.prod = f ∧ (∀ g ∈ l, IsCycle g) ∧ l.Pairwise Disjoint } :=
  cycleFactorsAux (sort (α := α) univ) f (fun {_ _} ↦ (mem_sort _).2 (mem_univ _))

/-- Factors a permutation `f` into a list of disjoint cyclic permutations that multiply to `f`,
  without a linear order. -/
def truncCycleFactors [DecidableEq α] [Fintype α] (f : Perm α) :
    Trunc { l : List (Perm α) // l.prod = f ∧ (∀ g ∈ l, IsCycle g) ∧ l.Pairwise Disjoint } :=
  Quotient.recOnSubsingleton (@univ α _).1 (fun l h => Trunc.mk (cycleFactorsAux l f (h _)))
    (show ∀ x, f x ≠ x → x ∈ (@univ α _).1 from fun _ _ => mem_univ _)

section CycleFactorsFinset

variable [DecidableEq α] [Fintype α] (f : Perm α)

/-- Factors a permutation `f` into a `Finset` of disjoint cyclic permutations that multiply to `f`.
-/
def cycleFactorsFinset : Finset (Perm α) :=
  (truncCycleFactors f).lift
    (fun l : { l : List (Perm α) // l.prod = f ∧ (∀ g ∈ l, IsCycle g) ∧ l.Pairwise Disjoint } =>
      ⟨↑l.val, nodup_of_pairwise_disjoint (fun h1 => not_isCycle_one <| l.2.2.1 _ h1) l.2.2.2⟩)
    fun ⟨_, hl⟩ ⟨_, hl'⟩ =>
    Finset.eq_of_veq <| Multiset.coe_eq_coe.mpr <|
      list_cycles_perm_list_cycles (hl'.left.symm ▸ hl.left) hl.right.left hl'.right.left
        hl.right.right hl'.right.right

open scoped List in
theorem cycleFactorsFinset_eq_list_toFinset {σ : Perm α} {l : List (Perm α)} (hn : l.Nodup) :
    σ.cycleFactorsFinset = l.toFinset ↔
      (∀ f : Perm α, f ∈ l → f.IsCycle) ∧ l.Pairwise Disjoint ∧ l.prod = σ := by
  obtain ⟨⟨l', hp', hc', hd'⟩, hl⟩ := Trunc.exists_rep σ.truncCycleFactors
  have ht : cycleFactorsFinset σ = l'.toFinset := by
    rw [cycleFactorsFinset, ← hl, Trunc.lift_mk, Multiset.toFinset_eq, List.toFinset_coe]
  rw [ht]
  constructor
  · intro h
    have hn' : l'.Nodup := nodup_of_pairwise_disjoint_cycles hc' hd'
    have hperm : l ~ l' := List.perm_of_nodup_nodup_toFinset_eq hn hn' h.symm
    refine ⟨?_, ?_, ?_⟩
    · exact fun _ h => hc' _ (hperm.subset h)
    · have := List.Perm.pairwise_iff (@Disjoint.symmetric _) hperm
      rwa [this]
    · rw [← hp', hperm.symm.prod_eq']
      refine hd'.imp ?_
      exact Disjoint.commute
  · rintro ⟨hc, hd, hp⟩
    refine List.toFinset_eq_of_perm _ _ ?_
    refine list_cycles_perm_list_cycles ?_ hc' hc hd' hd
    rw [hp, hp']

theorem cycleFactorsFinset_eq_finset {σ : Perm α} {s : Finset (Perm α)} :
    σ.cycleFactorsFinset = s ↔
      (∀ f : Perm α, f ∈ s → f.IsCycle) ∧
        ∃ h : (s : Set (Perm α)).Pairwise Disjoint,
          s.noncommProd id (h.mono' fun _ _ => Disjoint.commute) = σ := by
  obtain ⟨l, hl, rfl⟩ := s.exists_list_nodup_eq
  simp [cycleFactorsFinset_eq_list_toFinset, hl]

theorem cycleFactorsFinset_pairwise_disjoint :
    (cycleFactorsFinset f : Set (Perm α)).Pairwise Disjoint :=
  (cycleFactorsFinset_eq_finset.mp rfl).2.choose

/-- Two cycles of a permutation commute. -/
theorem cycleFactorsFinset_mem_commute : (cycleFactorsFinset f : Set (Perm α)).Pairwise Commute :=
  (cycleFactorsFinset_pairwise_disjoint _).mono' fun _ _ => Disjoint.commute

/-- Two cycles of a permutation commute. -/
theorem cycleFactorsFinset_mem_commute' {g1 g2 : Perm α}
    (h1 : g1 ∈ f.cycleFactorsFinset) (h2 : g2 ∈ f.cycleFactorsFinset) :
    Commute g1 g2 := by
  rcases eq_or_ne g1 g2 with rfl | h
  · apply Commute.refl
  · exact Equiv.Perm.cycleFactorsFinset_mem_commute f h1 h2 h

/-- The product of cycle factors is equal to the original `f : perm α`. -/
theorem cycleFactorsFinset_noncommProd
    (comm : (cycleFactorsFinset f : Set (Perm α)).Pairwise Commute :=
      cycleFactorsFinset_mem_commute f) :
    f.cycleFactorsFinset.noncommProd id comm = f :=
  (cycleFactorsFinset_eq_finset.mp rfl).2.choose_spec

theorem mem_cycleFactorsFinset_iff {f p : Perm α} :
    p ∈ cycleFactorsFinset f ↔ p.IsCycle ∧ ∀ a ∈ p.support, p a = f a := by
  obtain ⟨l, hl, hl'⟩ := f.cycleFactorsFinset.exists_list_nodup_eq
  rw [← hl']
  rw [eq_comm, cycleFactorsFinset_eq_list_toFinset hl] at hl'
  simpa [List.mem_toFinset, Ne, ← hl'.right.right] using
    mem_list_cycles_iff hl'.left hl'.right.left

theorem cycleOf_mem_cycleFactorsFinset_iff {f : Perm α} {x : α} :
    cycleOf f x ∈ cycleFactorsFinset f ↔ x ∈ f.support := by
  rw [mem_cycleFactorsFinset_iff]
  constructor
  · rintro ⟨hc, _⟩
    contrapose! hc
    rw [notMem_support, ← cycleOf_eq_one_iff] at hc
    simp [hc]
  · intro hx
    refine ⟨isCycle_cycleOf _ (mem_support.mp hx), ?_⟩
    intro y hy
    rw [mem_support] at hy
    rw [cycleOf_apply]
    split_ifs with H
    · rfl
    · rw [cycleOf_apply_of_not_sameCycle H] at hy
      contradiction

lemma cycleOf_ne_one_iff_mem_cycleFactorsFinset {g : Equiv.Perm α} {x : α} :
    g.cycleOf x ≠ 1 ↔ g.cycleOf x ∈ g.cycleFactorsFinset := by
  rw [cycleOf_mem_cycleFactorsFinset_iff, mem_support, ne_eq, cycleOf_eq_one_iff]

theorem mem_cycleFactorsFinset_support_le {p f : Perm α} (h : p ∈ cycleFactorsFinset f) :
    p.support ≤ f.support := by
  rw [mem_cycleFactorsFinset_iff] at h
  intro x hx
  rwa [mem_support, ← h.right x hx, ← mem_support]

lemma support_zpowers_of_mem_cycleFactorsFinset_le {g : Perm α}
    {c : g.cycleFactorsFinset} (v : Subgroup.zpowers (c : Perm α)) :
    (v : Perm α).support ≤ g.support := by
  obtain ⟨m, hm⟩ := v.prop
  simp only [← hm]
  exact le_trans (support_zpow_le _ _) (mem_cycleFactorsFinset_support_le c.prop)

theorem pairwise_disjoint_of_mem_zpowers :
    Pairwise fun (i j : f.cycleFactorsFinset) ↦
      ∀ (x y : Perm α), x ∈ Subgroup.zpowers ↑i → y ∈ Subgroup.zpowers ↑j → Disjoint x y :=
  fun c d hcd ↦ fun x y hx hy ↦ by
  obtain ⟨m, hm⟩ := hx; obtain ⟨n, hn⟩ := hy
  simp only [← hm, ← hn]
  apply Disjoint.zpow_disjoint_zpow
  exact f.cycleFactorsFinset_pairwise_disjoint c.prop d.prop (Subtype.coe_ne_coe.mpr hcd)

lemma pairwise_commute_of_mem_zpowers :
    Pairwise fun (i j : f.cycleFactorsFinset) ↦
      ∀ (x y : Perm α), x ∈ Subgroup.zpowers ↑i → y ∈ Subgroup.zpowers ↑j → Commute x y :=
  f.pairwise_disjoint_of_mem_zpowers.mono
    (fun _ _ ↦ forall₂_imp (fun _ _ h hx hy ↦ (h hx hy).commute))

lemma disjoint_ofSubtype_noncommPiCoprod (u : Perm (Function.fixedPoints f))
    (v : (c : { x // x ∈ f.cycleFactorsFinset }) → (Subgroup.zpowers (c : Perm α))) :
    Disjoint (ofSubtype u) ((Subgroup.noncommPiCoprod f.pairwise_commute_of_mem_zpowers) v) := by
  apply Finset.noncommProd_induction
  · intro a _ b _ h
    apply f.pairwise_commute_of_mem_zpowers h <;> simp only [Subgroup.coe_subtype, SetLike.coe_mem]
  · intro x y
    exact Disjoint.mul_right
  · exact disjoint_one_right _
  · intro c _
    simp only [Subgroup.coe_subtype]
    exact Disjoint.mono (disjoint_ofSubtype_of_memFixedPoints_self u)
      le_rfl (support_zpowers_of_mem_cycleFactorsFinset_le (v c))

lemma commute_ofSubtype_noncommPiCoprod (u : Perm (Function.fixedPoints f))
    (v : (c : { x // x ∈ f.cycleFactorsFinset }) → (Subgroup.zpowers (c : Perm α))) :
    Commute (ofSubtype u) ((Subgroup.noncommPiCoprod f.pairwise_commute_of_mem_zpowers) v) :=
  Disjoint.commute (f.disjoint_ofSubtype_noncommPiCoprod u v)

theorem mem_support_iff_mem_support_of_mem_cycleFactorsFinset {g : Equiv.Perm α} {x : α} :
    x ∈ g.support ↔ ∃ c ∈ g.cycleFactorsFinset, x ∈ c.support := by
  constructor
  · intro h
    use g.cycleOf x, cycleOf_mem_cycleFactorsFinset_iff.mpr h
    rw [mem_support_cycleOf_iff]
    exact ⟨SameCycle.refl g x, h⟩
  · rintro ⟨c, hc, hx⟩
    exact mem_cycleFactorsFinset_support_le hc hx

theorem cycleFactorsFinset_eq_empty_iff {f : Perm α} : cycleFactorsFinset f = ∅ ↔ f = 1 := by
  simpa [cycleFactorsFinset_eq_finset] using eq_comm

@[simp]
theorem cycleFactorsFinset_one : cycleFactorsFinset (1 : Perm α) = ∅ := by
  simp [cycleFactorsFinset_eq_empty_iff]

@[simp]
theorem cycleFactorsFinset_eq_singleton_self_iff {f : Perm α} :
    f.cycleFactorsFinset = {f} ↔ f.IsCycle := by simp [cycleFactorsFinset_eq_finset]

theorem IsCycle.cycleFactorsFinset_eq_singleton {f : Perm α} (hf : IsCycle f) :
    f.cycleFactorsFinset = {f} :=
  cycleFactorsFinset_eq_singleton_self_iff.mpr hf

theorem cycleFactorsFinset_eq_singleton_iff {f g : Perm α} :
    f.cycleFactorsFinset = {g} ↔ f.IsCycle ∧ f = g := by
  suffices f = g → (g.IsCycle ↔ f.IsCycle) by
    rw [cycleFactorsFinset_eq_finset]
    simpa [eq_comm]
  rintro rfl
  exact Iff.rfl

/-- Two permutations `f g : Perm α` have the same cycle factors iff they are the same. -/
theorem cycleFactorsFinset_injective : Function.Injective (@cycleFactorsFinset α _ _) := by
  intro f g h
  rw [← cycleFactorsFinset_noncommProd f]
  simpa [h] using cycleFactorsFinset_noncommProd g

theorem Disjoint.disjoint_cycleFactorsFinset {f g : Perm α} (h : Disjoint f g) :
    _root_.Disjoint (cycleFactorsFinset f) (cycleFactorsFinset g) := by
  rw [disjoint_iff_disjoint_support] at h
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [mem_cycleFactorsFinset_iff, mem_support] at hx hy
  obtain ⟨⟨⟨a, ha, -⟩, hf⟩, -, hg⟩ := hx, hy
  have := h.le_bot (by simp [ha, ← hf a ha, ← hg a ha] : a ∈ f.support ∩ g.support)
  tauto

theorem Disjoint.cycleFactorsFinset_mul_eq_union {f g : Perm α} (h : Disjoint f g) :
    cycleFactorsFinset (f * g) = cycleFactorsFinset f ∪ cycleFactorsFinset g := by
  rw [cycleFactorsFinset_eq_finset]
  refine ⟨?_, ?_, ?_⟩
  · simp [or_imp, mem_cycleFactorsFinset_iff, forall_swap]
  · rw [coe_union, Set.pairwise_union_of_symmetric Disjoint.symmetric]
    exact
      ⟨cycleFactorsFinset_pairwise_disjoint _, cycleFactorsFinset_pairwise_disjoint _,
        fun x hx y hy _ =>
        h.mono (mem_cycleFactorsFinset_support_le hx) (mem_cycleFactorsFinset_support_le hy)⟩
  · rw [noncommProd_union_of_disjoint h.disjoint_cycleFactorsFinset]
    rw [cycleFactorsFinset_noncommProd, cycleFactorsFinset_noncommProd]

theorem disjoint_mul_inv_of_mem_cycleFactorsFinset {f g : Perm α} (h : f ∈ cycleFactorsFinset g) :
    Disjoint (g * f⁻¹) f := by
  rw [mem_cycleFactorsFinset_iff] at h
  intro x
  by_cases hx : f x = x
  · exact Or.inr hx
  · refine Or.inl ?_
    rw [mul_apply, ← h.right, apply_inv_self]
    rwa [← support_inv, apply_mem_support, support_inv, mem_support]

/-- If c is a cycle, a ∈ c.support and c is a cycle of f, then `c = f.cycleOf a` -/
theorem cycle_is_cycleOf {f c : Equiv.Perm α} {a : α} (ha : a ∈ c.support)
    (hc : c ∈ f.cycleFactorsFinset) : c = f.cycleOf a := by
  suffices f.cycleOf a = c.cycleOf a by
    rw [this]
    apply symm
    exact
      Equiv.Perm.IsCycle.cycleOf_eq (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).left
        (Equiv.Perm.mem_support.mp ha)
  let hfc := (Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset hc).symm
  let hfc2 := Perm.Disjoint.commute hfc
  rw [← Equiv.Perm.cycleOf_mul_of_apply_right_eq_self hfc2]
  · simp only [hfc2.eq, inv_mul_cancel_right]
  -- `a` is in the support of `c`, hence it is not in the support of `g c⁻¹`
  exact
    Equiv.Perm.notMem_support.mp
      (Finset.disjoint_left.mp (Equiv.Perm.Disjoint.disjoint_support hfc) ha)

theorem isCycleOn_support_of_mem_cycleFactorsFinset {g c : Equiv.Perm α}
    (hc : c ∈ g.cycleFactorsFinset) :
    IsCycleOn g c.support := by
  obtain ⟨x, hx⟩ := IsCycle.nonempty_support (mem_cycleFactorsFinset_iff.mp hc).1
  rw [cycle_is_cycleOf hx hc]
  exact isCycleOn_support_cycleOf g x

theorem eq_cycleOf_of_mem_cycleFactorsFinset_iff
    (g c : Perm α) (hc : c ∈ g.cycleFactorsFinset) (x : α) :
    c = g.cycleOf x ↔ x ∈ c.support := by
  refine ⟨?_, (cycle_is_cycleOf · hc)⟩
  rintro rfl
  rw [mem_support, cycleOf_apply_self, ne_eq, ← cycleOf_eq_one_iff]
  exact (mem_cycleFactorsFinset_iff.mp hc).left.ne_one

theorem zpow_apply_mem_support_of_mem_cycleFactorsFinset_iff {g : Perm α}
    {x : α} {m : ℤ} {c : g.cycleFactorsFinset} :
    (g ^ m) x ∈ (c : Perm α).support ↔ x ∈ (c : Perm α).support := by
  rw [← g.eq_cycleOf_of_mem_cycleFactorsFinset_iff _ c.prop, cycleOf_self_apply_zpow,
    eq_cycleOf_of_mem_cycleFactorsFinset_iff _ _ c.prop]

/-- A permutation `c` is a cycle of `g` iff `k * c * k⁻¹` is a cycle of `k * g * k⁻¹` -/
theorem mem_cycleFactorsFinset_conj (g k c : Perm α) :
    k * c * k⁻¹ ∈ (k * g * k⁻¹).cycleFactorsFinset ↔ c ∈ g.cycleFactorsFinset := by
  suffices imp_lemma : ∀ {g k c : Perm α},
      c ∈ g.cycleFactorsFinset → k * c * k⁻¹ ∈ (k * g * k⁻¹).cycleFactorsFinset by
    refine ⟨fun h ↦ ?_, imp_lemma⟩
    have aux : ∀ h : Perm α, h = k⁻¹ * (k * h * k⁻¹) * k := fun _ ↦ by group
    rw [aux g, aux c]
    exact imp_lemma h
  intro g k c
  simp only [mem_cycleFactorsFinset_iff]
  apply And.imp IsCycle.conj
  intro hc a ha
  simp only [coe_mul, Function.comp_apply, EmbeddingLike.apply_eq_iff_eq]
  apply hc
  rw [mem_support] at ha ⊢
  contrapose! ha
  simp only [mul_smul, ← Perm.smul_def] at ha ⊢
  rw [ha]
  simp only [Perm.smul_def, apply_inv_self]

/-- If a permutation commutes with every cycle of `g`, then it commutes with `g`

NB. The converse is false. Commuting with every cycle of `g` means that we belong
to the kernel of the action of `Equiv.Perm α` on `g.cycleFactorsFinset` -/
theorem commute_of_mem_cycleFactorsFinset_commute (k g : Perm α)
    (hk : ∀ c ∈ g.cycleFactorsFinset, Commute k c) :
    Commute k g := by
  rw [← cycleFactorsFinset_noncommProd g (cycleFactorsFinset_mem_commute g)]
  apply Finset.noncommProd_commute
  simpa only [id_eq] using hk

/-- The cycles of a permutation commute with it -/
theorem self_mem_cycle_factors_commute {g c : Perm α}
    (hc : c ∈ g.cycleFactorsFinset) : Commute c g := by
  apply commute_of_mem_cycleFactorsFinset_commute
  intro c' hc'
  by_cases hcc' : c = c'
  · rw [hcc']
  · apply g.cycleFactorsFinset_mem_commute hc hc'; exact hcc'

/-- If `c` and `d` are cycles of `g`, then `d` stabilizes the support of `c` -/
theorem mem_support_cycle_of_cycle {g d c : Perm α}
    (hc : c ∈ g.cycleFactorsFinset) (hd : d ∈ g.cycleFactorsFinset) :
    ∀ x : α, d x ∈ c.support ↔ x ∈ c.support := by
  intro x
  simp only [mem_support, not_iff_not]
  by_cases h : c = d
  · rw [← h, EmbeddingLike.apply_eq_iff_eq]
  · rw [← Perm.mul_apply,
      Commute.eq (cycleFactorsFinset_mem_commute g hc hd h),
      mul_apply, EmbeddingLike.apply_eq_iff_eq]

/-- If a permutation is a cycle of `g`, then its support is invariant under `g`. -/
theorem mem_cycleFactorsFinset_support {g c : Perm α} (hc : c ∈ g.cycleFactorsFinset) (a : α) :
    g a ∈ c.support ↔ a ∈ c.support :=
  mem_support_iff_of_commute (self_mem_cycle_factors_commute hc).symm a

end CycleFactorsFinset

@[elab_as_elim]
theorem cycle_induction_on [Finite β] (P : Perm β → Prop) (σ : Perm β) (base_one : P 1)
    (base_cycles : ∀ σ : Perm β, σ.IsCycle → P σ)
    (induction_disjoint : ∀ σ τ : Perm β,
      Disjoint σ τ → IsCycle σ → P σ → P τ → P (σ * τ)) : P σ := by
  cases nonempty_fintype β
  suffices ∀ l : List (Perm β),
      (∀ τ : Perm β, τ ∈ l → τ.IsCycle) → l.Pairwise Disjoint → P l.prod by
    classical
      let x := σ.truncCycleFactors.out
      exact (congr_arg P x.2.1).mp (this x.1 x.2.2.1 x.2.2.2)
  intro l
  induction l with
  | nil => exact fun _ _ => base_one
  | cons σ l ih =>
    intro h1 h2
    rw [List.prod_cons]
    exact
      induction_disjoint σ l.prod (disjoint_prod_right _ (List.pairwise_cons.mp h2).1)
        (h1 _ List.mem_cons_self) (base_cycles σ (h1 σ List.mem_cons_self))
        (ih (fun τ hτ => h1 τ (List.mem_cons_of_mem σ hτ)) h2.of_cons)

theorem cycleFactorsFinset_mul_inv_mem_eq_sdiff [DecidableEq α] [Fintype α] {f g : Perm α}
    (h : f ∈ cycleFactorsFinset g) : cycleFactorsFinset (g * f⁻¹) = cycleFactorsFinset g \ {f} := by
  revert f
  refine
    cycle_induction_on (P := fun {g : Perm α} ↦
      ∀ {f}, (f ∈ cycleFactorsFinset g)
        → cycleFactorsFinset (g * f⁻¹) = cycleFactorsFinset g \ {f}) _ ?_ ?_ ?_
  · simp
  · intro σ hσ f hf
    simp only [cycleFactorsFinset_eq_singleton_self_iff.mpr hσ, mem_singleton] at hf ⊢
    simp [hf]
  · intro σ τ hd _ hσ hτ f
    simp_rw [hd.cycleFactorsFinset_mul_eq_union, mem_union]
    -- if only `wlog` could work here...
    rintro (hf | hf)
    · rw [hd.commute.eq, union_comm, union_sdiff_distrib, sdiff_singleton_eq_erase,
        erase_eq_of_notMem, mul_assoc, Disjoint.cycleFactorsFinset_mul_eq_union, hσ hf]
      · rw [mem_cycleFactorsFinset_iff] at hf
        intro x
        rcases hd.symm x with hx | hx
        · exact Or.inl hx
        · refine Or.inr ?_
          by_cases hfx : f x = x
          · rw [← hfx]
            simpa [hx] using hfx.symm
          · rw [mul_apply]
            rw [← hf.right _ (mem_support.mpr hfx)] at hx
            contradiction
      · exact fun H =>
        notMem_empty _ (hd.disjoint_cycleFactorsFinset.le_bot (mem_inter_of_mem hf H))
    · rw [union_sdiff_distrib, sdiff_singleton_eq_erase, erase_eq_of_notMem, mul_assoc,
        Disjoint.cycleFactorsFinset_mul_eq_union, hτ hf]
      · rw [mem_cycleFactorsFinset_iff] at hf
        intro x
        rcases hd x with hx | hx
        · exact Or.inl hx
        · refine Or.inr ?_
          by_cases hfx : f x = x
          · rw [← hfx]
            simpa [hx] using hfx.symm
          · rw [mul_apply]
            rw [← hf.right _ (mem_support.mpr hfx)] at hx
            contradiction
      · exact fun H =>
        notMem_empty _ (hd.disjoint_cycleFactorsFinset.le_bot (mem_inter_of_mem H hf))

theorem IsCycle.forall_commute_iff [DecidableEq α] [Fintype α] (g z : Perm α) :
    (∀ c ∈ g.cycleFactorsFinset, Commute z c) ↔
      ∀ c ∈ g.cycleFactorsFinset,
      ∃ (hc : ∀ x : α, z x ∈ c.support ↔ x ∈ c.support),
        ofSubtype (subtypePerm z hc) ∈ Subgroup.zpowers c := by
  apply forall_congr'
  intro c
  apply imp_congr_right
  intro hc
  exact IsCycle.commute_iff (mem_cycleFactorsFinset_iff.mp hc).1

/-- A permutation restricted to the support of a cycle factor is that cycle factor -/
theorem subtypePerm_on_cycleFactorsFinset [DecidableEq α] [Fintype α]
    {g c : Perm α} (hc : c ∈ g.cycleFactorsFinset) :
    g.subtypePerm (mem_cycleFactorsFinset_support hc) = c.subtypePermOfSupport := by
  ext ⟨x, hx⟩
  simp only [subtypePerm_apply, Subtype.coe_mk, subtypePermOfSupport]
  exact ((mem_cycleFactorsFinset_iff.mp hc).2 x hx).symm

theorem commute_iff_of_mem_cycleFactorsFinset [DecidableEq α] [Fintype α] {g k c : Equiv.Perm α}
    (hc : c ∈ g.cycleFactorsFinset) :
    Commute k c ↔
      ∃ hc' : ∀ x : α, k x ∈ c.support ↔ x ∈ c.support,
        k.subtypePerm hc' ∈ Subgroup.zpowers
          (g.subtypePerm (mem_cycleFactorsFinset_support hc)) := by
  rw [IsCycle.commute_iff' (mem_cycleFactorsFinset_iff.mp hc).1]
  apply exists_congr
  intro hc'
  simp only [Subgroup.mem_zpowers_iff]
  apply exists_congr
  intro n
  rw [Equiv.Perm.subtypePerm_on_cycleFactorsFinset hc]

end cycleFactors

end Perm

end Equiv
