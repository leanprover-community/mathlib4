/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Transitive

/-!
# Folkman's semi-symmetric graphs

A semi-symmetric graph is a regular edge-transitive but not vertex-transitive graph.
Jon Folkman [folkman] provided the first explicit examples using a general construction
based on an abelian group `A`, an automorphism of that group `T` and a number `r`,
which is reproduced here. "The" Folkman graph on 20 vertices, the smallest semi-symmetric graph,
is the result of this construction with `A = Fin 5`, `T = (2 * ·)` and `r = 2`.

## Main declarations

* `SimpleGraph.folkmanGraph`: the generalized Folkman graph as defined in [folkman].
* `SimpleGraph.isRegularOfDegree_folkmanGraph`: the generalized Folkman graph is `2 * r`-regular.
* `SimpleGraph.not_isVertexTransitive_folkmanGraph`: the generalized Folkman graph is
  **not** vertex-transitive.
* `SimpleGraph.isEdgeTransitive_folkmanGraph`: the generalized Folkman graph is edge-transitive.
* `SimpleGraph.theFolkmanGraph`: the 20-vertex Folkman graph.
-/

public section

namespace SimpleGraph

variable {A : Type*} [AddCommGroup A] {T : A ≃+ A} {a : A} {r : ℕ}

variable (T a r) in
/-- The generalized Folkman graph with automorphism `T`, distinguished element `a` and
size parameter `r`. -/
def folkmanGraph : SimpleGraph (Fin r × A ⊕ Fin r × A) where
  Adj
  | .inl v, .inr w | .inr w, .inl v => v.2 = w.2 ∨ v.2 + (v.1.1 • T) a = w.2
  | _, _ => False

section

variable {v w : Fin r × A}

@[simp] lemma folkmanGraph_adj_inl_inl : ¬(folkmanGraph T a r).Adj (.inl v) (.inl w) := id

@[simp] lemma folkmanGraph_adj_inl_inr :
    (folkmanGraph T a r).Adj (.inl v) (.inr w) ↔ v.2 = w.2 ∨ v.2 + (v.1.1 • T) a = w.2 :=
  Iff.rfl

@[simp] lemma folkmanGraph_adj_inr_inl :
    (folkmanGraph T a r).Adj (.inr w) (.inl v) ↔ v.2 = w.2 ∨ v.2 + (v.1.1 • T) a = w.2 :=
  Iff.rfl

@[simp] lemma folkmanGraph_adj_inr_inr : ¬(folkmanGraph T a r).Adj (.inr v) (.inr w) := id

instance [DecidableEq A] : DecidableRel (folkmanGraph T a r).Adj := fun x y ↦ by
  cases x <;> cases y
  · exact inferInstanceAs (Decidable False)
  · simp only [folkmanGraph_adj_inl_inr]; infer_instance
  · simp only [folkmanGraph_adj_inr_inl]; infer_instance
  · exact inferInstanceAs (Decidable False)

lemma neighborSet_folkmanGraph_inl :
    (folkmanGraph T a r).neighborSet (.inl v) =
    ⋃ j, {.inr (j, v.2), .inr (j, v.2 + (v.1.1 • T) a)} := by
  ext w
  cases w with | inl w => simp | inr w => simp; grind

lemma neighborSet_folkmanGraph_inr :
    (folkmanGraph T a r).neighborSet (.inr w) =
    ⋃ i, {.inl (i, w.2), .inl (i, w.2 - (i.1 • T) a)} := by
  ext v
  cases v with | inr v => simp | inl v => _
  simp only [mem_neighborSet, folkmanGraph_adj_inr_inl, Set.mem_iUnion]
  exact ⟨fun h ↦ ⟨v.1, h.imp (fun k ↦ by simp [← k]) (fun k ↦ by simp [← k])⟩, by grind⟩

instance [DecidableEq A] : (folkmanGraph T a r).LocallyFinite := fun x ↦ by
  cases x with
  | inl v => rw [neighborSet_folkmanGraph_inl]; infer_instance
  | inr w => rw [neighborSet_folkmanGraph_inr]; infer_instance

lemma neighborFinset_folkmanGraph_inl [DecidableEq A] :
    (folkmanGraph T a r).neighborFinset (.inl v) =
    Finset.univ.biUnion fun j ↦ {.inr (j, v.2), .inr (j, v.2 + (v.1.1 • T) a)} := by
  ext x
  simp [← mem_neighborSet, neighborSet_folkmanGraph_inl]

lemma neighborFinset_folkmanGraph_inr [DecidableEq A] :
    (folkmanGraph T a r).neighborFinset (.inr w) =
    Finset.univ.biUnion fun i ↦ {.inl (i, w.2), .inl (i, w.2 - (i.1 • T) a)} := by
  ext x
  simp [← mem_neighborSet, neighborSet_folkmanGraph_inr]

end

variable (rT : (r • T) a = a ∨ (r • T) a = -a)
  (pT : ∀ i < r, i ≠ 0 → (i • T) a ≠ a) (nT : ∀ i < r, (i • T) a ≠ -a)

open Finset in
include nT in
theorem isRegularOfDegree_folkmanGraph [DecidableEq A] [NeZero r] :
    (folkmanGraph T a r).IsRegularOfDegree (2 * r) := fun x ↦ by
  have na : a ≠ 0 := by grind [nT _ ‹NeZero r›.pos]
  have Tnz (i : Fin r) : (i.1 • T) a ≠ 0 := by rwa [AddEquiv.map_ne_zero_iff]
  cases x with
  | inl v =>
    rw [degree, neighborFinset_folkmanGraph_inl, card_biUnion (by rintro i - j - hn; simp; lia)]
    conv_lhs => enter [2, j]; rw [card_pair (by simp [na])]
    simp [mul_comm]
  | inr w =>
    rw [degree, neighborFinset_folkmanGraph_inr, card_biUnion (by rintro i - j - hn; simp; lia)]
    conv_lhs => enter [2, i]; rw [card_pair (by grind)]
    simp [mul_comm]

include pT nT in
theorem not_isVertexTransitive_folkmanGraph [r.AtLeastTwo] :
    ¬(folkmanGraph T a r).IsVertexTransitive := by
  by_contra vt
  obtain ⟨f, hf⟩ := vt.exists_iso (.inr (0, 0)) (.inl (0, 0))
  suffices f (.inr (1, 0)) = .inl (0, 0) by simp [← hf, ‹r.AtLeastTwo›.ne_one] at this
  obtain ⟨v, hv⟩ : ∃ v, f (.inr (1, 0)) = .inl v := by
    have a₁ : (folkmanGraph T a r).Adj (.inr (0, 0)) (.inl (0, 0)) := by simp
    have a₂ : (folkmanGraph T a r).Adj (.inl (0, 0)) (.inr (1, 0)) := by simp
    rw [← f.map_adj_iff] at a₁ a₂
    rw [hf] at a₁
    obtain ⟨w, hw⟩ : ∃ w, f (.inl (0, 0)) = .inr w := by
      cases hw : f (.inl (0, 0)) with
      | inl w => simp [hw] at a₁
      | inr w => simp
    cases hv : f (.inr (1, 0)) with
    | inl v => simp
    | inr v => simp [hw, hv] at a₂
  have nb : (folkmanGraph T a r).neighborSet (.inr (0, 0)) =
      (folkmanGraph T a r).neighborSet (.inr (1, 0)) := by simp_rw [neighborSet_folkmanGraph_inr]
  replace nb : ({0, a} : Set A) = {v.2, v.2 + (v.1.1 • T) a} := by
    apply_fun ({i | Sum.inr (0, i) ∈ f '' ·}) at nb
    simp_rw [f.image_neighborSet, hf, hv, neighborSet_folkmanGraph_inl, Fin.val_zero, zero_smul,
      AddAut.zero_apply, zero_add, Set.mem_iUnion, Set.mem_insert_iff, Set.mem_singleton_iff,
      Sum.inr.injEq, Prod.mk.injEq, ← and_or_left, existsAndEq, true_and] at nb
    exact nb
  grind [Set.pair_eq_pair_iff]

lemma _root_.Fin.add_one_eq_zero_iff {i : Fin r} (_ : NeZero r := i.neZero) :
    i + 1 = 0 ↔ i.1 + 1 = r := by
  rw [← Fin.val_inj, Fin.val_zero, Fin.val_add]
  obtain h | h : i.1 + 1 < r ∨ i.1 + 1 = r := by lia
  · simp [Nat.mod_eq_of_lt h, h.ne]
  · simp [h]

lemma _root_.Fin.add_one_ne_zero_iff {i : Fin r} (_ : NeZero r := i.neZero) :
    i + 1 ≠ 0 ↔ i.1 + 1 < r := by
  rw [← not_iff_not, not_ne_iff, Fin.add_one_eq_zero_iff]
  lia

/-- The automorphism `ρ` in [folkman] when `(r • T) a = a`. -/
def folkmanRhoPlus [NeZero r] (rT : (r • T) a = a) :
    folkmanGraph T a r ≃g folkmanGraph T a r where
  toFun
  | .inl v => .inl (v.1 + 1, T v.2)
  | .inr w => .inr (w.1, T w.2)
  invFun
  | .inl v => .inl (v.1 - 1, T.symm v.2)
  | .inr w => .inr (w.1, T.symm w.2)
  left_inv x := by cases x <;> simp
  right_inv x := by cases x <;> simp
  map_rel_iff' {x y} := by
    have red (i : Fin r) : ((i + 1).1 • T) a = T ((i.1 • T) a) := by
      rw [← AddAut.add_apply, ← succ_nsmul']
      obtain h | h : i.1 + 1 < r ∨ i.1 + 1 = r := by lia
      · rw [Fin.val_add_one_of_lt' h]
      · simp [h, rT, Fin.val_add]
    obtain v | w := x <;> obtain v' | w' := y
    case inl.inl | inr.inr => simp
    all_goals simp [red, ← map_add]

/-- The automorphism `ρ` in [folkman] when `(r • T) a = -a`. -/
def folkmanRhoMinus [NeZero r] (rT : (r • T) a = -a) :
    folkmanGraph T a r ≃g folkmanGraph T a r where
  toFun
  | .inl v => .inl (v.1 + 1, T v.2 - if v.1 + 1 = 0 then a else 0)
  | .inr w => .inr (w.1, T w.2)
  invFun
  | .inl v => .inl (v.1 - 1, T.symm (v.2 + if v.1 = 0 then a else 0))
  | .inr w => .inr (w.1, T.symm w.2)
  left_inv x := by cases x <;> simp
  right_inv x := by cases x <;> simp
  map_rel_iff' {x y} := by
    have red₁ {i : Fin r} (h : i + 1 = 0) : T ((i.1 • T) a) = -a := by
      rw [Fin.add_one_eq_zero_iff] at h
      rw [← AddAut.add_apply, ← succ_nsmul', h, rT]
    have red₂ {i : Fin r} (h : i + 1 ≠ 0) : ((i + 1).1 • T) a = T ((i.1 • T) a) := by
      rw [Fin.add_one_ne_zero_iff] at h
      rw [← AddAut.add_apply, ← succ_nsmul', Fin.val_add_one_of_lt' h]
    obtain v | w := x <;> obtain v' | w' := y
    case inl.inl | inr.inr => simp
    all_goals
      simp only [Equiv.coe_fn_mk, folkmanGraph_adj_inl_inr, folkmanGraph_adj_inr_inl]
      split_ifs with h
      · rw [h, Fin.val_zero, zero_smul, AddAut.zero_apply, sub_add_cancel, T.injective.eq_iff,
          or_comm]
        apply or_congr_right
        conv_rhs => rw [← T.injective.eq_iff, map_add, red₁ h, ← sub_eq_add_neg]
      · simp [red₂ h, ← map_add]

include rT in
lemma isEdgeTransitive_folkmanGraph_aux1 (v w : Fin r × A) (_ : NeZero r := v.1.neZero) :
    ∃ f : folkmanGraph T a r ≃g folkmanGraph T a r, ∃ b w',
    f (.inl v) = .inl (0, b) ∧ f (.inr w) = .inr w' := by
  cases r with | zero => exact v.1.elim0 | succ r => _
  obtain ⟨i, c⟩ := v
  induction i using Fin.induction generalizing w c with
  | zero => exact ⟨Iso.refl, c, by simp⟩
  | succ i ih =>
    obtain rT | rT := rT
    · have ll : ((folkmanRhoPlus rT).symm (.inl (i.succ, c))).isLeft := by simp [folkmanRhoPlus]
      rw [Sum.isLeft_iff] at ll
      obtain ⟨⟨i', c'⟩, hp⟩ := ll
      have rr : ((folkmanRhoPlus rT).symm (.inr w)).isRight := by simp [folkmanRhoPlus]
      rw [Sum.isRight_iff] at rr
      obtain ⟨w₁, hw₁⟩ := rr
      obtain ⟨f, b, w₂, hw₂⟩ := ih w₁ c'
      refine ⟨(folkmanRhoPlus rT).symm.trans f, b, w₂, ?_⟩
      have i'_eq : i' = i.castSucc := by
        simp_rw [folkmanRhoPlus, RelIso.coe_fn_symm_mk, Equiv.symm_mk, Equiv.coe_fn_mk,
          Sum.inl.injEq, Prod.mk.injEq, ← Fin.coeSucc_eq_succ, add_sub_cancel_right] at hp
        exact hp.1.symm
      rwa [RelIso.trans_apply, hp, i'_eq, RelIso.trans_apply, hw₁]
    · have ll : ((folkmanRhoMinus rT).symm (.inl (i.succ, c))).isLeft := by simp [folkmanRhoMinus]
      rw [Sum.isLeft_iff] at ll
      obtain ⟨⟨i', c'⟩, hp⟩ := ll
      have rr : ((folkmanRhoMinus rT).symm (.inr w)).isRight := by simp [folkmanRhoMinus]
      rw [Sum.isRight_iff] at rr
      obtain ⟨w₁, hw₁⟩ := rr
      obtain ⟨f, b, w₂, hw₂⟩ := ih w₁ c'
      refine ⟨(folkmanRhoMinus rT).symm.trans f, b, w₂, ?_⟩
      have i'_eq : i' = i.castSucc := by
        simp_rw [folkmanRhoMinus, RelIso.coe_fn_symm_mk, Equiv.symm_mk, Equiv.coe_fn_mk,
          Sum.inl.injEq, Prod.mk.injEq, ← Fin.coeSucc_eq_succ, add_sub_cancel_right] at hp
        exact hp.1.symm
      rwa [RelIso.trans_apply, hp, i'_eq, RelIso.trans_apply, hw₁]

variable (T a r) in
/-- A combination of the commuting automorphisms `σ` and `τ` in [folkman]. -/
def folkmanST (i : Fin r) (c : A) (_ : NeZero r := i.neZero) :
    folkmanGraph T a r ≃g folkmanGraph T a r where
  toFun
  | .inl v => .inl (v.1, v.2 + c)
  | .inr w => .inr (w.1 + i, w.2 + c)
  invFun
  | .inl v => .inl (v.1, v.2 - c)
  | .inr w => .inr (w.1 - i, w.2 - c)
  left_inv x := by cases x <;> simp
  right_inv x := by cases x <;> simp
  map_rel_iff' {x y} := by obtain _ | _ := x <;> obtain _ | _ := y <;> simp <;> grind

include rT in
lemma isEdgeTransitive_folkmanGraph_aux2 (v w : Fin r × A) (_ : NeZero r := v.1.neZero) :
    ∃ f : folkmanGraph T a r ≃g folkmanGraph T a r, ∃ b,
    f (.inl v) = .inl (0, b) ∧ f (.inr w) = .inr (0, 0) := by
  obtain ⟨f, b, w₁, fv, fw⟩ := isEdgeTransitive_folkmanGraph_aux1 rT v w
  have rr : ((folkmanST T a r (-w.1) (-w.2)) (.inr w₁)).isRight := by simp [folkmanST]
  rw [Sum.isRight_iff] at rr
  obtain ⟨⟨i', c'⟩, hp⟩ := rr
  refine ⟨f.trans (folkmanST T a r (-w₁.1) (-w₁.2)), b - w₁.2, ?_⟩
  simp_rw [RelIso.trans_apply, fv, fw, folkmanST, RelIso.coe_fn_mk, Equiv.coe_fn_mk, Sum.inl.injEq,
    Sum.inr.injEq, add_neg_cancel, sub_eq_add_neg, true_and]

variable (T a r) in
/-- The automorphism `η` in [folkman]. -/
def folkmanEta : folkmanGraph T a r ≃g folkmanGraph T a r where
  toFun
  | .inl v => .inl (v.1, -(v.2 + (v.1.1 • T) a))
  | .inr w => .inr (w.1, -w.2)
  invFun
  | .inl v => .inl (v.1, -(v.2 + (v.1.1 • T) a))
  | .inr w => .inr (w.1, -w.2)
  left_inv x := by cases x <;> simp
  right_inv x := by cases x <;> simp
  map_rel_iff' {x y} := by
    obtain _ | _ := x <;> obtain _ | _ := y
    case inl.inl | inr.inr => simp
    all_goals
      simp only [Equiv.coe_fn_mk, folkmanGraph_adj_inl_inr, folkmanGraph_adj_inr_inl, neg_add_rev]
      rw [neg_add_cancel_comm, ← neg_add_rev, neg_inj, neg_inj, or_comm]

include rT in
theorem isEdgeTransitive_folkmanGraph [NeZero r] : (folkmanGraph T a r).IsEdgeTransitive := by
  suffices ∀ v w, (folkmanGraph T a r).Adj (.inl v) (.inr w) →
      ∃ f : folkmanGraph T a r ≃g folkmanGraph T a r,
      f (.inl v) = .inl (0, 0) ∧ f (.inr w) = .inr (0, 0) by
    rw [isEdgeTransitive_iff]
    intro x y me₁ me₂
    obtain ⟨v | v, w | w⟩ := x
    case inl.inl | inr.inr => simp at me₁
    all_goals
      obtain ⟨f, f₁, f₂⟩ := this _ _ me₁
      obtain ⟨v' | v', w' | w'⟩ := y
      case inl.inl | inr.inr => simp at me₂
    all_goals
      obtain ⟨g, g₁, g₂⟩ := this _ _ me₂
      simp only [Sym2.map_mk, Sym2.eq_iff, exists_or]
    on_goal 1 4 => left
    on_goal 2 3 => right
    all_goals exact ⟨f.trans g.symm, by simp [f₁, f₂, ← g₁, ← g₂]⟩
  intro v w hvw
  obtain ⟨f, b, fv, fw⟩ := isEdgeTransitive_folkmanGraph_aux2 rT v w
  rw [← f.map_adj_iff, fv, fw, folkmanGraph_adj_inl_inr] at hvw
  simp_rw [Fin.val_zero, zero_smul, AddAut.zero_apply, add_eq_zero_iff_eq_neg] at hvw
  obtain rfl | rfl := hvw
  · exact ⟨f, fv, fw⟩
  · exact ⟨f.trans (folkmanEta T a r), by simp [fv, fw, folkmanEta]⟩

/-! ### "The" Folkman graph -/

/-- The `AddEquiv` on `Fin 5` used to define `theFolkmanGraph`. -/
def theFolkmanGraphAddEquiv : Fin 5 ≃+ Fin 5 where
  toFun := (2 * ·)
  invFun := (3 * ·)
  left_inv _ := by decide +revert
  right_inv _ := by decide +revert
  map_add' _ _ := by rw [mul_add]

/-- "The" Folkman graph on 20 vertices, the smallest semi-symmetric graph. -/
abbrev theFolkmanGraph : SimpleGraph (Fin 2 × Fin 5 ⊕ Fin 2 × Fin 5) :=
  folkmanGraph theFolkmanGraphAddEquiv 2 2

theorem isRegularOfDegree_theFolkmanGraph : theFolkmanGraph.IsRegularOfDegree 4 :=
  isRegularOfDegree_folkmanGraph (by decide)

theorem isEdgeTransitive_theFolkmanGraph : theFolkmanGraph.IsEdgeTransitive :=
  isEdgeTransitive_folkmanGraph (by decide)

theorem not_isVertexTransitive_theFolkmanGraph : ¬theFolkmanGraph.IsVertexTransitive :=
  not_isVertexTransitive_folkmanGraph (by decide) (by decide)

end SimpleGraph
