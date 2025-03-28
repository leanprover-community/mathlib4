/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.GroupTheory.GroupAction.Embedding
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.GroupAction.Transitive

/-! # Multiple transitivity

* `MulAction.IsMultiplyPretransitive`:
An multiplicative action of a group `G` on a type `α` is n-transitive
if the action of `G` on `Fin n ↪ α` is pretransitive.

* Any action is 0-pretransitive

* `MulAction.is_one_pretransitive_iff` :
An action is 1-pretransitive iff it is pretransitive

* `MulAction.is_two_pretransitive_iff` :
An action is 2-pretransitive if for any `a`, `b`, `c`, `d`, such that
`a ≠ b` and `c ≠ d`, there exist `g : G` such that `g • a = b` and `g • c = d`.

* `MulAction.isPreprimitive_of_is_two_pretransitive` :
A 2-transitive action is preprimitive

* `MulAction.isMultiplyPretransitive_of_le` :
If an action is `n`-pretransitive, then it is `m`-pretransitive for all `m ≤ n`,
provided `α` has at least `n` elements.

## Remarks on implementation

These results are results about actions on types `n ↪ α` induced by an action
on `α`, and some results are developed in this context.

-/

open MulAction MulActionHom Function.Embedding Fin Set Nat

section Functoriality

variable {G α : Type*} [Group G] [MulAction G α]
variable {H β : Type*} [Group H] [MulAction H β]
variable {σ : G → H} {f : α →ₑ[σ] β} {ι : Type*}

/-- An injective equivariant map `α →ₑ[σ] β` induces
an equivariant map on embedding types (ι ↪ α) → (ι ↪ β) -/
@[to_additive]
def Function.Injective.mulActionHom_embedding (hf : Function.Injective f) :
    (ι ↪ α) →ₑ[σ] (ι ↪ β) where
  toFun x := ⟨f.toFun ∘ x.toFun, hf.comp x.inj'⟩
  map_smul' m x := by
    ext i
    simp only [smul_apply, coeFn_mk, Function.comp_apply, toFun_eq_coe, smul_apply]
    rw [f.map_smul']

@[to_additive (attr := simp)]
theorem Function.Injective.mulActionHom_embedding_apply
    (hf : Function.Injective f) {x : ι ↪ α} {i : ι} :
    hf.mulActionHom_embedding x i = f (x i) := rfl

@[to_additive]
theorem Function.Injective.mulActionHom_embedding_isInjective
    (hf : Function.Injective f) :
    Function.Injective (hf.mulActionHom_embedding (ι := ι)) := by
  intro _ _ hxy
  ext
  apply hf
  simp only [← hf.mulActionHom_embedding_apply, hxy]

variable (hf' : Function.Bijective f)

@[to_additive]
theorem Function.Bijective.mulActionHom_embedding_isBijective (hf : Function.Bijective f) :
    Function.Bijective (hf.injective.mulActionHom_embedding (ι := ι)) := by
  refine ⟨hf.injective.mulActionHom_embedding_isInjective, ?_⟩
  intro y
  obtain ⟨g, _, hfg⟩ := Function.bijective_iff_has_inverse.mp hf
  use ⟨g ∘ y, hfg.injective.comp (EmbeddingLike.injective y)⟩
  ext
  simp only [hf.injective.mulActionHom_embedding_apply, coeFn_mk, comp_apply]
  exact hfg (y _)

end Functoriality

namespace MulAction

open scoped BigOperators Pointwise Cardinal

variable (G α : Type*) [Group G] [MulAction G α]

/-- An action of a group on a type α is n-pretransitive
if the associated action on (Fin n ↪ α) is pretransitive. -/
@[to_additive "An additive action of an additive group on a type α
is n-pretransitive if the associated action on (Fin n ↪ α) is pretransitive."]
abbrev IsMultiplyPretransitive (n : ℕ) := IsPretransitive G (Fin n ↪ α)

variable {G H α β : Type*} [Group G] [MulAction G α] [Group H] [MulAction H β]
  {σ : G → H} {f : α →ₑ[σ] β} (hf : Function.Injective f)

/- If there exists a surjective equivariant map `α →ₑ[σ] β`
then pretransitivity descends from `n ↪ α` to `n ↪ β`.

The subtlety is that if it is not injective, this map does not induce
an equivariant map from `n ↪ α` to `n ↪ β`. -/
@[to_additive]
theorem IsPretransitive.of_embedding {n : Type*}
    (hf : Function.Surjective f) [IsPretransitive G (n ↪ α)] :
    IsPretransitive H (n ↪ β) where
  exists_smul_eq x y := by
    let aux (x : n ↪ β) : (n ↪ α) :=
      x.trans (Function.Embedding.ofSurjective (⇑f) hf)
    have aux_apply (x : n ↪ β) (i : n) : f.toFun (aux x i) = x i := by
      simp only [trans_apply, aux]
      apply Function.surjInv_eq
    obtain ⟨g, hg⟩ := exists_smul_eq (M := G) (aux x) (aux y)
    use σ g
    ext i
    rw [DFunLike.ext_iff] at hg
    rw [smul_apply]
    simp only [← aux_apply, ← hg, smul_apply, MulActionHom.map_smul']

@[to_additive]
theorem IsPretransitive.of_embedding_congr {n : Type*}
    (hσ : Function.Surjective σ) (hf : Function.Bijective f) :
    IsPretransitive G (n ↪ α) ↔ IsPretransitive H (n ↪ β) :=
  isPretransitive_congr hσ hf.mulActionHom_embedding_isBijective

section Zero

/-- Any action is 0-pretransitive -/
@[to_additive]
theorem is_zero_pretransitive {n : Type*} [IsEmpty n] :
    IsPretransitive G (n ↪ α) := inferInstance

/-- Any action is 0-pretransitive -/
@[to_additive]
theorem is_zero_pretransitive' :
    IsMultiplyPretransitive G α 0 := inferInstance


end Zero

section One

def _root_.Function.Embedding.oneEmbeddingEquiv {one : Type*} [Unique one] : (one ↪ α) ≃ α where
  toFun f := f default
  invFun a := {
    toFun := fun _ ↦ a
    inj' x y h := by simp [Unique.uniq inferInstance] }
  left_inv f := by ext; simp [Unique.uniq]
  right_inv a := rfl

/-- When `Unique one`, the equivariant map from `one ↪ α` to `α` -/
@[to_additive]
def _root_.MulActionHom.oneEmbeddingMap {one : Type*} [Unique one] :
    (one ↪ α) →[G] α := {
  oneEmbeddingEquiv with
  map_smul' _ _ := rfl }

@[to_additive]
theorem _root_.MulActionHom.oneEmbeddingMap_bijective {one : Type*} [Unique one] :
    Function.Bijective (oneEmbeddingMap (one := one) (G := G) (α := α)) :=
  oneEmbeddingEquiv.bijective

/-- An action is 1-pretransitive iff it is pretransitive -/
@[to_additive]
theorem oneEmbedding_isPretransitive_iff {one : Type*} [Unique one] :
    IsPretransitive G (one ↪ α) ↔ IsPretransitive G α :=
  isPretransitive_congr Function.surjective_id oneEmbeddingMap_bijective

/-- An action is 1-pretransitive iff it is pretransitive -/
@[to_additive]
theorem is_one_pretransitive_iff :
    IsMultiplyPretransitive G α 1 ↔ IsPretransitive G α :=
  oneEmbedding_isPretransitive_iff

end One

section Two

-- Should be somewhere else, but where?
lemma _root_.Fin.eq_zero_or_one : ∀ (i : Fin 2), i = 0 ∨ i = 1 := by decide

/-- Two distinct elements of `α` give an embedding `Fin 2 ↪ α` -/
def _root_.Function.Embedding.embFinTwo {a b: α} (h : a ≠ b) : Fin 2 ↪ α where
  toFun
    | 0 => a
    | 1 => b
  inj' i j hij := by
    rcases i.eq_zero_or_one with hi | hi
    · rcases j.eq_zero_or_one with hj | hj
      · rw [hi, hj]
      · simp [hi, hj] at hij; exact False.elim (h hij)
    · rcases j.eq_zero_or_one with hj | hj
      · simp [hi, hj] at hij; exact False.elim (h hij.symm)
      · rw [hi, hj]

theorem _root_.Function.Embedding.embFinTwo_apply_zero
    {a b : α} (h : a ≠ b) : embFinTwo h 0 = a := rfl

theorem _root_.Function.Embedding.embFinTwo_apply_one
    {a b : α} (h : a ≠ b) : embFinTwo h 1 = b := rfl

/-- An action is 2-pretransitive iff it is two_pretransitive… -/
@[to_additive]
theorem is_two_pretransitive_iff :
    IsMultiplyPretransitive G α 2 ↔
      ∀ {a b c d : α} (_ : a ≠ b) (_ : c ≠ d), ∃ g : G, g • a = c ∧ g • b = d := by
  constructor
  · intro _ a b c d h h'
    obtain ⟨m, e⟩ := exists_smul_eq (M := G) (embFinTwo h) (embFinTwo h')
    exact ⟨m,
      by rw [← embFinTwo_apply_zero h, ← smul_apply, e, embFinTwo_apply_zero],
      by rw [← embFinTwo_apply_one h, ← smul_apply, e, embFinTwo_apply_one]⟩
  · intro H
    exact {
      exists_smul_eq j j' := by
        obtain ⟨g, h, h'⟩ :=
          H (j.injective.ne_iff.mpr Fin.zero_ne_one) (j'.injective.ne_iff.mpr Fin.zero_ne_one)
        use g
        ext i
        rcases i.eq_zero_or_one with hi | hi <;> simp only [hi, smul_apply, h, h'] }

/-- A 2-pretransitive action is pretransitive -/
@[to_additive]
theorem isPretransitive_of_is_two_pretransitive
    [h2 : IsMultiplyPretransitive G α 2] : IsPretransitive G α where
  exists_smul_eq a b := by
    by_cases h : a = b
    · exact ⟨1, by simp [h]⟩
    · rw [is_two_pretransitive_iff] at h2
      obtain ⟨g, h, _⟩ := h2 h (Ne.symm h)
      exact ⟨g, h⟩

/-- A 2-transitive action is primitive -/
@[to_additive]
theorem isPreprimitive_of_is_two_pretransitive
    (h2 : IsMultiplyPretransitive G α 2) : IsPreprimitive G α := by
  have : IsPretransitive G α := isPretransitive_of_is_two_pretransitive
  apply IsPreprimitive.mk
  intro B hB
  rcases B.subsingleton_or_nontrivial with h | h
  · left
    exact h
  · right
    obtain ⟨a, ha, b, hb, h⟩ := h
    rw [← top_eq_univ, eq_top_iff]
    intro c _
    by_cases h' : a = c
    · rw [← h']; exact ha
    · rw [is_two_pretransitive_iff] at h2
      obtain ⟨g, hga, hgb⟩ := h2 h h'
      rw [MulAction.isBlock_iff_smul_eq_of_mem] at hB
      rw [← hB (g := g) ha (by rw [hga]; exact ha), ← hgb]
      exact smul_mem_smul_set hb

end Two

section Higher

/-- The natural equivariant map from `n ↪ α` to `m ↪ α` given by an embedding
`e : m ↪ n`. -/
@[to_additive]
def embMap {m n : Type*} (e : m ↪ n) : (n ↪ α) →[G]  (m ↪ α) where
  toFun i := e.trans i
  map_smul' _ _ := rfl

theorem _root_.Function.Embedding.giveMeAName'
    {m n : ℕ} (hmn : m ≤ n) (hn : n ≤ ENat.card α) :
    Function.Surjective (fun x : Fin n ↪ α ↦ (Fin.castLEEmb hmn).trans x) := by
  intro x
  classical
  have : Nonempty (Fin (n - m) ↪ ((Set.range x)ᶜ : Set α)) := by
    rcases finite_or_infinite α with hα | hα
    · have : Fintype α := Fintype.ofFinite α
      classical
      apply Function.Embedding.nonempty_of_card_le
      rw [Fintype.card_fin, ← card_eq_fintype_card, Set.Nat.card_coe_set_eq,
        ← add_le_add_iff_left, ncard_add_ncard_compl, ← Set.Nat.card_coe_set_eq,
        Nat.card_range_of_injective x.injective, card_eq_fintype_card,
        Fintype.card_fin, Nat.add_sub_of_le hmn, ← ENat.coe_le_coe]
      exact le_trans hn (by simp)
    · exact ⟨valEmbedding.trans (finite_range x).infinite_compl.to_subtype.natEmbedding⟩
  obtain ⟨y⟩ := this
  let z (i : Fin n) : α := if hi : i < m then x ⟨i, hi⟩ else y ⟨i -m, by
    simp only [not_lt] at hi
    exact Nat.sub_lt_sub_right hi i.prop⟩
  have : Function.Injective z := fun i j h ↦ by
    by_cases hi : i < m
    · by_cases hj : j < m
      · apply Fin.eq_of_val_eq
        simpa [dif_pos hi, dif_pos hj, z] using h
      · simp only [dif_pos hi, dif_neg hj, z] at h
        exfalso
        apply ne_of_mem_of_not_mem (Set.mem_range_self _) _ h
        rw [← Set.mem_compl_iff]
        apply Subtype.coe_prop
    · by_cases hj : j < m
      · simp only [dif_neg hi, dif_pos hj, z] at h
        exfalso
        apply ne_of_mem_of_not_mem (Set.mem_range_self _) _ h.symm
        rw [← Set.mem_compl_iff]
        apply Subtype.coe_prop
      · apply Fin.eq_of_val_eq
        rw [← tsub_left_inj (not_lt.mp hi) (not_lt.mp hj)]
        simpa [dif_neg hi, dif_neg hj, Subtype.coe_inj, y.injective.eq_iff, z] using h
  use ⟨z, this⟩
  ext i
  simp [z, dif_pos i.prop]

theorem _root_.Function.Embedding.giveMeAName
    {m n : ℕ} [Finite α] (hmn : m ≤ n) (hn : n ≤ Nat.card α) :
    Function.Surjective (fun x : Fin n ↪ α ↦ (Fin.castLEEmb hmn).trans x) :=
  giveMeAName' hmn (by rwa [← ENat.coe_le_coe, ← ENat.card_eq_coe_natCard α] at hn)

/-- If `α` has at least n elements, then any n-pretransitive action on `α`
is m-pretransitive for any m ≤ n.

This version authorizes `α` to be infinite and uses `ENat.card`.
For `Finite α`, use `MulAction.isMultiplyPretransitive_of_le` -/
@[to_additive
"If `α` has at least n elements, then any n-pretransitive action on `α`
is m-pretransitive for any m ≤ n.

This version authorizes `α` to be infinite and uses `ENat.card`.
For `Finite α`, use `AddAction.isMultiplyPretransitive_of_le`."]
theorem isMultiplyPretransitive_of_le' {m n : ℕ} [IsMultiplyPretransitive G α n]
    (hmn : m ≤ n) (hα : n ≤ ENat.card α) :
    IsMultiplyPretransitive G α m :=
  IsPretransitive.of_surjective_map (f := embMap (castLEEmb hmn))
    (giveMeAName' hmn hα) inferInstance

/-- An n-pretransitive action is m-pretransitive for any m ≤ n -/
@[to_additive]
theorem isMultiplyPretransitive_of_le {m n : ℕ} [IsMultiplyPretransitive G α n]
    (hmn : m ≤ n) (hα : n ≤ Nat.card α) [Finite α] :
    IsMultiplyPretransitive G α m :=
  IsPretransitive.of_surjective_map (f := embMap (castLEEmb hmn)) (giveMeAName hmn hα) inferInstance

end Higher

end MulAction
