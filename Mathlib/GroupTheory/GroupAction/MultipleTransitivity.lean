/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.GroupTheory.GroupAction.Embedding
import Mathlib.GroupTheory.GroupAction.Primitive

import Mathlib.GroupTheory.GroupAction.SubMulAction.ofStabilizer
import Mathlib.Data.Finite.Card
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Finite

/-! # Multiple transitivity

* `MulAction.IsMultiplyPretransitive`:
  A multiplicative action of a group `G` on a type `α` is n-transitive
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

namespace Fin.Embedding

variable {α : Type*}

theorem exists_embedding_disjoint_range_of_add_le_ENat_card
    {s : Set α} [Finite s] {n : ℕ} (hs : s.ncard + n ≤ ENat.card α) :
    ∃ y : Fin n ↪ α, Disjoint s (range y) := by
  suffices Nonempty (Fin n ↪ (sᶜ : Set α)) by
    obtain ⟨y⟩ := this
    use y.trans (subtype _)
    rw [Set.disjoint_right]
    rintro _ ⟨i, rfl⟩
    simp only [trans_apply, subtype_apply, ← mem_compl_iff]
    exact Subtype.coe_prop (y i)
  rcases finite_or_infinite α with hα | hα
  · have _ : Fintype α := Fintype.ofFinite α
    classical
    apply Function.Embedding.nonempty_of_card_le
    rwa [Fintype.card_fin, ← add_le_add_iff_left s.ncard,
      ← Nat.card_eq_fintype_card, Set.Nat.card_coe_set_eq,
        Set.ncard_add_ncard_compl, ← ENat.coe_le_coe,
        ← ENat.card_eq_coe_natCard, ENat.coe_add]
  · exact ⟨valEmbedding.trans s.toFinite.infinite_compl.to_subtype.natEmbedding⟩

theorem restrictSurjective_of_add_le_ENatCard
    {m n : ℕ} (hn : m + n ≤ ENat.card α) :
    Function.Surjective (fun (x : Fin (m + n) ↪ α) ↦ (Fin.castAddEmb n).trans x) := by
  intro x
  obtain ⟨y : Fin n ↪ α, hxy⟩ :=
    exists_embedding_disjoint_range_of_add_le_ENat_card (s := range x)
      (by simpa [← Set.Nat.card_coe_set_eq, Nat.card_range_of_injective x.injective])
  use append hxy
  ext i
  simp [trans_apply, coe_castAddEmb, append]

theorem restrictSurjective_of_add_le_natCard
    {m n : ℕ} [Finite α] (hn : m + n ≤ Nat.card α) :
    Function.Surjective (fun x : Fin (m + n) ↪ α ↦ (Fin.castAddEmb n).trans x) := by
  apply Fin.Embedding.restrictSurjective_of_add_le_ENatCard
  rwa [← ENat.coe_add, ENat.card_eq_coe_natCard, ENat.coe_le_coe]

end Fin.Embedding

section Functoriality

variable {G α : Type*} [Group G] [MulAction G α]
variable {H β : Type*} [Group H] [MulAction H β]
variable {σ : G → H} {f : α →ₑ[σ] β} {ι : Type*}

/-- An injective equivariant map `α →ₑ[σ] β` induces
an equivariant map on embedding types (ι ↪ α) → (ι ↪ β) -/
@[to_additive "An injective equivariant map `α →ₑ[σ] β` induces
an equivariant map on embedding types (ι ↪ α) → (ι ↪ β)"]
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

/-- The equivalence `one ↪ α` with `α`, for `Unique one`. -/
def _root_.Function.Embedding.oneEmbeddingEquiv {one : Type*} [Unique one] : (one ↪ α) ≃ α where
  toFun f := f default
  invFun a := {
    toFun := fun _ ↦ a
    inj' x y h := by simp [Unique.uniq inferInstance] }
  left_inv f := by ext; simp [Unique.uniq]
  right_inv a := rfl

/-- For `Unique one`, the equivariant map from `one ↪ α` to `α` -/
@[to_additive "For `Unique one`, the equivariant map from `one ↪ α` to `α`"]
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

/-- Two distinct elements of `α` give an embedding `Fin 2 ↪ α` -/
def _root_.Function.Embedding.embFinTwo {a b: α} (h : a ≠ b) : Fin 2 ↪ α where
  toFun := ![a, b]
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

variable (G α) in
/-- The natural equivariant map from `n ↪ α` to `m ↪ α` given by an embedding
`e : m ↪ n`. -/
@[to_additive
"The natural equivariant map from `n ↪ α` to `m ↪ α` given by an embedding `e : m ↪ n`."]
def _root_.MulActionHom.embMap {m n : Type*} (e : m ↪ n) :
    (n ↪ α) →[G]  (m ↪ α) where
  toFun i := e.trans i
  map_smul' _ _ := rfl

/-- If `α` has at least n elements, then any n-pretransitive action on `α`
is m-pretransitive for any m ≤ n.

This version allows `α` to be infinite and uses `ENat.card`.
For `Finite α`, use `MulAction.isMultiplyPretransitive_of_le` -/
@[to_additive
"If `α` has at least n elements, then any n-pretransitive action on `α`
is m-pretransitive for any m ≤ n.

This version allows `α` to be infinite and uses `ENat.card`.
For `Finite α`, use `AddAction.isMultiplyPretransitive_of_le`."]
theorem isMultiplyPretransitive_of_le' {m n : ℕ} [IsMultiplyPretransitive G α n]
    (hmn : m ≤ n) (hα : n ≤ ENat.card α) :
    IsMultiplyPretransitive G α m := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact IsPretransitive.of_surjective_map
    (f := embMap G α (castAddEmb p))
    (Fin.Embedding.restrictSurjective_of_add_le_ENatCard hα) inferInstance

/-- If α has at least n elements, then an n-pretransitive action
is m-pretransitive for any m ≤ n.

For an infinite `α`, use `MulAction.isMultiplyPretransitive_of_le'`. -/
@[to_additive
"If α has at least n elements, then an n-pretransitive action
is m-pretransitive for any m ≤ n.

For an infinite `α`, use `MulAction.isMultiplyPretransitive_of_le'`."]
theorem isMultiplyPretransitive_of_le {m n : ℕ} [IsMultiplyPretransitive G α n]
    (hmn : m ≤ n) (hα : n ≤ Nat.card α) [Finite α] :
    IsMultiplyPretransitive G α m := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact IsPretransitive.of_surjective_map (f := embMap G α (castAddEmb p))
    (Fin.Embedding.restrictSurjective_of_add_le_natCard hα) inferInstance

end Higher

end MulAction

section Stabilizer

variable {G α : Type*} [Group G] [MulAction G α]

namespace SubMulAction.ofStabilizer

open scoped BigOperators Pointwise Cardinal

open MulAction Function.Embedding

@[to_additive]
theorem isMultiplyPretransitive_iff_of_conj
    {n : ℕ} {a b : α} {g : G} (hg : b = g • a) :
    IsMultiplyPretransitive (stabilizer G a) (ofStabilizer G a) n ↔
      IsMultiplyPretransitive (stabilizer G b) (ofStabilizer G b) n :=
  IsPretransitive.of_embedding_congr (MulEquiv.surjective _) (ofStabilizer.conjMap_bijective hg)

@[to_additive]
theorem isMultiplyPretransitive_iff [IsPretransitive G α] {n : ℕ} {a b : α} :
    IsMultiplyPretransitive (stabilizer G a) (ofStabilizer G a) n ↔
      IsMultiplyPretransitive (stabilizer G b) (ofStabilizer G b) n :=
  let ⟨_, hg⟩ := exists_smul_eq G a b
  isMultiplyPretransitive_iff_of_conj hg.symm

/-- Multiple transitivity of a pretransitive action
  is equivalent to one less transitivity of stabilizer of a point
  (Wielandt, th. 9.1, 1st part) -/
@[to_additive
  "Multiple transitivity of a pretransitive action
  is equivalent to one less transitivity of stabilizer of a point
  (Wielandt, th. 9.1, 1st part)"]
theorem isMultiplyPretransitive [IsPretransitive G α] {n : ℕ} {a : α} :
    IsMultiplyPretransitive G α n.succ ↔
      IsMultiplyPretransitive (stabilizer G a) (SubMulAction.ofStabilizer G a) n := by
  constructor
  · exact fun hn ↦ {
      exists_smul_eq x y := by
        obtain ⟨g, hgxy⟩ := exists_smul_eq G (snoc x) (snoc y)
        have hg : g ∈ stabilizer G a := by
          rw [mem_stabilizer_iff]
          rw [DFunLike.ext_iff] at hgxy
          convert hgxy (last n) <;> simp [smul_apply, snoc_last]
        use ⟨g, hg⟩
        ext i
        simp only [smul_apply, SubMulAction.val_smul_of_tower, subgroup_smul_def]
        rw [← snoc_castSucc x, ← smul_apply, hgxy, snoc_castSucc] }
  · exact fun hn ↦ {
      exists_smul_eq x y := by
        -- gx • x = x1 :: a
        obtain ⟨gx, x1, hgx⟩ := exists_smul_of_last_eq G a x
        -- gy • y = y1 :: a
        obtain ⟨gy, y1, hgy⟩ := exists_smul_of_last_eq G a y
        -- g • x1 = y1,
        obtain ⟨g, hg⟩ := hn.exists_smul_eq x1 y1
        use gy⁻¹ * g * gx
        ext i
        simp only [mul_smul, smul_apply, inv_smul_eq_iff]
        simp only [← smul_apply _ _ i, hgy, hgx]
        simp only [smul_apply]
        rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | ⟨rfl⟩
        · -- rw [Function.Embedding.ext_iff] at hgx hgy hg
          simp [snoc_castSucc, ← hg, SetLike.val_smul, subgroup_smul_def]
        · simp only [snoc_last, ← hg, subgroup_smul_def]
          exact g.prop }

end SubMulAction.ofStabilizer

end Stabilizer
