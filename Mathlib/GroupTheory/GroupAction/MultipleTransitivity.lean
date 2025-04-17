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

/-- Merge two disjoint embeddings from `Fin m` and `Fin n` into `α`
  to an embedding from `Fin m + n`. -/
def merge {m n p : ℕ} (h : m + n = p)
    (x : Fin m ↪ α) (y : Fin n ↪ α) (hxy : Disjoint (range x) (range y)) :
    Fin p ↪ α where
  toFun (i : Fin p) : α :=
    if hi : i < m
    then x ⟨i, hi⟩
    else y ⟨i - m, by
      rw [Nat.sub_lt_iff_lt_add (not_lt.mp hi), h]
      exact i.prop⟩
  inj' i j h := by
    by_cases hi : i < m
    · by_cases hj : j < m
      · apply Fin.eq_of_val_eq
        simpa [dif_pos hi, dif_pos hj] using h
      · simp only [dif_pos hi, dif_neg hj] at h
        exfalso
        apply ne_of_mem_of_not_mem (Set.mem_range_self _) _ h
        apply hxy.not_mem_of_mem_right (by simp)
    · by_cases hj : j < m
      · simp only [dif_neg hi, dif_pos hj] at h
        exfalso
        apply ne_of_mem_of_not_mem (Set.mem_range_self _) _ h.symm
        apply hxy.not_mem_of_mem_right (by simp)
      · apply Fin.eq_of_val_eq
        rw [← tsub_left_inj (not_lt.mp hi) (not_lt.mp hj)]
        simpa [dif_neg hi, dif_neg hj, Subtype.coe_inj, y.injective.eq_iff] using h

@[simp]
theorem merge_apply {m n p : ℕ} (h : m + n = p)
    (x : Fin m ↪ α) (y : Fin n ↪ α) (hxy : Disjoint (range x) (range y)) (i : Fin p) :
    Fin.Embedding.merge h x y hxy i =
    if hi : i < m then x ⟨i, hi⟩ else y ⟨i - m, by
      rw [Nat.sub_lt_iff_lt_add (not_lt.mp hi), h]
      exact i.prop⟩ :=
  rfl

/-- Merge two disjoint embeddings from `Fin m` and `Fin n` into `α`
  to an embedding from `Fin m + n`. -/
def merge_compl {m n p : ℕ} (h : m + n = p)
    (x : Fin m ↪ α) (y : Fin n ↪ ↑(range ⇑x)ᶜ) : Fin p ↪ α :=
  Fin.Embedding.merge h x (y.trans (subtype _)) (by
    rw [Set.disjoint_right]
    rintro _ ⟨i, rfl⟩
    simp only [trans_apply, subtype_apply, ← mem_compl_iff]
    exact Subtype.coe_prop (y i))

/-- Extend a fin embedding by another element -/
def append {n : ℕ} (x : Fin n ↪ α) {a : α} (ha : a ∉ range ⇑x) : Fin n.succ ↪ α :=
  Fin.Embedding.merge_compl (Nat.succ_eq_add_one n).symm x
    { toFun _ := ⟨a, ha⟩, inj' _ _ _ := Subsingleton.elim _ _ }

theorem append_apply {n : ℕ} {x : Fin n ↪ α}
    {a : α} {ha : a ∉ range ⇑x} {i : Fin n.succ} :
    append x ha i = if hi : i.val < n then  x ⟨i, hi⟩ else a :=
  rfl

theorem append_apply_of_lt {n : ℕ} {x : Fin n ↪ α}
    {a : α} {ha : a ∉ range ⇑x} {i : Fin n.succ} (hi : i.val < n) :
    Fin.Embedding.append x ha i = x ⟨i, hi⟩ := by
  simp_all [append_apply]

theorem append_apply_last {n : ℕ} (x : Fin n ↪ α) {a : α} (ha : a ∉ range ⇑x) :
    Fin.Embedding.append x ha (Fin.last n) = a := by
  simp [append_apply]

theorem restrictSurjective_of_le_ENatCard
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
  use Fin.Embedding.merge_compl (add_sub_of_le hmn) x y
  ext i
  simp [Fin.Embedding.merge_compl, Fin.Embedding.merge, dif_pos i.prop]

theorem restrictSurjective_of_le_natCard
    {m n : ℕ} [Finite α] (hmn : m ≤ n) (hn : n ≤ Nat.card α) :
    Function.Surjective (fun x : Fin n ↪ α ↦ (Fin.castLEEmb hmn).trans x) :=
  Fin.Embedding.restrictSurjective_of_le_ENatCard
    hmn (by rwa [← ENat.coe_le_coe, ← ENat.card_eq_coe_natCard α] at hn)

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

/-- The natural equivariant map from `n ↪ α` to `m ↪ α` given by an embedding
`e : m ↪ n`. -/
@[to_additive
"The natural equivariant map from `n ↪ α` to `m ↪ α` given by an embedding `e : m ↪ n`."]
def embMap {m n : Type*} (e : m ↪ n) : (n ↪ α) →[G]  (m ↪ α) where
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
    IsMultiplyPretransitive G α m :=
  IsPretransitive.of_surjective_map (f := embMap (castLEEmb hmn))
    (Fin.Embedding.restrictSurjective_of_le_ENatCard hmn hα) inferInstance

/-- An n-pretransitive action is m-pretransitive for any m ≤ n -/
@[to_additive]
theorem isMultiplyPretransitive_of_le {m n : ℕ} [IsMultiplyPretransitive G α n]
    (hmn : m ≤ n) (hα : n ≤ Nat.card α) [Finite α] :
    IsMultiplyPretransitive G α m :=
  IsPretransitive.of_surjective_map (f := embMap (castLEEmb hmn))
    (Fin.Embedding.restrictSurjective_of_le_natCard hmn hα) inferInstance

end Higher

end MulAction

namespace Equiv.Perm

variable {α : Type*} [Fintype α]

-- Move?
/-- The permutation group of `α` acts transitively on `α`. -/
instance : IsPretransitive (Perm α) α where
  exists_smul_eq x y := by
    classical
    use Equiv.swap x y
    simp only [Equiv.Perm.smul_def, Equiv.swap_apply_left x y]

/-- The permutation group of `α` acts 2-pretransitively on `α`. -/
theorem is_two_pretransitive (α : Type*) :
    IsMultiplyPretransitive (Perm α) α 2 := by
  rw [is_two_pretransitive_iff]
  classical
  intro a b c d hab hcd
  let k := Equiv.swap a c
  have hc : c = k • a := by simp [k]
  simp only [show c = k • a from by simp [k]]
  suffices ∃ g, g • a = a ∧ g • b = k⁻¹ • d by
    obtain ⟨g, h1, h2⟩ := this
    use k * g
    simp [mul_smul, h1, h2]
  use swap b (k⁻¹ • d)
  refine ⟨?_, by simp⟩
  apply Equiv.swap_apply_of_ne_of_ne hab
  intro ha'
  apply hcd
  have hd : d = k • a := by simp [ha']
  rw [hc, hd]

/-- The action of the permutation group of `α` on `α` is preprimitive -/
instance {α : Type*} : IsPreprimitive (Equiv.Perm α) α := by
  cases subsingleton_or_nontrivial α
  · exact IsPreprimitive.of_subsingleton
  · exact isPreprimitive_of_is_two_pretransitive (is_two_pretransitive α)

-- TODO : generalize when `α` is infinite. This simplifies a proof above
variable (α) in
/-- The permutation group of a finite type `α` acts `n`-pretransitively on `a`, for all `n`,
for a trivial reason when `Nat.card α < n`. -/
theorem isMultiplyPretransitive (n : ℕ) : IsMultiplyPretransitive (Perm  α) α n := by
  by_cases hα : n ≤ Nat.card α
  · suffices IsMultiplyPretransitive (Perm α) α (Nat.card α) by
      apply isMultiplyPretransitive_of_le hα (le_rfl)
    exact {
      exists_smul_eq x y := by
        suffices h : Function.Bijective x ∧ Function.Bijective y by
          use (Equiv.ofBijective x h.1).symm.trans (Equiv.ofBijective y h.2)
          ext; simp
        constructor
        all_goals
          simp only [Fintype.bijective_iff_injective_and_card, card_eq_fintype_card,
            Fintype.card_fin, and_true, EmbeddingLike.injective] }
  · suffices IsEmpty (Fin n ↪ α) by
      infer_instance
    exact {
      false x := by
        apply hα (le_of_eq_of_le _ (Finite.card_le_of_embedding x))
        simp only [card_eq_fintype_card, Fintype.card_fin] }

-- This is optimal, `AlternatingGroup α` is `Nat.card α - 2`-pretransitive.
/-- A subgroup of `Perm α` is `⊤` if(f) it is `(Nat.card α - 1)`-pretransitive. -/
theorem eq_top_if_isMultiplyPretransitive {G : Subgroup (Equiv.Perm α)}
    (hmt : IsMultiplyPretransitive G α (Nat.card α - 1)) : G = ⊤ := by
  simp only [Nat.card_eq_fintype_card] at hmt
  let j : Fin (Fintype.card α - 1) ↪ Fin (Fintype.card α) :=
    (Fin.castLEEmb ((Fintype.card α).sub_le 1))
  rw [eq_top_iff]; intro k _
  let x : Fin (Fintype.card α) ↪ α :=
    (Fintype.equivFinOfCardEq rfl).symm.toEmbedding
  let x' := j.trans x
  obtain ⟨g, hg'⟩ := exists_smul_eq G x' (k • x')
  suffices k = g by rw [this]; exact SetLike.coe_mem g
  have hx : ∀ x : Fin (Fintype.card α) ↪ α, Function.Surjective x.toFun := by
    intro x
    apply Function.Bijective.surjective
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨EmbeddingLike.injective x, Fintype.card_fin (Fintype.card α)⟩
  have hgk' : ∀ (i : Fin (Fintype.card α)) (_ : i.val < Fintype.card α - 1),
    (g • x) i = (k • x) i := by
    intro i hi
    exact Function.Embedding.ext_iff.mp hg' ⟨i.val, hi⟩
  have hgk : ∀ i : Fin (Fintype.card α), (g • x) i = (k • x) i := by
    intro i
    rcases lt_or_eq_of_le (le_sub_one_of_lt i.prop) with hi | hi
    · exact hgk' i hi
    · obtain ⟨j, hxj : (k • x) j = (g • x) i⟩ := hx (k • x) ((g • x) i)
      rcases lt_or_eq_of_le (le_sub_one_of_lt j.prop) with hj | hj
      · exfalso
        suffices i = j by rw [← this, ← hi] at hj ; refine lt_irrefl _ hj
        apply EmbeddingLike.injective (g • x)
        rw [hgk' j hj]; rw [hxj]
      · rw [← hxj]
        apply congr_arg
        rw [Fin.ext_iff, hi, hj]
  apply Equiv.Perm.ext; intro a
  obtain ⟨i, rfl⟩ := (hx x) a
  let zi := hgk i
  simp only [Function.Embedding.smul_apply, Equiv.Perm.smul_def] at zi
  simp only [Function.Embedding.toFun_eq_coe]
  rw [← zi]
  rfl

end Equiv.Perm
