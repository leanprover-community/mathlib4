/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.GroupTheory.GroupAction.Embedding
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.GroupAction.Transitive
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.GroupAction.FixingSubgroup

import Mathlib.Data.Fin.Embedding

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

## Results for permutation groups

* The permutation group is pretransitive, is multiply pretransitive,
and is preprimitive (for its natural action)

* `Equiv.Perm.eq_top_if_isMultiplyPretransitive`:
a subgroup of `Equiv.Perm α` which is `Nat.card α - 1` pretransitive
is equal to `⊤`.

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

open Equiv MulAction

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
theorem eq_top_of_isMultiplyPretransitive {G : Subgroup (Equiv.Perm α)}
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
        suffices i = j by rw [← this, ← hi] at hj; refine lt_irrefl _ hj
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

namespace IsMultiplyPretransitive

variable (α : Type*) [Fintype α]

/-- The `alternatingGroup` on α is (Fintype.card α - 2)-pretransitive -/
theorem alternatingGroup_of_sub_two [DecidableEq α] :
    IsMultiplyPretransitive (alternatingGroup α) α (Nat.card α - 2) := by
  rcases lt_or_ge (Nat.card α) 2 with h2 | h2
  · rw [Nat.sub_eq_zero_of_le (le_of_lt h2)]
    apply is_zero_pretransitive
  have h2' : Nat.card α - 2 ≤ Nat.card α := sub_le (Nat.card α) 2
  exact {
    exists_smul_eq x y := by
      have : IsMultiplyPretransitive (Equiv.Perm α) α (Nat.card α) :=
        Equiv.Perm.isMultiplyPretransitive α (Nat.card α)
      obtain ⟨x' : Fin (Nat.card α) ↪ α, hx'⟩ :=
        Fin.Embedding.restrictSurjective_of_le_natCard h2' (le_refl _) x
      obtain ⟨y' : Fin (Nat.card α) ↪ α, hy'⟩ :=
        Fin.Embedding.restrictSurjective_of_le_natCard h2' (le_refl _) y
      obtain ⟨g , hg⟩ := exists_smul_eq (Equiv.Perm α) x' y'
      rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h | h
      · use ⟨g, h⟩
        ext i
        simp only [← hx', subgroup_smul_def, smul_apply, trans_apply, castLEEmb_apply, ← hy']
        simp only [← smul_apply, hg]
      · let u : Fin (Nat.card α) :=
          ⟨Nat.card α - 1, by exact sub_one_lt_of_lt h2⟩
        let v : Fin (Nat.card α) :=
          ⟨Nat.card α - 2, Nat.sub_lt (zero_lt_of_lt h2) (Nat.zero_lt_two)⟩
        refine ⟨⟨g * (Equiv.swap (x' u) (x' v)), ?_⟩, ?_⟩
        · suffices u ≠ v by
            simp [h, this]
          exact ne_of_val_ne (Nat.ne_of_gt (sub_succ_lt_self (Nat.card α) 1 h2))
        · ext i
          suffices (Equiv.swap (x' u) (x' v)) • (x' (castLE h2' i)) = x' (castLE h2' i) by
            simp only [← hx', Subgroup.mk_smul, smul_apply, trans_apply, castLEEmb_apply,
              Equiv.Perm.coe_mul, Function.comp_apply, this, ← hy', mul_smul, this, hg]
            simp only [← smul_apply, hg]
          have hiv : (i : ℕ) < v := (lt_of_lt_of_le i.prop (le_of_eq rfl))
          have hiu : (i : ℕ) < u := by
            apply lt_trans hiv
            simp only [u, v, ← one_add_one_eq_two, ← Nat.sub_sub]
            apply Nat.sub_lt_self Nat.zero_lt_one (le_sub_one_of_lt h2)
          apply Equiv.swap_apply_of_ne_of_ne <;>
            simp [ne_eq, EmbeddingLike.apply_eq_iff_eq, ← val_inj,
              coe_castLE, Nat.ne_of_lt hiu, Nat.ne_of_lt hiv] }


variable {α}

/-- A subgroup of `Equiv.Perm α` which is (Fintype.card α - 2)-pretransitive
  contains `alternatingGroup α` -/
theorem alternatingGroup_le [DecidableEq α] (G : Subgroup (Equiv.Perm α))
    (hmt : IsMultiplyPretransitive G α (Nat.card α - 2)) :
    alternatingGroup α ≤ G := by
  classical
  rcases Nat.lt_or_ge (Nat.card α) 2 with hα1 | hα
  · -- Nat.card α  < 2
    rw [Nat.lt_succ_iff] at hα1
    suffices alternatingGroup α = ⊥ by
      rw [this]; exact bot_le
    refine alternatingGroup.eq_bot_of_card_le_two ?_
    rw [← Nat.card_eq_fintype_card]
    exact le_succ_of_le hα1
  apply Equiv.Perm.alternatingGroup_le_of_index_le_two

  -- rw [Fintype.card_equiv (Equiv.refl _)]
  obtain ⟨s, _, hs⟩ :=
    Set.exists_subset_card_eq (s := (Set.univ : Set α)) (n := Nat.card α - 2)
      (by rw [Set.ncard_univ]; exact sub_le (Nat.card α) 2)
  rw [← hs] at hmt

  rw [← hmt.index_of_fixingSubgroup G α s, hs, Nat.sub_sub_self hα,
    Nat.factorial_two, mul_comm]
  apply Nat.mul_le_mul_left
  have : Nonempty G := One.instNonempty
  apply Nat.le_of_dvd (Fintype.card_pos)
  rw [← Nat.card_eq_fintype_card]
  apply Subgroup.index_dvd_card

/-- The alternating group on 3 letters or more acts transitively -/
theorem alternatingGroup.isPretransitive [DecidableEq α] (h : 3 ≤ Fintype.card α) :
    IsPretransitive (alternatingGroup α) α := by
  rw [isPretransitive_iff_is_one_pretransitive]
  apply isMultiplyPretransitive_of_higher
  apply IsMultiplyPretransitive.alternatingGroup_of_sub_two
  apply le_trans _ (Nat.sub_le_sub_right h 2)
  norm_num
  simp only [ge_iff_le, ENat.card_eq_coe_fintype_card, ENat.coe_le_coe,
    tsub_le_iff_right, le_add_iff_nonneg_right]
  norm_num

/- This lemma proves the trivial blocks property for the alternating group.
  This holds even when `Fintype.card α ≤ 2`
  — then the action is not preprimitive  because it is not pretransitive -/
theorem alternatingGroup.has_trivial_blocks [DecidableEq α]
    (B : Set α) (hB : IsBlock (alternatingGroup α) B) :
    IsTrivialBlock B := by
  classical
  cases' le_or_lt (Fintype.card α) 2 with h2 h2
  · exact IsTrivialBlock.of_card_le_2 h2 B
  cases' le_or_lt (Fintype.card α) 3 with h3 h4
  · have h3' : Fintype.card α = 3 := le_antisymm h3 h2
    cases' le_or_lt (Fintype.card B) 1 with h1 h2
    · apply Or.intro_left
      rw [← Set.subsingleton_coe, ← Fintype.card_le_one_iff_subsingleton]
      exact h1
    · apply Or.intro_right
      rw [Fintype.one_lt_card_iff] at h2
      -- using h2, get a ≠ b in B
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := h2
      simp only [Ne, Subtype.mk_eq_mk] at hab
      -- using h3', get c ≠ a, b
      have : ∃ c : α, c ∉ ({a, b}  : Finset α) := by
        by_contra h
        push_neg at h
        have : ({a, b} : Finset α) = Finset.univ := by
          ext c
          constructor
          · intro _; exact Finset.mem_univ c
          · intro _; exact h c
        rw [lt_iff_not_ge] at h2 ; apply h2; rw [ge_iff_le]
        rw [← Finset.card_eq_iff_eq_univ] at this
        rw [← this]
        rw [Finset.card_pair hab]
      obtain ⟨c, hc⟩ := this
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
      suffices ({a, b, c} : Finset α) = Finset.univ by
        rw [eq_top_iff]
        rw [Set.top_eq_univ, ← Finset.coe_univ, ← this]
        intro x hx
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hx
        cases' hx with hxa hx
        rw [hxa]; exact ha
        cases' hx with hxb hxc
        rw [hxb]; exact hb
        rw [hxc]
        -- get a three_cycle g = c[a,b,c]
        let g : alternatingGroup α :=
          ⟨Equiv.swap a b * Equiv.swap c b,-- cycle [a,b,c]
          by  rw [Equiv.Perm.mem_alternatingGroup]
              rw [Equiv.Perm.sign_mul]
              rw [Equiv.Perm.sign_swap hab]
              rw [Equiv.Perm.sign_swap hc.right]
              simp only [Int.units_mul_self]⟩
        suffices g • B = B by
          rw [← this]
          use b
          apply And.intro hb
          change (Equiv.swap a b * Equiv.swap c b) • b = c
          simp only [Equiv.Perm.smul_def, Equiv.Perm.coe_mul, Function.comp_apply]
          rw [Equiv.swap_apply_right]
          rw [Equiv.swap_apply_of_ne_of_ne hc.left hc.right]
        -- g • B = B
        apply hB.def_mem ha
        change (Equiv.swap a b * Equiv.swap c b) • a ∈ B
        simp only [Equiv.Perm.smul_def, Equiv.Perm.coe_mul, Function.comp_apply]
        rw [Equiv.swap_apply_of_ne_of_ne (ne_comm.mp hc.left) hab]
        rw [Equiv.swap_apply_left]
        exact hb
      -- {a, b, c} = Finset.univ
      rw [← Finset.card_eq_iff_eq_univ, h3']
      rw [Finset.card_insert_of_not_mem]
      rw [Finset.card_pair (ne_comm.mp hc.right)]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      apply And.intro hab
      exact ne_comm.mp hc.left
  -- IsTrivialBlock hB
  apply IsPreprimitive.has_trivial_blocks ?_ hB
  apply IsMultiplyPretransitive.isPreprimitive_of_two
  apply isMultiplyPretransitive_of_higher
  apply IsMultiplyPretransitive.alternatingGroup_of_sub_two
  apply le_trans _ (Nat.sub_le_sub_right h4 2); norm_num
  simp only [ENat.card_eq_coe_fintype_card, cast_le, tsub_le_iff_right, le_add_iff_nonneg_right,
    _root_.zero_le]

/-- The alternating group on 3 letters or more acts primitively -/
theorem AlternatingGroup.isPreprimitive [DecidableEq α] (h : 3 ≤ Fintype.card α) :
    IsPreprimitive (alternatingGroup α) α := by
  have := alternatingGroup.isPretransitive h
  apply IsPreprimitive.mk
  apply alternatingGroup.has_trivial_blocks


