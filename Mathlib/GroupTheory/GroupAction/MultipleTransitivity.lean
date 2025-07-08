/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup
import Mathlib.SetTheory.Cardinal.Embedding
import Mathlib.SetTheory.Cardinal.Arithmetic

/-! # Multiple transitivity

* `MulAction.IsMultiplyPretransitive`:
  A multiplicative action of a group `G` on a type `α` is n-transitive
  if the action of `G` on `Fin n ↪ α` is pretransitive.

* `MulAction.is_zero_pretransitive` : any action is 0-pretransitive

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

variable (ι) in
/-- An injective equivariant map `α →ₑ[σ] β` induces
an equivariant map on embedding types `(ι ↪ α) → (ι ↪ β)`. -/
@[to_additive "An injective equivariant map `α →ₑ[σ] β` induces
an equivariant map on embedding types `(ι ↪ α) → (ι ↪ β)`."]
def Function.Injective.mulActionHom_embedding (hf : Function.Injective f) :
    (ι ↪ α) →ₑ[σ] (ι ↪ β) where
  toFun x := ⟨f.toFun ∘ x.toFun, hf.comp x.inj'⟩
  map_smul' m x := by ext; simp [f.map_smul']

@[to_additive (attr := simp)]
theorem Function.Injective.mulActionHom_embedding_apply
    (hf : Function.Injective f) {x : ι ↪ α} {i : ι} :
    hf.mulActionHom_embedding ι x i = f (x i) := rfl

@[to_additive]
theorem Function.Injective.mulActionHom_embedding_isInjective
    (hf : Function.Injective f) :
    Function.Injective (hf.mulActionHom_embedding ι) := by
  intro _ _ hxy
  ext
  apply hf
  simp only [← hf.mulActionHom_embedding_apply, hxy]

variable (hf' : Function.Bijective f)

@[to_additive]
theorem Function.Bijective.mulActionHom_embedding_isBijective (hf : Function.Bijective f) :
    Function.Bijective (hf.injective.mulActionHom_embedding ι) := by
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

variable {G α : Type*} [Group G] [MulAction G α]

variable (G α) in
/-- An action of a group on a type `α` is `n`-pretransitive
if the associated action on `Fin n ↪ α` is pretransitive. -/
@[to_additive "An additive action of an additive group on a type `α`
is `n`-pretransitive if the associated action on `Fin n ↪ α` is pretransitive."]
abbrev IsMultiplyPretransitive (n : ℕ) := IsPretransitive G (Fin n ↪ α)

@[to_additive]
theorem isMultiplyPretransitive_iff {n : ℕ} :
    IsMultiplyPretransitive G α n ↔ ∀ x y : Fin n ↪ α, ∃ g : G, g • x = y :=
  isPretransitive_iff _ _

variable {H β : Type*} [Group H] [MulAction H β] {σ : G → H}
  {f : α →ₑ[σ] β} (hf : Function.Injective f)

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
    simp [← aux_apply, ← hg, MulActionHom.map_smul']

@[to_additive]
theorem IsPretransitive.of_embedding_congr {n : Type*}
    (hσ : Function.Surjective σ) (hf : Function.Bijective f) :
    IsPretransitive G (n ↪ α) ↔ IsPretransitive H (n ↪ β) :=
  isPretransitive_congr hσ hf.mulActionHom_embedding_isBijective

section Zero

/-- Any action is 0-pretransitive. -/
@[to_additive]
theorem is_zero_pretransitive {n : Type*} [IsEmpty n] :
    IsPretransitive G (n ↪ α) := inferInstance

/-- Any action is 0-pretransitive. -/
@[to_additive]
theorem is_zero_pretransitive' :
    IsMultiplyPretransitive G α 0 := inferInstance

end Zero

section One

variable {one : Type*} [Unique one]

/-- For `Unique one`, the equivariant map from `one ↪ α` to `α`. -/
@[to_additive "For `Unique one`, the equivariant map from `one ↪ α` to `α`"]
def _root_.MulActionHom.oneEmbeddingMap :
    (one ↪ α) →[G] α := {
  oneEmbeddingEquiv with
  map_smul' _ _ := rfl }

@[to_additive]
theorem _root_.MulActionHom.oneEmbeddingMap_bijective :
    Function.Bijective (oneEmbeddingMap (one := one) (G := G) (α := α)) :=
  oneEmbeddingEquiv.bijective

/-- An action is `1`-pretransitive iff it is pretransitive. -/
@[to_additive "An additive action is `1`-pretransitive iff it is pretransitive."]
theorem oneEmbedding_isPretransitive_iff :
    IsPretransitive G (one ↪ α) ↔ IsPretransitive G α :=
  isPretransitive_congr Function.surjective_id oneEmbeddingMap_bijective

/-- An action is `1`-pretransitive iff it is pretransitive. -/
@[to_additive "An additive action is `1`-pretransitive iff it is pretransitive."]
theorem is_one_pretransitive_iff :
    IsMultiplyPretransitive G α 1 ↔ IsPretransitive G α :=
  oneEmbedding_isPretransitive_iff

end One

section Two

/-- An action is `2`-pretransitive iff
it can move any two distinct elements to any two distinct elements. -/
@[to_additive "An additive action is `2`-pretransitive iff
it can move any two distinct elements to any two distinct elements."]
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
    constructor
    intro j j'
    obtain ⟨g, h, h'⟩ :=
      H (j.injective.ne_iff.mpr Fin.zero_ne_one) (j'.injective.ne_iff.mpr Fin.zero_ne_one)
    use g
    ext i
    by_cases hi : i = 0
    · simp [hi, h]
    · simp [eq_one_of_ne_zero i hi, h']

/-- A `2`-pretransitive action is pretransitive. -/
@[to_additive "A `2`-pretransitive additive action is pretransitive."]
theorem isPretransitive_of_is_two_pretransitive
    [h2 : IsMultiplyPretransitive G α 2] : IsPretransitive G α where
  exists_smul_eq a b := by
    by_cases h : a = b
    · exact ⟨1, by simp [h]⟩
    · rw [is_two_pretransitive_iff] at h2
      obtain ⟨g, h, _⟩ := h2 h (Ne.symm h)
      exact ⟨g, h⟩

/-- A `2`-transitive action is primitive. -/
@[to_additive "A `2`-transitive additive action is primitive."]
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

/-- If `α` has at least `n` elements, then any `n`-pretransitive action on `α`
is `m`-pretransitive for any `m ≤ n`.

This version allows `α` to be infinite and uses `ENat.card`.
For `Finite α`, use `MulAction.isMultiplyPretransitive_of_le` -/
@[to_additive
"If `α` has at least `n` elements, then any `n`-pretransitive action on `α`
is `n`-pretransitive for any `m ≤ n`.

This version allows `α` to be infinite and uses `ENat.card`.
For `Finite α`, use `AddAction.isMultiplyPretransitive_of_le`."]
theorem isMultiplyPretransitive_of_le' {m n : ℕ} [IsMultiplyPretransitive G α n]
    (hmn : m ≤ n) (hα : n ≤ ENat.card α) :
    IsMultiplyPretransitive G α m := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact IsPretransitive.of_surjective_map
    (f := embMap G α (castAddEmb p))
    (Fin.Embedding.restrictSurjective_of_add_le_ENatCard hα) inferInstance

/-- If `α` has at least `n` elements, then an `n`-pretransitive action
is `m`-pretransitive for any `m ≤ n`.

For an infinite `α`, use `MulAction.isMultiplyPretransitive_of_le'`. -/
@[to_additive
"If `α` has at least `n` elements, then an `n`-pretransitive action
is `m`-pretransitive for any `m ≤ n`.

For an infinite `α`, use `MulAction.isMultiplyPretransitive_of_le'`."]
theorem isMultiplyPretransitive_of_le {m n : ℕ} [IsMultiplyPretransitive G α n]
    (hmn : m ≤ n) (hα : n ≤ Nat.card α) [Finite α] :
    IsMultiplyPretransitive G α m := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact IsPretransitive.of_surjective_map (f := embMap G α (castAddEmb p))
    (Fin.Embedding.restrictSurjective_of_add_le_natCard hα) inferInstance

end Higher

end MulAction

namespace Equiv.Perm

variable {α : Type*}

variable (α) in
/-- The permutation group `Equiv.Perm α` acts `n`-pretransitively on `α` for all `n`. -/
theorem isMultiplyPretransitive (n : ℕ) :
    IsMultiplyPretransitive (Perm  α) α n := by
  rw [isMultiplyPretransitive_iff]
  classical
  intro x y
  have (x : Fin n ↪ α) : Cardinal.mk (range x) = n := by
    simp [Finset.card_image_of_injective, PLift.down_injective]
  have hxy : Cardinal.mk ((range x)ᶜ : Set α) = Cardinal.mk ((range y)ᶜ : Set α) := by
    rw [← Cardinal.add_nat_inj n]
    nth_rewrite 1 [← this x]
    rw [← this y]
    simp only [add_comm, Cardinal.mk_sum_compl]
  rw [Cardinal.eq] at hxy
  obtain ⟨φ⟩ := hxy
  let φ' : α → α := Function.extend Subtype.val (fun a ↦ ↑(φ a)) id
  set ψ : α → α := Function.extend x y φ'
  have : Function.Bijective ψ := by
    constructor
    · intro a b hab
      by_cases ha : a ∈ range x
      · obtain ⟨i, rfl⟩ := ha
        by_cases hb : b ∈ range x
        · obtain ⟨j, rfl⟩ := hb
          simp only [ψ, x.injective.extend_apply, y.injective.eq_iff] at hab
          rw [hab]
        · simp only [ψ, φ', x.injective.extend_apply] at hab
          rw [Function.extend_apply' _ _ _ hb] at hab
          rw [← Set.mem_compl_iff] at hb
          rw [← Subtype.coe_mk b hb, Subtype.val_injective.extend_apply] at hab
          exfalso
          have : y i ∈ (range y)ᶜ := by
            rw [hab]
            exact Subtype.coe_prop (φ ⟨b, hb⟩)
          rw [Set.mem_compl_iff] at this
          apply this
          exact mem_range_self i
      · by_cases hb : b ∈ range x
        obtain ⟨j, rfl⟩ := hb
        · simp only [ψ, φ', x.injective.extend_apply] at hab
          rw [Function.extend_apply' _ _ _ ha] at hab
          rw [← Set.mem_compl_iff] at ha
          rw [← Subtype.coe_mk a ha, Subtype.val_injective.extend_apply] at hab
          exfalso
          have : y j ∈ (range y)ᶜ := by
            rw [← hab]
            exact Subtype.coe_prop (φ ⟨a, ha⟩)
          rw [Set.mem_compl_iff] at this
          apply this
          exact mem_range_self j
        · simp only [ψ, Function.extend_apply' _ _ _ ha,
            Function.extend_apply' _ _ _ hb, φ'] at hab
          rw [← Set.mem_compl_iff] at ha hb
          rw [← Subtype.coe_mk b hb, ← Subtype.coe_mk a ha] at hab
          rw [Subtype.val_injective.extend_apply, Subtype.val_injective.extend_apply] at hab
          rwa [← Subtype.coe_mk a ha, ← Subtype.coe_mk b hb,
              Subtype.coe_inj, ← φ.injective.eq_iff, ← Subtype.coe_inj]
    · intro b
      by_cases hb : b ∈ range y
      · obtain ⟨i, rfl⟩ := hb
        use x i
        simp only [ψ, x.injective.extend_apply]
      · rw [← Set.mem_compl_iff] at hb
        use φ.invFun ⟨b, hb⟩
        simp only [ψ]
        rw [Function.extend_apply' _ _ _ ?_]
        · simp only [φ']
          set a : α := (φ.invFun ⟨b, hb⟩ : α)
          have ha : a ∈ (range x)ᶜ := Subtype.coe_prop (φ.invFun ⟨b, hb⟩)
          rw [← Subtype.coe_mk a ha]
          simp [a]
        · rintro ⟨i, hi⟩
          apply Subtype.coe_prop (φ.invFun ⟨b, hb⟩)
          rw [← hi]
          exact mem_range_self i
  use Equiv.ofBijective ψ this
  ext i
  simp [ψ, x.injective.extend_apply]

/-- The action of the permutation group of `α` on `α` is preprimitive -/
instance : IsPreprimitive (Perm α) α :=
  isPreprimitive_of_is_two_pretransitive (isMultiplyPretransitive _ _)

-- This is optimal, `AlternatingGroup α` is `Nat.card α - 2`-pretransitive.
/-- A subgroup of `Perm α` is `⊤` if(f) it is `(Nat.card α - 1)`-pretransitive. -/
theorem eq_top_if_isMultiplyPretransitive [Finite α] {G : Subgroup (Equiv.Perm α)}
    (hmt : IsMultiplyPretransitive G α (Nat.card α - 1)) : G = ⊤ := by
  have := Fintype.ofFinite α
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
  specialize hgk i
  simp only [Function.Embedding.smul_apply, Equiv.Perm.smul_def] at hgk
  simp [← hgk, Subgroup.smul_def, Perm.smul_def]

end Equiv.Perm

section Stabilizer

variable {G α : Type*} [Group G] [MulAction G α]

namespace SubMulAction.ofStabilizer

open scoped BigOperators Pointwise Cardinal

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
  [Wielandt, th. 9.1, 1st part][Wielandt-1964]. -/
@[to_additive
  "Multiple transitivity of a pretransitive action
  is equivalent to one less transitivity of stabilizer of a point
  [Wielandt, th. 9.1, 1st part][Wielandt-1964]."]
theorem isMultiplyPretransitive [IsPretransitive G α] {n : ℕ} {a : α} :
    IsMultiplyPretransitive G α n.succ ↔
      IsMultiplyPretransitive (stabilizer G a) (SubMulAction.ofStabilizer G a) n := by
  constructor
  · refine fun hn ↦ ⟨fun x y ↦ ?_⟩
    obtain ⟨g, hgxy⟩ := exists_smul_eq G (snoc x) (snoc y)
    have hg : g ∈ stabilizer G a := by
      rw [mem_stabilizer_iff]
      rw [DFunLike.ext_iff] at hgxy
      convert hgxy (last n) <;> simp [snoc_last]
    use ⟨g, hg⟩
    ext i
    simp only [smul_apply, SubMulAction.val_smul_of_tower, subgroup_smul_def]
    rw [← snoc_castSucc x, ← smul_apply, hgxy, snoc_castSucc]
  · refine fun hn ↦ ⟨fun x y ↦ ?_⟩
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
    simp [smul_apply]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | ⟨rfl⟩
    · simp [snoc_castSucc, ← hg, subgroup_smul_def]
    · simpa only [snoc_last, ← hg, subgroup_smul_def] using g.prop

end SubMulAction.ofStabilizer

end Stabilizer

section FixingSubgroup

variable {G α : Type*} [Group G] [MulAction G α]

namespace SubMulAction.ofFixingSubgroup

/-- The fixator of a finite subset of cardinal `d` in an `n`-transitive action
acts `(n-d)` transitively on the complement. -/
@[to_additive
"The fixator of a finite subset of cardinal `d` in an `n`-transitive additive action
acts `(n-d)` transitively on the complement."]
theorem isMultiplyPretransitive {m n : ℕ} [Hn : IsMultiplyPretransitive G α n]
    (s : Set α) [Finite s] (hmn : s.ncard + m = n) :
    IsMultiplyPretransitive (fixingSubgroup G s) (ofFixingSubgroup G s) m where
  exists_smul_eq x y := by
    have : IsMultiplyPretransitive G α (s.ncard + m) := by rw [hmn]; infer_instance
    have Hs : Nonempty (Fin (s.ncard) ≃ s) :=
      Finite.card_eq.mp (by simp [Nat.card_coe_set_eq])
    set x' := ofFixingSubgroup.append x with hx
    set y' := ofFixingSubgroup.append y with hy
    obtain ⟨g, hg⟩ := exists_smul_eq G x' y'
    suffices g ∈ fixingSubgroup G s by
      use ⟨g, this⟩
      ext i
      rw [smul_apply, SetLike.val_smul, Subgroup.mk_smul]
      simp [← ofFixingSubgroup.append_right, ← smul_apply, ← hx, ← hy, hg]
    intro a
    set i := (Classical.choice Hs).symm a
    have ha : (Classical.choice Hs) i = a := by simp [i]
    rw [← ha]
    nth_rewrite 1 [← ofFixingSubgroup.append_left x i]
    rw [← ofFixingSubgroup.append_left y i, ← hy, ← hg, smul_apply, ← hx]

/-- The fixator of a finite subset of cardinal `d` in an `n`-transitive action
acts `m` transitively on the complement if `d + m ≤ n`. -/
@[to_additive
"The fixator of a finite subset of cardinal `d` in an `n`-transitive additive action
acts `m` transitively on the complement if `d + m ≤ n`."]
theorem isMultiplyPretransitive'
    {m n : ℕ} [IsMultiplyPretransitive G α n]
    (s : Set α) [Finite s] (hmn : s.ncard + m ≤ n) (hn : (n : ENat) ≤ ENat.card α) :
    IsMultiplyPretransitive (fixingSubgroup G s) (SubMulAction.ofFixingSubgroup G s) m :=
  have : IsMultiplyPretransitive G α (s.ncard + m) := isMultiplyPretransitive_of_le' hmn hn
  isMultiplyPretransitive s rfl

end SubMulAction.ofFixingSubgroup

end FixingSubgroup
