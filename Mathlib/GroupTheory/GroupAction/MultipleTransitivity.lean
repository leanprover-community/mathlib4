/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.GroupTheory.GroupAction.Embedding
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup
import Mathlib.GroupTheory.GroupAction.SubMulAction.OfStabilizer
import Mathlib.SetTheory.Cardinal.Embedding

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

variable (G α : Type*) [Group G] [MulAction G α]

/-- An action of a group on a type `α` is `n`-pretransitive
if the associated action on `Fin n ↪ α` is pretransitive. -/
@[to_additive "An additive action of an additive group on a type `α`
is `n`-pretransitive if the associated action on `Fin n ↪ α` is pretransitive."]
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
@[to_additive "A `2`-transitive additive action is primitive." ]
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

namespace SubMulAction

variable {G : Type*} [Group G] {α : Type*} [MulAction G α]

open MulAction Function.Embedding SubMulAction

namespace ofStabilizer

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
  (Wielandt, th. 9.1, 1st part) -/
@[to_additive
   "Multiple transitivity of a pretransitive action
   is equivalent to one less transitivity of stabilizer of a point
   (Wielandt, th. 9.1, 1st part)"]
theorem isMultiplyPretransitive_iff_succ [IsPretransitive G α] {n : ℕ} {a : α} :
    IsMultiplyPretransitive (stabilizer G a) (SubMulAction.ofStabilizer G a) n ↔
      IsMultiplyPretransitive G α n.succ := by
  constructor
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
          simp [ofStabilizer.snoc_castSucc, ← hg, SetLike.val_smul, subgroup_smul_def]
        · simp only [ofStabilizer.snoc_last, ← hg, subgroup_smul_def]
          exact g.prop }
  · intro hn
    exact {
      exists_smul_eq x y := by
        obtain ⟨g, hgxy⟩ := exists_smul_eq G (ofStabilizer.snoc x) (ofStabilizer.snoc y)
        have hg : g ∈ stabilizer G a := by
          rw [mem_stabilizer_iff]
          rw [DFunLike.ext_iff] at hgxy
          convert hgxy (last n) <;> simp [smul_apply, ofStabilizer.snoc_last]
        use ⟨g, hg⟩
        ext i
        simp only [smul_apply, SubMulAction.val_smul_of_tower, subgroup_smul_def]
        rw [← ofStabilizer.snoc_castSucc x, ← smul_apply, hgxy, ofStabilizer.snoc_castSucc] }

end ofStabilizer

namespace ofFixingSubgroup

variable {G α : Type*} [Group G] [MulAction G α]

open SubMulAction Fin.Embedding

variable (G) in
/-- The fixator of a finite subset of cardinal d in an n-transitive action
acts (n-d) transitively on the complement. -/
@[to_additive
"The fixator of a finite subset of cardinal d in an n-transitive additive action
acts (n-d) transitively on the complement."]
theorem isMultiplyPretransitive {m n : ℕ} [Hn : IsMultiplyPretransitive G α n]
    (s : Set α) [Finite s] (hmn : s.ncard + m = n) :
    IsMultiplyPretransitive (fixingSubgroup G s) (ofFixingSubgroup G s) m :=
  let _ : IsMultiplyPretransitive G α (s.ncard + m) := by rw [hmn]; infer_instance
  let Hs : Nonempty (Fin (s.ncard) ≃ s) :=
      Finite.card_eq.mp (by simp [Set.Nat.card_coe_set_eq])
  { exists_smul_eq x y := by
      set x' := SubMulAction.ofFixingSubgroup.append x with hx
      set y' := ofFixingSubgroup.append y with hy
      obtain ⟨g, hg⟩ := exists_smul_eq G x' y'
      suffices g ∈ fixingSubgroup G s by
        use ⟨g, this⟩
        ext i
        simp only [smul_apply, SetLike.val_smul, Subgroup.mk_smul]
        simp only [← ofFixingSubgroup.append_right, ← smul_apply, ← hx, ← hy, hg]
      intro a
      set i := (Classical.choice Hs).symm a
      have ha : (Classical.choice Hs) i = a := by simp [i]
      rw [← ha]
      nth_rewrite 1 [← ofFixingSubgroup.append_left x i]
      rw [← ofFixingSubgroup.append_left y i, ← hy, ← hg, smul_apply, ← hx] }

/-- The fixator of a finite subset of cardinal d in an n-transitive action
acts m transitively on the complement if d + m ≤ n. -/
@[to_additive
"The fixator of a finite subset of cardinal d in an n-transitive additive action
acts m transitively on the complement if d + m ≤ n."]
theorem isMultiplyPretransitive'
    {m n : ℕ} [IsMultiplyPretransitive G α n]
    (s : Set α) [Finite s] (hmn : s.ncard + m ≤ n) (hn : (n : ENat) ≤ ENat.card α) :
    IsMultiplyPretransitive (fixingSubgroup G s) (SubMulAction.ofFixingSubgroup G s) m :=
  letI : IsMultiplyPretransitive G α (s.ncard + m) := isMultiplyPretransitive_of_le' hmn hn
  isMultiplyPretransitive G s rfl

end ofFixingSubgroup

end SubMulAction

namespace MulAction

section Index

open SubMulAction

variable (G : Type*) [Group G] {α : Type*} [MulAction G α]

/-- Cardinal vs index of stabilizers, for a pretransitive action, in nat.card -/
theorem stabilizer_index_of_pretransitive [IsPretransitive G α] (a : α) :
    (stabilizer G a).index = Nat.card α := by
  rw [index_stabilizer, orbit_eq_univ, Set.ncard_univ]

/-- For a multiply pretransitive action, computes the index
of the fixing_subgroup of a subset of adequate cardinality -/
private theorem index_of_fixingSubgroup_aux
    [Finite α]
    {k : ℕ} (Hk : IsMultiplyPretransitive G α k)
    {s : Set α} (hs : s.ncard = k) :
    (fixingSubgroup G s).index * (Nat.card α - s.ncard).factorial =
      (Nat.card α).factorial := by
  revert G α
  induction k with
  | zero =>
    intro G _ α _ _ _ s hs
    simp only [hs, zero_eq, ge_iff_le, nonpos_iff_eq_zero, tsub_zero, ne_eq]
    rw [Set.ncard_eq_zero] at hs
    simp only [hs]
    suffices fixingSubgroup G ∅ = ⊤ by
      rw [this, Subgroup.index_top, one_mul]
    exact GaloisConnection.l_bot (fixingSubgroup_fixedPoints_gc G α)
  | succ k hrec =>
    intro G _ α _ _ hmk s hs
    have hGX : IsPretransitive G α := by
      rw [← is_one_pretransitive_iff]
      apply isMultiplyPretransitive_of_le (n := k + 1)
      · rw [Nat.succ_le_succ_iff]; apply Nat.zero_le
      · rw [← hs, ← Set.ncard_univ]
        exact ncard_le_ncard s.subset_univ finite_univ
    have : s.Nonempty := by
      rw [← Set.ncard_pos, hs]
      exact succ_pos k
    obtain ⟨a, has⟩ := this
    let t : Set (SubMulAction.ofStabilizer G a) := Subtype.val ⁻¹' s
    have hat : Subtype.val '' t = s \ {a} := by
      rw [Set.image_preimage_eq_inter_range]
      simp only [Subtype.range_coe_subtype]
      rw [Set.diff_eq_compl_inter, Set.inter_comm]
      congr
    have hat' : s = insert a (Subtype.val '' t) := by
      rw [hat, Set.insert_diff_singleton, Set.insert_eq_of_mem has]
    have hfs := SubMulAction.fixingSubgroup_of_insert a t
    rw [← hat'] at hfs
    rw [hfs]
    rw [Subgroup.index_map]
    rw [(MonoidHom.ker_eq_bot_iff (stabilizer G a).subtype).mpr
        (by simp only [Subgroup.coe_subtype, Subtype.coe_injective])]
    simp only [sup_bot_eq, Subgroup.range_subtype]
    have hscard : s.ncard = 1 + t.ncard := by
      rw [hat']
      suffices ¬ a ∈ (Subtype.val '' t) by
        rw [add_comm]
        convert Set.ncard_insert_of_not_mem this ?_
        rw [Set.ncard_image_of_injective _ Subtype.coe_injective]
        apply Set.toFinite
      intro h
      obtain ⟨⟨b, hb⟩, _, hb'⟩ := h
      apply hb
      simp only [Set.mem_singleton_iff]
      rw [← hb']
    have htcard : t.ncard = k := by
      rw [← Nat.succ_inj, Nat.succ_eq_add_one, Nat.succ_eq_add_one, ← hs, hscard, add_comm]
    suffices (fixingSubgroup (stabilizer G a) t).index *
      (Nat.card α - 1 - t.ncard).factorial =
        (Nat.card α - 1).factorial by
      · rw [mul_comm] at this
        rw [hscard, mul_comm, ← mul_assoc, mul_comm, Nat.sub_add_eq, this,
          stabilizer_index_of_pretransitive G a]
        exact Nat.mul_factorial_pred (card_ne_zero.mpr ⟨⟨a⟩, inferInstance⟩)
    · rw [add_comm] at hscard
      have := Nat.sub_eq_of_eq_add hscard
      simp only [hs, Nat.pred_succ] at this
      convert hrec (stabilizer G a) (α := SubMulAction.ofStabilizer G a)
        (ofStabilizer.isMultiplyPretransitive_iff_succ.mpr hmk) htcard
      all_goals { rw [nat_card_ofStabilizer_eq G a] }

 /-- For a multiply pretransitive action,
  computes the index of the fixing_subgroup of a subset
  of adequate cardinality -/
theorem index_of_fixingSubgroup_eq_of_isMultiplyPretransitive
    [Finite α] (s : Set α) (hMk : IsMultiplyPretransitive G α s.ncard) :
    (fixingSubgroup G s).index =
      Nat.choose (Nat.card α) s.ncard * s.ncard.factorial := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos _)
  rw [index_of_fixingSubgroup_aux G hMk rfl, Nat.choose_mul_factorial_mul_factorial]
  rw [← ncard_univ]
  exact ncard_le_ncard (subset_univ s)

end Index

end MulAction

namespace Equiv.Perm

open Equiv MulAction

variable {α : Type*} [Finite α]

-- Move?
/-- The permutation group of `α` acts transitively on `α`. -/
instance : IsPretransitive (Perm α) α where
  exists_smul_eq x y := by
    classical
    exact ⟨Equiv.swap x y, by simp⟩

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
          simp only [Nat.bijective_iff_injective_and_card, card_eq_fintype_card,
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
  have : Fintype α := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card] at hmt
  let j : Fin (Fintype.card α - 1) ↪ Fin (Fintype.card α) :=
    (Fin.castLEEmb ((Fintype.card α).sub_le 1))
  rw [eq_top_iff]
  intro k _
  let x : Fin (Fintype.card α) ↪ α := (Fintype.equivFinOfCardEq rfl).symm.toEmbedding
  let x' := j.trans x
  obtain ⟨g, hg'⟩ := exists_smul_eq G x' (k • x')
  suffices k = g by rw [this]; exact SetLike.coe_mem g
  have hx (x : Fin (Fintype.card α) ↪ α) : Function.Surjective x.toFun := by
    apply Function.Bijective.surjective
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨EmbeddingLike.injective x, Fintype.card_fin (Fintype.card α)⟩
  have hgk' (i : Fin (Fintype.card α)) (hi : i.val < Fintype.card α - 1) :
      (g • x) i = (k • x) i :=
    Function.Embedding.ext_iff.mp hg' ⟨i.val, hi⟩
  have hgk (i : Fin (Fintype.card α)) : (g • x) i = (k • x) i := by
    rcases lt_or_eq_of_le (le_sub_one_of_lt i.prop) with hi | hi
    · exact hgk' i hi
    · obtain ⟨j, hxj : (k • x) j = (g • x) i⟩ := hx (k • x) ((g • x) i)
      rcases lt_or_eq_of_le (le_sub_one_of_lt j.prop) with hj | hj
      · suffices i = j by
          rw [← this, ← hi] at hj
          exact (lt_irrefl _ hj).elim
        apply EmbeddingLike.injective (g • x)
        rw [hgk' j hj, hxj]
      · rw [← hxj]
        apply congr_arg
        rw [Fin.ext_iff, hi, hj]
  ext a
  obtain ⟨i, rfl⟩ := (hx x) a
  simp [← hgk, subgroup_smul_def, ← Equiv.Perm.smul_def, ← Function.Embedding.smul_apply]

end Equiv.Perm

namespace AlternatingGroup

variable (α : Type*) [Fintype α] [DecidableEq α]

/-- The `alternatingGroup` on α is (Fintype.card α - 2)-pretransitive. -/
theorem isMultiplyPretransitive :
    IsMultiplyPretransitive (alternatingGroup α) α (Nat.card α - 2) := by
  rcases lt_or_le (Nat.card α) 2 with h2 | h2
  · rw [Nat.sub_eq_zero_of_le (le_of_lt h2)]
    apply is_zero_pretransitive
  have : IsMultiplyPretransitive (Equiv.Perm α) α (Nat.card α) :=
        Equiv.Perm.isMultiplyPretransitive α _
  have h2le : Nat.card α - 2 ≤ Nat.card α:= sub_le (Nat.card α) 2
  exact {
    exists_smul_eq x y := by
      have : IsMultiplyPretransitive (Equiv.Perm α) α (Nat.card α) :=
        Equiv.Perm.isMultiplyPretransitive α _
      obtain ⟨x', hx'⟩ := Fin.Embedding.restrictSurjective_of_le_natCard h2le (le_refl _) x
      obtain ⟨y', hy'⟩ := Fin.Embedding.restrictSurjective_of_le_natCard h2le (le_refl _) y
      obtain ⟨g , hg⟩ := exists_smul_eq (Equiv.Perm α) x' y'
      rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h | h
      · use ⟨g, h⟩
        ext i
        simp only [← hx', subgroup_smul_def, smul_apply,
          Function.Embedding.trans_apply, castLEEmb_apply, ← hy']
        simp only [← smul_apply, hg]
      · let u : Fin (Nat.card α) := ⟨Nat.card α - 1, sub_one_lt_of_lt h2⟩
        let v : Fin (Nat.card α) := ⟨Nat.card α - 2,
            Nat.sub_lt_left_of_lt_add h2 (Nat.lt_add_of_pos_left Nat.zero_lt_two)⟩
        refine ⟨⟨g * (Equiv.swap (x' u) (x' v)), ?_⟩, ?_⟩
        · suffices u ≠ v by simp [h, this]
          exact ne_of_val_ne (Nat.ne_of_gt (sub_succ_lt_self (Nat.card α) 1 h2))
        · ext i
          suffices (Equiv.swap (x' u) (x' v)) • (x' (castLE h2le i)) = x' (castLE h2le i) by
            rw [← hy', ← hg, ← hx']
            simp only [Subgroup.mk_smul, smul_apply, trans_apply, castLEEmb_apply,
              Equiv.Perm.smul_def, Equiv.Perm.coe_mul, Function.comp_apply,
              EmbeddingLike.apply_eq_iff_eq]
            rw [← Equiv.Perm.smul_def, this]
          have hiv : (i : ℕ) < v := (lt_of_lt_of_le i.prop (le_of_eq rfl))
          have hiu : (i : ℕ) < u := by
            apply lt_trans hiv
            simp only [u, v, ← one_add_one_eq_two, ← Nat.sub_sub]
            apply Nat.sub_lt_self Nat.zero_lt_one (le_sub_one_of_lt h2)
          apply Equiv.swap_apply_of_ne_of_ne <;>
            simp [ne_eq, EmbeddingLike.apply_eq_iff_eq, ← val_inj,
              coe_castLE, Nat.ne_of_lt hiu, Nat.ne_of_lt hiv] }

/-- A subgroup of `Equiv.Perm α` which is (Fintype.card α - 2)-pretransitive
  contains `alternatingGroup α`. -/
theorem _root_.IsMultiplyPretransitive.alternatingGroup_le
    (G : Subgroup (Equiv.Perm α))
    (hmt : IsMultiplyPretransitive G α (Nat.card α - 2)) :
    alternatingGroup α ≤ G := by
  rcases Nat.lt_or_ge (Nat.card α) 2 with hα1 | hα
  · -- Nat.card α  < 2
    rw [Nat.lt_succ_iff] at hα1
    suffices alternatingGroup α = ⊥ by rw [this]; exact bot_le
    refine alternatingGroup.eq_bot_of_card_le_two ?_
    rw [← Nat.card_eq_fintype_card]
    exact le_succ_of_le hα1
  -- 2 ≤ Nat.card α
  apply Equiv.Perm.alternatingGroup_le_of_index_le_two
  -- one picks up a set of cardinality (card α - 2)
  obtain ⟨s, _, hs⟩ :=
    Set.exists_subset_card_eq (s := (Set.univ : Set α)) (n := Nat.card α - 2)
      (by rw [Set.ncard_univ]; exact sub_le (Nat.card α) 2)
  rw [← hs] at hmt
  -- The index of (fixingSubgroup G s) is (card α)!/2
  have := MulAction.index_of_fixingSubgroup_eq_of_isMultiplyPretransitive G s hmt
  rw [hs,
    ← Nat.mul_right_cancel_iff (factorial_pos (Nat.card α - (Nat.card α - 2))),
    Nat.choose_mul_factorial_mul_factorial (Nat.sub_le _ _),
    Nat.sub_sub_self hα, factorial_two] at this
  -- conclude
  rw [← mul_le_mul_iff_of_pos_left (a := Nat.card G) card_pos,
    Subgroup.card_mul_index, ← (fixingSubgroup G s).index_mul_card,
    mul_assoc, mul_comm _ 2, ← mul_assoc]
  rw [this, Nat.card_perm]
  refine Nat.le_mul_of_pos_right (Nat.card α)! card_pos

/-- The alternating group on 3 letters or more acts transitively. -/
theorem isPretransitive_of_three_le_card (h : 3 ≤ Nat.card α) :
    IsPretransitive (alternatingGroup α) α := by
  rw [← is_one_pretransitive_iff]
  letI := isMultiplyPretransitive α
  apply isMultiplyPretransitive_of_le (n := Nat.card α - 2) _ (sub_le _ _)
  rw [← add_le_add_iff_right 2, Nat.sub_add_cancel (le_trans (by norm_num) h)]
  exact h

open scoped Pointwise

/-- The action of the alternation group has trivial blocks.

This holds for any `α`, even when `Nat.card α ≤ 2` and the action
is not preprimitive, because it is not pretransitive. -/
theorem isTrivialBlock_of_isBlock {B : Set α} (hB : IsBlock (alternatingGroup α) B) :
    IsTrivialBlock B := by
  rcases le_or_lt (Nat.card α) 2 with h2 | h2
  · exact isTrivialBlock_of_card_le_two h2 B
  rcases le_or_lt (Nat.card α) 3 with h3 | h4
  · have h3' : Nat.card α = 3 := le_antisymm h3 h2
    rcases le_or_lt B.ncard 1 with h1 | h2
    · apply Or.intro_left
      rwa [← Set.ncard_le_one_iff_subsingleton]
    · apply Or.intro_right
      rw [Set.one_lt_ncard_iff] at h2
      -- using h2, get a ≠ b in B
      obtain ⟨a, b, ha, hb, hab⟩ := h2
      -- using h3', get c ≠ a, b
      obtain ⟨c, _, hc⟩ := Finset.exists_mem_not_mem_of_card_lt_card
          (s := {a, b}) (t := Finset.univ) (by
            simp only [Finset.card_univ, ← Nat.card_eq_fintype_card, h3']
            exact lt_of_le_of_lt Finset.card_le_two (by norm_num))
      have H1 : {c, a, b} = Finset.univ := by
        apply Finset.eq_univ_of_card
        rw [← Nat.card_eq_fintype_card, h3', Finset.card_insert_of_not_mem hc,
          Finset.card_insert_of_not_mem (by simpa only [Finset.mem_singleton]),
          Finset.card_singleton]
      suffices c ∈ B by
        apply subset_antisymm B.subset_univ
        rw [← Finset.coe_univ, ← H1]
        simp only [Finset.coe_insert, Finset.coe_singleton,
          insert_subset_iff, singleton_subset_iff]
        exact ⟨this, ha, hb⟩
      -- get a three_cycle g = c[a,b,c]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
      let g : alternatingGroup α := -- cycle [a, b, c]
        ⟨Equiv.swap a b * Equiv.swap c b, by
          rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
            Equiv.Perm.sign_swap hab, Equiv.Perm.sign_swap hc.right,
            Int.units_mul_self]⟩
      suffices g • B = B by
        rw [← this]
        use b
        apply And.intro hb
        change (Equiv.swap a b * Equiv.swap c b) • b = c
        simp only [Equiv.Perm.smul_def, Equiv.Perm.coe_mul, Function.comp_apply]
        rw [Equiv.swap_apply_right]
        rw [Equiv.swap_apply_of_ne_of_ne hc.left hc.right]
      -- g • B = B
      rw [isBlock_iff_smul_eq_of_mem] at hB
      apply hB ha
      simp only [Subgroup.mk_smul, Equiv.Perm.smul_def, Equiv.Perm.coe_mul, Function.comp_apply, g]
      convert hb
      rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hc.1) hab]
      rw [Equiv.swap_apply_left]
  -- IsTrivialBlock hB, for 4 ≤ Nat.card α
  suffices IsPreprimitive (alternatingGroup α) α by
    apply IsPreprimitive.isTrivialBlock_of_isBlock hB
  apply isPreprimitive_of_is_two_pretransitive
  letI := isMultiplyPretransitive α
  apply isMultiplyPretransitive_of_le (n := Nat.card α - 2) _ (sub_le _ _)
  rw [← add_le_add_iff_right 2, Nat.sub_add_cancel (le_of_lt h2)]
  exact h4

/-- The alternating group on 3 letters or more acts primitively -/
theorem isPreprimitive_of_three_le_card (h : 3 ≤ Nat.card α) :
    IsPreprimitive (alternatingGroup α) α :=
  letI := isPretransitive_of_three_le_card α h
  { isTrivialBlock_of_isBlock := isTrivialBlock_of_isBlock α }

end AlternatingGroup

