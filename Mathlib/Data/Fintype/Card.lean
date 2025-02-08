/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Set.Image
import Mathlib.Order.WellFounded

/-!
# Cardinalities of finite types

## Main declarations

* `Fintype.card α`: Cardinality of a fintype. Equal to `Finset.univ.card`.
* `Fintype.truncEquivFin`: A fintype `α` is computably equivalent to `Fin (card α)`. The
  `Trunc`-free, noncomputable version is `Fintype.equivFin`.
* `Fintype.truncEquivOfCardEq` `Fintype.equivOfCardEq`: Two fintypes of same cardinality are
  equivalent. See above.
* `Fin.equiv_iff_eq`: `Fin m ≃ Fin n` iff `m = n`.
* `Infinite.natEmbedding`: An embedding of `ℕ` into an infinite type.

We also provide the following versions of the pigeonholes principle.
* `Fintype.exists_ne_map_eq_of_card_lt` and `isEmpty_of_card_lt`: Finitely many pigeons and
  pigeonholes. Weak formulation.
* `Finite.exists_ne_map_eq_of_infinite`: Infinitely many pigeons in finitely many pigeonholes.
  Weak formulation.
* `Finite.exists_infinite_fiber`: Infinitely many pigeons in finitely many pigeonholes. Strong
  formulation.

Some more pigeonhole-like statements can be found in `Data.Fintype.CardEmbedding`.

Types which have an injection from/a surjection to an `Infinite` type are themselves `Infinite`.
See `Infinite.of_injective` and `Infinite.of_surjective`.

## Instances

We provide `Infinite` instances for
* specific types: `ℕ`, `ℤ`, `String`
* type constructors: `Multiset α`, `List α`

-/

assert_not_exists MonoidWithZero MulAction

open Function

universe u v

variable {α β γ : Type*}

open Finset Function

namespace Fintype

/-- `card α` is the number of elements in `α`, defined when `α` is a fintype. -/
def card (α) [Fintype α] : ℕ :=
  (@univ α _).card

/-- There is (computably) an equivalence between `α` and `Fin (card α)`.

Since it is not unique and depends on which permutation
of the universe list is used, the equivalence is wrapped in `Trunc` to
preserve computability.

See `Fintype.equivFin` for the noncomputable version,
and `Fintype.truncEquivFinOfCardEq` and `Fintype.equivFinOfCardEq`
for an equiv `α ≃ Fin n` given `Fintype.card α = n`.

See `Fintype.truncFinBijection` for a version without `[DecidableEq α]`.
-/
def truncEquivFin (α) [DecidableEq α] [Fintype α] : Trunc (α ≃ Fin (card α)) := by
  unfold card Finset.card
  exact
    Quot.recOnSubsingleton
      (motive := fun s : Multiset α =>
        (∀ x : α, x ∈ s) → s.Nodup → Trunc (α ≃ Fin (Multiset.card s)))
      univ.val
      (fun l (h : ∀ x : α, x ∈ l) (nd : l.Nodup) => Trunc.mk (nd.getEquivOfForallMemList _ h).symm)
      mem_univ_val univ.2

/-- There is (noncomputably) an equivalence between `α` and `Fin (card α)`.

See `Fintype.truncEquivFin` for the computable version,
and `Fintype.truncEquivFinOfCardEq` and `Fintype.equivFinOfCardEq`
for an equiv `α ≃ Fin n` given `Fintype.card α = n`.
-/
noncomputable def equivFin (α) [Fintype α] : α ≃ Fin (card α) :=
  letI := Classical.decEq α
  (truncEquivFin α).out

/-- There is (computably) a bijection between `Fin (card α)` and `α`.

Since it is not unique and depends on which permutation
of the universe list is used, the bijection is wrapped in `Trunc` to
preserve computability.

See `Fintype.truncEquivFin` for a version that gives an equivalence
given `[DecidableEq α]`.
-/
def truncFinBijection (α) [Fintype α] : Trunc { f : Fin (card α) → α // Bijective f } := by
  unfold card Finset.card
  refine
    Quot.recOnSubsingleton
      (motive := fun s : Multiset α =>
        (∀ x : α, x ∈ s) → s.Nodup → Trunc {f : Fin (Multiset.card s) → α // Bijective f})
      univ.val
      (fun l (h : ∀ x : α, x ∈ l) (nd : l.Nodup) => Trunc.mk (nd.getBijectionOfForallMemList _ h))
      mem_univ_val univ.2

theorem subtype_card {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x) :
    @card { x // p x } (Fintype.subtype s H) = #s :=
  Multiset.card_pmap _ _ _

theorem card_of_subtype {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x)
    [Fintype { x // p x }] : card { x // p x } = #s := by
  rw [← subtype_card s H]
  congr!

@[simp]
theorem card_ofFinset {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) :
    @Fintype.card p (ofFinset s H) = #s :=
  Fintype.subtype_card s H

theorem card_of_finset' {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) [Fintype p] :
    Fintype.card p = #s := by rw [← card_ofFinset s H]; congr!

end Fintype

namespace Fintype

theorem ofEquiv_card [Fintype α] (f : α ≃ β) : @card β (ofEquiv α f) = card α :=
  Multiset.card_map _ _

theorem card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β) : card α = card β := by
  rw [← ofEquiv_card f]; congr!

@[congr]
theorem card_congr' {α β} [Fintype α] [Fintype β] (h : α = β) : card α = card β :=
  card_congr (by rw [h])

section

variable [Fintype α] [Fintype β]

/-- If the cardinality of `α` is `n`, there is computably a bijection between `α` and `Fin n`.

See `Fintype.equivFinOfCardEq` for the noncomputable definition,
and `Fintype.truncEquivFin` and `Fintype.equivFin` for the bijection `α ≃ Fin (card α)`.
-/
def truncEquivFinOfCardEq [DecidableEq α] {n : ℕ} (h : Fintype.card α = n) : Trunc (α ≃ Fin n) :=
  (truncEquivFin α).map fun e => e.trans (finCongr h)

/-- If the cardinality of `α` is `n`, there is noncomputably a bijection between `α` and `Fin n`.

See `Fintype.truncEquivFinOfCardEq` for the computable definition,
and `Fintype.truncEquivFin` and `Fintype.equivFin` for the bijection `α ≃ Fin (card α)`.
-/
noncomputable def equivFinOfCardEq {n : ℕ} (h : Fintype.card α = n) : α ≃ Fin n :=
  letI := Classical.decEq α
  (truncEquivFinOfCardEq h).out

/-- Two `Fintype`s with the same cardinality are (computably) in bijection.

See `Fintype.equivOfCardEq` for the noncomputable version,
and `Fintype.truncEquivFinOfCardEq` and `Fintype.equivFinOfCardEq` for
the specialization to `Fin`.
-/
def truncEquivOfCardEq [DecidableEq α] [DecidableEq β] (h : card α = card β) : Trunc (α ≃ β) :=
  (truncEquivFinOfCardEq h).bind fun e => (truncEquivFin β).map fun e' => e.trans e'.symm

/-- Two `Fintype`s with the same cardinality are (noncomputably) in bijection.

See `Fintype.truncEquivOfCardEq` for the computable version,
and `Fintype.truncEquivFinOfCardEq` and `Fintype.equivFinOfCardEq` for
the specialization to `Fin`.
-/
noncomputable def equivOfCardEq (h : card α = card β) : α ≃ β := by
  letI := Classical.decEq α
  letI := Classical.decEq β
  exact (truncEquivOfCardEq h).out

end

theorem card_eq {α β} [_F : Fintype α] [_G : Fintype β] : card α = card β ↔ Nonempty (α ≃ β) :=
  ⟨fun h =>
    haveI := Classical.propDecidable
    (truncEquivOfCardEq h).nonempty,
    fun ⟨f⟩ => card_congr f⟩

/-- Note: this lemma is specifically about `Fintype.ofSubsingleton`. For a statement about
arbitrary `Fintype` instances, use either `Fintype.card_le_one_iff_subsingleton` or
`Fintype.card_unique`. -/
theorem card_ofSubsingleton (a : α) [Subsingleton α] : @Fintype.card _ (ofSubsingleton a) = 1 :=
  rfl

@[simp]
theorem card_unique [Unique α] [h : Fintype α] : Fintype.card α = 1 :=
  Subsingleton.elim (ofSubsingleton default) h ▸ card_ofSubsingleton _

/-- Note: this lemma is specifically about `Fintype.ofIsEmpty`. For a statement about
arbitrary `Fintype` instances, use `Fintype.card_eq_zero`. -/
theorem card_ofIsEmpty [IsEmpty α] : @Fintype.card α Fintype.ofIsEmpty = 0 :=
  rfl

end Fintype

namespace Set

variable {s t : Set α}

-- We use an arbitrary `[Fintype s]` instance here,
-- not necessarily coming from a `[Fintype α]`.
@[simp]
theorem toFinset_card {α : Type*} (s : Set α) [Fintype s] : s.toFinset.card = Fintype.card s :=
  Multiset.card_map Subtype.val Finset.univ.val

end Set

@[simp]
theorem Finset.card_univ [Fintype α] : #(univ : Finset α) = Fintype.card α := rfl

theorem Finset.eq_univ_of_card [Fintype α] (s : Finset α) (hs : #s = Fintype.card α) :
    s = univ :=
  eq_of_subset_of_card_le (subset_univ _) <| by rw [hs, Finset.card_univ]

theorem Finset.card_eq_iff_eq_univ [Fintype α] (s : Finset α) : #s = Fintype.card α ↔ s = univ :=
  ⟨s.eq_univ_of_card, by
    rintro rfl
    exact Finset.card_univ⟩

theorem Finset.card_le_univ [Fintype α] (s : Finset α) : #s ≤ Fintype.card α :=
  card_le_card (subset_univ s)

theorem Finset.card_lt_univ_of_not_mem [Fintype α] {s : Finset α} {x : α} (hx : x ∉ s) :
    #s < Fintype.card α :=
  card_lt_card ⟨subset_univ s, not_forall.2 ⟨x, fun hx' => hx (hx' <| mem_univ x)⟩⟩

theorem Finset.card_lt_iff_ne_univ [Fintype α] (s : Finset α) :
    #s < Fintype.card α ↔ s ≠ Finset.univ :=
  s.card_le_univ.lt_iff_ne.trans (not_congr s.card_eq_iff_eq_univ)

theorem Finset.card_compl_lt_iff_nonempty [Fintype α] [DecidableEq α] (s : Finset α) :
    #sᶜ < Fintype.card α ↔ s.Nonempty :=
  sᶜ.card_lt_iff_ne_univ.trans s.compl_ne_univ_iff_nonempty

theorem Finset.card_univ_diff [DecidableEq α] [Fintype α] (s : Finset α) :
    #(univ \ s) = Fintype.card α - #s :=
  Finset.card_sdiff (subset_univ s)

theorem Finset.card_compl [DecidableEq α] [Fintype α] (s : Finset α) : #sᶜ = Fintype.card α - #s :=
  Finset.card_univ_diff s

@[simp]
theorem Finset.card_add_card_compl [DecidableEq α] [Fintype α] (s : Finset α) :
    #s + #sᶜ = Fintype.card α := by
  rw [Finset.card_compl, ← Nat.add_sub_assoc (card_le_univ s), Nat.add_sub_cancel_left]

@[simp]
theorem Finset.card_compl_add_card [DecidableEq α] [Fintype α] (s : Finset α) :
    #sᶜ + #s = Fintype.card α := by
  rw [add_comm, card_add_card_compl]

theorem Fintype.card_compl_set [Fintype α] (s : Set α) [Fintype s] [Fintype (↥sᶜ : Sort _)] :
    Fintype.card (↥sᶜ : Sort _) = Fintype.card α - Fintype.card s := by
  classical rw [← Set.toFinset_card, ← Set.toFinset_card, ← Finset.card_compl, Set.toFinset_compl]

@[simp]
theorem Fintype.card_fin (n : ℕ) : Fintype.card (Fin n) = n :=
  List.length_finRange n

theorem Fintype.card_fin_lt_of_le {m n : ℕ} (h : m ≤ n) :
    Fintype.card {i : Fin n // i < m} = m := by
  conv_rhs => rw [← Fintype.card_fin m]
  apply Fintype.card_congr
  exact { toFun := fun ⟨⟨i, _⟩, hi⟩ ↦ ⟨i, hi⟩
          invFun := fun ⟨i, hi⟩ ↦ ⟨⟨i, lt_of_lt_of_le hi h⟩, hi⟩
          left_inv := fun i ↦ rfl
          right_inv := fun i ↦ rfl }

theorem Finset.card_fin (n : ℕ) : #(univ : Finset (Fin n)) = n := by simp

/-- `Fin` as a map from `ℕ` to `Type` is injective. Note that since this is a statement about
equality of types, using it should be avoided if possible. -/
theorem fin_injective : Function.Injective Fin := fun m n h =>
  (Fintype.card_fin m).symm.trans <| (Fintype.card_congr <| Equiv.cast h).trans (Fintype.card_fin n)

theorem Fin.val_eq_val_of_heq {k l : ℕ} {i : Fin k} {j : Fin l} (h : HEq i j) :
    (i : ℕ) = (j : ℕ) :=
  (Fin.heq_ext_iff (fin_injective (type_eq_of_heq h))).1 h

/-- A reversed version of `Fin.cast_eq_cast` that is easier to rewrite with. -/
theorem Fin.cast_eq_cast' {n m : ℕ} (h : Fin n = Fin m) :
    _root_.cast h = Fin.cast (fin_injective h) := by
  cases fin_injective h
  rfl

theorem card_finset_fin_le {n : ℕ} (s : Finset (Fin n)) : #s ≤ n := by
  simpa only [Fintype.card_fin] using s.card_le_univ

theorem Fintype.card_subtype_eq (y : α) [Fintype { x // x = y }] :
    Fintype.card { x // x = y } = 1 :=
  Fintype.card_unique

theorem Fintype.card_subtype_eq' (y : α) [Fintype { x // y = x }] :
    Fintype.card { x // y = x } = 1 :=
  Fintype.card_unique

theorem Fintype.card_empty : Fintype.card Empty = 0 :=
  rfl

theorem Fintype.card_pempty : Fintype.card PEmpty = 0 :=
  rfl

theorem Fintype.card_unit : Fintype.card Unit = 1 :=
  rfl

@[simp]
theorem Fintype.card_punit : Fintype.card PUnit = 1 :=
  rfl

@[simp]
theorem Fintype.card_bool : Fintype.card Bool = 2 :=
  rfl

@[simp]
theorem Fintype.card_ulift (α : Type*) [Fintype α] : Fintype.card (ULift α) = Fintype.card α :=
  Fintype.ofEquiv_card _

@[simp]
theorem Fintype.card_plift (α : Type*) [Fintype α] : Fintype.card (PLift α) = Fintype.card α :=
  Fintype.ofEquiv_card _

@[simp]
theorem Fintype.card_orderDual (α : Type*) [Fintype α] : Fintype.card αᵒᵈ = Fintype.card α :=
  rfl

@[simp]
theorem Fintype.card_lex (α : Type*) [Fintype α] : Fintype.card (Lex α) = Fintype.card α :=
  rfl

@[simp] lemma Fintype.card_multiplicative (α : Type*) [Fintype α] :
    card (Multiplicative α) = card α := Finset.card_map _

@[simp] lemma Fintype.card_additive (α : Type*) [Fintype α] : card (Additive α) = card α :=
  Finset.card_map _

/-- Given that `α ⊕ β` is a fintype, `α` is also a fintype. This is non-computable as it uses
that `Sum.inl` is an injection, but there's no clear inverse if `α` is empty. -/
noncomputable def Fintype.sumLeft {α β} [Fintype (α ⊕ β)] : Fintype α :=
  Fintype.ofInjective (Sum.inl : α → α ⊕ β) Sum.inl_injective

/-- Given that `α ⊕ β` is a fintype, `β` is also a fintype. This is non-computable as it uses
that `Sum.inr` is an injection, but there's no clear inverse if `β` is empty. -/
noncomputable def Fintype.sumRight {α β} [Fintype (α ⊕ β)] : Fintype β :=
  Fintype.ofInjective (Sum.inr : β → α ⊕ β) Sum.inr_injective

/-!
### Relation to `Finite`

In this section we prove that `α : Type*` is `Finite` if and only if `Fintype α` is nonempty.
-/


-- @[nolint fintype_finite] -- Porting note: do we need this
protected theorem Fintype.finite {α : Type*} (_inst : Fintype α) : Finite α :=
  ⟨Fintype.equivFin α⟩

/-- For efficiency reasons, we want `Finite` instances to have higher
priority than ones coming from `Fintype` instances. -/
-- @[nolint fintype_finite] -- Porting note: do we need this
instance (priority := 900) Finite.of_fintype (α : Type*) [Fintype α] : Finite α :=
  Fintype.finite ‹_›

theorem finite_iff_nonempty_fintype (α : Type*) : Finite α ↔ Nonempty (Fintype α) :=
  ⟨fun _ => nonempty_fintype α, fun ⟨_⟩ => inferInstance⟩

/-- Noncomputably get a `Fintype` instance from a `Finite` instance. This is not an
instance because we want `Fintype` instances to be useful for computations. -/
noncomputable def Fintype.ofFinite (α : Type*) [Finite α] : Fintype α :=
  (nonempty_fintype α).some

theorem Finite.of_injective {α β : Sort*} [Finite β] (f : α → β) (H : Injective f) : Finite α := by
  rcases Finite.exists_equiv_fin β with ⟨n, ⟨e⟩⟩
  classical exact .of_equiv (Set.range (e ∘ f)) (Equiv.ofInjective _ (e.injective.comp H)).symm

-- see Note [lower instance priority]
instance (priority := 100) Finite.of_subsingleton {α : Sort*} [Subsingleton α] : Finite α :=
  Finite.of_injective (Function.const α ()) <| Function.injective_of_subsingleton _

-- Higher priority for `Prop`s
-- Porting note (https://github.com/leanprover-community/mathlib4/issues/12096): removed @[nolint instance_priority], linter not ported yet
instance prop (p : Prop) : Finite p :=
  Finite.of_subsingleton

/-- This instance also provides `[Finite s]` for `s : Set α`. -/
instance Subtype.finite {α : Sort*} [Finite α] {p : α → Prop} : Finite { x // p x } :=
  Finite.of_injective Subtype.val Subtype.coe_injective

theorem Finite.of_surjective {α β : Sort*} [Finite α] (f : α → β) (H : Surjective f) : Finite β :=
  Finite.of_injective _ <| injective_surjInv H

instance Quot.finite {α : Sort*} [Finite α] (r : α → α → Prop) : Finite (Quot r) :=
  Finite.of_surjective _ Quot.mk_surjective

instance Quotient.finite {α : Sort*} [Finite α] (s : Setoid α) : Finite (Quotient s) :=
  Quot.finite _

theorem Finite.exists_univ_list (α) [Finite α] : ∃ l : List α, l.Nodup ∧ ∀ x : α, x ∈ l := by
  cases nonempty_fintype α
  obtain ⟨l, e⟩ := Quotient.exists_rep (@univ α _).1
  have := And.intro (@univ α _).2 (@mem_univ_val α _)
  exact ⟨_, by rwa [← e] at this⟩

theorem List.Nodup.length_le_card {α : Type*} [Fintype α] {l : List α} (h : l.Nodup) :
    l.length ≤ Fintype.card α := by
  classical exact List.toFinset_card_of_nodup h ▸ l.toFinset.card_le_univ

namespace Fintype

variable [Fintype α] [Fintype β]

theorem card_le_of_injective (f : α → β) (hf : Function.Injective f) : card α ≤ card β :=
  Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) fun _ _ _ _ h => hf h

theorem card_le_of_embedding (f : α ↪ β) : card α ≤ card β :=
  card_le_of_injective f f.2

theorem card_lt_of_injective_of_not_mem (f : α → β) (h : Function.Injective f) {b : β}
    (w : b ∉ Set.range f) : card α < card β :=
  calc
    card α = (univ.map ⟨f, h⟩).card := (card_map _).symm
    _ < card β :=
      Finset.card_lt_univ_of_not_mem (x := b) <| by
        rwa [← mem_coe, coe_map, coe_univ, Set.image_univ]

theorem card_lt_of_injective_not_surjective (f : α → β) (h : Function.Injective f)
    (h' : ¬Function.Surjective f) : card α < card β :=
  let ⟨_y, hy⟩ := not_forall.1 h'
  card_lt_of_injective_of_not_mem f h hy

theorem card_le_of_surjective (f : α → β) (h : Function.Surjective f) : card β ≤ card α :=
  card_le_of_injective _ (Function.injective_surjInv h)

theorem card_range_le {α β : Type*} (f : α → β) [Fintype α] [Fintype (Set.range f)] :
    Fintype.card (Set.range f) ≤ Fintype.card α :=
  Fintype.card_le_of_surjective (fun a => ⟨f a, by simp⟩) fun ⟨_, a, ha⟩ => ⟨a, by simpa using ha⟩

theorem card_range {α β F : Type*} [FunLike F α β] [EmbeddingLike F α β] (f : F) [Fintype α]
    [Fintype (Set.range f)] : Fintype.card (Set.range f) = Fintype.card α :=
  Eq.symm <| Fintype.card_congr <| Equiv.ofInjective _ <| EmbeddingLike.injective f

/-- The pigeonhole principle for finitely many pigeons and pigeonholes.
This is the `Fintype` version of `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`.
-/
theorem exists_ne_map_eq_of_card_lt (f : α → β) (h : Fintype.card β < Fintype.card α) :
    ∃ x y, x ≠ y ∧ f x = f y :=
  let ⟨x, _, y, _, h⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to h fun x _ => mem_univ (f x)
  ⟨x, y, h⟩

theorem card_eq_one_iff : card α = 1 ↔ ∃ x : α, ∀ y, y = x := by
  rw [← card_unit, card_eq]
  exact
    ⟨fun ⟨a⟩ => ⟨a.symm (), fun y => a.injective (Subsingleton.elim _ _)⟩,
     fun ⟨x, hx⟩ =>
      ⟨⟨fun _ => (), fun _ => x, fun _ => (hx _).trans (hx _).symm, fun _ =>
          Subsingleton.elim _ _⟩⟩⟩

theorem card_eq_zero_iff : card α = 0 ↔ IsEmpty α := by
  rw [card, Finset.card_eq_zero, univ_eq_empty_iff]

@[simp] theorem card_eq_zero [IsEmpty α] : card α = 0 :=
  card_eq_zero_iff.2 ‹_›

alias card_of_isEmpty := card_eq_zero

theorem card_eq_one_iff_nonempty_unique : card α = 1 ↔ Nonempty (Unique α) :=
  ⟨fun h =>
    let ⟨d, h⟩ := Fintype.card_eq_one_iff.mp h
    ⟨{  default := d
        uniq := h }⟩,
    fun ⟨_h⟩ => Fintype.card_unique⟩

/-- A `Fintype` with cardinality zero is equivalent to `Empty`. -/
def cardEqZeroEquivEquivEmpty : card α = 0 ≃ (α ≃ Empty) :=
  (Equiv.ofIff card_eq_zero_iff).trans (Equiv.equivEmptyEquiv α).symm

theorem card_pos_iff : 0 < card α ↔ Nonempty α :=
  Nat.pos_iff_ne_zero.trans <| not_iff_comm.mp <| not_nonempty_iff.trans card_eq_zero_iff.symm

theorem card_pos [h : Nonempty α] : 0 < card α :=
  card_pos_iff.mpr h

@[simp]
theorem card_ne_zero [Nonempty α] : card α ≠ 0 :=
  _root_.ne_of_gt card_pos

instance [Nonempty α] : NeZero (card α) := ⟨card_ne_zero⟩

theorem card_le_one_iff : card α ≤ 1 ↔ ∀ a b : α, a = b :=
  let n := card α
  have hn : n = card α := rfl
  match n, hn with
  | 0, ha =>
    ⟨fun _h => fun a => (card_eq_zero_iff.1 ha.symm).elim a, fun _ => ha ▸ Nat.le_succ _⟩
  | 1, ha =>
    ⟨fun _h => fun a b => by
      let ⟨x, hx⟩ := card_eq_one_iff.1 ha.symm
      rw [hx a, hx b], fun _ => ha ▸ le_rfl⟩
  | n + 2, ha =>
    ⟨fun h => False.elim <| by rw [← ha] at h; cases h with | step h => cases h; , fun h =>
      card_unit ▸ card_le_of_injective (fun _ => ()) fun _ _ _ => h _ _⟩

theorem card_le_one_iff_subsingleton : card α ≤ 1 ↔ Subsingleton α :=
  card_le_one_iff.trans subsingleton_iff.symm

theorem one_lt_card_iff_nontrivial : 1 < card α ↔ Nontrivial α := by
  rw [← not_iff_not, not_lt, not_nontrivial_iff_subsingleton, card_le_one_iff_subsingleton]

theorem exists_ne_of_one_lt_card (h : 1 < card α) (a : α) : ∃ b : α, b ≠ a :=
  haveI : Nontrivial α := one_lt_card_iff_nontrivial.1 h
  exists_ne a

theorem exists_pair_of_one_lt_card (h : 1 < card α) : ∃ a b : α, a ≠ b :=
  haveI : Nontrivial α := one_lt_card_iff_nontrivial.1 h
  exists_pair_ne α

theorem card_eq_one_of_forall_eq {i : α} (h : ∀ j, j = i) : card α = 1 :=
  Fintype.card_eq_one_iff.2 ⟨i, h⟩

theorem existsUnique_iff_card_one {α} [Fintype α] (p : α → Prop) [DecidablePred p] :
    (∃! a : α, p a) ↔ #{x | p x} = 1 := by
  rw [Finset.card_eq_one]
  refine exists_congr fun x => ?_
  simp only [forall_true_left, Subset.antisymm_iff, subset_singleton_iff', singleton_subset_iff,
      true_and, and_comm, mem_univ, mem_filter]

@[deprecated (since := "2024-12-17")] alias exists_unique_iff_card_one := existsUnique_iff_card_one

theorem one_lt_card [h : Nontrivial α] : 1 < Fintype.card α :=
  Fintype.one_lt_card_iff_nontrivial.mpr h

theorem one_lt_card_iff : 1 < card α ↔ ∃ a b : α, a ≠ b :=
  one_lt_card_iff_nontrivial.trans nontrivial_iff

nonrec theorem two_lt_card_iff : 2 < card α ↔ ∃ a b c : α, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  simp_rw [← Finset.card_univ, two_lt_card_iff, mem_univ, true_and]

theorem card_of_bijective {f : α → β} (hf : Bijective f) : card α = card β :=
  card_congr (Equiv.ofBijective f hf)

end Fintype

namespace Finite

variable [Finite α]

theorem surjective_of_injective {f : α → α} (hinj : Injective f) : Surjective f := by
  intro x
  have := Classical.propDecidable
  cases nonempty_fintype α
  have h₁ : image f univ = univ :=
    eq_of_subset_of_card_le (subset_univ _)
      ((card_image_of_injective univ hinj).symm ▸ le_rfl)
  have h₂ : x ∈ image f univ := h₁.symm ▸ mem_univ x
  obtain ⟨y, h⟩ := mem_image.1 h₂
  exact ⟨y, h.2⟩

theorem injective_iff_surjective {f : α → α} : Injective f ↔ Surjective f :=
  ⟨surjective_of_injective, fun hsurj =>
    HasLeftInverse.injective ⟨surjInv hsurj, leftInverse_of_surjective_of_rightInverse
      (surjective_of_injective (injective_surjInv _))
      (rightInverse_surjInv _)⟩⟩

theorem injective_iff_bijective {f : α → α} : Injective f ↔ Bijective f := by
  simp [Bijective, injective_iff_surjective]

theorem surjective_iff_bijective {f : α → α} : Surjective f ↔ Bijective f := by
  simp [Bijective, injective_iff_surjective]

theorem injective_iff_surjective_of_equiv {f : α → β} (e : α ≃ β) : Injective f ↔ Surjective f :=
  have : Injective (e.symm ∘ f) ↔ Surjective (e.symm ∘ f) := injective_iff_surjective
  ⟨fun hinj => by
    simpa [Function.comp] using e.surjective.comp (this.1 (e.symm.injective.comp hinj)),
    fun hsurj => by
    simpa [Function.comp] using e.injective.comp (this.2 (e.symm.surjective.comp hsurj))⟩

alias ⟨_root_.Function.Injective.bijective_of_finite, _⟩ := injective_iff_bijective

alias ⟨_root_.Function.Surjective.bijective_of_finite, _⟩ := surjective_iff_bijective

alias ⟨_root_.Function.Injective.surjective_of_fintype,
    _root_.Function.Surjective.injective_of_fintype⟩ :=
  injective_iff_surjective_of_equiv

end Finite

namespace Fintype

variable [Fintype α] [Fintype β]

theorem bijective_iff_injective_and_card (f : α → β) :
    Bijective f ↔ Injective f ∧ card α = card β :=
  ⟨fun h => ⟨h.1, card_of_bijective h⟩, fun h =>
    ⟨h.1, h.1.surjective_of_fintype <| equivOfCardEq h.2⟩⟩

theorem bijective_iff_surjective_and_card (f : α → β) :
    Bijective f ↔ Surjective f ∧ card α = card β :=
  ⟨fun h => ⟨h.2, card_of_bijective h⟩, fun h =>
    ⟨h.1.injective_of_fintype <| equivOfCardEq h.2, h.1⟩⟩

theorem _root_.Function.LeftInverse.rightInverse_of_card_le {f : α → β} {g : β → α}
    (hfg : LeftInverse f g) (hcard : card α ≤ card β) : RightInverse f g :=
  have hsurj : Surjective f := surjective_iff_hasRightInverse.2 ⟨g, hfg⟩
  rightInverse_of_injective_of_leftInverse
    ((bijective_iff_surjective_and_card _).2
        ⟨hsurj, le_antisymm hcard (card_le_of_surjective f hsurj)⟩).1
    hfg

theorem _root_.Function.RightInverse.leftInverse_of_card_le {f : α → β} {g : β → α}
    (hfg : RightInverse f g) (hcard : card β ≤ card α) : LeftInverse f g :=
  Function.LeftInverse.rightInverse_of_card_le hfg hcard

end Fintype

namespace Equiv

variable [Fintype α] [Fintype β]

open Fintype

/-- Construct an equivalence from functions that are inverse to each other. -/
@[simps]
def ofLeftInverseOfCardLE (hβα : card β ≤ card α) (f : α → β) (g : β → α) (h : LeftInverse g f) :
    α ≃ β where
  toFun := f
  invFun := g
  left_inv := h
  right_inv := h.rightInverse_of_card_le hβα

/-- Construct an equivalence from functions that are inverse to each other. -/
@[simps]
def ofRightInverseOfCardLE (hαβ : card α ≤ card β) (f : α → β) (g : β → α) (h : RightInverse g f) :
    α ≃ β where
  toFun := f
  invFun := g
  left_inv := h.leftInverse_of_card_le hαβ
  right_inv := h

end Equiv

@[simp]
theorem Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.card s = #s :=
  @Fintype.card_of_finset' _ _ _ (fun _ => Iff.rfl) (id _)

/-- Noncomputable equivalence between a finset `s` coerced to a type and `Fin #s`. -/
noncomputable def Finset.equivFin (s : Finset α) : s ≃ Fin #s :=
  Fintype.equivFinOfCardEq (Fintype.card_coe _)

/-- Noncomputable equivalence between a finset `s` as a fintype and `Fin n`, when there is a
proof that `#s = n`. -/
noncomputable def Finset.equivFinOfCardEq {s : Finset α} {n : ℕ} (h : #s = n) : s ≃ Fin n :=
  Fintype.equivFinOfCardEq ((Fintype.card_coe _).trans h)

theorem Finset.card_eq_of_equiv_fin {s : Finset α} {n : ℕ} (i : s ≃ Fin n) : #s = n :=
  Fin.equiv_iff_eq.1 ⟨s.equivFin.symm.trans i⟩

theorem Finset.card_eq_of_equiv_fintype {s : Finset α} [Fintype β] (i : s ≃ β) :
    #s = Fintype.card β := card_eq_of_equiv_fin <| i.trans <| Fintype.equivFin β

/-- Noncomputable equivalence between two finsets `s` and `t` as fintypes when there is a proof
that `#s = #t`. -/
noncomputable def Finset.equivOfCardEq {s : Finset α} {t : Finset β} (h : #s = #t) :
    s ≃ t := Fintype.equivOfCardEq ((Fintype.card_coe _).trans (h.trans (Fintype.card_coe _).symm))

theorem Finset.card_eq_of_equiv {s : Finset α} {t : Finset β} (i : s ≃ t) : #s = #t :=
  (card_eq_of_equiv_fintype i).trans (Fintype.card_coe _)

/-- We can inflate a set `s` to any bigger size. -/
lemma Finset.exists_superset_card_eq [Fintype α] {n : ℕ} {s : Finset α} (hsn : #s ≤ n)
    (hnα : n ≤ Fintype.card α) :
    ∃ t, s ⊆ t ∧ #t = n := by simpa using exists_subsuperset_card_eq s.subset_univ hsn hnα

@[simp]
theorem Fintype.card_prop : Fintype.card Prop = 2 :=
  rfl

theorem set_fintype_card_le_univ [Fintype α] (s : Set α) [Fintype s] :
    Fintype.card s ≤ Fintype.card α :=
  Fintype.card_le_of_embedding (Function.Embedding.subtype s)

theorem set_fintype_card_eq_univ_iff [Fintype α] (s : Set α) [Fintype s] :
    Fintype.card s = Fintype.card α ↔ s = Set.univ := by
  rw [← Set.toFinset_card, Finset.card_eq_iff_eq_univ, ← Set.toFinset_univ, Set.toFinset_inj]

namespace Function.Embedding

/-- An embedding from a `Fintype` to itself can be promoted to an equivalence. -/
noncomputable def equivOfFiniteSelfEmbedding [Finite α] (e : α ↪ α) : α ≃ α :=
  Equiv.ofBijective e e.2.bijective_of_finite

@[deprecated (since := "2024-12-05")]
alias equivOfFintypeSelfEmbedding := equivOfFiniteSelfEmbedding

@[simp]
theorem toEmbedding_equivOfFiniteSelfEmbedding [Finite α] (e : α ↪ α) :
    e.equivOfFiniteSelfEmbedding.toEmbedding = e := by
  ext
  rfl

@[deprecated (since := "2024-12-05")]
alias equiv_of_fintype_self_embedding_to_embedding := toEmbedding_equivOfFiniteSelfEmbedding

/-- On a finite type, equivalence between the self-embeddings and the bijections. -/
@[simps] noncomputable def _root_.Equiv.embeddingEquivOfFinite (α : Type*) [Finite α] :
    (α ↪ α) ≃ (α ≃ α) where
  toFun e := e.equivOfFiniteSelfEmbedding
  invFun e := e.toEmbedding
  left_inv e := rfl
  right_inv e := by ext; rfl

/-- If `‖β‖ < ‖α‖` there are no embeddings `α ↪ β`.
This is a formulation of the pigeonhole principle.

Note this cannot be an instance as it needs `h`. -/
@[simp]
theorem isEmpty_of_card_lt [Fintype α] [Fintype β] (h : Fintype.card β < Fintype.card α) :
    IsEmpty (α ↪ β) :=
  ⟨fun f =>
    let ⟨_x, _y, ne, feq⟩ := Fintype.exists_ne_map_eq_of_card_lt f h
    ne <| f.injective feq⟩

/-- A constructive embedding of a fintype `α` in another fintype `β` when `card α ≤ card β`. -/
def truncOfCardLE [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (h : Fintype.card α ≤ Fintype.card β) : Trunc (α ↪ β) :=
  (Fintype.truncEquivFin α).bind fun ea =>
    (Fintype.truncEquivFin β).map fun eb =>
      ea.toEmbedding.trans ((Fin.castLEEmb h).trans eb.symm.toEmbedding)

theorem nonempty_of_card_le [Fintype α] [Fintype β] (h : Fintype.card α ≤ Fintype.card β) :
    Nonempty (α ↪ β) := by classical exact (truncOfCardLE h).nonempty

theorem nonempty_iff_card_le [Fintype α] [Fintype β] :
    Nonempty (α ↪ β) ↔ Fintype.card α ≤ Fintype.card β :=
  ⟨fun ⟨e⟩ => Fintype.card_le_of_embedding e, nonempty_of_card_le⟩

theorem exists_of_card_le_finset [Fintype α] {s : Finset β} (h : Fintype.card α ≤ #s) :
    ∃ f : α ↪ β, Set.range f ⊆ s := by
  rw [← Fintype.card_coe] at h
  rcases nonempty_of_card_le h with ⟨f⟩
  exact ⟨f.trans (Embedding.subtype _), by simp [Set.range_subset_iff]⟩

end Function.Embedding

@[simp]
theorem Finset.univ_map_embedding {α : Type*} [Fintype α] (e : α ↪ α) : univ.map e = univ := by
  rw [← e.toEmbedding_equivOfFiniteSelfEmbedding, univ_map_equiv_to_embedding]

namespace Fintype

theorem card_lt_of_surjective_not_injective [Fintype α] [Fintype β] (f : α → β)
    (h : Function.Surjective f) (h' : ¬Function.Injective f) : card β < card α :=
  card_lt_of_injective_not_surjective _ (Function.injective_surjInv h) fun hg =>
    have w : Function.Bijective (Function.surjInv h) := ⟨Function.injective_surjInv h, hg⟩
    h' <| h.injective_of_fintype (Equiv.ofBijective _ w).symm

end Fintype

theorem Fintype.card_subtype_le [Fintype α] (p : α → Prop) [DecidablePred p] :
    Fintype.card { x // p x } ≤ Fintype.card α :=
  Fintype.card_le_of_embedding (Function.Embedding.subtype _)

theorem Fintype.card_subtype_lt [Fintype α] {p : α → Prop} [DecidablePred p] {x : α} (hx : ¬p x) :
    Fintype.card { x // p x } < Fintype.card α :=
  Fintype.card_lt_of_injective_of_not_mem (b := x) (↑) Subtype.coe_injective <| by
    rwa [Subtype.range_coe_subtype]

theorem Fintype.card_subtype [Fintype α] (p : α → Prop) [DecidablePred p] :
    Fintype.card { x // p x } = #{x | p x} := by
  refine Fintype.card_of_subtype _ ?_
  simp

@[simp]
theorem Fintype.card_subtype_compl [Fintype α] (p : α → Prop) [Fintype { x // p x }]
    [Fintype { x // ¬p x }] :
    Fintype.card { x // ¬p x } = Fintype.card α - Fintype.card { x // p x } := by
  classical
    rw [Fintype.card_of_subtype (Set.toFinset { x | p x }ᶜ), Set.toFinset_compl,
      Finset.card_compl, Fintype.card_of_subtype] <;>
    · intro
      simp only [Set.mem_toFinset, Set.mem_compl_iff, Set.mem_setOf]

theorem Fintype.card_subtype_mono (p q : α → Prop) (h : p ≤ q) [Fintype { x // p x }]
    [Fintype { x // q x }] : Fintype.card { x // p x } ≤ Fintype.card { x // q x } :=
  Fintype.card_le_of_embedding (Subtype.impEmbedding _ _ h)

/-- If two subtypes of a fintype have equal cardinality, so do their complements. -/
theorem Fintype.card_compl_eq_card_compl [Finite α] (p q : α → Prop) [Fintype { x // p x }]
    [Fintype { x // ¬p x }] [Fintype { x // q x }] [Fintype { x // ¬q x }]
    (h : Fintype.card { x // p x } = Fintype.card { x // q x }) :
    Fintype.card { x // ¬p x } = Fintype.card { x // ¬q x } := by
  cases nonempty_fintype α
  simp only [Fintype.card_subtype_compl, h]

theorem Fintype.card_quotient_le [Fintype α] (s : Setoid α)
    [DecidableRel ((· ≈ ·) : α → α → Prop)] : Fintype.card (Quotient s) ≤ Fintype.card α :=
  Fintype.card_le_of_surjective _ Quotient.mk'_surjective

theorem Fintype.card_quotient_lt [Fintype α] {s : Setoid α} [DecidableRel ((· ≈ ·) : α → α → Prop)]
    {x y : α} (h1 : x ≠ y) (h2 : x ≈ y) : Fintype.card (Quotient s) < Fintype.card α :=
  Fintype.card_lt_of_surjective_not_injective _ Quotient.mk'_surjective fun w =>
    h1 (w <| Quotient.eq.mpr h2)

theorem univ_eq_singleton_of_card_one {α} [Fintype α] (x : α) (h : Fintype.card α = 1) :
    (univ : Finset α) = {x} := by
  symm
  apply eq_of_subset_of_card_le (subset_univ {x})
  apply le_of_eq
  simp [h, Finset.card_univ]

namespace Finite

variable [Finite α]

theorem wellFounded_of_trans_of_irrefl (r : α → α → Prop) [IsTrans α r] [IsIrrefl α r] :
    WellFounded r := by
  classical
  cases nonempty_fintype α
  have (x y) (hxy : r x y) : #{z | r z x} < #{z | r z y} :=
    Finset.card_lt_card <| by
      simp only [Finset.lt_iff_ssubset.symm, lt_iff_le_not_le, Finset.le_iff_subset,
          Finset.subset_iff, mem_filter, true_and, mem_univ, hxy]
      exact
        ⟨fun z hzx => _root_.trans hzx hxy,
          not_forall_of_exists_not ⟨x, Classical.not_imp.2 ⟨hxy, irrefl x⟩⟩⟩
  exact Subrelation.wf (this _ _) (measure _).wf

-- See note [lower instance priority]
instance (priority := 100) to_wellFoundedLT [Preorder α] : WellFoundedLT α :=
  ⟨wellFounded_of_trans_of_irrefl _⟩

-- See note [lower instance priority]
instance (priority := 100) to_wellFoundedGT [Preorder α] : WellFoundedGT α :=
  ⟨wellFounded_of_trans_of_irrefl _⟩

end Finite

-- Shortcut instances to make sure those are found even in the presence of other instances
-- See https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/WellFoundedLT.20Prop.20is.20not.20found.20when.20importing.20too.20much
instance Bool.instWellFoundedLT : WellFoundedLT Bool := inferInstance
instance Bool.instWellFoundedGT : WellFoundedGT Bool := inferInstance
instance Prop.instWellFoundedLT : WellFoundedLT Prop := inferInstance
instance Prop.instWellFoundedGT : WellFoundedGT Prop := inferInstance

-- @[nolint fintype_finite] -- Porting note: do we need this?
protected theorem Fintype.false [Infinite α] (_h : Fintype α) : False :=
  not_finite α

@[simp]
theorem isEmpty_fintype {α : Type*} : IsEmpty (Fintype α) ↔ Infinite α :=
  ⟨fun ⟨h⟩ => ⟨fun h' => (@nonempty_fintype α h').elim h⟩, fun ⟨h⟩ => ⟨fun h' => h h'.finite⟩⟩

/-- A non-infinite type is a fintype. -/
noncomputable def fintypeOfNotInfinite {α : Type*} (h : ¬Infinite α) : Fintype α :=
  @Fintype.ofFinite _ (not_infinite_iff_finite.mp h)

section

open scoped Classical in
/-- Any type is (classically) either a `Fintype`, or `Infinite`.

One can obtain the relevant typeclasses via `cases fintypeOrInfinite α`.
-/
noncomputable def fintypeOrInfinite (α : Type*) : Fintype α ⊕' Infinite α :=
  if h : Infinite α then PSum.inr h else PSum.inl (fintypeOfNotInfinite h)

end

theorem Finset.exists_minimal {α : Type*} [Preorder α] (s : Finset α) (h : s.Nonempty) :
    ∃ m ∈ s, ∀ x ∈ s, ¬x < m := by
  obtain ⟨c, hcs : c ∈ s⟩ := h
  have : WellFounded (@LT.lt { x // x ∈ s } _) := Finite.wellFounded_of_trans_of_irrefl _
  obtain ⟨⟨m, hms : m ∈ s⟩, -, H⟩ := this.has_min Set.univ ⟨⟨c, hcs⟩, trivial⟩
  exact ⟨m, hms, fun x hx hxm => H ⟨x, hx⟩ trivial hxm⟩

theorem Finset.exists_maximal {α : Type*} [Preorder α] (s : Finset α) (h : s.Nonempty) :
    ∃ m ∈ s, ∀ x ∈ s, ¬m < x :=
  @Finset.exists_minimal αᵒᵈ _ s h

namespace Infinite

theorem of_not_fintype (h : Fintype α → False) : Infinite α :=
  isEmpty_fintype.mp ⟨h⟩

/-- If `s : Set α` is a proper subset of `α` and `f : α → s` is injective, then `α` is infinite. -/
theorem of_injective_to_set {s : Set α} (hs : s ≠ Set.univ) {f : α → s} (hf : Injective f) :
    Infinite α :=
  of_not_fintype fun h => by
    classical
      refine lt_irrefl (Fintype.card α) ?_
      calc
        Fintype.card α ≤ Fintype.card s := Fintype.card_le_of_injective f hf
        _ = #s.toFinset := s.toFinset_card.symm
        _ < Fintype.card α :=
          Finset.card_lt_card <| by rwa [Set.toFinset_ssubset_univ, Set.ssubset_univ_iff]

/-- If `s : Set α` is a proper subset of `α` and `f : s → α` is surjective, then `α` is infinite. -/
theorem of_surjective_from_set {s : Set α} (hs : s ≠ Set.univ) {f : s → α} (hf : Surjective f) :
    Infinite α :=
  of_injective_to_set hs (injective_surjInv hf)

theorem exists_not_mem_finset [Infinite α] (s : Finset α) : ∃ x, x ∉ s :=
  not_forall.1 fun h => Fintype.false ⟨s, h⟩

-- see Note [lower instance priority]
instance (priority := 100) (α : Type*) [Infinite α] : Nontrivial α :=
  ⟨let ⟨x, _hx⟩ := exists_not_mem_finset (∅ : Finset α)
    let ⟨y, hy⟩ := exists_not_mem_finset ({x} : Finset α)
    ⟨y, x, by simpa only [mem_singleton] using hy⟩⟩

protected theorem nonempty (α : Type*) [Infinite α] : Nonempty α := by infer_instance

theorem of_injective {α β} [Infinite β] (f : β → α) (hf : Injective f) : Infinite α :=
  ⟨fun _I => (Finite.of_injective f hf).false⟩

theorem of_surjective {α β} [Infinite β] (f : α → β) (hf : Surjective f) : Infinite α :=
  ⟨fun _I => (Finite.of_surjective f hf).false⟩

instance {β : α → Type*} [Infinite α] [∀ a, Nonempty (β a)] : Infinite ((a : α) × β a) :=
  Infinite.of_surjective Sigma.fst Sigma.fst_surjective

theorem sigma_of_right {β : α → Type*} {a : α} [Infinite (β a)] :
    Infinite ((a : α) × β a) :=
  Infinite.of_injective (f := fun x ↦ ⟨a,x⟩) fun _ _ ↦ by simp

instance {β : α → Type*} [Nonempty α] [∀ a, Infinite (β a)] : Infinite ((a : α) × β a) :=
  Infinite.sigma_of_right (a := Classical.arbitrary α)

end Infinite

instance : Infinite ℕ :=
  Infinite.of_not_fintype <| by
    intro h
    exact (Finset.range _).card_le_univ.not_lt ((Nat.lt_succ_self _).trans_eq (card_range _).symm)

instance Int.infinite : Infinite ℤ :=
  Infinite.of_injective Int.ofNat fun _ _ => Int.ofNat.inj

instance [Nonempty α] : Infinite (Multiset α) :=
  let ⟨x⟩ := ‹Nonempty α›
  Infinite.of_injective (fun n => Multiset.replicate n x) (Multiset.replicate_left_injective _)

instance [Nonempty α] : Infinite (List α) :=
  Infinite.of_surjective ((↑) : List α → Multiset α) Quot.mk_surjective

instance String.infinite : Infinite String :=
  Infinite.of_injective (String.mk) <| by
    intro _ _ h
    cases h with
    | refl => rfl

instance Infinite.set [Infinite α] : Infinite (Set α) :=
  Infinite.of_injective singleton Set.singleton_injective

instance [Infinite α] : Infinite (Finset α) :=
  Infinite.of_injective singleton Finset.singleton_injective

instance [Infinite α] : Infinite (Option α) :=
  Infinite.of_injective some (Option.some_injective α)

instance Sum.infinite_of_left [Infinite α] : Infinite (α ⊕ β) :=
  Infinite.of_injective Sum.inl Sum.inl_injective

instance Sum.infinite_of_right [Infinite β] : Infinite (α ⊕ β) :=
  Infinite.of_injective Sum.inr Sum.inr_injective

instance Prod.infinite_of_right [Nonempty α] [Infinite β] : Infinite (α × β) :=
  Infinite.of_surjective Prod.snd Prod.snd_surjective

instance Prod.infinite_of_left [Infinite α] [Nonempty β] : Infinite (α × β) :=
  Infinite.of_surjective Prod.fst Prod.fst_surjective

instance instInfiniteProdSubtypeCommute [Mul α] [Infinite α] :
    Infinite { p : α × α // Commute p.1 p.2 } :=
  Infinite.of_injective (fun a => ⟨⟨a, a⟩, rfl⟩) (by intro; simp)

namespace Infinite

private noncomputable def natEmbeddingAux (α : Type*) [Infinite α] : ℕ → α
  | n =>
    letI := Classical.decEq α
    Classical.choose
      (exists_not_mem_finset
        ((Multiset.range n).pmap (fun m (_ : m < n) => natEmbeddingAux _ m) fun _ =>
            Multiset.mem_range.1).toFinset)

private theorem natEmbeddingAux_injective (α : Type*) [Infinite α] :
    Function.Injective (natEmbeddingAux α) := by
  rintro m n h
  letI := Classical.decEq α
  wlog hmlen : m ≤ n generalizing m n
  · exact (this h.symm <| le_of_not_le hmlen).symm
  by_contra hmn
  have hmn : m < n := lt_of_le_of_ne hmlen hmn
  refine (Classical.choose_spec (exists_not_mem_finset
    ((Multiset.range n).pmap (fun m (_ : m < n) ↦ natEmbeddingAux α m)
      (fun _ ↦ Multiset.mem_range.1)).toFinset)) ?_
  refine Multiset.mem_toFinset.2 (Multiset.mem_pmap.2 ⟨m, Multiset.mem_range.2 hmn, ?_⟩)
  rw [h, natEmbeddingAux]

/-- Embedding of `ℕ` into an infinite type. -/
noncomputable def natEmbedding (α : Type*) [Infinite α] : ℕ ↪ α :=
  ⟨_, natEmbeddingAux_injective α⟩

/-- See `Infinite.exists_superset_card_eq` for a version that, for an `s : Finset α`,
provides a superset `t : Finset α`, `s ⊆ t` such that `#t` is fixed. -/
theorem exists_subset_card_eq (α : Type*) [Infinite α] (n : ℕ) : ∃ s : Finset α, #s = n :=
  ⟨(range n).map (natEmbedding α), by rw [card_map, card_range]⟩

/-- See `Infinite.exists_subset_card_eq` for a version that provides an arbitrary
`s : Finset α` for any cardinality. -/
theorem exists_superset_card_eq [Infinite α] (s : Finset α) (n : ℕ) (hn : #s ≤ n) :
    ∃ t : Finset α, s ⊆ t ∧ #t = n := by
  induction' n with n IH generalizing s
  · exact ⟨s, subset_refl _, Nat.eq_zero_of_le_zero hn⟩
  · rcases hn.eq_or_lt with hn' | hn'
    · exact ⟨s, subset_refl _, hn'⟩
    obtain ⟨t, hs, ht⟩ := IH _ (Nat.le_of_lt_succ hn')
    obtain ⟨x, hx⟩ := exists_not_mem_finset t
    refine ⟨Finset.cons x t hx, hs.trans (Finset.subset_cons _), ?_⟩
    simp [hx, ht]

end Infinite

/-- If every finset in a type has bounded cardinality, that type is finite. -/
noncomputable def fintypeOfFinsetCardLe {ι : Type*} (n : ℕ) (w : ∀ s : Finset ι, #s ≤ n) :
    Fintype ι := by
  apply fintypeOfNotInfinite
  intro i
  obtain ⟨s, c⟩ := Infinite.exists_subset_card_eq ι (n + 1)
  specialize w s
  rw [c] at w
  exact Nat.not_succ_le_self n w

theorem not_injective_infinite_finite {α β} [Infinite α] [Finite β] (f : α → β) : ¬Injective f :=
  fun hf => (Finite.of_injective f hf).false

/-- The pigeonhole principle for infinitely many pigeons in finitely many pigeonholes. If there are
infinitely many pigeons in finitely many pigeonholes, then there are at least two pigeons in the
same pigeonhole.

See also: `Fintype.exists_ne_map_eq_of_card_lt`, `Finite.exists_infinite_fiber`.
-/
theorem Finite.exists_ne_map_eq_of_infinite {α β} [Infinite α] [Finite β] (f : α → β) :
    ∃ x y : α, x ≠ y ∧ f x = f y := by
  simpa [Injective, and_comm] using not_injective_infinite_finite f

instance Function.Embedding.is_empty {α β} [Infinite α] [Finite β] : IsEmpty (α ↪ β) :=
  ⟨fun f => not_injective_infinite_finite f f.2⟩

/-- The strong pigeonhole principle for infinitely many pigeons in
finitely many pigeonholes.  If there are infinitely many pigeons in
finitely many pigeonholes, then there is a pigeonhole with infinitely
many pigeons.

See also: `Finite.exists_ne_map_eq_of_infinite`
-/
theorem Finite.exists_infinite_fiber [Infinite α] [Finite β] (f : α → β) :
    ∃ y : β, Infinite (f ⁻¹' {y}) := by
  classical
    by_contra! hf
    cases nonempty_fintype β
    haveI := fun y => fintypeOfNotInfinite <| hf y
    let key : Fintype α :=
      { elems := univ.biUnion fun y : β => (f ⁻¹' {y}).toFinset
        complete := by simp }
    exact key.false

theorem not_surjective_finite_infinite {α β} [Finite α] [Infinite β] (f : α → β) : ¬Surjective f :=
  fun hf => (Infinite.of_surjective f hf).not_finite ‹_›

section Ranges

/-- For any `c : List ℕ` whose sum is at most `Fintype.card α`,
  we can find `o : List (List α)` whose members have no duplicate,
  whose lengths given by `c`, and which are pairwise disjoint -/
theorem List.exists_pw_disjoint_with_card {α : Type*} [Fintype α]
    {c : List ℕ} (hc : c.sum ≤ Fintype.card α) :
    ∃ o : List (List α),
      o.map length = c ∧ (∀ s ∈ o, s.Nodup) ∧ Pairwise List.Disjoint o := by
  let klift (n : ℕ) (hn : n < Fintype.card α) : Fin (Fintype.card α) :=
    (⟨n, hn⟩ : Fin (Fintype.card α))
  let klift' (l : List ℕ) (hl : ∀ a ∈ l, a < Fintype.card α) :
    List (Fin (Fintype.card α)) := List.pmap klift l hl
  have hc'_lt : ∀ l ∈ c.ranges, ∀ n ∈ l, n < Fintype.card α := by
    intro l hl n hn
    apply lt_of_lt_of_le _ hc
    rw [← mem_mem_ranges_iff_lt_sum]
    exact ⟨l, hl, hn⟩
  let l := (ranges c).pmap klift' hc'_lt
  have hl : ∀ (a : List ℕ) (ha : a ∈ c.ranges),
    (klift' a (hc'_lt a ha)).map Fin.valEmbedding = a := by
    intro a ha
    conv_rhs => rw [← List.map_id a]
    rw [List.map_pmap]
    simp [klift, Fin.valEmbedding_apply, Fin.val_mk, List.pmap_eq_map, List.map_id']
  use l.map (List.map (Fintype.equivFin α).symm)
  constructor
  · -- length
    rw [← ranges_length c]
    simp only [l, klift', map_map, map_pmap, Function.comp_apply, length_map, length_pmap,
      pmap_eq_map]
  constructor
  · -- nodup
    intro s
    rw [mem_map]
    rintro ⟨t, ht, rfl⟩
    apply Nodup.map (Equiv.injective _)
    obtain ⟨u, hu, rfl⟩ := mem_pmap.mp ht
    apply Nodup.of_map
    rw [hl u hu]
    exact ranges_nodup hu
  · -- pairwise disjoint
    refine Pairwise.map _ (fun s t ↦ disjoint_map (Equiv.injective _)) ?_
    -- List.Pairwise List.disjoint l
    apply Pairwise.pmap (List.ranges_disjoint c)
    intro u hu v hv huv
    apply disjoint_pmap
    · intro a a' ha ha' h
      simpa only [klift, Fin.mk_eq_mk] using h
    exact huv

end Ranges

section Trunc

/-- A `Fintype` with positive cardinality constructively contains an element.
-/
def truncOfCardPos {α} [Fintype α] (h : 0 < Fintype.card α) : Trunc α :=
  letI := Fintype.card_pos_iff.mp h
  truncOfNonemptyFintype α

end Trunc

/-- A custom induction principle for fintypes. The base case is a subsingleton type,
and the induction step is for non-trivial types, and one can assume the hypothesis for
smaller types (via `Fintype.card`).

The major premise is `Fintype α`, so to use this with the `induction` tactic you have to give a name
to that instance and use that name.
-/
@[elab_as_elim]
theorem Fintype.induction_subsingleton_or_nontrivial {P : ∀ (α) [Fintype α], Prop} (α : Type*)
    [Fintype α] (hbase : ∀ (α) [Fintype α] [Subsingleton α], P α)
    (hstep : ∀ (α) [Fintype α] [Nontrivial α],
      (∀ (β) [Fintype β], Fintype.card β < Fintype.card α → P β) → P α) :
    P α := by
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card α = n := ⟨Fintype.card α, rfl⟩
  induction' n using Nat.strong_induction_on with n ih generalizing α
  cases' subsingleton_or_nontrivial α with hsing hnontriv
  · apply hbase
  · apply hstep
    intro β _ hlt
    rw [hn] at hlt
    exact ih (Fintype.card β) hlt _ rfl
