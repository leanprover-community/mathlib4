/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Tactic.Positivity

#align_import data.fintype.card from "leanprover-community/mathlib"@"bf2428c9486c407ca38b5b3fb10b87dad0bc99fa"

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


open Function

open Nat

universe u v

variable {α β γ : Type*}

open Finset Function

namespace Fintype

/-- `card α` is the number of elements in `α`, defined when `α` is a fintype. -/
def card (α) [Fintype α] : ℕ :=
  (@univ α _).card
#align fintype.card Fintype.card

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
  -- ⊢ Trunc (α ≃ Fin (↑Multiset.card univ.val))
  exact
    Quot.recOnSubsingleton'
      (motive := fun s : Multiset α =>
        (∀ x : α, x ∈ s) → s.Nodup → Trunc (α ≃ Fin (Multiset.card s)))
      univ.val
      (fun l (h : ∀ x : α, x ∈ l) (nd : l.Nodup) => Trunc.mk (nd.getEquivOfForallMemList _ h).symm)
      mem_univ_val univ.2
#align fintype.trunc_equiv_fin Fintype.truncEquivFin

/-- There is (noncomputably) an equivalence between `α` and `Fin (card α)`.

See `Fintype.truncEquivFin` for the computable version,
and `Fintype.truncEquivFinOfCardEq` and `Fintype.equivFinOfCardEq`
for an equiv `α ≃ Fin n` given `Fintype.card α = n`.
-/
noncomputable def equivFin (α) [Fintype α] : α ≃ Fin (card α) :=
  letI := Classical.decEq α
  (truncEquivFin α).out
#align fintype.equiv_fin Fintype.equivFin

/-- There is (computably) a bijection between `Fin (card α)` and `α`.

Since it is not unique and depends on which permutation
of the universe list is used, the bijection is wrapped in `Trunc` to
preserve computability.

See `Fintype.truncEquivFin` for a version that gives an equivalence
given `[DecidableEq α]`.
-/
def truncFinBijection (α) [Fintype α] : Trunc { f : Fin (card α) → α // Bijective f } := by
  unfold card Finset.card
  -- ⊢ Trunc { f // Bijective f }
  refine
    Quot.recOnSubsingleton'
      (motive := fun s : Multiset α =>
        (∀ x : α, x ∈ s) → s.Nodup → Trunc {f : Fin (Multiset.card s) → α // Bijective f})
      univ.val
      (fun l (h : ∀ x : α, x ∈ l) (nd : l.Nodup) => Trunc.mk (nd.getBijectionOfForallMemList _ h))
      mem_univ_val univ.2
#align fintype.trunc_fin_bijection Fintype.truncFinBijection

theorem subtype_card {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x) :
    @card { x // p x } (Fintype.subtype s H) = s.card :=
  Multiset.card_pmap _ _ _
#align fintype.subtype_card Fintype.subtype_card

theorem card_of_subtype {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x)
    [Fintype { x // p x }] : card { x // p x } = s.card := by
  rw [← subtype_card s H]
  -- ⊢ card { x // p x } = card { x // p x }
  congr
  -- ⊢ inst✝ = Fintype.subtype s H
  apply Subsingleton.elim
  -- 🎉 no goals
#align fintype.card_of_subtype Fintype.card_of_subtype

@[simp]
theorem card_ofFinset {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) :
    @Fintype.card p (ofFinset s H) = s.card :=
  Fintype.subtype_card s H
#align fintype.card_of_finset Fintype.card_ofFinset

theorem card_of_finset' {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) [Fintype p] :
    Fintype.card p = s.card := by rw [← card_ofFinset s H]; congr; apply Subsingleton.elim
                                  -- ⊢ card ↑p = card ↑p
                                                            -- ⊢ inst✝ = ofFinset s H
                                                                   -- 🎉 no goals
#align fintype.card_of_finset' Fintype.card_of_finset'

end Fintype

namespace Fintype

theorem ofEquiv_card [Fintype α] (f : α ≃ β) : @card β (ofEquiv α f) = card α :=
  Multiset.card_map _ _
#align fintype.of_equiv_card Fintype.ofEquiv_card

theorem card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β) : card α = card β := by
  rw [← ofEquiv_card f]; congr; apply Subsingleton.elim
  -- ⊢ card β = card β
                         -- ⊢ ofEquiv α f = inst✝
                                -- 🎉 no goals
#align fintype.card_congr Fintype.card_congr

@[congr]
theorem card_congr' {α β} [Fintype α] [Fintype β] (h : α = β) : card α = card β :=
  card_congr (by rw [h])
                 -- 🎉 no goals
#align fintype.card_congr' Fintype.card_congr'

section

variable [Fintype α] [Fintype β]

/-- If the cardinality of `α` is `n`, there is computably a bijection between `α` and `Fin n`.

See `Fintype.equivFinOfCardEq` for the noncomputable definition,
and `Fintype.truncEquivFin` and `Fintype.equivFin` for the bijection `α ≃ Fin (card α)`.
-/
def truncEquivFinOfCardEq [DecidableEq α] {n : ℕ} (h : Fintype.card α = n) : Trunc (α ≃ Fin n) :=
  (truncEquivFin α).map fun e => e.trans (Fin.castIso h).toEquiv
#align fintype.trunc_equiv_fin_of_card_eq Fintype.truncEquivFinOfCardEq

/-- If the cardinality of `α` is `n`, there is noncomputably a bijection between `α` and `Fin n`.

See `Fintype.truncEquivFinOfCardEq` for the computable definition,
and `Fintype.truncEquivFin` and `Fintype.equivFin` for the bijection `α ≃ Fin (card α)`.
-/
noncomputable def equivFinOfCardEq {n : ℕ} (h : Fintype.card α = n) : α ≃ Fin n :=
  letI := Classical.decEq α
  (truncEquivFinOfCardEq h).out
#align fintype.equiv_fin_of_card_eq Fintype.equivFinOfCardEq

/-- Two `Fintype`s with the same cardinality are (computably) in bijection.

See `Fintype.equivOfCardEq` for the noncomputable version,
and `Fintype.truncEquivFinOfCardEq` and `Fintype.equivFinOfCardEq` for
the specialization to `Fin`.
-/
def truncEquivOfCardEq [DecidableEq α] [DecidableEq β] (h : card α = card β) : Trunc (α ≃ β) :=
  (truncEquivFinOfCardEq h).bind fun e => (truncEquivFin β).map fun e' => e.trans e'.symm
#align fintype.trunc_equiv_of_card_eq Fintype.truncEquivOfCardEq

/-- Two `Fintype`s with the same cardinality are (noncomputably) in bijection.

See `Fintype.truncEquivOfCardEq` for the computable version,
and `Fintype.truncEquivFinOfCardEq` and `Fintype.equivFinOfCardEq` for
the specialization to `Fin`.
-/
noncomputable def equivOfCardEq (h : card α = card β) : α ≃ β := by
  letI := Classical.decEq α
  -- ⊢ α ≃ β
  letI := Classical.decEq β
  -- ⊢ α ≃ β
  exact (truncEquivOfCardEq h).out
  -- 🎉 no goals
#align fintype.equiv_of_card_eq Fintype.equivOfCardEq

end

theorem card_eq {α β} [_F : Fintype α] [_G : Fintype β] : card α = card β ↔ Nonempty (α ≃ β) :=
  ⟨fun h =>
    haveI := Classical.propDecidable
    (truncEquivOfCardEq h).nonempty,
    fun ⟨f⟩ => card_congr f⟩
#align fintype.card_eq Fintype.card_eq

/-- Note: this lemma is specifically about `Fintype.ofSubsingleton`. For a statement about
arbitrary `Fintype` instances, use either `Fintype.card_le_one_iff_subsingleton` or
`Fintype.card_unique`. -/
@[simp]
theorem card_ofSubsingleton (a : α) [Subsingleton α] : @Fintype.card _ (ofSubsingleton a) = 1 :=
  rfl
#align fintype.card_of_subsingleton Fintype.card_ofSubsingleton

@[simp]
theorem card_unique [Unique α] [h : Fintype α] : Fintype.card α = 1 :=
  Subsingleton.elim (ofSubsingleton default) h ▸ card_ofSubsingleton _
#align fintype.card_unique Fintype.card_unique

/-- Note: this lemma is specifically about `Fintype.of_is_empty`. For a statement about
arbitrary `Fintype` instances, use `Fintype.card_eq_zero_iff`. -/
@[simp]
theorem card_of_isEmpty [IsEmpty α] : Fintype.card α = 0 :=
  rfl
#align fintype.card_of_is_empty Fintype.card_of_isEmpty

end Fintype

namespace Set

variable {s t : Set α}

-- We use an arbitrary `[Fintype s]` instance here,
-- not necessarily coming from a `[Fintype α]`.
@[simp]
theorem toFinset_card {α : Type*} (s : Set α) [Fintype s] : s.toFinset.card = Fintype.card s :=
  Multiset.card_map Subtype.val Finset.univ.val
#align set.to_finset_card Set.toFinset_card

end Set

theorem Finset.card_univ [Fintype α] : (Finset.univ : Finset α).card = Fintype.card α :=
  rfl
#align finset.card_univ Finset.card_univ

theorem Finset.eq_univ_of_card [Fintype α] (s : Finset α) (hs : s.card = Fintype.card α) :
    s = univ :=
  eq_of_subset_of_card_le (subset_univ _) <| by rw [hs, Finset.card_univ]
                                                -- 🎉 no goals
#align finset.eq_univ_of_card Finset.eq_univ_of_card

theorem Finset.card_eq_iff_eq_univ [Fintype α] (s : Finset α) :
    s.card = Fintype.card α ↔ s = Finset.univ :=
  ⟨s.eq_univ_of_card, by
    rintro rfl
    -- ⊢ card univ = Fintype.card α
    exact Finset.card_univ⟩
    -- 🎉 no goals
#align finset.card_eq_iff_eq_univ Finset.card_eq_iff_eq_univ

theorem Finset.card_le_univ [Fintype α] (s : Finset α) : s.card ≤ Fintype.card α :=
  card_le_of_subset (subset_univ s)
#align finset.card_le_univ Finset.card_le_univ

theorem Finset.card_lt_univ_of_not_mem [Fintype α] {s : Finset α} {x : α} (hx : x ∉ s) :
    s.card < Fintype.card α :=
  card_lt_card ⟨subset_univ s, not_forall.2 ⟨x, fun hx' => hx (hx' <| mem_univ x)⟩⟩
#align finset.card_lt_univ_of_not_mem Finset.card_lt_univ_of_not_mem

theorem Finset.card_lt_iff_ne_univ [Fintype α] (s : Finset α) :
    s.card < Fintype.card α ↔ s ≠ Finset.univ :=
  s.card_le_univ.lt_iff_ne.trans (not_congr s.card_eq_iff_eq_univ)
#align finset.card_lt_iff_ne_univ Finset.card_lt_iff_ne_univ

theorem Finset.card_compl_lt_iff_nonempty [Fintype α] [DecidableEq α] (s : Finset α) :
    sᶜ.card < Fintype.card α ↔ s.Nonempty :=
  sᶜ.card_lt_iff_ne_univ.trans s.compl_ne_univ_iff_nonempty
#align finset.card_compl_lt_iff_nonempty Finset.card_compl_lt_iff_nonempty

theorem Finset.card_univ_diff [DecidableEq α] [Fintype α] (s : Finset α) :
    (Finset.univ \ s).card = Fintype.card α - s.card :=
  Finset.card_sdiff (subset_univ s)
#align finset.card_univ_diff Finset.card_univ_diff

theorem Finset.card_compl [DecidableEq α] [Fintype α] (s : Finset α) :
    sᶜ.card = Fintype.card α - s.card :=
  Finset.card_univ_diff s
#align finset.card_compl Finset.card_compl

theorem Fintype.card_compl_set [Fintype α] (s : Set α) [Fintype s] [Fintype (↥sᶜ : Sort _)] :
    Fintype.card (↥sᶜ : Sort _) = Fintype.card α - Fintype.card s := by
  classical rw [← Set.toFinset_card, ← Set.toFinset_card, ← Finset.card_compl, Set.toFinset_compl]
  -- 🎉 no goals
#align fintype.card_compl_set Fintype.card_compl_set

@[simp]
theorem Fintype.card_fin (n : ℕ) : Fintype.card (Fin n) = n :=
  List.length_finRange n
#align fintype.card_fin Fintype.card_fin

@[simp]
theorem Finset.card_fin (n : ℕ) : Finset.card (Finset.univ : Finset (Fin n)) = n := by
  rw [Finset.card_univ, Fintype.card_fin]
  -- 🎉 no goals
#align finset.card_fin Finset.card_fin

/-- `Fin` as a map from `ℕ` to `Type` is injective. Note that since this is a statement about
equality of types, using it should be avoided if possible. -/
theorem fin_injective : Function.Injective Fin := fun m n h =>
  (Fintype.card_fin m).symm.trans <| (Fintype.card_congr <| Equiv.cast h).trans (Fintype.card_fin n)
#align fin_injective fin_injective

/-- A reversed version of `Fin.cast_eq_cast` that is easier to rewrite with. -/
theorem Fin.cast_eq_cast' {n m : ℕ} (h : Fin n = Fin m) :
    _root_.cast h = ⇑(Fin.castIso <| fin_injective h) := by
  cases fin_injective h
  -- ⊢ _root_.cast h = ↑(castIso (_ : n = n))
  rfl
  -- 🎉 no goals
#align fin.cast_eq_cast' Fin.cast_eq_cast'

theorem card_finset_fin_le {n : ℕ} (s : Finset (Fin n)) : s.card ≤ n := by
  simpa only [Fintype.card_fin] using s.card_le_univ
  -- 🎉 no goals
#align card_finset_fin_le card_finset_fin_le

theorem Fin.equiv_iff_eq {m n : ℕ} : Nonempty (Fin m ≃ Fin n) ↔ m = n :=
  ⟨fun ⟨h⟩ => by simpa using Fintype.card_congr h, fun h => ⟨Equiv.cast <| h ▸ rfl⟩⟩
                 -- 🎉 no goals
#align fin.equiv_iff_eq Fin.equiv_iff_eq

--@[simp] Porting note: simp can prove it
theorem Fintype.card_subtype_eq (y : α) [Fintype { x // x = y }] :
    Fintype.card { x // x = y } = 1 :=
  Fintype.card_unique
#align fintype.card_subtype_eq Fintype.card_subtype_eq

--@[simp] Porting note: simp can prove it
theorem Fintype.card_subtype_eq' (y : α) [Fintype { x // y = x }] :
    Fintype.card { x // y = x } = 1 :=
  Fintype.card_unique
#align fintype.card_subtype_eq' Fintype.card_subtype_eq'

@[simp]
theorem Fintype.card_empty : Fintype.card Empty = 0 :=
  rfl
#align fintype.card_empty Fintype.card_empty

@[simp]
theorem Fintype.card_pempty : Fintype.card PEmpty = 0 :=
  rfl
#align fintype.card_pempty Fintype.card_pempty

theorem Fintype.card_unit : Fintype.card Unit = 1 :=
  rfl
#align fintype.card_unit Fintype.card_unit

@[simp]
theorem Fintype.card_punit : Fintype.card PUnit = 1 :=
  rfl
#align fintype.card_punit Fintype.card_punit

@[simp]
theorem Fintype.card_bool : Fintype.card Bool = 2 :=
  rfl
#align fintype.card_bool Fintype.card_bool

@[simp]
theorem Fintype.card_ulift (α : Type*) [Fintype α] : Fintype.card (ULift α) = Fintype.card α :=
  Fintype.ofEquiv_card _
#align fintype.card_ulift Fintype.card_ulift

@[simp]
theorem Fintype.card_plift (α : Type*) [Fintype α] : Fintype.card (PLift α) = Fintype.card α :=
  Fintype.ofEquiv_card _
#align fintype.card_plift Fintype.card_plift

@[simp]
theorem Fintype.card_orderDual (α : Type*) [Fintype α] : Fintype.card αᵒᵈ = Fintype.card α :=
  rfl
#align fintype.card_order_dual Fintype.card_orderDual

@[simp]
theorem Fintype.card_lex (α : Type*) [Fintype α] : Fintype.card (Lex α) = Fintype.card α :=
  rfl
#align fintype.card_lex Fintype.card_lex

/-- Given that `α ⊕ β` is a fintype, `α` is also a fintype. This is non-computable as it uses
that `Sum.inl` is an injection, but there's no clear inverse if `α` is empty. -/
noncomputable def Fintype.sumLeft {α β} [Fintype (Sum α β)] : Fintype α :=
  Fintype.ofInjective (Sum.inl : α → Sum α β) Sum.inl_injective
#align fintype.sum_left Fintype.sumLeft

/-- Given that `α ⊕ β` is a fintype, `β` is also a fintype. This is non-computable as it uses
that `Sum.inr` is an injection, but there's no clear inverse if `β` is empty. -/
noncomputable def Fintype.sumRight {α β} [Fintype (Sum α β)] : Fintype β :=
  Fintype.ofInjective (Sum.inr : β → Sum α β) Sum.inr_injective
#align fintype.sum_right Fintype.sumRight

/-!
### Relation to `Finite`

In this section we prove that `α : Type*` is `Finite` if and only if `Fintype α` is nonempty.
-/


-- @[nolint fintype_finite] -- Porting note: do we need this
protected theorem Fintype.finite {α : Type*} (_inst : Fintype α) : Finite α :=
  ⟨Fintype.equivFin α⟩
#align fintype.finite Fintype.finite

/-- For efficiency reasons, we want `Finite` instances to have higher
priority than ones coming from `Fintype` instances. -/
-- @[nolint fintype_finite] -- Porting note: do we need this
instance (priority := 900) Finite.of_fintype (α : Type*) [Fintype α] : Finite α :=
  Fintype.finite ‹_›
#align finite.of_fintype Finite.of_fintype

theorem finite_iff_nonempty_fintype (α : Type*) : Finite α ↔ Nonempty (Fintype α) :=
  ⟨fun h =>
    let ⟨_k, ⟨e⟩⟩ := @Finite.exists_equiv_fin α h
    ⟨Fintype.ofEquiv _ e.symm⟩,
    fun ⟨_⟩ => inferInstance⟩
#align finite_iff_nonempty_fintype finite_iff_nonempty_fintype

/-- See also `nonempty_encodable`, `nonempty_denumerable`. -/
theorem nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fintype α) :=
  (finite_iff_nonempty_fintype α).mp ‹_›
#align nonempty_fintype nonempty_fintype

/-- Noncomputably get a `Fintype` instance from a `Finite` instance. This is not an
instance because we want `Fintype` instances to be useful for computations. -/
noncomputable def Fintype.ofFinite (α : Type*) [Finite α] : Fintype α :=
  (nonempty_fintype α).some
#align fintype.of_finite Fintype.ofFinite

theorem Finite.of_injective {α β : Sort*} [Finite β] (f : α → β) (H : Injective f) : Finite α := by
  cases nonempty_fintype (PLift β)
  -- ⊢ Finite α
  rw [← Equiv.injective_comp Equiv.plift f, ← Equiv.comp_injective _ Equiv.plift.symm] at H
  -- ⊢ Finite α
  haveI := Fintype.ofInjective _ H
  -- ⊢ Finite α
  exact Finite.of_equiv _ Equiv.plift
  -- 🎉 no goals
#align finite.of_injective Finite.of_injective

theorem Finite.of_surjective {α β : Sort*} [Finite α] (f : α → β) (H : Surjective f) : Finite β :=
  Finite.of_injective _ <| injective_surjInv H
#align finite.of_surjective Finite.of_surjective

theorem Finite.exists_univ_list (α) [Finite α] : ∃ l : List α, l.Nodup ∧ ∀ x : α, x ∈ l := by
  cases nonempty_fintype α
  -- ⊢ ∃ l, List.Nodup l ∧ ∀ (x : α), x ∈ l
  obtain ⟨l, e⟩ := Quotient.exists_rep (@univ α _).1
  -- ⊢ ∃ l, List.Nodup l ∧ ∀ (x : α), x ∈ l
  have := And.intro (@univ α _).2 (@mem_univ_val α _)
  -- ⊢ ∃ l, List.Nodup l ∧ ∀ (x : α), x ∈ l
  exact ⟨_, by rwa [← e] at this⟩
  -- 🎉 no goals
#align finite.exists_univ_list Finite.exists_univ_list

theorem List.Nodup.length_le_card {α : Type*} [Fintype α] {l : List α} (h : l.Nodup) :
    l.length ≤ Fintype.card α := by
  classical exact List.toFinset_card_of_nodup h ▸ l.toFinset.card_le_univ
  -- 🎉 no goals
#align list.nodup.length_le_card List.Nodup.length_le_card

namespace Fintype

variable [Fintype α] [Fintype β]

theorem card_le_of_injective (f : α → β) (hf : Function.Injective f) : card α ≤ card β :=
  Finset.card_le_card_of_inj_on f (fun _ _ => Finset.mem_univ _) fun _ _ _ _ h => hf h
#align fintype.card_le_of_injective Fintype.card_le_of_injective

theorem card_le_of_embedding (f : α ↪ β) : card α ≤ card β :=
  card_le_of_injective f f.2
#align fintype.card_le_of_embedding Fintype.card_le_of_embedding

theorem card_lt_of_injective_of_not_mem (f : α → β) (h : Function.Injective f) {b : β}
    (w : b ∉ Set.range f) : card α < card β :=
  calc
    card α = (univ.map ⟨f, h⟩).card := (card_map _).symm
    _ < card β :=
      Finset.card_lt_univ_of_not_mem <| by rwa [← mem_coe, coe_map, coe_univ, Set.image_univ]
                                           -- 🎉 no goals
#align fintype.card_lt_of_injective_of_not_mem Fintype.card_lt_of_injective_of_not_mem

theorem card_lt_of_injective_not_surjective (f : α → β) (h : Function.Injective f)
    (h' : ¬Function.Surjective f) : card α < card β :=
  let ⟨_y, hy⟩ := not_forall.1 h'
  card_lt_of_injective_of_not_mem f h hy
#align fintype.card_lt_of_injective_not_surjective Fintype.card_lt_of_injective_not_surjective

theorem card_le_of_surjective (f : α → β) (h : Function.Surjective f) : card β ≤ card α :=
  card_le_of_injective _ (Function.injective_surjInv h)
#align fintype.card_le_of_surjective Fintype.card_le_of_surjective

theorem card_range_le {α β : Type*} (f : α → β) [Fintype α] [Fintype (Set.range f)] :
    Fintype.card (Set.range f) ≤ Fintype.card α :=
  Fintype.card_le_of_surjective (fun a => ⟨f a, by simp⟩) fun ⟨_, a, ha⟩ => ⟨a, by simpa using ha⟩
                                                   -- 🎉 no goals
                                                                                   -- 🎉 no goals
#align fintype.card_range_le Fintype.card_range_le

theorem card_range {α β F : Type*} [EmbeddingLike F α β] (f : F) [Fintype α]
    [Fintype (Set.range f)] : Fintype.card (Set.range f) = Fintype.card α :=
  Eq.symm <| Fintype.card_congr <| Equiv.ofInjective _ <| EmbeddingLike.injective f
#align fintype.card_range Fintype.card_range

/-- The pigeonhole principle for finitely many pigeons and pigeonholes.
This is the `Fintype` version of `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`.
-/
theorem exists_ne_map_eq_of_card_lt (f : α → β) (h : Fintype.card β < Fintype.card α) :
    ∃ x y, x ≠ y ∧ f x = f y :=
  let ⟨x, _, y, _, h⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to h fun x _ => mem_univ (f x)
  ⟨x, y, h⟩
#align fintype.exists_ne_map_eq_of_card_lt Fintype.exists_ne_map_eq_of_card_lt

theorem card_eq_one_iff : card α = 1 ↔ ∃ x : α, ∀ y, y = x := by
  rw [← card_unit, card_eq]
  -- ⊢ Nonempty (α ≃ Unit) ↔ ∃ x, ∀ (y : α), y = x
  exact
    ⟨fun ⟨a⟩ => ⟨a.symm (), fun y => a.injective (Subsingleton.elim _ _)⟩,
     fun ⟨x, hx⟩ =>
      ⟨⟨fun _ => (), fun _ => x, fun _ => (hx _).trans (hx _).symm, fun _ =>
          Subsingleton.elim _ _⟩⟩⟩
#align fintype.card_eq_one_iff Fintype.card_eq_one_iff

theorem card_eq_zero_iff : card α = 0 ↔ IsEmpty α := by
  rw [card, Finset.card_eq_zero, univ_eq_empty_iff]
  -- 🎉 no goals
#align fintype.card_eq_zero_iff Fintype.card_eq_zero_iff

theorem card_eq_zero [IsEmpty α] : card α = 0 :=
  card_eq_zero_iff.2 ‹_›
#align fintype.card_eq_zero Fintype.card_eq_zero

theorem card_eq_one_iff_nonempty_unique : card α = 1 ↔ Nonempty (Unique α) :=
  ⟨fun h =>
    let ⟨d, h⟩ := Fintype.card_eq_one_iff.mp h
    ⟨{  default := d
        uniq := h }⟩,
    fun ⟨_h⟩ => Fintype.card_unique⟩
#align fintype.card_eq_one_iff_nonempty_unique Fintype.card_eq_one_iff_nonempty_unique

/-- A `Fintype` with cardinality zero is equivalent to `Empty`. -/
def cardEqZeroEquivEquivEmpty : card α = 0 ≃ (α ≃ Empty) :=
  (Equiv.ofIff card_eq_zero_iff).trans (Equiv.equivEmptyEquiv α).symm
#align fintype.card_eq_zero_equiv_equiv_empty Fintype.cardEqZeroEquivEquivEmpty

theorem card_pos_iff : 0 < card α ↔ Nonempty α :=
  pos_iff_ne_zero.trans <| not_iff_comm.mp <| not_nonempty_iff.trans card_eq_zero_iff.symm
#align fintype.card_pos_iff Fintype.card_pos_iff

theorem card_pos [h : Nonempty α] : 0 < card α :=
  card_pos_iff.mpr h
#align fintype.card_pos Fintype.card_pos

theorem card_ne_zero [Nonempty α] : card α ≠ 0 :=
  _root_.ne_of_gt card_pos
#align fintype.card_ne_zero Fintype.card_ne_zero

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
      -- ⊢ a = b
      rw [hx a, hx b], fun _ => ha ▸ le_rfl⟩
      -- 🎉 no goals
  | n + 2, ha =>
    ⟨fun h => False.elim $ by rw [← ha] at h; cases h with | step h => cases h; done, fun h =>
                              -- ⊢ False
                                              -- 🎉 no goals
                                              -- ⊢ False
      card_unit ▸ card_le_of_injective (fun _ => ()) fun _ _ _ => h _ _⟩
#align fintype.card_le_one_iff Fintype.card_le_one_iff

theorem card_le_one_iff_subsingleton : card α ≤ 1 ↔ Subsingleton α :=
  card_le_one_iff.trans subsingleton_iff.symm
#align fintype.card_le_one_iff_subsingleton Fintype.card_le_one_iff_subsingleton

theorem one_lt_card_iff_nontrivial : 1 < card α ↔ Nontrivial α := by
  classical
    rw [← not_iff_not]
    push_neg
    rw [not_nontrivial_iff_subsingleton, card_le_one_iff_subsingleton]
#align fintype.one_lt_card_iff_nontrivial Fintype.one_lt_card_iff_nontrivial

theorem exists_ne_of_one_lt_card (h : 1 < card α) (a : α) : ∃ b : α, b ≠ a :=
  haveI : Nontrivial α := one_lt_card_iff_nontrivial.1 h
  exists_ne a
#align fintype.exists_ne_of_one_lt_card Fintype.exists_ne_of_one_lt_card

theorem exists_pair_of_one_lt_card (h : 1 < card α) : ∃ a b : α, a ≠ b :=
  haveI : Nontrivial α := one_lt_card_iff_nontrivial.1 h
  exists_pair_ne α
#align fintype.exists_pair_of_one_lt_card Fintype.exists_pair_of_one_lt_card

theorem card_eq_one_of_forall_eq {i : α} (h : ∀ j, j = i) : card α = 1 :=
  Fintype.card_eq_one_iff.2 ⟨i, h⟩
#align fintype.card_eq_one_of_forall_eq Fintype.card_eq_one_of_forall_eq

theorem one_lt_card [h : Nontrivial α] : 1 < Fintype.card α :=
  Fintype.one_lt_card_iff_nontrivial.mpr h
#align fintype.one_lt_card Fintype.one_lt_card

theorem one_lt_card_iff : 1 < card α ↔ ∃ a b : α, a ≠ b :=
  one_lt_card_iff_nontrivial.trans nontrivial_iff
#align fintype.one_lt_card_iff Fintype.one_lt_card_iff

nonrec theorem two_lt_card_iff : 2 < card α ↔ ∃ a b c : α, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  simp_rw [← Finset.card_univ, two_lt_card_iff, mem_univ, true_and_iff]
  -- 🎉 no goals
#align fintype.two_lt_card_iff Fintype.two_lt_card_iff

theorem card_of_bijective {f : α → β} (hf : Bijective f) : card α = card β :=
  card_congr (Equiv.ofBijective f hf)
#align fintype.card_of_bijective Fintype.card_of_bijective

end Fintype

namespace Finite

variable [Finite α]

-- Porting note: new theorem
theorem surjective_of_injective {f : α → α} (hinj : Injective f) : Surjective f := by
  intro x
  -- ⊢ ∃ a, f a = x
  have := Classical.propDecidable
  -- ⊢ ∃ a, f a = x
  cases nonempty_fintype α
  -- ⊢ ∃ a, f a = x
  have h₁ : image f univ = univ :=
    eq_of_subset_of_card_le (subset_univ _)
      ((card_image_of_injective univ hinj).symm ▸ le_rfl)
  have h₂ : x ∈ image f univ := h₁.symm ▸ mem_univ x
  -- ⊢ ∃ a, f a = x
  obtain ⟨y, h⟩ := mem_image.1 h₂
  -- ⊢ ∃ a, f a = x
  exact ⟨y, h.2⟩
  -- 🎉 no goals

theorem injective_iff_surjective {f : α → α} : Injective f ↔ Surjective f :=
  ⟨surjective_of_injective, fun hsurj =>
    HasLeftInverse.injective ⟨surjInv hsurj, leftInverse_of_surjective_of_rightInverse
      (surjective_of_injective (injective_surjInv _))
      (rightInverse_surjInv _)⟩⟩
#align finite.injective_iff_surjective Finite.injective_iff_surjective

theorem injective_iff_bijective {f : α → α} : Injective f ↔ Bijective f := by
  simp [Bijective, injective_iff_surjective]
  -- 🎉 no goals
#align finite.injective_iff_bijective Finite.injective_iff_bijective

theorem surjective_iff_bijective {f : α → α} : Surjective f ↔ Bijective f := by
  simp [Bijective, injective_iff_surjective]
  -- 🎉 no goals
#align finite.surjective_iff_bijective Finite.surjective_iff_bijective

theorem injective_iff_surjective_of_equiv {f : α → β} (e : α ≃ β) : Injective f ↔ Surjective f :=
  have : Injective (e.symm ∘ f) ↔ Surjective (e.symm ∘ f) := injective_iff_surjective
  ⟨fun hinj => by
    simpa [Function.comp] using e.surjective.comp (this.1 (e.symm.injective.comp hinj)),
    -- 🎉 no goals
    fun hsurj => by
    simpa [Function.comp] using e.injective.comp (this.2 (e.symm.surjective.comp hsurj))⟩
    -- 🎉 no goals
#align finite.injective_iff_surjective_of_equiv Finite.injective_iff_surjective_of_equiv

alias ⟨_root_.Function.Injective.bijective_of_finite, _⟩ := injective_iff_bijective
#align function.injective.bijective_of_finite Function.Injective.bijective_of_finite

alias ⟨_root_.Function.Surjective.bijective_of_finite, _⟩ := surjective_iff_bijective
#align function.surjective.bijective_of_finite Function.Surjective.bijective_of_finite

alias ⟨_root_.Function.Injective.surjective_of_fintype,
    _root_.Function.Surjective.injective_of_fintype⟩ :=
  injective_iff_surjective_of_equiv
#align function.injective.surjective_of_fintype Function.Injective.surjective_of_fintype
#align function.surjective.injective_of_fintype Function.Surjective.injective_of_fintype

end Finite

namespace Fintype

variable [Fintype α] [Fintype β]

theorem bijective_iff_injective_and_card (f : α → β) :
    Bijective f ↔ Injective f ∧ card α = card β :=
  ⟨fun h => ⟨h.1, card_of_bijective h⟩, fun h =>
    ⟨h.1, h.1.surjective_of_fintype <| equivOfCardEq h.2⟩⟩
#align fintype.bijective_iff_injective_and_card Fintype.bijective_iff_injective_and_card

theorem bijective_iff_surjective_and_card (f : α → β) :
    Bijective f ↔ Surjective f ∧ card α = card β :=
  ⟨fun h => ⟨h.2, card_of_bijective h⟩, fun h =>
    ⟨h.1.injective_of_fintype <| equivOfCardEq h.2, h.1⟩⟩
#align fintype.bijective_iff_surjective_and_card Fintype.bijective_iff_surjective_and_card

theorem _root_.Function.LeftInverse.rightInverse_of_card_le {f : α → β} {g : β → α}
    (hfg : LeftInverse f g) (hcard : card α ≤ card β) : RightInverse f g :=
  have hsurj : Surjective f := surjective_iff_hasRightInverse.2 ⟨g, hfg⟩
  rightInverse_of_injective_of_leftInverse
    ((bijective_iff_surjective_and_card _).2
        ⟨hsurj, le_antisymm hcard (card_le_of_surjective f hsurj)⟩).1
    hfg
#align function.left_inverse.right_inverse_of_card_le Function.LeftInverse.rightInverse_of_card_le

theorem _root_.Function.RightInverse.leftInverse_of_card_le {f : α → β} {g : β → α}
    (hfg : RightInverse f g) (hcard : card β ≤ card α) : LeftInverse f g :=
  Function.LeftInverse.rightInverse_of_card_le hfg hcard
#align function.right_inverse.left_inverse_of_card_le Function.RightInverse.leftInverse_of_card_le

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
#align equiv.of_left_inverse_of_card_le Equiv.ofLeftInverseOfCardLE
#align equiv.of_left_inverse_of_card_le_symm_apply Equiv.ofLeftInverseOfCardLE_symm_apply
#align equiv.of_left_inverse_of_card_le_apply Equiv.ofLeftInverseOfCardLE_apply

/-- Construct an equivalence from functions that are inverse to each other. -/
@[simps]
def ofRightInverseOfCardLE (hαβ : card α ≤ card β) (f : α → β) (g : β → α) (h : RightInverse g f) :
    α ≃ β where
  toFun := f
  invFun := g
  left_inv := h.leftInverse_of_card_le hαβ
  right_inv := h
#align equiv.of_right_inverse_of_card_le Equiv.ofRightInverseOfCardLE
#align equiv.of_right_inverse_of_card_le_symm_apply Equiv.ofRightInverseOfCardLE_symm_apply
#align equiv.of_right_inverse_of_card_le_apply Equiv.ofRightInverseOfCardLE_apply

end Equiv

@[simp]
theorem Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.card s = s.card :=
  @Fintype.card_of_finset' _ _ _ (fun _ => Iff.rfl) (id _)
#align fintype.card_coe Fintype.card_coe

/-- Noncomputable equivalence between a finset `s` coerced to a type and `Fin s.card`. -/
noncomputable def Finset.equivFin (s : Finset α) : s ≃ Fin s.card :=
  Fintype.equivFinOfCardEq (Fintype.card_coe _)
#align finset.equiv_fin Finset.equivFin

/-- Noncomputable equivalence between a finset `s` as a fintype and `Fin n`, when there is a
proof that `s.card = n`. -/
noncomputable def Finset.equivFinOfCardEq {s : Finset α} {n : ℕ} (h : s.card = n) : s ≃ Fin n :=
  Fintype.equivFinOfCardEq ((Fintype.card_coe _).trans h)
#align finset.equiv_fin_of_card_eq Finset.equivFinOfCardEq

/-- Noncomputable equivalence between two finsets `s` and `t` as fintypes when there is a proof
that `s.card = t.card`.-/
noncomputable def Finset.equivOfCardEq {s t : Finset α} (h : s.card = t.card) : s ≃ t :=
  Fintype.equivOfCardEq ((Fintype.card_coe _).trans (h.trans (Fintype.card_coe _).symm))
#align finset.equiv_of_card_eq Finset.equivOfCardEq

@[simp]
theorem Fintype.card_prop : Fintype.card Prop = 2 :=
  rfl
#align fintype.card_Prop Fintype.card_prop

theorem set_fintype_card_le_univ [Fintype α] (s : Set α) [Fintype s] :
    Fintype.card s ≤ Fintype.card α :=
  Fintype.card_le_of_embedding (Function.Embedding.subtype s)
#align set_fintype_card_le_univ set_fintype_card_le_univ

theorem set_fintype_card_eq_univ_iff [Fintype α] (s : Set α) [Fintype s] :
    Fintype.card s = Fintype.card α ↔ s = Set.univ := by
  rw [← Set.toFinset_card, Finset.card_eq_iff_eq_univ, ← Set.toFinset_univ, Set.toFinset_inj]
  -- 🎉 no goals
#align set_fintype_card_eq_univ_iff set_fintype_card_eq_univ_iff

namespace Function.Embedding

/-- An embedding from a `Fintype` to itself can be promoted to an equivalence. -/
noncomputable def equivOfFintypeSelfEmbedding [Finite α] (e : α ↪ α) : α ≃ α :=
  Equiv.ofBijective e e.2.bijective_of_finite
#align function.embedding.equiv_of_fintype_self_embedding Function.Embedding.equivOfFintypeSelfEmbedding

@[simp]
theorem equiv_of_fintype_self_embedding_to_embedding [Finite α] (e : α ↪ α) :
    e.equivOfFintypeSelfEmbedding.toEmbedding = e := by
  ext
  -- ⊢ ↑(Equiv.toEmbedding (equivOfFintypeSelfEmbedding e)) x✝ = ↑e x✝
  rfl
  -- 🎉 no goals
#align function.embedding.equiv_of_fintype_self_embedding_to_embedding Function.Embedding.equiv_of_fintype_self_embedding_to_embedding

/-- If `‖β‖ < ‖α‖` there are no embeddings `α ↪ β`.
This is a formulation of the pigeonhole principle.

Note this cannot be an instance as it needs `h`. -/
@[simp]
theorem isEmpty_of_card_lt [Fintype α] [Fintype β] (h : Fintype.card β < Fintype.card α) :
    IsEmpty (α ↪ β) :=
  ⟨fun f =>
    let ⟨_x, _y, ne, feq⟩ := Fintype.exists_ne_map_eq_of_card_lt f h
    ne <| f.injective feq⟩
#align function.embedding.is_empty_of_card_lt Function.Embedding.isEmpty_of_card_lt

/-- A constructive embedding of a fintype `α` in another fintype `β` when `card α ≤ card β`. -/
def truncOfCardLE [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (h : Fintype.card α ≤ Fintype.card β) : Trunc (α ↪ β) :=
  (Fintype.truncEquivFin α).bind fun ea =>
    (Fintype.truncEquivFin β).map fun eb =>
      ea.toEmbedding.trans ((Fin.castLEEmb h).toEmbedding.trans eb.symm.toEmbedding)
#align function.embedding.trunc_of_card_le Function.Embedding.truncOfCardLE

theorem nonempty_of_card_le [Fintype α] [Fintype β] (h : Fintype.card α ≤ Fintype.card β) :
    Nonempty (α ↪ β) := by classical exact (truncOfCardLE h).nonempty
                           -- 🎉 no goals
#align function.embedding.nonempty_of_card_le Function.Embedding.nonempty_of_card_le

theorem nonempty_iff_card_le [Fintype α] [Fintype β] :
    Nonempty (α ↪ β) ↔ Fintype.card α ≤ Fintype.card β :=
  ⟨fun ⟨e⟩ => Fintype.card_le_of_embedding e, nonempty_of_card_le⟩
#align function.embedding.nonempty_iff_card_le Function.Embedding.nonempty_iff_card_le

theorem exists_of_card_le_finset [Fintype α] {s : Finset β} (h : Fintype.card α ≤ s.card) :
    ∃ f : α ↪ β, Set.range f ⊆ s := by
  rw [← Fintype.card_coe] at h
  -- ⊢ ∃ f, Set.range ↑f ⊆ ↑s
  rcases nonempty_of_card_le h with ⟨f⟩
  -- ⊢ ∃ f, Set.range ↑f ⊆ ↑s
  exact ⟨f.trans (Embedding.subtype _), by simp [Set.range_subset_iff]⟩
  -- 🎉 no goals
#align function.embedding.exists_of_card_le_finset Function.Embedding.exists_of_card_le_finset

end Function.Embedding

@[simp]
theorem Finset.univ_map_embedding {α : Type*} [Fintype α] (e : α ↪ α) : univ.map e = univ := by
  rw [← e.equiv_of_fintype_self_embedding_to_embedding, univ_map_equiv_to_embedding]
  -- 🎉 no goals
#align finset.univ_map_embedding Finset.univ_map_embedding

namespace Fintype

theorem card_lt_of_surjective_not_injective [Fintype α] [Fintype β] (f : α → β)
    (h : Function.Surjective f) (h' : ¬Function.Injective f) : card β < card α :=
  card_lt_of_injective_not_surjective _ (Function.injective_surjInv h) fun hg =>
    have w : Function.Bijective (Function.surjInv h) := ⟨Function.injective_surjInv h, hg⟩
    h' <| h.injective_of_fintype (Equiv.ofBijective _ w).symm
#align fintype.card_lt_of_surjective_not_injective Fintype.card_lt_of_surjective_not_injective

end Fintype

theorem Fintype.card_subtype_le [Fintype α] (p : α → Prop) [DecidablePred p] :
    Fintype.card { x // p x } ≤ Fintype.card α :=
  Fintype.card_le_of_embedding (Function.Embedding.subtype _)
#align fintype.card_subtype_le Fintype.card_subtype_le

theorem Fintype.card_subtype_lt [Fintype α] {p : α → Prop} [DecidablePred p] {x : α} (hx : ¬p x) :
    Fintype.card { x // p x } < Fintype.card α :=
  Fintype.card_lt_of_injective_of_not_mem (↑) Subtype.coe_injective <| by
    rwa [Subtype.range_coe_subtype]
    -- 🎉 no goals
#align fintype.card_subtype_lt Fintype.card_subtype_lt

theorem Fintype.card_subtype [Fintype α] (p : α → Prop) [DecidablePred p] :
    Fintype.card { x // p x } = ((Finset.univ : Finset α).filter p).card := by
  refine' Fintype.card_of_subtype _ _
  -- ⊢ ∀ (x : α), x ∈ filter p univ ↔ p x
  simp
  -- 🎉 no goals
#align fintype.card_subtype Fintype.card_subtype

@[simp]
theorem Fintype.card_subtype_compl [Fintype α] (p : α → Prop) [Fintype { x // p x }]
    [Fintype { x // ¬p x }] :
    Fintype.card { x // ¬p x } = Fintype.card α - Fintype.card { x // p x } := by
  classical
    rw [Fintype.card_of_subtype (Set.toFinset { x | p x }ᶜ), Set.toFinset_compl,
      Finset.card_compl, Fintype.card_of_subtype] <;>
    · intro
      simp only [Set.mem_toFinset, Set.mem_compl_iff, Set.mem_setOf]
#align fintype.card_subtype_compl Fintype.card_subtype_compl

theorem Fintype.card_subtype_mono (p q : α → Prop) (h : p ≤ q) [Fintype { x // p x }]
    [Fintype { x // q x }] : Fintype.card { x // p x } ≤ Fintype.card { x // q x } :=
  Fintype.card_le_of_embedding (Subtype.impEmbedding _ _ h)
#align fintype.card_subtype_mono Fintype.card_subtype_mono

/-- If two subtypes of a fintype have equal cardinality, so do their complements. -/
theorem Fintype.card_compl_eq_card_compl [Finite α] (p q : α → Prop) [Fintype { x // p x }]
    [Fintype { x // ¬p x }] [Fintype { x // q x }] [Fintype { x // ¬q x }]
    (h : Fintype.card { x // p x } = Fintype.card { x // q x }) :
    Fintype.card { x // ¬p x } = Fintype.card { x // ¬q x } := by
  cases nonempty_fintype α
  -- ⊢ card { x // ¬p x } = card { x // ¬q x }
  simp only [Fintype.card_subtype_compl, h]
  -- 🎉 no goals
#align fintype.card_compl_eq_card_compl Fintype.card_compl_eq_card_compl

theorem Fintype.card_quotient_le [Fintype α] (s : Setoid α)
    [DecidableRel ((· ≈ ·) : α → α → Prop)] : Fintype.card (Quotient s) ≤ Fintype.card α :=
  Fintype.card_le_of_surjective _ (surjective_quotient_mk _)
#align fintype.card_quotient_le Fintype.card_quotient_le

theorem Fintype.card_quotient_lt [Fintype α] {s : Setoid α} [DecidableRel ((· ≈ ·) : α → α → Prop)]
    {x y : α} (h1 : x ≠ y) (h2 : x ≈ y) : Fintype.card (Quotient s) < Fintype.card α :=
  Fintype.card_lt_of_surjective_not_injective _ (surjective_quotient_mk _) fun w =>
    h1 (w <| Quotient.eq.mpr h2)
#align fintype.card_quotient_lt Fintype.card_quotient_lt

theorem univ_eq_singleton_of_card_one {α} [Fintype α] (x : α) (h : Fintype.card α = 1) :
    (univ : Finset α) = {x} := by
  symm
  -- ⊢ {x} = univ
  apply eq_of_subset_of_card_le (subset_univ {x})
  -- ⊢ card univ ≤ card {x}
  apply le_of_eq
  -- ⊢ card univ = card {x}
  simp [h, Finset.card_univ]
  -- 🎉 no goals
#align univ_eq_singleton_of_card_one univ_eq_singleton_of_card_one

namespace Finite

variable [Finite α]

theorem wellFounded_of_trans_of_irrefl (r : α → α → Prop) [IsTrans α r] [IsIrrefl α r] :
    WellFounded r := by
  classical
  cases nonempty_fintype α
  have :
    ∀ x y, r x y → (univ.filter fun z => r z x).card < (univ.filter fun z => r z y).card :=
    fun x y hxy =>
    Finset.card_lt_card <| by
      simp only [Finset.lt_iff_ssubset.symm, lt_iff_le_not_le, Finset.le_iff_subset,
          Finset.subset_iff, mem_filter, true_and_iff, mem_univ, hxy];
      exact
        ⟨fun z hzx => _root_.trans hzx hxy,
          not_forall_of_exists_not ⟨x, not_imp.2 ⟨hxy, irrefl x⟩⟩⟩
  exact Subrelation.wf (this _ _) (measure _).wf
#align finite.well_founded_of_trans_of_irrefl Finite.wellFounded_of_trans_of_irrefl

-- See note [lower instance priority]
instance (priority := 100) to_wellFoundedLT [Preorder α] : WellFoundedLT α :=
  ⟨wellFounded_of_trans_of_irrefl _⟩
#align finite.finite.to_well_founded_lt Finite.to_wellFoundedLT

-- See note [lower instance priority]
instance (priority := 100) to_wellFoundedGT [Preorder α] : WellFoundedGT α :=
  ⟨wellFounded_of_trans_of_irrefl _⟩
#align finite.finite.to_well_founded_gt Finite.to_wellFoundedGT

instance (priority := 10) LinearOrder.isWellOrder_lt [LinearOrder α] : IsWellOrder α (· < ·) := {}
#align finite.linear_order.is_well_order_lt Finite.LinearOrder.isWellOrder_lt

instance (priority := 10) LinearOrder.isWellOrder_gt [LinearOrder α] : IsWellOrder α (· > ·) := {}
#align finite.linear_order.is_well_order_gt Finite.LinearOrder.isWellOrder_gt

end Finite

-- @[nolint fintype_finite] -- Porting note: do we need this?
protected theorem Fintype.false [Infinite α] (_h : Fintype α) : False :=
  not_finite α
#align fintype.false Fintype.false

@[simp]
theorem isEmpty_fintype {α : Type*} : IsEmpty (Fintype α) ↔ Infinite α :=
  ⟨fun ⟨h⟩ => ⟨fun h' => (@nonempty_fintype α h').elim h⟩, fun ⟨h⟩ => ⟨fun h' => h h'.finite⟩⟩
#align is_empty_fintype isEmpty_fintype

/-- A non-infinite type is a fintype. -/
noncomputable def fintypeOfNotInfinite {α : Type*} (h : ¬Infinite α) : Fintype α :=
  @Fintype.ofFinite _ (not_infinite_iff_finite.mp h)
#align fintype_of_not_infinite fintypeOfNotInfinite

section

open Classical

/-- Any type is (classically) either a `Fintype`, or `Infinite`.

One can obtain the relevant typeclasses via `cases fintypeOrInfinite α`.
-/
noncomputable def fintypeOrInfinite (α : Type*) : PSum (Fintype α) (Infinite α) :=
  if h : Infinite α then PSum.inr h else PSum.inl (fintypeOfNotInfinite h)
#align fintype_or_infinite fintypeOrInfinite

end

theorem Finset.exists_minimal {α : Type*} [Preorder α] (s : Finset α) (h : s.Nonempty) :
    ∃ m ∈ s, ∀ x ∈ s, ¬x < m := by
  obtain ⟨c, hcs : c ∈ s⟩ := h
  -- ⊢ ∃ m, m ∈ s ∧ ∀ (x : α), x ∈ s → ¬x < m
  have : WellFounded (@LT.lt { x // x ∈ s } _) := Finite.wellFounded_of_trans_of_irrefl _
  -- ⊢ ∃ m, m ∈ s ∧ ∀ (x : α), x ∈ s → ¬x < m
  obtain ⟨⟨m, hms : m ∈ s⟩, -, H⟩ := this.has_min Set.univ ⟨⟨c, hcs⟩, trivial⟩
  -- ⊢ ∃ m, m ∈ s ∧ ∀ (x : α), x ∈ s → ¬x < m
  exact ⟨m, hms, fun x hx hxm => H ⟨x, hx⟩ trivial hxm⟩
  -- 🎉 no goals
#align finset.exists_minimal Finset.exists_minimal

theorem Finset.exists_maximal {α : Type*} [Preorder α] (s : Finset α) (h : s.Nonempty) :
    ∃ m ∈ s, ∀ x ∈ s, ¬m < x :=
  @Finset.exists_minimal αᵒᵈ _ s h
#align finset.exists_maximal Finset.exists_maximal

namespace Infinite

theorem of_not_fintype (h : Fintype α → False) : Infinite α :=
  isEmpty_fintype.mp ⟨h⟩
#align infinite.of_not_fintype Infinite.of_not_fintype

/-- If `s : Set α` is a proper subset of `α` and `f : α → s` is injective, then `α` is infinite. -/
theorem of_injective_to_set {s : Set α} (hs : s ≠ Set.univ) {f : α → s} (hf : Injective f) :
    Infinite α :=
  of_not_fintype fun h => by
    classical
      refine' lt_irrefl (Fintype.card α) _
      calc
        Fintype.card α ≤ Fintype.card s := Fintype.card_le_of_injective f hf
        _ = s.toFinset.card := s.toFinset_card.symm
        _ < Fintype.card α :=
          Finset.card_lt_card <| by rwa [Set.toFinset_ssubset_univ, Set.ssubset_univ_iff]
#align infinite.of_injective_to_set Infinite.of_injective_to_set

/-- If `s : Set α` is a proper subset of `α` and `f : s → α` is surjective, then `α` is infinite. -/
theorem of_surjective_from_set {s : Set α} (hs : s ≠ Set.univ) {f : s → α} (hf : Surjective f) :
    Infinite α :=
  of_injective_to_set hs (injective_surjInv hf)
#align infinite.of_surjective_from_set Infinite.of_surjective_from_set

theorem exists_not_mem_finset [Infinite α] (s : Finset α) : ∃ x, x ∉ s :=
  not_forall.1 fun h => Fintype.false ⟨s, h⟩
#align infinite.exists_not_mem_finset Infinite.exists_not_mem_finset

-- see Note [lower instance priority]
instance (priority := 100) (α : Type*) [H : Infinite α] : Nontrivial α :=
  ⟨let ⟨x, _hx⟩ := exists_not_mem_finset (∅ : Finset α)
    let ⟨y, hy⟩ := exists_not_mem_finset ({x} : Finset α)
    ⟨y, x, by simpa only [mem_singleton] using hy⟩⟩
              -- 🎉 no goals

protected theorem nonempty (α : Type*) [Infinite α] : Nonempty α := by infer_instance
                                                                       -- 🎉 no goals
#align infinite.nonempty Infinite.nonempty

theorem of_injective {α β} [Infinite β] (f : β → α) (hf : Injective f) : Infinite α :=
  ⟨fun _I => (Finite.of_injective f hf).false⟩
#align infinite.of_injective Infinite.of_injective

theorem of_surjective {α β} [Infinite β] (f : α → β) (hf : Surjective f) : Infinite α :=
  ⟨fun _I => (Finite.of_surjective f hf).false⟩
#align infinite.of_surjective Infinite.of_surjective

end Infinite

instance : Infinite ℕ :=
  Infinite.of_not_fintype <| by
    intro h
    -- ⊢ False
    exact (Finset.range _).card_le_univ.not_lt ((Nat.lt_succ_self _).trans_eq (card_range _).symm)
    -- 🎉 no goals

instance Int.infinite : Infinite ℤ :=
  Infinite.of_injective Int.ofNat fun _ _ => Int.ofNat.inj

instance [Nonempty α] : Infinite (Multiset α) :=
  let ⟨x⟩ := ‹Nonempty α›
  Infinite.of_injective (fun n => Multiset.replicate n x) (Multiset.replicate_left_injective _)

instance [Nonempty α] : Infinite (List α) :=
  Infinite.of_surjective ((↑) : List α → Multiset α) (surjective_quot_mk _)

instance String.infinite : Infinite String :=
  Infinite.of_injective (String.mk) <| by
    intro _ _ h
    -- ⊢ a₁✝ = a₂✝
    cases h with
    | refl => rfl

instance Infinite.set [Infinite α] : Infinite (Set α) :=
  Infinite.of_injective singleton Set.singleton_injective
#align infinite.set Infinite.set

instance [Infinite α] : Infinite (Finset α) :=
  Infinite.of_injective singleton Finset.singleton_injective

instance [Infinite α] : Infinite (Option α) :=
  Infinite.of_injective some (Option.some_injective α)

instance Sum.infinite_of_left [Infinite α] : Infinite (Sum α β) :=
  Infinite.of_injective Sum.inl Sum.inl_injective
#align sum.infinite_of_left Sum.infinite_of_left

instance Sum.infinite_of_right [Infinite β] : Infinite (Sum α β) :=
  Infinite.of_injective Sum.inr Sum.inr_injective
#align sum.infinite_of_right Sum.infinite_of_right

instance Prod.infinite_of_right [Nonempty α] [Infinite β] : Infinite (α × β) :=
  Infinite.of_surjective Prod.snd Prod.snd_surjective
#align prod.infinite_of_right Prod.infinite_of_right

instance Prod.infinite_of_left [Infinite α] [Nonempty β] : Infinite (α × β) :=
  Infinite.of_surjective Prod.fst Prod.fst_surjective
#align prod.infinite_of_left Prod.infinite_of_left

instance instInfiniteProdSubtypeCommute [Mul α] [Infinite α] :
    Infinite { p : α × α // Commute p.1 p.2 } :=
  Infinite.of_injective (fun a => ⟨⟨a, a⟩, rfl⟩) (by intro; simp)
                                                     -- ⊢ ∀ ⦃a₂ : α⦄, (fun a => { val := (a, a), property := (_ : (a, a).fst * (a, a). …
                                                            -- 🎉 no goals

namespace Infinite

private noncomputable def natEmbeddingAux (α : Type*) [Infinite α] : ℕ → α
  | n =>
    letI := Classical.decEq α
    Classical.choose
      (exists_not_mem_finset
        ((Multiset.range n).pmap (fun m (hm : m < n) => natEmbeddingAux _ m) fun _ =>
            Multiset.mem_range.1).toFinset)

-- Porting note: new theorem, to work around missing `wlog`
private theorem natEmbeddingAux_injective_aux (α : Type*) [Infinite α] (m n : ℕ)
  (h : Infinite.natEmbeddingAux α m = Infinite.natEmbeddingAux α n) (hmn : m < n) : m = n := by
  letI := Classical.decEq α
  -- ⊢ m = n
  exfalso
  -- ⊢ False
  refine'
    (Classical.choose_spec
        (exists_not_mem_finset
          ((Multiset.range n).pmap (fun m (_hm : m < n) => natEmbeddingAux α m) fun _ =>
              Multiset.mem_range.1).toFinset))
      _
  refine' Multiset.mem_toFinset.2 (Multiset.mem_pmap.2 ⟨m, Multiset.mem_range.2 hmn, _⟩)
  -- ⊢ Infinite.natEmbeddingAux α m = Classical.choose (_ : ∃ x, ¬x ∈ Multiset.toFi …
  rw [h, natEmbeddingAux]
  -- 🎉 no goals

private theorem natEmbeddingAux_injective (α : Type*) [Infinite α] :
    Function.Injective (natEmbeddingAux α) := by
  rintro m n h
  -- ⊢ m = n
  letI := Classical.decEq α
  -- ⊢ m = n
  rcases lt_trichotomy m n with hmn | rfl | hnm
  · apply natEmbeddingAux_injective_aux α m n h hmn
    -- 🎉 no goals
  · rfl
    -- 🎉 no goals
  · apply (natEmbeddingAux_injective_aux α n m h.symm hnm).symm
    -- 🎉 no goals

/-- Embedding of `ℕ` into an infinite type. -/
noncomputable def natEmbedding (α : Type*) [Infinite α] : ℕ ↪ α :=
  ⟨_, natEmbeddingAux_injective α⟩
#align infinite.nat_embedding Infinite.natEmbedding

/-- See `Infinite.exists_superset_card_eq` for a version that, for an `s : Finset α`,
provides a superset `t : Finset α`, `s ⊆ t` such that `t.card` is fixed. -/
theorem exists_subset_card_eq (α : Type*) [Infinite α] (n : ℕ) : ∃ s : Finset α, s.card = n :=
  ⟨(range n).map (natEmbedding α), by rw [card_map, card_range]⟩
                                      -- 🎉 no goals
#align infinite.exists_subset_card_eq Infinite.exists_subset_card_eq

/-- See `Infinite.exists_subset_card_eq` for a version that provides an arbitrary
`s : Finset α` for any cardinality. -/
theorem exists_superset_card_eq [Infinite α] (s : Finset α) (n : ℕ) (hn : s.card ≤ n) :
    ∃ t : Finset α, s ⊆ t ∧ t.card = n := by
  induction' n with n IH generalizing s
  -- ⊢ ∃ t, s ⊆ t ∧ card t = zero
  · exact ⟨s, subset_refl _, Nat.eq_zero_of_le_zero hn⟩
    -- 🎉 no goals
  · cases' hn.eq_or_lt with hn' hn'
    -- ⊢ ∃ t, s ⊆ t ∧ card t = succ n
    · exact ⟨s, subset_refl _, hn'⟩
      -- 🎉 no goals
    obtain ⟨t, hs, ht⟩ := IH _ (Nat.le_of_lt_succ hn')
    -- ⊢ ∃ t, s ⊆ t ∧ card t = succ n
    obtain ⟨x, hx⟩ := exists_not_mem_finset t
    -- ⊢ ∃ t, s ⊆ t ∧ card t = succ n
    refine' ⟨Finset.cons x t hx, hs.trans (Finset.subset_cons _), _⟩
    -- ⊢ card (cons x t hx) = succ n
    simp [hx, ht]
    -- 🎉 no goals
#align infinite.exists_superset_card_eq Infinite.exists_superset_card_eq

end Infinite

/-- If every finset in a type has bounded cardinality, that type is finite. -/
noncomputable def fintypeOfFinsetCardLe {ι : Type*} (n : ℕ) (w : ∀ s : Finset ι, s.card ≤ n) :
    Fintype ι := by
  apply fintypeOfNotInfinite
  -- ⊢ ¬Infinite ι
  intro i
  -- ⊢ False
  obtain ⟨s, c⟩ := Infinite.exists_subset_card_eq ι (n + 1)
  -- ⊢ False
  specialize w s
  -- ⊢ False
  rw [c] at w
  -- ⊢ False
  exact Nat.not_succ_le_self n w
  -- 🎉 no goals
#align fintype_of_finset_card_le fintypeOfFinsetCardLe

theorem not_injective_infinite_finite {α β} [Infinite α] [Finite β] (f : α → β) : ¬Injective f :=
  fun hf => (Finite.of_injective f hf).false
#align not_injective_infinite_finite not_injective_infinite_finite

/-- The pigeonhole principle for infinitely many pigeons in finitely many pigeonholes. If there are
infinitely many pigeons in finitely many pigeonholes, then there are at least two pigeons in the
same pigeonhole.

See also: `Fintype.exists_ne_map_eq_of_card_lt`, `Finite.exists_infinite_fiber`.
-/
theorem Finite.exists_ne_map_eq_of_infinite {α β} [Infinite α] [Finite β] (f : α → β) :
    ∃ x y : α, x ≠ y ∧ f x = f y := by
  simpa only [Injective, not_forall, not_imp, and_comm] using not_injective_infinite_finite f
  -- 🎉 no goals
#align finite.exists_ne_map_eq_of_infinite Finite.exists_ne_map_eq_of_infinite

instance Function.Embedding.is_empty {α β} [Infinite α] [Finite β] : IsEmpty (α ↪ β) :=
  ⟨fun f => not_injective_infinite_finite f f.2⟩
#align function.embedding.is_empty Function.Embedding.is_empty

/-- The strong pigeonhole principle for infinitely many pigeons in
finitely many pigeonholes.  If there are infinitely many pigeons in
finitely many pigeonholes, then there is a pigeonhole with infinitely
many pigeons.

See also: `Finite.exists_ne_map_eq_of_infinite`
-/
theorem Finite.exists_infinite_fiber [Infinite α] [Finite β] (f : α → β) :
    ∃ y : β, Infinite (f ⁻¹' {y}) := by
  classical
    by_contra' hf
    cases nonempty_fintype β
    haveI := fun y => fintypeOfNotInfinite <| hf y
    let key : Fintype α :=
      { elems := univ.biUnion fun y : β => (f ⁻¹' {y}).toFinset
        complete := by simp }
    exact key.false
#align finite.exists_infinite_fiber Finite.exists_infinite_fiber

theorem not_surjective_finite_infinite {α β} [Finite α] [Infinite β] (f : α → β) : ¬Surjective f :=
  fun hf => (Infinite.of_surjective f hf).not_finite ‹_›
#align not_surjective_finite_infinite not_surjective_finite_infinite

section Trunc

/-- A `Fintype` with positive cardinality constructively contains an element.
-/
def truncOfCardPos {α} [Fintype α] (h : 0 < Fintype.card α) : Trunc α :=
  letI := Fintype.card_pos_iff.mp h
  truncOfNonemptyFintype α
#align trunc_of_card_pos truncOfCardPos

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
    (hstep :
      ∀ (α) [Fintype α] [Nontrivial α],
        ∀ _ih : ∀ (β) [Fintype β], ∀ _h : Fintype.card β < Fintype.card α, P β, P α) :
    P α := by
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card α = n := ⟨Fintype.card α, rfl⟩
  -- ⊢ P α
  induction' n using Nat.strong_induction_on with n ih generalizing α
  -- ⊢ P α
  cases' subsingleton_or_nontrivial α with hsing hnontriv
  -- ⊢ P α
  · apply hbase
    -- 🎉 no goals
  · apply hstep
    -- ⊢ ∀ (β : Type u_4) [inst : Fintype β], card β < card α → P β
    intro β _ hlt
    -- ⊢ P β
    rw [hn] at hlt
    -- ⊢ P β
    exact ih (Fintype.card β) hlt _ rfl
    -- 🎉 no goals
#align fintype.induction_subsingleton_or_nontrivial Fintype.induction_subsingleton_or_nontrivial

namespace Tactic

--open Positivity

private theorem card_univ_pos (α : Type*) [Fintype α] [Nonempty α] :
    0 < (Finset.univ : Finset α).card :=
  Finset.univ_nonempty.card_pos

--Porting note(https://github.com/leanprover-community/mathlib4/issues/6038): restore
-- /-- Extension for the `positivity` tactic: `finset.card s` is positive if `s` is nonempty. -/
-- @[positivity]
-- unsafe def positivity_finset_card : expr → tactic strictness
--   | q(Finset.card $(s)) => do
--     let p
--       ←-- TODO: Partial decision procedure for `finset.nonempty`
--             to_expr
--             ``(Finset.Nonempty $(s)) >>=
--           find_assumption
--     positive <$> mk_app `` Finset.Nonempty.card_pos [p]
--   | q(@Fintype.card $(α) $(i)) => positive <$> mk_mapp `` Fintype.card_pos [α, i, none]
--   | e =>
--     pp e >>=
--       fail ∘
--       format.bracket "The expression `" "` isn't of the form `finset.card s` or `fintype.card α`"
-- #align tactic.positivity_finset_card tactic.positivity_finset_card

end Tactic
