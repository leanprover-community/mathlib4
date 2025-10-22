/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.NodupEquivFin

/-!
# Equivalences between `Fintype`, `Fin` and `Finite`

This file defines the bijection between a `Fintype α` and `Fin (Fintype.card α)`, and uses this to
relate `Fintype` with `Finite`. From that we can derive properties of `Finite` and `Infinite`,
and show some instances of `Infinite`.

## Main declarations

* `Fintype.truncEquivFin`: A fintype `α` is computably equivalent to `Fin (card α)`. The
  `Trunc`-free, noncomputable version is `Fintype.equivFin`.
* `Fintype.truncEquivOfCardEq` `Fintype.equivOfCardEq`: Two fintypes of same cardinality are
  equivalent. See above.
* `Fin.equiv_iff_eq`: `Fin m ≃ Fin n` iff `m = n`.
* `Infinite.natEmbedding`: An embedding of `ℕ` into an infinite type.

Types which have an injection from/a surjection to an `Infinite` type are themselves `Infinite`.
See `Infinite.of_injective` and `Infinite.of_surjective`.

## Instances

We provide `Infinite` instances for
* specific types: `ℕ`, `ℤ`, `String`
* type constructors: `Multiset α`, `List α`

-/

assert_not_exists Monoid

open Function

universe u v

variable {α β γ : Type*}

open Finset

namespace Fintype

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

end Fintype

namespace Fintype

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

end Fintype

/-!
### Relation to `Finite`

In this section we prove that `α : Type*` is `Finite` if and only if `Fintype α` is nonempty.
-/

protected theorem Fintype.finite {α : Type*} (_inst : Fintype α) : Finite α :=
  ⟨Fintype.equivFin α⟩

/-- For efficiency reasons, we want `Finite` instances to have higher
priority than ones coming from `Fintype` instances. -/
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

namespace Fintype

variable [Fintype α] [Fintype β]

theorem card_eq_one_iff : card α = 1 ↔ ∃ x : α, ∀ y, y = x := by
  rw [← card_unit, card_eq]
  exact
    ⟨fun ⟨a⟩ => ⟨a.symm (), fun y => a.injective (Subsingleton.elim _ _)⟩,
     fun ⟨x, hx⟩ =>
      ⟨⟨fun _ => (), fun _ => x, fun _ => (hx _).trans (hx _).symm, fun _ =>
          Subsingleton.elim _ _⟩⟩⟩

theorem card_eq_one_iff_nonempty_unique : card α = 1 ↔ Nonempty (Unique α) :=
  ⟨fun h =>
    let ⟨d, h⟩ := Fintype.card_eq_one_iff.mp h
    ⟨{  default := d
        uniq := h }⟩,
    fun ⟨_h⟩ => Fintype.card_unique⟩

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

theorem one_lt_card [h : Nontrivial α] : 1 < Fintype.card α :=
  Fintype.one_lt_card_iff_nontrivial.mpr h

theorem one_lt_card_iff : 1 < card α ↔ ∃ a b : α, a ≠ b :=
  one_lt_card_iff_nontrivial.trans nontrivial_iff

end Fintype

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

namespace Function.Embedding

/-- An embedding from a `Fintype` to itself can be promoted to an equivalence. -/
noncomputable def equivOfFiniteSelfEmbedding [Finite α] (e : α ↪ α) : α ≃ α :=
  Equiv.ofBijective e e.2.bijective_of_finite

@[simp]
theorem toEmbedding_equivOfFiniteSelfEmbedding [Finite α] (e : α ↪ α) :
    e.equivOfFiniteSelfEmbedding.toEmbedding = e := by
  ext
  rfl

/-- On a finite type, equivalence between the self-embeddings and the bijections. -/
@[simps] noncomputable def _root_.Equiv.embeddingEquivOfFinite (α : Type*) [Finite α] :
    (α ↪ α) ≃ (α ≃ α) where
  toFun e := e.equivOfFiniteSelfEmbedding
  invFun e := e.toEmbedding

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

theorem exists_notMem_finset [Infinite α] (s : Finset α) : ∃ x, x ∉ s :=
  not_forall.1 fun h => Fintype.false ⟨s, h⟩

@[deprecated (since := "2025-05-23")] alias exists_not_mem_finset := exists_notMem_finset

-- see Note [lower instance priority]
instance (priority := 100) (α : Type*) [Infinite α] : Nontrivial α :=
  ⟨let ⟨x, _hx⟩ := exists_notMem_finset (∅ : Finset α)
    let ⟨y, hy⟩ := exists_notMem_finset ({x} : Finset α)
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
    exact (Finset.range _).card_le_univ.not_gt ((Nat.lt_succ_self _).trans_eq (card_range _).symm)

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

namespace Infinite

private noncomputable def natEmbeddingAux (α : Type*) [Infinite α] : ℕ → α
  | n =>
    letI := Classical.decEq α
    Classical.choose
      (exists_notMem_finset
        ((Multiset.range n).pmap (fun m (_ : m < n) => natEmbeddingAux _ m) fun _ =>
            Multiset.mem_range.1).toFinset)

private theorem natEmbeddingAux_injective (α : Type*) [Infinite α] :
    Function.Injective (natEmbeddingAux α) := by
  rintro m n h
  letI := Classical.decEq α
  wlog hmlen : m ≤ n generalizing m n
  · exact (this h.symm <| le_of_not_ge hmlen).symm
  by_contra hmn
  have hmn : m < n := lt_of_le_of_ne hmlen hmn
  refine (Classical.choose_spec (exists_notMem_finset
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
  induction n generalizing s with
  | zero => exact ⟨s, subset_rfl, Nat.eq_zero_of_le_zero hn⟩
  | succ n IH =>
    rcases hn.eq_or_lt with hn' | hn'
    · exact ⟨s, subset_rfl, hn'⟩
    obtain ⟨t, hs, ht⟩ := IH _ (Nat.le_of_lt_succ hn')
    obtain ⟨x, hx⟩ := exists_notMem_finset t
    refine ⟨Finset.cons x t hx, hs.trans (Finset.subset_cons _), ?_⟩
    simp [ht]

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

instance Function.Embedding.is_empty {α β} [Infinite α] [Finite β] : IsEmpty (α ↪ β) :=
  ⟨fun f => not_injective_infinite_finite f f.2⟩

theorem not_surjective_finite_infinite {α β} [Finite α] [Infinite β] (f : α → β) : ¬Surjective f :=
  fun hf => (Infinite.of_surjective f hf).not_finite ‹_›
