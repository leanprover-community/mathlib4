/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.List.FinRange

/-!
# Instances for finite types

This file is a collection of basic `Fintype` instances for types such as `Fin`, `Prod` and pi types.
-/

assert_not_exists Monoid

open Function

open Nat

universe u v

variable {α β γ : Type*}

open Finset

instance Fin.fintype (n : ℕ) : Fintype (Fin n) :=
  ⟨⟨List.finRange n, List.nodup_finRange n⟩, List.mem_finRange⟩

theorem Fin.univ_def (n : ℕ) : (univ : Finset (Fin n)) = ⟨List.finRange n, List.nodup_finRange n⟩ :=
  rfl

theorem Finset.val_univ_fin (n : ℕ) : (Finset.univ : Finset (Fin n)).val = List.finRange n := rfl

/-- See also `nonempty_encodable`, `nonempty_denumerable`. -/
theorem nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fintype α) := by
  rcases Finite.exists_equiv_fin α with ⟨n, ⟨e⟩⟩
  exact ⟨.ofEquiv _ e.symm⟩

@[simp] theorem List.toFinset_finRange (n : ℕ) : (List.finRange n).toFinset = Finset.univ := by
  ext; simp

@[simp] theorem Fin.univ_val_map {n : ℕ} (f : Fin n → α) :
    Finset.univ.val.map f = List.ofFn f := by
  simp [List.ofFn_eq_map, univ_def]

theorem Fin.univ_image_def {n : ℕ} [DecidableEq α] (f : Fin n → α) :
    Finset.univ.image f = (List.ofFn f).toFinset := by
  simp [Finset.image]

theorem Fin.univ_map_def {n : ℕ} (f : Fin n ↪ α) :
    Finset.univ.map f = ⟨List.ofFn f, List.nodup_ofFn.mpr f.injective⟩ := by
  simp [Finset.map]

@[simp]
theorem Fin.image_succAbove_univ {n : ℕ} (i : Fin (n + 1)) : univ.image i.succAbove = {i}ᶜ := by
  ext m
  simp

@[simp]
theorem Fin.image_succ_univ (n : ℕ) : (univ : Finset (Fin n)).image Fin.succ = {0}ᶜ := by
  rw [← Fin.succAbove_zero, Fin.image_succAbove_univ]

@[simp]
theorem Fin.image_castSucc (n : ℕ) :
    (univ : Finset (Fin n)).image Fin.castSucc = {Fin.last n}ᶜ := by
  rw [← Fin.succAbove_last, Fin.image_succAbove_univ]

/- The following three lemmas use `Finset.cons` instead of `insert` and `Finset.map` instead of
`Finset.image` to reduce proof obligations downstream. -/
/-- Embed `Fin n` into `Fin (n + 1)` by prepending zero to the `univ` -/
theorem Fin.univ_succ (n : ℕ) :
    (univ : Finset (Fin (n + 1))) =
      Finset.cons 0 (univ.map ⟨Fin.succ, Fin.succ_injective _⟩) (by simp [map_eq_image]) := by
  simp [map_eq_image]

/-- Embed `Fin n` into `Fin (n + 1)` by appending a new `Fin.last n` to the `univ` -/
theorem Fin.univ_castSuccEmb (n : ℕ) :
    (univ : Finset (Fin (n + 1))) =
      Finset.cons (Fin.last n) (univ.map Fin.castSuccEmb) (by simp [map_eq_image]) := by
  simp [map_eq_image]

/-- Embed `Fin n` into `Fin (n + 1)` by inserting
around a specified pivot `p : Fin (n + 1)` into the `univ` -/
theorem Fin.univ_succAbove (n : ℕ) (p : Fin (n + 1)) :
    (univ : Finset (Fin (n + 1))) = Finset.cons p (univ.map <| Fin.succAboveEmb p) (by simp) := by
  simp [map_eq_image]

@[simp] theorem Fin.univ_image_get [DecidableEq α] (l : List α) :
    Finset.univ.image l.get = l.toFinset := by
  simp [univ_image_def]

@[simp] theorem Fin.univ_image_getElem' [DecidableEq β] (l : List α) (f : α → β) :
    Finset.univ.image (fun i : Fin l.length => f <| l[(i : Nat)]) = (l.map f).toFinset := by
  simp only [univ_image_def, List.ofFn_getElem_eq_map]

theorem Fin.univ_image_get' [DecidableEq β] (l : List α) (f : α → β) :
    Finset.univ.image (f <| l.get ·) = (l.map f).toFinset := by
  simp

@[instance]
def Unique.fintype {α : Type*} [Unique α] : Fintype α :=
  Fintype.ofSubsingleton default

/-- Short-circuit instance to decrease search for `Unique.fintype`,
since that relies on a subsingleton elimination for `Unique`. -/
instance Fintype.subtypeEq (y : α) : Fintype { x // x = y } :=
  Fintype.subtype {y} (by simp)

/-- Short-circuit instance to decrease search for `Unique.fintype`,
since that relies on a subsingleton elimination for `Unique`. -/
instance Fintype.subtypeEq' (y : α) : Fintype { x // y = x } :=
  Fintype.subtype {y} (by simp [eq_comm])

theorem Fintype.univ_empty : @univ Empty _ = ∅ :=
  rfl

theorem Fintype.univ_pempty : @univ PEmpty _ = ∅ :=
  rfl

instance Unit.fintype : Fintype Unit :=
  Fintype.ofSubsingleton ()

theorem Fintype.univ_unit : @univ Unit _ = {()} :=
  rfl

instance PUnit.fintype : Fintype PUnit :=
  Fintype.ofSubsingleton PUnit.unit

theorem Fintype.univ_punit : @univ PUnit _ = {PUnit.unit} :=
  rfl

@[simp]
theorem Fintype.univ_bool : @univ Bool _ = {true, false} :=
  rfl

/-- Given that `α × β` is a fintype, `α` is also a fintype. -/
def Fintype.prodLeft {α β} [DecidableEq α] [Fintype (α × β)] [Nonempty β] : Fintype α :=
  ⟨(@univ (α × β) _).image Prod.fst, fun a => by simp⟩

/-- Given that `α × β` is a fintype, `β` is also a fintype. -/
def Fintype.prodRight {α β} [DecidableEq β] [Fintype (α × β)] [Nonempty α] : Fintype β :=
  ⟨(@univ (α × β) _).image Prod.snd, fun b => by simp⟩

instance ULift.fintype (α : Type*) [Fintype α] : Fintype (ULift α) :=
  Fintype.ofEquiv _ Equiv.ulift.symm

instance PLift.fintype (α : Type*) [Fintype α] : Fintype (PLift α) :=
  Fintype.ofEquiv _ Equiv.plift.symm

instance PLift.fintypeProp (p : Prop) [Decidable p] : Fintype (PLift p) :=
  ⟨if h : p then {⟨h⟩} else ∅, fun ⟨h⟩ => by simp [h]⟩

instance Quotient.fintype [Fintype α] (s : Setoid α) [DecidableRel ((· ≈ ·) : α → α → Prop)] :
    Fintype (Quotient s) :=
  Fintype.ofSurjective Quotient.mk'' Quotient.mk''_surjective

instance PSigma.fintypePropLeft {α : Prop} {β : α → Type*} [Decidable α] [∀ a, Fintype (β a)] :
    Fintype (Σ' a, β a) :=
  if h : α then Fintype.ofEquiv (β h) ⟨fun x => ⟨h, x⟩, PSigma.snd, fun _ => rfl, fun ⟨_, _⟩ => rfl⟩
  else ⟨∅, fun x => (h x.1).elim⟩

instance PSigma.fintypePropRight {α : Type*} {β : α → Prop} [∀ a, Decidable (β a)] [Fintype α] :
    Fintype (Σ' a, β a) :=
  Fintype.ofEquiv { a // β a }
    ⟨fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨_, _⟩ => rfl, fun ⟨_, _⟩ => rfl⟩

instance PSigma.fintypePropProp {α : Prop} {β : α → Prop} [Decidable α] [∀ a, Decidable (β a)] :
    Fintype (Σ' a, β a) :=
  if h : ∃ a, β a then ⟨{⟨h.fst, h.snd⟩}, fun ⟨_, _⟩ => by simp⟩ else ⟨∅, fun ⟨x, y⟩ =>
    (h ⟨x, y⟩).elim⟩

instance pfunFintype (p : Prop) [Decidable p] (α : p → Type*) [∀ hp, Fintype (α hp)] :
    Fintype (∀ hp : p, α hp) :=
  if hp : p then Fintype.ofEquiv (α hp) ⟨fun a _ => a, fun f => f hp, fun _ => rfl, fun _ => rfl⟩
  else ⟨singleton fun h => (hp h).elim, fun h => mem_singleton.2
    (funext fun x => by contradiction)⟩

section Trunc

/-- For `s : Multiset α`, we can lift the existential statement that `∃ x, x ∈ s` to a `Trunc α`.
-/
def truncOfMultisetExistsMem {α} (s : Multiset α) : (∃ x, x ∈ s) → Trunc α :=
  Quotient.recOnSubsingleton s fun l h =>
    match l, h with
    | [], _ => False.elim (by tauto)
    | a :: _, _ => Trunc.mk a

/-- A `Nonempty` `Fintype` constructively contains an element.
-/
def truncOfNonemptyFintype (α) [Nonempty α] [Fintype α] : Trunc α :=
  truncOfMultisetExistsMem Finset.univ.val (by simp)

/-- By iterating over the elements of a fintype, we can lift an existential statement `∃ a, P a`
to `Trunc (Σ' a, P a)`, containing data.
-/
def truncSigmaOfExists {α} [Fintype α] {P : α → Prop} [DecidablePred P] (h : ∃ a, P a) :
    Trunc (Σ' a, P a) :=
  @truncOfNonemptyFintype (Σ' a, P a) ((Exists.elim h) fun a ha => ⟨⟨a, ha⟩⟩) _

end Trunc

namespace Multiset

variable [Fintype α] [Fintype β]

@[simp]
theorem count_univ [DecidableEq α] (a : α) : count a Finset.univ.val = 1 :=
  count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ _)

@[simp]
theorem map_univ_val_equiv (e : α ≃ β) :
    map e univ.val = univ.val := by
  rw [← congr_arg Finset.val (Finset.map_univ_equiv e), Finset.map_val, Equiv.coe_toEmbedding]

/-- For functions on finite sets, they are bijections iff they map universes into universes. -/
@[simp]
theorem bijective_iff_map_univ_eq_univ (f : α → β) :
    f.Bijective ↔ map f (Finset.univ : Finset α).val = univ.val :=
  ⟨fun bij ↦ congr_arg (·.val) (map_univ_equiv <| Equiv.ofBijective f bij),
    fun eq ↦ ⟨
      fun a₁ a₂ ↦ inj_on_of_nodup_map (eq.symm ▸ univ.nodup) _ (mem_univ a₁) _ (mem_univ a₂),
      fun b ↦ have ⟨a, _, h⟩ := mem_map.mp (eq.symm ▸ mem_univ_val b); ⟨a, h⟩⟩⟩

end Multiset

/-- Auxiliary definition to show `exists_seq_of_forall_finset_exists`. -/
noncomputable def seqOfForallFinsetExistsAux {α : Type*} [DecidableEq α] (P : α → Prop)
    (r : α → α → Prop) (h : ∀ s : Finset α, ∃ y, (∀ x ∈ s, P x) → P y ∧ ∀ x ∈ s, r x y) : ℕ → α
  | n =>
    Classical.choose
      (h
        (Finset.image (fun i : Fin n => seqOfForallFinsetExistsAux P r h i)
          (Finset.univ : Finset (Fin n))))

/-- Induction principle to build a sequence, by adding one point at a time satisfying a given
relation with respect to all the previously chosen points.

More precisely, Assume that, for any finite set `s`, one can find another point satisfying
some relation `r` with respect to all the points in `s`. Then one may construct a
function `f : ℕ → α` such that `r (f m) (f n)` holds whenever `m < n`.
We also ensure that all constructed points satisfy a given predicate `P`. -/
theorem exists_seq_of_forall_finset_exists {α : Type*} (P : α → Prop) (r : α → α → Prop)
    (h : ∀ s : Finset α, (∀ x ∈ s, P x) → ∃ y, P y ∧ ∀ x ∈ s, r x y) :
    ∃ f : ℕ → α, (∀ n, P (f n)) ∧ ∀ m n, m < n → r (f m) (f n) := by
  classical
    have : Nonempty α := by
      rcases h ∅ (by simp) with ⟨y, _⟩
      exact ⟨y⟩
    choose! F hF using h
    have h' : ∀ s : Finset α, ∃ y, (∀ x ∈ s, P x) → P y ∧ ∀ x ∈ s, r x y := fun s => ⟨F s, hF s⟩
    set f := seqOfForallFinsetExistsAux P r h' with hf
    have A : ∀ n : ℕ, P (f n) := by
      intro n
      induction n using Nat.strong_induction_on with | _ n IH
      have IH' : ∀ x : Fin n, P (f x) := fun n => IH n.1 n.2
      rw [hf, seqOfForallFinsetExistsAux]
      exact
        (Classical.choose_spec
            (h' (Finset.image (fun i : Fin n => f i) (Finset.univ : Finset (Fin n))))
            (by simp [IH'])).1
    refine ⟨f, A, fun m n hmn => ?_⟩
    conv_rhs => rw [hf]
    rw [seqOfForallFinsetExistsAux]
    apply
      (Classical.choose_spec
          (h' (Finset.image (fun i : Fin n => f i) (Finset.univ : Finset (Fin n)))) (by simp [A])).2
    exact Finset.mem_image.2 ⟨⟨m, hmn⟩, Finset.mem_univ _, rfl⟩

/-- Induction principle to build a sequence, by adding one point at a time satisfying a given
symmetric relation with respect to all the previously chosen points.

More precisely, Assume that, for any finite set `s`, one can find another point satisfying
some relation `r` with respect to all the points in `s`. Then one may construct a
function `f : ℕ → α` such that `r (f m) (f n)` holds whenever `m ≠ n`.
We also ensure that all constructed points satisfy a given predicate `P`. -/
theorem exists_seq_of_forall_finset_exists' {α : Type*} (P : α → Prop) (r : α → α → Prop)
    [IsSymm α r] (h : ∀ s : Finset α, (∀ x ∈ s, P x) → ∃ y, P y ∧ ∀ x ∈ s, r x y) :
    ∃ f : ℕ → α, (∀ n, P (f n)) ∧ Pairwise (r on f) := by
  rcases exists_seq_of_forall_finset_exists P r h with ⟨f, hf, hf'⟩
  refine ⟨f, hf, fun m n hmn => ?_⟩
  rcases lt_trichotomy m n with (h | rfl | h)
  · exact hf' m n h
  · exact (hmn rfl).elim
  · unfold Function.onFun
    apply symm
    exact hf' n m h
