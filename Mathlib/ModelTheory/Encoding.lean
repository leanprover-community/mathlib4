/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Computability.Encoding
import Mathlib.Logic.Small.List
import Mathlib.ModelTheory.Syntax
import Mathlib.SetTheory.Cardinal.Ordinal

#align_import model_theory.encoding from "leanprover-community/mathlib"@"91288e351d51b3f0748f0a38faa7613fb0ae2ada"

/-! # Encodings and Cardinality of First-Order Syntax

## Main Definitions
* `FirstOrder.Language.Term.encoding` encodes terms as lists.
* `FirstOrder.Language.BoundedFormula.encoding` encodes bounded formulas as lists.

## Main Results
* `FirstOrder.Language.Term.card_le` shows that the number of terms in `L.Term α` is at most
`max ℵ₀ # (α ⊕ Σ i, L.Functions i)`.
* `FirstOrder.Language.BoundedFormula.card_le` shows that the number of bounded formulas in
`Σ n, L.BoundedFormula α n` is at most
`max ℵ₀ (Cardinal.lift.{max u v} #α + Cardinal.lift.{u'} L.card)`.

## TODO
* `Primcodable` instances for terms and formulas, based on the `encoding`s
* Computability facts about term and formula operations, to set up a computability approach to
incompleteness

-/


universe u v w u' v'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}
variable {M : Type w} {N P : Type*} [L.Structure M] [L.Structure N] [L.Structure P]
variable {α : Type u'} {β : Type v'}

open FirstOrder Cardinal

open Computability List Structure Cardinal Fin

namespace Term

/-- Encodes a term as a list of variables and function symbols. -/
def listEncode : L.Term α → List (Sum α (Σi, L.Functions i))
  | var i => [Sum.inl i]
  | func f ts =>
    Sum.inr (⟨_, f⟩ : Σi, L.Functions i)::(List.finRange _).bind fun i => (ts i).listEncode
#align first_order.language.term.list_encode FirstOrder.Language.Term.listEncode

/-- Decodes a list of variables and function symbols as a list of terms. -/
def listDecode : List (Sum α (Σi, L.Functions i)) → List (Option (L.Term α))
  | [] => []
  | Sum.inl a::l => some (var a)::listDecode l
  | Sum.inr ⟨n, f⟩::l =>
    if h : ∀ i : Fin n, ((listDecode l).get? i).join.isSome then
      (func f fun i => Option.get _ (h i))::(listDecode l).drop n
    else [none]
#align first_order.language.term.list_decode FirstOrder.Language.Term.listDecode

theorem listDecode_encode_list (l : List (L.Term α)) :
    listDecode (l.bind listEncode) = l.map Option.some := by
  suffices h : ∀ (t : L.Term α) (l : List (Sum α (Σi, L.Functions i))),
      listDecode (t.listEncode ++ l) = some t::listDecode l by
    induction' l with t l lih
    · rfl
    · rw [cons_bind, h t (l.bind listEncode), lih, List.map]
  intro t
  induction' t with a n f ts ih <;> intro l
  · rw [listEncode, singleton_append, listDecode]
  · rw [listEncode, cons_append, listDecode]
    have h : listDecode (((finRange n).bind fun i : Fin n => (ts i).listEncode) ++ l) =
        (finRange n).map (Option.some ∘ ts) ++ listDecode l := by
      induction' finRange n with i l' l'ih
      · rfl
      · rw [cons_bind, List.append_assoc, ih, map_cons, l'ih, cons_append, Function.comp]
    have h' : ∀ i : Fin n,
        (listDecode (((finRange n).bind fun i : Fin n => (ts i).listEncode) ++ l)).get? ↑i =
          some (some (ts i)) := by
      intro i
      rw [h, get?_append, get?_map]
      · simp only [Option.map_eq_some', Function.comp_apply, get?_eq_some]
        refine ⟨i, ⟨lt_of_lt_of_le i.2 (ge_of_eq (length_finRange _)), ?_⟩, rfl⟩
        rw [get_finRange, Fin.eta]
      · refine lt_of_lt_of_le i.2 ?_
        simp
    refine (dif_pos fun i => Option.isSome_iff_exists.2 ⟨ts i, ?_⟩).trans ?_
    · rw [Option.join_eq_some, h']
    refine congr (congr rfl (congr rfl (congr rfl (funext fun i => Option.get_of_mem _ ?_)))) ?_
    · simp [h']
    · rw [h, drop_left']
      rw [length_map, length_finRange]
#align first_order.language.term.list_decode_encode_list FirstOrder.Language.Term.listDecode_encode_list

/-- An encoding of terms as lists. -/
@[simps]
protected def encoding : Encoding (L.Term α) where
  Γ := Sum α (Σi, L.Functions i)
  encode := listEncode
  decode l := (listDecode l).head?.join
  decode_encode t := by
    have h := listDecode_encode_list [t]
    rw [bind_singleton] at h
    simp only [h, Option.join, head?, List.map, Option.some_bind, id]
#align first_order.language.term.encoding FirstOrder.Language.Term.encoding

theorem listEncode_injective :
    Function.Injective (listEncode : L.Term α → List (Sum α (Σi, L.Functions i))) :=
  Term.encoding.encode_injective
#align first_order.language.term.list_encode_injective FirstOrder.Language.Term.listEncode_injective

theorem card_le : #(L.Term α) ≤ max ℵ₀ #(Sum α (Σi, L.Functions i)) :=
  lift_le.1 (_root_.trans Term.encoding.card_le_card_list (lift_le.2 (mk_list_le_max _)))
#align first_order.language.term.card_le FirstOrder.Language.Term.card_le

theorem card_sigma : #(Σn, L.Term (Sum α (Fin n))) = max ℵ₀ #(Sum α (Σi, L.Functions i)) := by
  refine le_antisymm ?_ ?_
  · rw [mk_sigma]
    refine (sum_le_iSup_lift _).trans ?_
    rw [mk_nat, lift_aleph0, mul_eq_max_of_aleph0_le_left le_rfl, max_le_iff,
      ciSup_le_iff' (bddAbove_range _)]
    · refine ⟨le_max_left _ _, fun i => card_le.trans ?_⟩
      refine max_le (le_max_left _ _) ?_
      rw [← add_eq_max le_rfl, mk_sum, mk_sum, mk_sum, add_comm (Cardinal.lift #α), lift_add,
        add_assoc, lift_lift, lift_lift, mk_fin, lift_natCast]
      exact add_le_add_right (nat_lt_aleph0 _).le _
    · rw [← one_le_iff_ne_zero]
      refine _root_.trans ?_ (le_ciSup (bddAbove_range _) 1)
      rw [one_le_iff_ne_zero, mk_ne_zero_iff]
      exact ⟨var (Sum.inr 0)⟩
  · rw [max_le_iff, ← infinite_iff]
    refine ⟨Infinite.of_injective (fun i => ⟨i + 1, var (Sum.inr i)⟩) fun i j ij => ?_, ?_⟩
    · cases ij
      rfl
    · rw [Cardinal.le_def]
      refine ⟨⟨Sum.elim (fun i => ⟨0, var (Sum.inl i)⟩)
        fun F => ⟨1, func F.2 fun _ => var (Sum.inr 0)⟩, ?_⟩⟩
      rintro (a | a) (b | b) h
      · simp only [Sum.elim_inl, Sigma.mk.inj_iff, heq_eq_eq, var.injEq, Sum.inl.injEq, true_and]
          at h
        rw [h]
      · simp only [Sum.elim_inl, Sum.elim_inr, Sigma.mk.inj_iff, false_and] at h
      · simp only [Sum.elim_inr, Sum.elim_inl, Sigma.mk.inj_iff, false_and] at h
      · simp only [Sum.elim_inr, Sigma.mk.inj_iff, heq_eq_eq, func.injEq, true_and] at h
        rw [Sigma.ext_iff.2 ⟨h.1, h.2.1⟩]
#align first_order.language.term.card_sigma FirstOrder.Language.Term.card_sigma

instance [Encodable α] [Encodable (Σi, L.Functions i)] : Encodable (L.Term α) :=
  Encodable.ofLeftInjection listEncode (fun l => (listDecode l).head?.join) fun t => by
    simp only
    rw [← bind_singleton listEncode, listDecode_encode_list]
    simp only [Option.join, head?, List.map, Option.some_bind, id]

instance [h1 : Countable α] [h2 : Countable (Σl, L.Functions l)] : Countable (L.Term α) := by
  refine mk_le_aleph0_iff.1 (card_le.trans (max_le_iff.2 ?_))
  simp only [le_refl, mk_sum, add_le_aleph0, lift_le_aleph0, true_and_iff]
  exact ⟨Cardinal.mk_le_aleph0, Cardinal.mk_le_aleph0⟩

instance small [Small.{u} α] : Small.{u} (L.Term α) :=
  small_of_injective listEncode_injective
#align first_order.language.term.small FirstOrder.Language.Term.small

end Term

namespace BoundedFormula

/-- Encodes a bounded formula as a list of symbols. -/
def listEncode : ∀ {n : ℕ},
    L.BoundedFormula α n → List (Sum (Σk, L.Term (Sum α (Fin k))) (Sum (Σn, L.Relations n) ℕ))
  | n, falsum => [Sum.inr (Sum.inr (n + 2))]
  | _, equal t₁ t₂ => [Sum.inl ⟨_, t₁⟩, Sum.inl ⟨_, t₂⟩]
  | n, rel R ts => [Sum.inr (Sum.inl ⟨_, R⟩), Sum.inr (Sum.inr n)] ++
      (List.finRange _).map fun i => Sum.inl ⟨n, ts i⟩
  | _, imp φ₁ φ₂ => (Sum.inr (Sum.inr 0)::φ₁.listEncode) ++ φ₂.listEncode
  | _, all φ => Sum.inr (Sum.inr 1)::φ.listEncode
#align first_order.language.bounded_formula.list_encode FirstOrder.Language.BoundedFormula.listEncode

/-- Applies the `forall` quantifier to an element of `(Σ n, L.BoundedFormula α n)`,
or returns `default` if not possible. -/
def sigmaAll : (Σn, L.BoundedFormula α n) → Σn, L.BoundedFormula α n
  | ⟨n + 1, φ⟩ => ⟨n, φ.all⟩
  | _ => default
#align first_order.language.bounded_formula.sigma_all FirstOrder.Language.BoundedFormula.sigmaAll

/-- Applies `imp` to two elements of `(Σ n, L.BoundedFormula α n)`,
or returns `default` if not possible. -/
def sigmaImp : (Σn, L.BoundedFormula α n) → (Σn, L.BoundedFormula α n) → Σn, L.BoundedFormula α n
  | ⟨m, φ⟩, ⟨n, ψ⟩ => if h : m = n then ⟨m, φ.imp (Eq.mp (by rw [h]) ψ)⟩ else default
#align first_order.language.bounded_formula.sigma_imp FirstOrder.Language.BoundedFormula.sigmaImp

/-- Decodes a list of symbols as a list of formulas. -/
@[simp]
def listDecode : ∀ l : List (Sum (Σk, L.Term (Sum α (Fin k))) (Sum (Σn, L.Relations n) ℕ)),
    (Σn, L.BoundedFormula α n) ×
    { l' : List (Sum (Σk, L.Term (Sum α (Fin k))) (Sum (Σn, L.Relations n) ℕ)) //
      SizeOf.sizeOf l' ≤ max 1 (SizeOf.sizeOf l) }
  | Sum.inr (Sum.inr (n + 2))::l => ⟨⟨n, falsum⟩, l, le_max_of_le_right le_add_self⟩
  | Sum.inl ⟨n₁, t₁⟩::Sum.inl ⟨n₂, t₂⟩::l =>
    ⟨if h : n₁ = n₂ then ⟨n₁, equal t₁ (Eq.mp (by rw [h]) t₂)⟩ else default, l, by
      simp only [SizeOf.sizeOf, List._sizeOf_1, ← add_assoc]
      exact le_max_of_le_right le_add_self⟩
  | Sum.inr (Sum.inl ⟨n, R⟩)::Sum.inr (Sum.inr k)::l =>
    ⟨if h : ∀ i : Fin n, ((l.map Sum.getLeft?).get? i).join.isSome then
        if h' : ∀ i, (Option.get _ (h i)).1 = k then
          ⟨k, BoundedFormula.rel R fun i => Eq.mp (by rw [h' i]) (Option.get _ (h i)).2⟩
        else default
      else default,
      l.drop n, le_max_of_le_right (le_add_left (le_add_left (List.drop_sizeOf_le _ _)))⟩
  | Sum.inr (Sum.inr 0)::l =>
    have : SizeOf.sizeOf
        (↑(listDecode l).2 : List (Sum (Σk, L.Term (Sum α (Fin k))) (Sum (Σn, L.Relations n) ℕ))) <
        1 + (1 + 1) + SizeOf.sizeOf l := by
      refine lt_of_le_of_lt (listDecode l).2.2 (max_lt ?_ (Nat.lt_add_of_pos_left (by decide)))
      rw [add_assoc, lt_add_iff_pos_right, add_pos_iff]
      exact Or.inl zero_lt_two
    ⟨sigmaImp (listDecode l).1 (listDecode (listDecode l).2).1,
      (listDecode (listDecode l).2).2,
      le_max_of_le_right
        (_root_.trans (listDecode _).2.2
          (max_le (le_add_right le_self_add)
            (_root_.trans (listDecode _).2.2 (max_le (le_add_right le_self_add) le_add_self))))⟩
  | Sum.inr (Sum.inr 1)::l =>
    ⟨sigmaAll (listDecode l).1, (listDecode l).2,
      (listDecode l).2.2.trans (max_le_max le_rfl le_add_self)⟩
  | _ => ⟨default, [], le_max_left _ _⟩
#align first_order.language.bounded_formula.list_decode FirstOrder.Language.BoundedFormula.listDecode

@[simp]
theorem listDecode_encode_list (l : List (Σn, L.BoundedFormula α n)) :
    (listDecode (l.bind fun φ => φ.2.listEncode)).1 = l.headI := by
  suffices h : ∀ (φ : Σn, L.BoundedFormula α n) (l),
      (listDecode (listEncode φ.2 ++ l)).1 = φ ∧ (listDecode (listEncode φ.2 ++ l)).2.1 = l by
    induction' l with φ l _
    · rw [List.nil_bind]
      simp [listDecode]
    · rw [cons_bind, (h φ _).1, headI_cons]
  rintro ⟨n, φ⟩
  induction' φ with _ _ _ _ φ_n φ_l φ_R ts _ _ _ ih1 ih2 _ _ ih <;> intro l
  · rw [listEncode, singleton_append, listDecode]
    simp only [eq_self_iff_true, heq_iff_eq, and_self_iff]
  · rw [listEncode, cons_append, cons_append, listDecode, dif_pos]
    · simp only [eq_mp_eq_cast, cast_eq, eq_self_iff_true, heq_iff_eq, and_self_iff, nil_append]
    · simp only [eq_self_iff_true, heq_iff_eq, and_self_iff]
  · rw [listEncode, cons_append, cons_append, singleton_append, cons_append, listDecode]
    have h : ∀ i : Fin φ_l, ((List.map Sum.getLeft? (List.map (fun i : Fin φ_l =>
      Sum.inl (⟨(⟨φ_n, rel φ_R ts⟩ : Σn, L.BoundedFormula α n).fst, ts i⟩ :
        Σn, L.Term (Sum α (Fin n)))) (finRange φ_l) ++ l)).get? ↑i).join = some ⟨_, ts i⟩ := by
      intro i
      simp only [Option.join, map_append, map_map, Option.bind_eq_some, id, exists_eq_right,
        get?_eq_some, length_append, length_map, length_finRange]
      refine ⟨lt_of_lt_of_le i.2 le_self_add, ?_⟩
      rw [get_append, get_map]
      · simp only [Sum.getLeft?, get_finRange, Fin.eta, Function.comp_apply, eq_self_iff_true,
          heq_iff_eq, and_self_iff]
      · simp only [length_map, length_finRange, is_lt]
    rw [dif_pos]
    swap
    · exact fun i => Option.isSome_iff_exists.2 ⟨⟨_, ts i⟩, h i⟩
    rw [dif_pos]
    swap
    · intro i
      obtain ⟨h1, h2⟩ := Option.eq_some_iff_get_eq.1 (h i)
      rw [h2]
    simp only [Sigma.mk.inj_iff, heq_eq_eq, rel.injEq, true_and]
    refine ⟨funext fun i => ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := Option.eq_some_iff_get_eq.1 (h i)
      rw [eq_mp_eq_cast, cast_eq_iff_heq]
      exact (Sigma.ext_iff.1 ((Sigma.eta (Option.get _ h1)).trans h2)).2
    rw [List.drop_append_eq_append_drop, length_map, length_finRange, Nat.sub_self, drop,
      drop_eq_nil_of_le, nil_append]
    rw [length_map, length_finRange]
  · rw [listEncode, List.append_assoc, cons_append, listDecode]
    simp only [] at *
    rw [(ih1 _).1, (ih1 _).2, (ih2 _).1, (ih2 _).2, sigmaImp]
    simp only [dite_true]
    exact ⟨rfl, trivial⟩
  · rw [listEncode, cons_append, listDecode]
    simp only
    simp only [] at *
    rw [(ih _).1, (ih _).2, sigmaAll]
    exact ⟨rfl, rfl⟩
#align first_order.language.bounded_formula.list_decode_encode_list FirstOrder.Language.BoundedFormula.listDecode_encode_list

/-- An encoding of bounded formulas as lists. -/
@[simps]
protected def encoding : Encoding (Σn, L.BoundedFormula α n) where
  Γ := Sum (Σk, L.Term (Sum α (Fin k))) (Sum (Σn, L.Relations n) ℕ)
  encode φ := φ.2.listEncode
  decode l := (listDecode l).1
  decode_encode φ := by
    have h := listDecode_encode_list [φ]
    rw [bind_singleton] at h
    simp only
    rw [h]
    rfl
#align first_order.language.bounded_formula.encoding FirstOrder.Language.BoundedFormula.encoding

theorem listEncode_sigma_injective :
    Function.Injective fun φ : Σn, L.BoundedFormula α n => φ.2.listEncode :=
  BoundedFormula.encoding.encode_injective
#align first_order.language.bounded_formula.list_encode_sigma_injective FirstOrder.Language.BoundedFormula.listEncode_sigma_injective

theorem card_le : #(Σn, L.BoundedFormula α n) ≤
    max ℵ₀ (Cardinal.lift.{max u v} #α + Cardinal.lift.{u'} L.card) := by
  refine lift_le.1 (BoundedFormula.encoding.card_le_card_list.trans ?_)
  rw [encoding_Γ, mk_list_eq_max_mk_aleph0, lift_max, lift_aleph0, lift_max, lift_aleph0,
    max_le_iff]
  refine ⟨?_, le_max_left _ _⟩
  rw [mk_sum, Term.card_sigma, mk_sum, ← add_eq_max le_rfl, mk_sum, mk_nat]
  simp only [lift_add, lift_lift, lift_aleph0]
  rw [← add_assoc, add_comm, ← add_assoc, ← add_assoc, aleph0_add_aleph0, add_assoc,
    add_eq_max le_rfl, add_assoc, card, Symbols, mk_sum, lift_add, lift_lift, lift_lift]
#align first_order.language.bounded_formula.card_le FirstOrder.Language.BoundedFormula.card_le

end BoundedFormula

end Language

end FirstOrder
