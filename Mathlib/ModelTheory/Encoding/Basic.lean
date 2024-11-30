/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Computability.Encoding.Basic
import Mathlib.Logic.Equiv.List
import Mathlib.ModelTheory.Syntax

/-!
# Encodings of First-Order Syntax

## Main Definitions

- `FirstOrder.Language.Term.encoding` encodes terms as lists.
- `FirstOrder.Language.BoundedFormula.encoding` encodes bounded formulas as lists.

## TODO

- `Primcodable` instances for terms and formulas, based on the `encoding`s
- Computability facts about term and formula operations, to set up a computability approach to
  incompleteness

-/

assert_not_exists Cardinal

universe u v w u'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}
variable {α : Type u'}

open FirstOrder

open Computability List Structure Fin

namespace Term

/-- Encodes a term as a list of variables and function symbols. -/
def listEncode : L.Term α → List (α ⊕ (Σi, L.Functions i))
  | var i => [Sum.inl i]
  | func f ts =>
    Sum.inr (⟨_, f⟩ : Σi, L.Functions i)::(List.finRange _).flatMap fun i => (ts i).listEncode

/-- Decodes a list of variables and function symbols as a list of terms. -/
def listDecode : List (α ⊕ (Σi, L.Functions i)) → List (L.Term α)
  | [] => []
  | Sum.inl a::l => (var a)::listDecode l
  | Sum.inr ⟨n, f⟩::l =>
    if h : n ≤ (listDecode l).length then
      (func f (fun i => (listDecode l)[i])) :: (listDecode l).drop n
    else []

theorem listDecode_encode_list (l : List (L.Term α)) :
    listDecode (l.flatMap listEncode) = l := by
  suffices h : ∀ (t : L.Term α) (l : List (α ⊕ (Σi, L.Functions i))),
      listDecode (t.listEncode ++ l) = t::listDecode l by
    induction' l with t l lih
    · rfl
    · rw [flatMap_cons, h t (l.flatMap listEncode), lih]
  intro t
  induction' t with a n f ts ih <;> intro l
  · rw [listEncode, singleton_append, listDecode]
  · rw [listEncode, cons_append, listDecode]
    have h : listDecode (((finRange n).flatMap fun i : Fin n => (ts i).listEncode) ++ l) =
        (finRange n).map ts ++ listDecode l := by
      induction' finRange n with i l' l'ih
      · rfl
      · rw [flatMap_cons, List.append_assoc, ih, map_cons, l'ih, cons_append]
    simp only [h, length_append, length_map, length_finRange, le_add_iff_nonneg_right,
      _root_.zero_le, ↓reduceDIte, getElem_fin, cons.injEq, func.injEq, heq_eq_eq, true_and]
    refine ⟨funext (fun i => ?_), ?_⟩
    · simp only [length_map, length_finRange, is_lt, getElem_append_left, getElem_map,
      getElem_finRange, cast_mk, Fin.eta]
    · simp only [length_map, length_finRange, drop_left']

/-- An encoding of terms as lists. -/
@[simps]
protected def encoding : Encoding (L.Term α) where
  Γ := α ⊕ (Σi, L.Functions i)
  encode := listEncode
  decode l := (listDecode l).head?.join
  decode_encode t := by
    have h := listDecode_encode_list [t]
    rw [flatMap_singleton] at h
    simp only [Option.join, h, head?_cons, Option.pure_def, Option.bind_eq_bind, Option.some_bind,
      id_eq]

theorem listEncode_injective :
    Function.Injective (listEncode : L.Term α → List (α ⊕ (Σi, L.Functions i))) :=
  Term.encoding.encode_injective

instance [Encodable α] [Encodable (Σi, L.Functions i)] : Encodable (L.Term α) :=
  Encodable.ofLeftInjection listEncode (fun l => (listDecode l).head?.join) fun t => by
    simp only
    rw [← flatMap_singleton listEncode, listDecode_encode_list]
    simp only [Option.join, head?_cons, Option.pure_def, Option.bind_eq_bind, Option.some_bind,
      id_eq]

end Term

namespace BoundedFormula

/-- Encodes a bounded formula as a list of symbols. -/
def listEncode : ∀ {n : ℕ},
    L.BoundedFormula α n → List ((Σk, L.Term (α ⊕ Fin k)) ⊕ ((Σn, L.Relations n) ⊕ ℕ))
  | n, falsum => [Sum.inr (Sum.inr (n + 2))]
  | _, equal t₁ t₂ => [Sum.inl ⟨_, t₁⟩, Sum.inl ⟨_, t₂⟩]
  | n, rel R ts => [Sum.inr (Sum.inl ⟨_, R⟩), Sum.inr (Sum.inr n)] ++
      (List.finRange _).map fun i => Sum.inl ⟨n, ts i⟩
  | _, imp φ₁ φ₂ => (Sum.inr (Sum.inr 0)::φ₁.listEncode) ++ φ₂.listEncode
  | _, all φ => Sum.inr (Sum.inr 1)::φ.listEncode

/-- Applies the `forall` quantifier to an element of `(Σ n, L.BoundedFormula α n)`,
or returns `default` if not possible. -/
def sigmaAll : (Σn, L.BoundedFormula α n) → Σn, L.BoundedFormula α n
  | ⟨n + 1, φ⟩ => ⟨n, φ.all⟩
  | _ => default


@[simp]
lemma sigmaAll_apply {n} {φ : L.BoundedFormula α (n + 1)} :
    sigmaAll ⟨n + 1, φ⟩ = ⟨n, φ.all⟩ := rfl

/-- Applies `imp` to two elements of `(Σ n, L.BoundedFormula α n)`,
or returns `default` if not possible. -/
def sigmaImp : (Σn, L.BoundedFormula α n) → (Σn, L.BoundedFormula α n) → Σn, L.BoundedFormula α n
  | ⟨m, φ⟩, ⟨n, ψ⟩ => if h : m = n then ⟨m, φ.imp (Eq.mp (by rw [h]) ψ)⟩ else default

/-- Decodes a list of symbols as a list of formulas. -/
@[simp]
lemma sigmaImp_apply {n} {φ ψ : L.BoundedFormula α n} :
    sigmaImp ⟨n, φ⟩ ⟨n, ψ⟩ = ⟨n, φ.imp ψ⟩ := by
  simp only [sigmaImp, ↓reduceDIte, eq_mp_eq_cast, cast_eq]

/-- Decodes a list of symbols as a list of formulas. -/
def listDecode :
    List ((Σk, L.Term (α ⊕ Fin k)) ⊕ ((Σn, L.Relations n) ⊕ ℕ)) → List (Σn, L.BoundedFormula α n)
  | Sum.inr (Sum.inr (n + 2))::l => ⟨n, falsum⟩::(listDecode l)
  | Sum.inl ⟨n₁, t₁⟩::Sum.inl ⟨n₂, t₂⟩::l =>
    (if h : n₁ = n₂ then ⟨n₁, equal t₁ (Eq.mp (by rw [h]) t₂)⟩ else default)::(listDecode l)
  | Sum.inr (Sum.inl ⟨n, R⟩)::Sum.inr (Sum.inr k)::l => (
    if h : ∀ i : Fin n, ((l.map Sum.getLeft?).get? i).join.isSome then
        if h' : ∀ i, (Option.get _ (h i)).1 = k then
          ⟨k, BoundedFormula.rel R fun i => Eq.mp (by rw [h' i]) (Option.get _ (h i)).2⟩
        else default
      else default)::(listDecode (l.drop n))
  | Sum.inr (Sum.inr 0)::l => if h : 2 ≤ (listDecode l).length
    then (sigmaImp (listDecode l)[0] (listDecode l)[1])::(drop 2 (listDecode l))
    else []
  | Sum.inr (Sum.inr 1)::l => if h : 1 ≤ (listDecode l).length
    then (sigmaAll (listDecode l)[0])::(drop 1 (listDecode l))
    else []
  | _ => []
  termination_by l => l.length

@[simp]
theorem listDecode_encode_list (l : List (Σn, L.BoundedFormula α n)) :
    listDecode (l.flatMap (fun φ => φ.2.listEncode)) = l := by
  suffices h : ∀ (φ : Σn, L.BoundedFormula α n)
      (l' : List ((Σk, L.Term (α ⊕ Fin k)) ⊕ ((Σn, L.Relations n) ⊕ ℕ))),
      (listDecode (listEncode φ.2 ++ l')) = φ::(listDecode l') by
    induction' l with φ l ih
    · rw [List.flatMap_nil]
      simp [listDecode]
    · rw [flatMap_cons, h φ _, ih]
  rintro ⟨n, φ⟩
  induction φ with
  | falsum => intro l; rw [listEncode, singleton_append, listDecode]
  | equal =>
    intro l
    rw [listEncode, cons_append, cons_append, listDecode, dif_pos]
    · simp only [eq_mp_eq_cast, cast_eq, eq_self_iff_true, heq_iff_eq, and_self_iff, nil_append]
    · simp only [eq_self_iff_true, heq_iff_eq, and_self_iff]
  | @rel φ_n φ_l φ_R ts =>
    intro l
    rw [listEncode, cons_append, cons_append, singleton_append, cons_append, listDecode]
    have h : ∀ i : Fin φ_l, ((List.map Sum.getLeft? (List.map (fun i : Fin φ_l =>
      Sum.inl (⟨(⟨φ_n, rel φ_R ts⟩ : Σn, L.BoundedFormula α n).fst, ts i⟩ :
        Σn, L.Term (α ⊕ (Fin n)))) (finRange φ_l) ++ l)).get? ↑i).join = some ⟨_, ts i⟩ := by
      intro i
      simp only [Option.join, map_append, map_map, Option.bind_eq_some, id, exists_eq_right,
        get?_eq_some, length_append, length_map, length_finRange]
      refine ⟨lt_of_lt_of_le i.2 le_self_add, ?_⟩
      rw [get_eq_getElem, getElem_append_left, getElem_map]
      · simp only [getElem_finRange, cast_mk, Fin.eta, Function.comp_apply, Sum.getLeft?_inl]
      · simp only [length_map, length_finRange, is_lt]
    rw [dif_pos]
    swap
    · exact fun i => Option.isSome_iff_exists.2 ⟨⟨_, ts i⟩, h i⟩
    rw [dif_pos]
    swap
    · intro i
      obtain ⟨h1, h2⟩ := Option.eq_some_iff_get_eq.1 (h i)
      rw [h2]
    simp only [Option.join, eq_mp_eq_cast, cons.injEq, Sigma.mk.inj_iff, heq_eq_eq, rel.injEq,
      true_and]
    refine ⟨funext fun i => ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := Option.eq_some_iff_get_eq.1 (h i)
      rw [cast_eq_iff_heq]
      exact (Sigma.ext_iff.1 ((Sigma.eta (Option.get _ h1)).trans h2)).2
    rw [List.drop_append_eq_append_drop, length_map, length_finRange, Nat.sub_self, drop,
      drop_eq_nil_of_le, nil_append]
    rw [length_map, length_finRange]
  | imp _ _ ih1 ih2 =>
    intro l
    simp only [] at *
    rw [listEncode, List.append_assoc, cons_append, listDecode]
    simp only [ih1, ih2, length_cons, le_add_iff_nonneg_left, _root_.zero_le, ↓reduceDIte,
      getElem_cons_zero, getElem_cons_succ, sigmaImp_apply, drop_succ_cons, drop_zero]
  | all _ ih =>
    intro l
    simp only [] at *
    rw [listEncode, cons_append, listDecode]
    simp only [ih, length_cons, le_add_iff_nonneg_left, _root_.zero_le, ↓reduceDIte,
      getElem_cons_zero, sigmaAll_apply, drop_succ_cons, drop_zero]

/-- An encoding of bounded formulas as lists. -/
@[simps]
protected def encoding : Encoding (Σn, L.BoundedFormula α n) where
  Γ := (Σk, L.Term (α ⊕ Fin k)) ⊕ ((Σn, L.Relations n) ⊕ ℕ)
  encode φ := φ.2.listEncode
  decode l := (listDecode l)[0]?
  decode_encode φ := by
    have h := listDecode_encode_list [φ]
    rw [flatMap_singleton] at h
    simp only
    rw [h]
    rfl

theorem listEncode_sigma_injective :
    Function.Injective fun φ : Σn, L.BoundedFormula α n => φ.2.listEncode :=
  BoundedFormula.encoding.encode_injective

end BoundedFormula

end Language

end FirstOrder
