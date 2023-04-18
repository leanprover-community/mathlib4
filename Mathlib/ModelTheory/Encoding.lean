/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module model_theory.encoding
! leanprover-community/mathlib commit 91288e351d51b3f0748f0a38faa7613fb0ae2ada
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Computability.Encoding
import Mathbin.Logic.Small.List
import Mathbin.ModelTheory.Syntax
import Mathbin.SetTheory.Cardinal.Ordinal

/-! # Encodings and Cardinality of First-Order Syntax

## Main Definitions
* `first_order.language.term.encoding` encodes terms as lists.
* `first_order.language.bounded_formula.encoding` encodes bounded formulas as lists.

## Main Results
* `first_order.language.term.card_le` shows that the number of terms in `L.term α` is at most
`max ℵ₀ # (α ⊕ Σ i, L.functions i)`.
* `first_order.language.bounded_formula.card_le` shows that the number of bounded formulas in
`Σ n, L.bounded_formula α n` is at most
`max ℵ₀ (cardinal.lift.{max u v} (#α) + cardinal.lift.{u'} L.card)`.

## TODO
* `primcodable` instances for terms and formulas, based on the `encoding`s
* Computability facts about term and formula operations, to set up a computability approach to
incompleteness

-/


universe u v w u' v'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

variable {M : Type w} {N P : Type _} [L.Structure M] [L.Structure N] [L.Structure P]

variable {α : Type u'} {β : Type v'}

open FirstOrder Cardinal

open Computability List Structure Cardinal Fin

namespace Term

/- warning: first_order.language.term.list_encode -> FirstOrder.Language.Term.listEncode is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {α : Type.{u3}}, (FirstOrder.Language.Term.{u1, u2, u3} L α) -> (List.{max u3 u1} (Sum.{u3, u1} α (Sigma.{0, u1} Nat (fun (i : Nat) => FirstOrder.Language.Functions.{u1, u2} L i))))
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u3}} {α : Type.{u2}}, (FirstOrder.Language.Term.{u1, u3, u2} L α) -> (List.{max u2 u1} (Sum.{u2, u1} α (Sigma.{0, u1} Nat (fun (i : Nat) => FirstOrder.Language.Functions.{u1, u3} L i))))
Case conversion may be inaccurate. Consider using '#align first_order.language.term.list_encode FirstOrder.Language.Term.listEncodeₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Encodes a term as a list of variables and function symbols. -/
def listEncode : L.term α → List (Sum α (Σi, L.Functions i))
  | var i => [Sum.inl i]
  | func f ts =>
    Sum.inr (⟨_, f⟩ : Σi, L.Functions i)::(List.finRange _).bind fun i => (ts i).listEncode
#align first_order.language.term.list_encode FirstOrder.Language.Term.listEncode

/- warning: first_order.language.term.list_decode -> FirstOrder.Language.Term.listDecode is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {α : Type.{u3}}, (List.{max u3 u1} (Sum.{u3, u1} α (Sigma.{0, u1} Nat (fun (i : Nat) => FirstOrder.Language.Functions.{u1, u2} L i)))) -> (List.{max u1 u3} (Option.{max u1 u3} (FirstOrder.Language.Term.{u1, u2, u3} L α)))
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u3}} {α : Type.{u2}}, (List.{max u2 u1} (Sum.{u2, u1} α (Sigma.{0, u1} Nat (fun (i : Nat) => FirstOrder.Language.Functions.{u1, u3} L i)))) -> (List.{max u1 u2} (Option.{max u1 u2} (FirstOrder.Language.Term.{u1, u3, u2} L α)))
Case conversion may be inaccurate. Consider using '#align first_order.language.term.list_decode FirstOrder.Language.Term.listDecodeₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Decodes a list of variables and function symbols as a list of terms. -/
def listDecode : List (Sum α (Σi, L.Functions i)) → List (Option (L.term α))
  | [] => []
  | Sum.inl a::l => some (var a)::list_decode l
  | Sum.inr ⟨n, f⟩::l =>
    if h : ∀ i : Fin n, ((list_decode l).get? i).join.isSome then
      (func f fun i => Option.get (h i))::(list_decode l).drop n
    else [none]
#align first_order.language.term.list_decode FirstOrder.Language.Term.listDecode

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem listDecode_encode_list (l : List (L.term α)) :
    listDecode (l.bind listEncode) = l.map Option.some :=
  by
  suffices h :
    ∀ (t : L.term α) (l : List (Sum α (Σi, L.functions i))),
      list_decode (t.listEncode ++ l) = some t::list_decode l
  · induction' l with t l lih
    · rfl
    · rw [cons_bind, h t (l.bind list_encode), lih, List.map]
  · intro t
    induction' t with a n f ts ih <;> intro l
    · rw [list_encode, singleton_append, list_decode]
    · rw [list_encode, cons_append, list_decode]
      have h :
        list_decode (((fin_range n).bind fun i : Fin n => (ts i).listEncode) ++ l) =
          (fin_range n).map (Option.some ∘ ts) ++ list_decode l :=
        by
        induction' fin_range n with i l' l'ih
        · rfl
        · rw [cons_bind, List.append_assoc, ih, map_cons, l'ih, cons_append]
      have h' :
        ∀ i,
          (list_decode (((fin_range n).bind fun i : Fin n => (ts i).listEncode) ++ l)).get? ↑i =
            some (some (ts i)) :=
        by
        intro i
        rw [h, nth_append, nth_map]
        · simp only [Option.map_eq_some', Function.comp_apply, nth_eq_some]
          refine' ⟨i, ⟨lt_of_lt_of_le i.2 (ge_of_eq (length_fin_range _)), _⟩, rfl⟩
          rw [nth_le_fin_range, Fin.eta]
        · refine' lt_of_lt_of_le i.2 _
          simp
      refine' (dif_pos fun i => Option.isSome_iff_exists.2 ⟨ts i, _⟩).trans _
      · rw [Option.join_eq_some, h']
      refine' congr (congr rfl (congr rfl (congr rfl (funext fun i => Option.get_of_mem _ _)))) _
      · simp [h']
      · rw [h, drop_left']
        rw [length_map, length_fin_range]
#align first_order.language.term.list_decode_encode_list FirstOrder.Language.Term.listDecode_encode_list

/-- An encoding of terms as lists. -/
@[simps]
protected def encoding : Encoding (L.term α)
    where
  Γ := Sum α (Σi, L.Functions i)
  encode := listEncode
  decode l := (listDecode l).head?.join
  decode_encode t := by
    have h := list_decode_encode_list [t]
    rw [bind_singleton] at h
    simp only [h, Option.join, head', List.map, Option.some_bind, id.def]
#align first_order.language.term.encoding FirstOrder.Language.Term.encoding

theorem listEncode_injective :
    Function.Injective (listEncode : L.term α → List (Sum α (Σi, L.Functions i))) :=
  Term.encoding.encode_injective
#align first_order.language.term.list_encode_injective FirstOrder.Language.Term.listEncode_injective

theorem card_le : (#L.term α) ≤ max ℵ₀ (#Sum α (Σi, L.Functions i)) :=
  lift_le.1 (trans Term.encoding.card_le_card_list (lift_le.2 (mk_list_le_max _)))
#align first_order.language.term.card_le FirstOrder.Language.Term.card_le

theorem card_sigma : (#Σn, L.term (Sum α (Fin n))) = max ℵ₀ (#Sum α (Σi, L.Functions i)) :=
  by
  refine' le_antisymm _ _
  · rw [mk_sigma]
    refine' (sum_le_supr_lift _).trans _
    rw [mk_nat, lift_aleph_0, mul_eq_max_of_aleph_0_le_left le_rfl, max_le_iff,
      csupᵢ_le_iff' (bdd_above_range _)]
    · refine' ⟨le_max_left _ _, fun i => card_le.trans _⟩
      refine' max_le (le_max_left _ _) _
      rw [← add_eq_max le_rfl, mk_sum, mk_sum, mk_sum, add_comm (Cardinal.lift (#α)), lift_add,
        add_assoc, lift_lift, lift_lift, mk_fin, lift_nat_cast]
      exact add_le_add_right (nat_lt_aleph_0 _).le _
    · rw [← one_le_iff_ne_zero]
      refine' trans _ (le_csupᵢ (bdd_above_range _) 1)
      rw [one_le_iff_ne_zero, mk_ne_zero_iff]
      exact ⟨var (Sum.inr 0)⟩
  · rw [max_le_iff, ← infinite_iff]
    refine' ⟨Infinite.of_injective (fun i => ⟨i + 1, var (Sum.inr i)⟩) fun i j ij => _, _⟩
    · cases ij
      rfl
    · rw [Cardinal.le_def]
      refine'
        ⟨⟨Sum.elim (fun i => ⟨0, var (Sum.inl i)⟩) fun F => ⟨1, func F.2 fun _ => var (Sum.inr 0)⟩,
            _⟩⟩
      · rintro (a | a) (b | b) h
        · simp only [Sum.elim_inl, eq_self_iff_true, heq_iff_eq, true_and_iff] at h
          rw [h]
        · simp only [Sum.elim_inl, Sum.elim_inr, Nat.zero_ne_one, false_and_iff] at h
          exact h.elim
        · simp only [Sum.elim_inr, Sum.elim_inl, Nat.one_ne_zero, false_and_iff] at h
          exact h.elim
        · simp only [Sum.elim_inr, eq_self_iff_true, heq_iff_eq, true_and_iff] at h
          rw [Sigma.ext_iff.2 ⟨h.1, h.2.1⟩]
#align first_order.language.term.card_sigma FirstOrder.Language.Term.card_sigma

instance [Encodable α] [Encodable (Σi, L.Functions i)] : Encodable (L.term α) :=
  Encodable.ofLeftInjection listEncode (fun l => (listDecode l).head?.join) fun t =>
    by
    rw [← bind_singleton list_encode, list_decode_encode_list]
    simp only [Option.join, head', List.map, Option.some_bind, id.def]

instance [h1 : Countable α] [h2 : Countable (Σl, L.Functions l)] : Countable (L.term α) :=
  by
  refine' mk_le_aleph_0_iff.1 (card_le.trans (max_le_iff.2 _))
  simp only [le_refl, mk_sum, add_le_aleph_0, lift_le_aleph_0, true_and_iff]
  exact ⟨Cardinal.mk_le_aleph0, Cardinal.mk_le_aleph0⟩

instance small [Small.{u} α] : Small.{u} (L.term α) :=
  small_of_injective listEncode_injective
#align first_order.language.term.small FirstOrder.Language.Term.small

end Term

namespace BoundedFormula

/- warning: first_order.language.bounded_formula.list_encode -> FirstOrder.Language.BoundedFormula.listEncode is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {α : Type.{u3}} {n : Nat}, (FirstOrder.Language.BoundedFormula.{u1, u2, u3} L α n) -> (List.{max (max u1 u3) u2} (Sum.{max u1 u3, u2} (Sigma.{0, max u1 u3} Nat (fun (k : Nat) => FirstOrder.Language.Term.{u1, u2, u3} L (Sum.{u3, 0} α (Fin k)))) (Sum.{u2, 0} (Sigma.{0, u2} Nat (fun (n : Nat) => FirstOrder.Language.Relations.{u1, u2} L n)) Nat)))
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u3}} {α : Type.{u2}} {n : Nat}, (FirstOrder.Language.BoundedFormula.{u1, u3, u2} L α n) -> (List.{max (max u1 u2) u3} (Sum.{max u1 u2, u3} (Sigma.{0, max u1 u2} Nat (fun (k : Nat) => FirstOrder.Language.Term.{u1, u3, u2} L (Sum.{u2, 0} α (Fin k)))) (Sum.{u3, 0} (Sigma.{0, u3} Nat (fun (n : Nat) => FirstOrder.Language.Relations.{u1, u3} L n)) Nat)))
Case conversion may be inaccurate. Consider using '#align first_order.language.bounded_formula.list_encode FirstOrder.Language.BoundedFormula.listEncodeₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Encodes a bounded formula as a list of symbols. -/
def listEncode :
    ∀ {n : ℕ},
      L.BoundedFormula α n → List (Sum (Σk, L.term (Sum α (Fin k))) (Sum (Σn, L.Relations n) ℕ))
  | n, falsum => [Sum.inr (Sum.inr (n + 2))]
  | n, equal t₁ t₂ => [Sum.inl ⟨_, t₁⟩, Sum.inl ⟨_, t₂⟩]
  | n, Rel R ts =>
    [Sum.inr (Sum.inl ⟨_, R⟩), Sum.inr (Sum.inr n)] ++
      (List.finRange _).map fun i => Sum.inl ⟨n, ts i⟩
  | n, imp φ₁ φ₂ => (Sum.inr (Sum.inr 0)::φ₁.listEncode) ++ φ₂.listEncode
  | n, all φ => Sum.inr (Sum.inr 1)::φ.listEncode
#align first_order.language.bounded_formula.list_encode FirstOrder.Language.BoundedFormula.listEncode

/- warning: first_order.language.bounded_formula.sigma_all -> FirstOrder.Language.BoundedFormula.sigmaAll is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {α : Type.{u3}}, (Sigma.{0, max u1 u2 u3} Nat (fun (n : Nat) => FirstOrder.Language.BoundedFormula.{u1, u2, u3} L α n)) -> (Sigma.{0, max u1 u2 u3} Nat (fun (n : Nat) => FirstOrder.Language.BoundedFormula.{u1, u2, u3} L α n))
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u3}} {α : Type.{u2}}, (Sigma.{0, max u1 u3 u2} Nat (fun (n : Nat) => FirstOrder.Language.BoundedFormula.{u1, u3, u2} L α n)) -> (Sigma.{0, max u1 u3 u2} Nat (fun (n : Nat) => FirstOrder.Language.BoundedFormula.{u1, u3, u2} L α n))
Case conversion may be inaccurate. Consider using '#align first_order.language.bounded_formula.sigma_all FirstOrder.Language.BoundedFormula.sigmaAllₓ'. -/
/-- Applies the `forall` quantifier to an element of `(Σ n, L.bounded_formula α n)`,
or returns `default` if not possible. -/
def sigmaAll : (Σn, L.BoundedFormula α n) → Σn, L.BoundedFormula α n
  | ⟨n + 1, φ⟩ => ⟨n, φ.all⟩
  | _ => default
#align first_order.language.bounded_formula.sigma_all FirstOrder.Language.BoundedFormula.sigmaAll

/- warning: first_order.language.bounded_formula.sigma_imp -> FirstOrder.Language.BoundedFormula.sigmaImp is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {α : Type.{u3}}, (Sigma.{0, max u1 u2 u3} Nat (fun (n : Nat) => FirstOrder.Language.BoundedFormula.{u1, u2, u3} L α n)) -> (Sigma.{0, max u1 u2 u3} Nat (fun (n : Nat) => FirstOrder.Language.BoundedFormula.{u1, u2, u3} L α n)) -> (Sigma.{0, max u1 u2 u3} Nat (fun (n : Nat) => FirstOrder.Language.BoundedFormula.{u1, u2, u3} L α n))
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u3}} {α : Type.{u2}}, (Sigma.{0, max u1 u3 u2} Nat (fun (n : Nat) => FirstOrder.Language.BoundedFormula.{u1, u3, u2} L α n)) -> (Sigma.{0, max u1 u3 u2} Nat (fun (n : Nat) => FirstOrder.Language.BoundedFormula.{u1, u3, u2} L α n)) -> (Sigma.{0, max u1 u3 u2} Nat (fun (n : Nat) => FirstOrder.Language.BoundedFormula.{u1, u3, u2} L α n))
Case conversion may be inaccurate. Consider using '#align first_order.language.bounded_formula.sigma_imp FirstOrder.Language.BoundedFormula.sigmaImpₓ'. -/
/-- Applies `imp` to two elements of `(Σ n, L.bounded_formula α n)`,
or returns `default` if not possible. -/
def sigmaImp : (Σn, L.BoundedFormula α n) → (Σn, L.BoundedFormula α n) → Σn, L.BoundedFormula α n
  | ⟨m, φ⟩, ⟨n, ψ⟩ => if h : m = n then ⟨m, φ.imp (Eq.mp (by rw [h]) ψ)⟩ else default
#align first_order.language.bounded_formula.sigma_imp FirstOrder.Language.BoundedFormula.sigmaImp

/- warning: first_order.language.bounded_formula.list_decode -> FirstOrder.Language.BoundedFormula.listDecode is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {α : Type.{u3}} (l : List.{max (max u1 u3) u2} (Sum.{max u1 u3, u2} (Sigma.{0, max u1 u3} Nat (fun (k : Nat) => FirstOrder.Language.Term.{u1, u2, u3} L (Sum.{u3, 0} α (Fin k)))) (Sum.{u2, 0} (Sigma.{0, u2} Nat (fun (n : Nat) => FirstOrder.Language.Relations.{u1, u2} L n)) Nat))), Prod.{max u1 u2 u3, max (max u1 u3) u2} (Sigma.{0, max u1 u2 u3} Nat (fun (n : Nat) => FirstOrder.Language.BoundedFormula.{u1, u2, u3} L α n)) (Subtype.{succ (max (max u1 u3) u2)} (List.{max (max u1 u3) u2} (Sum.{max u1 u3, u2} (Sigma.{0, max u1 u3} Nat (fun (k : Nat) => FirstOrder.Language.Term.{u1, u2, u3} L (Sum.{u3, 0} α (Fin k)))) (Sum.{u2, 0} (Sigma.{0, u2} Nat (fun (n : Nat) => FirstOrder.Language.Relations.{u1, u2} L n)) Nat))) (fun (l' : List.{max (max u1 u3) u2} (Sum.{max u1 u3, u2} (Sigma.{0, max u1 u3} Nat (fun (k : Nat) => FirstOrder.Language.Term.{u1, u2, u3} L (Sum.{u3, 0} α (Fin k)))) (Sum.{u2, 0} (Sigma.{0, u2} Nat (fun (n : Nat) => FirstOrder.Language.Relations.{u1, u2} L n)) Nat))) => LE.le.{0} Nat Nat.hasLe (List.sizeof.{max (max u1 u3) u2} (Sum.{max u1 u3, u2} (Sigma.{0, max u1 u3} Nat (fun (k : Nat) => FirstOrder.Language.Term.{u1, u2, u3} L (Sum.{u3, 0} α (Fin k)))) (Sum.{u2, 0} (Sigma.{0, u2} Nat (fun (n : Nat) => FirstOrder.Language.Relations.{u1, u2} L n)) Nat)) (Sum.hasSizeof.{max u1 u3, u2} (Sigma.{0, max u1 u3} Nat (fun (k : Nat) => FirstOrder.Language.Term.{u1, u2, u3} L (Sum.{u3, 0} α (Fin k)))) (Sum.{u2, 0} (Sigma.{0, u2} Nat (fun (n : Nat) => FirstOrder.Language.Relations.{u1, u2} L n)) Nat) (Sigma.hasSizeof.{0, max u1 u3} Nat (fun (k : Nat) => FirstOrder.Language.Term.{u1, u2, u3} L (Sum.{u3, 0} α (Fin k))) Nat.hasSizeof (fun (a : Nat) => FirstOrder.Language.Term.hasSizeofInst.{u1, u2, u3} L (Sum.{u3, 0} α (Fin a)) (Sum.hasSizeof.{u3, 0} α (Fin a) (defaultHasSizeof.{succ u3} α) (Fin.hasSizeofInst a)))) (Sum.hasSizeof.{u2, 0} (Sigma.{0, u2} Nat (fun (n : Nat) => FirstOrder.Language.Relations.{u1, u2} L n)) Nat (Sigma.hasSizeof.{0, u2} Nat (fun (n : Nat) => FirstOrder.Language.Relations.{u1, u2} L n) Nat.hasSizeof (fun (a : Nat) => defaultHasSizeof.{succ u2} (FirstOrder.Language.Relations.{u1, u2} L a))) Nat.hasSizeof)) l') (LinearOrder.max.{0} Nat Nat.linearOrder (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (List.sizeof.{max (max u1 u3) u2} (Sum.{max u1 u3, u2} (Sigma.{0, max u1 u3} Nat (fun (k : Nat) => FirstOrder.Language.Term.{u1, u2, u3} L (Sum.{u3, 0} α (Fin k)))) (Sum.{u2, 0} (Sigma.{0, u2} Nat (fun (n : Nat) => FirstOrder.Language.Relations.{u1, u2} L n)) Nat)) (Sum.hasSizeof.{max u1 u3, u2} (Sigma.{0, max u1 u3} Nat (fun (k : Nat) => FirstOrder.Language.Term.{u1, u2, u3} L (Sum.{u3, 0} α (Fin k)))) (Sum.{u2, 0} (Sigma.{0, u2} Nat (fun (n : Nat) => FirstOrder.Language.Relations.{u1, u2} L n)) Nat) (Sigma.hasSizeof.{0, max u1 u3} Nat (fun (k : Nat) => FirstOrder.Language.Term.{u1, u2, u3} L (Sum.{u3, 0} α (Fin k))) Nat.hasSizeof (fun (a : Nat) => FirstOrder.Language.Term.hasSizeofInst.{u1, u2, u3} L (Sum.{u3, 0} α (Fin a)) (Sum.hasSizeof.{u3, 0} α (Fin a) (defaultHasSizeof.{succ u3} α) (Fin.hasSizeofInst a)))) (Sum.hasSizeof.{u2, 0} (Sigma.{0, u2} Nat (fun (n : Nat) => FirstOrder.Language.Relations.{u1, u2} L n)) Nat (Sigma.hasSizeof.{0, u2} Nat (fun (n : Nat) => FirstOrder.Language.Relations.{u1, u2} L n) Nat.hasSizeof (fun (a : Nat) => defaultHasSizeof.{succ u2} (FirstOrder.Language.Relations.{u1, u2} L a))) Nat.hasSizeof)) l))))
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u3}} {α : Type.{u2}} (l : List.{max (max u1 u2) u3} (Sum.{max u1 u2, u3} (Sigma.{0, max u1 u2} Nat (fun (k : Nat) => FirstOrder.Language.Term.{u1, u3, u2} L (Sum.{u2, 0} α (Fin k)))) (Sum.{u3, 0} (Sigma.{0, u3} Nat (fun (n : Nat) => FirstOrder.Language.Relations.{u1, u3} L n)) Nat))), Prod.{max u1 u3 u2, max (max u1 u2) u3} (Sigma.{0, max u1 u3 u2} Nat (fun (n : Nat) => FirstOrder.Language.BoundedFormula.{u1, u3, u2} L α n)) (Subtype.{succ (max (max u1 u2) u3)} (List.{max (max u1 u2) u3} (Sum.{max u1 u2, u3} (Sigma.{0, max u1 u2} Nat (fun (k : Nat) => FirstOrder.Language.Term.{u1, u3, u2} L (Sum.{u2, 0} α (Fin k)))) (Sum.{u3, 0} (Sigma.{0, u3} Nat (fun (n : Nat) => FirstOrder.Language.Relations.{u1, u3} L n)) Nat))) (fun (l' : List.{max (max u1 u2) u3} (Sum.{max u1 u2, u3} (Sigma.{0, max u1 u2} Nat (fun (k : Nat) => FirstOrder.Language.Term.{u1, u3, u2} L (Sum.{u2, 0} α (Fin k)))) (Sum.{u3, 0} (Sigma.{0, u3} Nat (fun (n : Nat) => FirstOrder.Language.Relations.{u1, u3} L n)) Nat))) => LE.le.{0} Nat Nat.hasLe (List.sizeof.{max (max u1 u2) u3} (Sum.{max u1 u2, u3} (Sigma.{0, max u1 u2} Nat (fun (k : Nat) => FirstOrder.Language.Term.{u1, u3, u2} L (Sum.{u2, 0} α (Fin k)))) (Sum.{u3, 0} (Sigma.{0, u3} Nat (fun (n : Nat) => FirstOrder.Language.Relations.{u1, u3} L n)) Nat)) (Sum.hasSizeof.{max u1 u2, u3} (Sigma.{0, max u1 u2} Nat (fun (k : Nat) => FirstOrder.Language.Term.{u1, u3, u2} L (Sum.{u2, 0} α (Fin k)))) (Sum.{u3, 0} (Sigma.{0, u3} Nat (fun (n : Nat) => FirstOrder.Language.Relations.{u1, u3} L n)) Nat) (Sigma.hasSizeof.{0, max u1 u2} Nat (fun (k : Nat) => FirstOrder.Language.Term.{u1, u3, u2} L (Sum.{u2, 0} α (Fin k))) Nat.hasSizeof (fun (a : Nat) => FirstOrder.Language.Term.hasSizeofInst.{u1, u3, u2} L (Sum.{u2, 0} α (Fin a)) (Sum.hasSizeof.{u2, 0} α (Fin a) (defaultHasSizeof.{succ u2} α) (Fin.hasSizeofInst a)))) (Sum.hasSizeof.{u3, 0} (Sigma.{0, u3} Nat (fun (n : Nat) => FirstOrder.Language.Relations.{u1, u3} L n)) Nat (Sigma.hasSizeof.{0, u3} Nat (fun (n : Nat) => FirstOrder.Language.Relations.{u1, u3} L n) Nat.hasSizeof (fun (a : Nat) => defaultHasSizeof.{succ u3} (FirstOrder.Language.Relations.{u1, u3} L a))) Nat.hasSizeof)) l') (LinearOrder.max.{0} Nat Nat.linearOrder (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (List.sizeof.{max (max u1 u2) u3} (Sum.{max u1 u2, u3} (Sigma.{0, max u1 u2} Nat (fun (k : Nat) => FirstOrder.Language.Term.{u1, u3, u2} L (Sum.{u2, 0} α (Fin k)))) (Sum.{u3, 0} (Sigma.{0, u3} Nat (fun (n : Nat) => FirstOrder.Language.Relations.{u1, u3} L n)) Nat)) (Sum.hasSizeof.{max u1 u2, u3} (Sigma.{0, max u1 u2} Nat (fun (k : Nat) => FirstOrder.Language.Term.{u1, u3, u2} L (Sum.{u2, 0} α (Fin k)))) (Sum.{u3, 0} (Sigma.{0, u3} Nat (fun (n : Nat) => FirstOrder.Language.Relations.{u1, u3} L n)) Nat) (Sigma.hasSizeof.{0, max u1 u2} Nat (fun (k : Nat) => FirstOrder.Language.Term.{u1, u3, u2} L (Sum.{u2, 0} α (Fin k))) Nat.hasSizeof (fun (a : Nat) => FirstOrder.Language.Term.hasSizeofInst.{u1, u3, u2} L (Sum.{u2, 0} α (Fin a)) (Sum.hasSizeof.{u2, 0} α (Fin a) (defaultHasSizeof.{succ u2} α) (Fin.hasSizeofInst a)))) (Sum.hasSizeof.{u3, 0} (Sigma.{0, u3} Nat (fun (n : Nat) => FirstOrder.Language.Relations.{u1, u3} L n)) Nat (Sigma.hasSizeof.{0, u3} Nat (fun (n : Nat) => FirstOrder.Language.Relations.{u1, u3} L n) Nat.hasSizeof (fun (a : Nat) => defaultHasSizeof.{succ u3} (FirstOrder.Language.Relations.{u1, u3} L a))) Nat.hasSizeof)) l))))
Case conversion may be inaccurate. Consider using '#align first_order.language.bounded_formula.list_decode FirstOrder.Language.BoundedFormula.listDecodeₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Decodes a list of symbols as a list of formulas. -/
@[simp]
def listDecode :
    ∀ l : List (Sum (Σk, L.term (Sum α (Fin k))) (Sum (Σn, L.Relations n) ℕ)),
      (Σn, L.BoundedFormula α n) ×
        { l' : List (Sum (Σk, L.term (Sum α (Fin k))) (Sum (Σn, L.Relations n) ℕ)) //
          l'.sizeOf ≤ max 1 l.sizeOf }
  | Sum.inr (Sum.inr (n + 2))::l => ⟨⟨n, falsum⟩, l, le_max_of_le_right le_add_self⟩
  | Sum.inl ⟨n₁, t₁⟩::Sum.inl ⟨n₂, t₂⟩::l =>
    ⟨if h : n₁ = n₂ then ⟨n₁, equal t₁ (Eq.mp (by rw [h]) t₂)⟩ else default, l,
      by
      simp only [List.sizeof, ← add_assoc]
      exact le_max_of_le_right le_add_self⟩
  | Sum.inr (Sum.inl ⟨n, R⟩)::Sum.inr (Sum.inr k)::l =>
    ⟨if h : ∀ i : Fin n, ((l.map Sum.getLeft).get? i).join.isSome then
        if h' : ∀ i, (Option.get (h i)).1 = k then
          ⟨k, BoundedFormula.Rel R fun i => Eq.mp (by rw [h' i]) (Option.get (h i)).2⟩
        else default
      else default,
      l.drop n, le_max_of_le_right (le_add_left (le_add_left (List.drop_sizeOf_le _ _)))⟩
  | Sum.inr (Sum.inr 0)::l =>
    have :
      (↑(list_decode l).2 :
            List (Sum (Σk, L.term (Sum α (Fin k))) (Sum (Σn, L.Relations n) ℕ))).sizeOf <
        1 + (1 + 1) + l.sizeOf :=
      by
      refine' lt_of_le_of_lt (list_decode l).2.2 (max_lt _ (Nat.lt_add_of_pos_left (by decide)))
      rw [add_assoc, add_comm, Nat.lt_succ_iff, add_assoc]
      exact le_self_add
    ⟨sigmaImp (list_decode l).1 (list_decode (list_decode l).2).1,
      (list_decode (list_decode l).2).2,
      le_max_of_le_right
        (trans (list_decode _).2.2
          (max_le (le_add_right le_self_add)
            (trans (list_decode _).2.2 (max_le (le_add_right le_self_add) le_add_self))))⟩
  | Sum.inr (Sum.inr 1)::l =>
    ⟨sigmaAll (list_decode l).1, (list_decode l).2,
      (list_decode l).2.2.trans (max_le_max le_rfl le_add_self)⟩
  | _ => ⟨default, [], le_max_left _ _⟩
#align first_order.language.bounded_formula.list_decode FirstOrder.Language.BoundedFormula.listDecode

@[simp]
theorem listDecode_encode_list (l : List (Σn, L.BoundedFormula α n)) :
    (listDecode (l.bind fun φ => φ.2.listEncode)).1 = l.headI :=
  by
  suffices h :
    ∀ (φ : Σn, L.bounded_formula α n) (l),
      (list_decode (list_encode φ.2 ++ l)).1 = φ ∧ (list_decode (list_encode φ.2 ++ l)).2.1 = l
  · induction' l with φ l lih
    · rw [List.nil_bind]
      simp [list_decode]
    · rw [cons_bind, (h φ _).1, head_cons]
  · rintro ⟨n, φ⟩
    induction' φ with _ _ _ _ _ _ _ ts _ _ _ ih1 ih2 _ _ ih <;> intro l
    · rw [list_encode, singleton_append, list_decode]
      simp only [eq_self_iff_true, heq_iff_eq, and_self_iff]
    · rw [list_encode, cons_append, cons_append, list_decode, dif_pos]
      · simp only [eq_mp_eq_cast, cast_eq, eq_self_iff_true, heq_iff_eq, and_self_iff, nil_append]
      · simp only [eq_self_iff_true, heq_iff_eq, and_self_iff]
    · rw [list_encode, cons_append, cons_append, singleton_append, cons_append, list_decode]
      · have h :
          ∀ i : Fin φ_l,
            ((List.map Sum.getLeft
                      (List.map
                          (fun i : Fin φ_l =>
                            Sum.inl
                              (⟨(⟨φ_n, Rel φ_R ts⟩ : Σn, L.bounded_formula α n).fst, ts i⟩ :
                                Σn, L.term (Sum α (Fin n))))
                          (fin_range φ_l) ++
                        l)).get?
                  ↑i).join =
              some ⟨_, ts i⟩ :=
          by
          intro i
          simp only [Option.join, map_append, map_map, Option.bind_eq_some, id.def, exists_eq_right,
            nth_eq_some, length_append, length_map, length_fin_range]
          refine' ⟨lt_of_lt_of_le i.2 le_self_add, _⟩
          rw [nth_le_append, nth_le_map]
          ·
            simp only [Sum.getLeft, nth_le_fin_range, Fin.eta, Function.comp_apply,
              eq_self_iff_true, heq_iff_eq, and_self_iff]
          · exact lt_of_lt_of_le i.is_lt (ge_of_eq (length_fin_range _))
          · rw [length_map, length_fin_range]
            exact i.2
        rw [dif_pos]
        swap
        · exact fun i => Option.isSome_iff_exists.2 ⟨⟨_, ts i⟩, h i⟩
        rw [dif_pos]
        swap
        · intro i
          obtain ⟨h1, h2⟩ := Option.eq_some_iff_get_eq.1 (h i)
          rw [h2]
        simp only [eq_self_iff_true, heq_iff_eq, true_and_iff]
        refine' ⟨funext fun i => _, _⟩
        · obtain ⟨h1, h2⟩ := Option.eq_some_iff_get_eq.1 (h i)
          rw [eq_mp_eq_cast, cast_eq_iff_heq]
          exact (Sigma.ext_iff.1 ((Sigma.eta (Option.get h1)).trans h2)).2
        rw [List.drop_append_eq_append_drop, length_map, length_fin_range, Nat.sub_self, drop,
          drop_eq_nil_of_le, nil_append]
        rw [length_map, length_fin_range]
    · rw [list_encode, List.append_assoc, cons_append, list_decode]
      simp only [Subtype.val_eq_coe] at *
      rw [(ih1 _).1, (ih1 _).2, (ih2 _).1, (ih2 _).2, sigma_imp, dif_pos rfl]
      exact ⟨rfl, rfl⟩
    · rw [list_encode, cons_append, list_decode]
      simp only
      simp only [Subtype.val_eq_coe] at *
      rw [(ih _).1, (ih _).2, sigma_all]
      exact ⟨rfl, rfl⟩
#align first_order.language.bounded_formula.list_decode_encode_list FirstOrder.Language.BoundedFormula.listDecode_encode_list

/-- An encoding of bounded formulas as lists. -/
@[simps]
protected def encoding : Encoding (Σn, L.BoundedFormula α n)
    where
  Γ := Sum (Σk, L.term (Sum α (Fin k))) (Sum (Σn, L.Relations n) ℕ)
  encode φ := φ.2.listEncode
  decode l := (listDecode l).1
  decode_encode φ := by
    have h := list_decode_encode_list [φ]
    rw [bind_singleton] at h
    rw [h]
    rfl
#align first_order.language.bounded_formula.encoding FirstOrder.Language.BoundedFormula.encoding

theorem listEncode_sigma_injective :
    Function.Injective fun φ : Σn, L.BoundedFormula α n => φ.2.listEncode :=
  BoundedFormula.encoding.encode_injective
#align first_order.language.bounded_formula.list_encode_sigma_injective FirstOrder.Language.BoundedFormula.listEncode_sigma_injective

theorem card_le :
    (#Σn, L.BoundedFormula α n) ≤
      max ℵ₀ (Cardinal.lift.{max u v} (#α) + Cardinal.lift.{u'} L.card) :=
  by
  refine' lift_le.1 (bounded_formula.encoding.card_le_card_list.trans _)
  rw [encoding_Γ, mk_list_eq_max_mk_aleph_0, lift_max, lift_aleph_0, lift_max, lift_aleph_0,
    max_le_iff]
  refine' ⟨_, le_max_left _ _⟩
  rw [mk_sum, term.card_sigma, mk_sum, ← add_eq_max le_rfl, mk_sum, mk_nat]
  simp only [lift_add, lift_lift, lift_aleph_0]
  rw [← add_assoc, add_comm, ← add_assoc, ← add_assoc, aleph_0_add_aleph_0, add_assoc,
    add_eq_max le_rfl, add_assoc, card, symbols, mk_sum, lift_add, lift_lift, lift_lift]
#align first_order.language.bounded_formula.card_le FirstOrder.Language.BoundedFormula.card_le

end BoundedFormula

end Language

end FirstOrder

