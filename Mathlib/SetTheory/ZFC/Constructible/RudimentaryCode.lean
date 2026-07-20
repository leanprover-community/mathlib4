/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.Data.List.Shortlex
public import Mathlib.Data.Sum.Order
public import Mathlib.SetTheory.ZFC.Constructible.Rudimentary

/-!
# Canonical codes for rudimentary terms

A term is encoded in prefix form.  An application token stores the lengths of
both encoded subterms, making the code unambiguously decodable.  Shortlex on
these finite token lists gives a well-order whenever the variable labels are
well-ordered.  Consequently every value in a rudimentary closure has a unique
least representing term.
-/

@[expose] public section

universe u

namespace Constructible.Godel

namespace RudimentaryTerm

/--
Tokens for prefix codes.  A left token is a variable; a right token records
an operation together with the lengths of its two subterm codes.
-/
abbrev CodeToken (alpha : Type u) :=
  alpha ⊕ (Fin 9 × Nat × Nat)

/-- An injective, length-delimited prefix code for rudimentary terms. -/
def code {alpha : Type u} : RudimentaryTerm alpha -> List (CodeToken alpha)
  | .var a => [Sum.inl a]
  | .app i left right =>
      let leftCode := code left
      let rightCode := code right
      Sum.inr (i, leftCode.length, rightCode.length) ::
        (leftCode ++ rightCode)

@[simp]
theorem code_var {alpha : Type u} (a : alpha) :
    code (.var a : RudimentaryTerm alpha) = [Sum.inl a] :=
  rfl

@[simp]
theorem code_app {alpha : Type u} (i : Fin 9)
    (left right : RudimentaryTerm alpha) :
    code (.app i left right) =
      Sum.inr (i, (code left).length, (code right).length) ::
        (code left ++ code right) :=
  rfl

/-- The prefix code determines the term uniquely. -/
theorem code_injective {alpha : Type u} :
    Function.Injective (@code alpha) := by
  intro first second hcode
  induction first generalizing second with
  | var a =>
      cases second with
      | var b =>
          have hab : a = b := Sum.inl.inj (List.cons.inj hcode).1
          subst b
          rfl
      | app i left right =>
          have hhead := (List.cons.inj hcode).1
          cases hhead
  | app i left right ihLeft ihRight =>
      cases second with
      | var b =>
          have hhead := (List.cons.inj hcode).1
          cases hhead
      | app j left' right' =>
          have hcons := List.cons.inj hcode
          have htuple := Sum.inr.inj hcons.1
          have hij : i = j := congrArg Prod.fst htuple
          have hlengths := congrArg Prod.snd htuple
          have hleftLength : (code left).length = (code left').length :=
            congrArg Prod.fst hlengths
          have hrightLength : (code right).length = (code right').length :=
            congrArg Prod.snd hlengths
          have htail := hcons.2
          have hleftCode : code left = code left' := by
            calc
              code left =
                  List.take (code left).length (code left ++ code right) := by
                simp
              _ = List.take (code left).length
                  (code left' ++ code right') :=
                congrArg (List.take (code left).length) htail
              _ = code left' := by
                rw [hleftLength]
                simp
          have hrightCode : code right = code right' := by
            calc
              code right =
                  List.drop (code left).length (code left ++ code right) := by
                simp
              _ = List.drop (code left).length
                  (code left' ++ code right') :=
                congrArg (List.drop (code left).length) htail
              _ = code right' := by
                rw [hleftLength]
                simp
          have hleft : left = left' := ihLeft hleftCode
          have hright : right = right' := ihRight hrightCode
          subst j
          subst left'
          subst right'
          rfl

/-! ## The structural well-order -/

/-- Lexicographic order on operation tokens. -/
def operationTokenRel :
    (Fin 9 × Nat × Nat) -> (Fin 9 × Nat × Nat) -> Prop :=
  Prod.Lex (fun i j : Fin 9 => i < j)
    (Prod.Lex (fun m n : Nat => m < n) (fun m n : Nat => m < n))

/-- Variables precede applications; each part uses its canonical order. -/
def codeTokenRel {alpha : Type u} (r : alpha -> alpha -> Prop) :
    CodeToken alpha -> CodeToken alpha -> Prop :=
  Sum.Lex r operationTokenRel

/-- Shortlex order pulled back along the injective term code. -/
def codeRel {alpha : Type u} (r : alpha -> alpha -> Prop) :
    RudimentaryTerm alpha -> RudimentaryTerm alpha -> Prop :=
  InvImage (List.Shortlex (codeTokenRel r)) code

theorem operationTokenRel_isWellOrder :
    IsWellOrder (Fin 9 × Nat × Nat) operationTokenRel := by
  unfold operationTokenRel
  infer_instance

theorem codeTokenRel_isWellOrder {alpha : Type u}
    (r : alpha -> alpha -> Prop) [IsWellOrder alpha r] :
    IsWellOrder (CodeToken alpha) (codeTokenRel r) := by
  unfold codeTokenRel
  letI : IsWellOrder (Fin 9 × Nat × Nat) operationTokenRel :=
    operationTokenRel_isWellOrder
  infer_instance

/-- The structural order on terms is a well-order. -/
theorem codeRel_isWellOrder {alpha : Type u}
    (r : alpha -> alpha -> Prop) [IsWellOrder alpha r] :
    IsWellOrder (RudimentaryTerm alpha) (codeRel r) := by
  letI : IsWellOrder (CodeToken alpha) (codeTokenRel r) :=
    codeTokenRel_isWellOrder r
  refine
    { wf := InvImage.wf code
        (List.Shortlex.wf (IsWellFounded.wf :
          WellFounded (codeTokenRel r)))
      trichotomous :=
        (InvImage.trichotomous (r := List.Shortlex (codeTokenRel r))
          code_injective).trichotomous }

/-! ## Least representations -/

/-- The set of rudimentary terms evaluating to `z`. -/
def representingTerms (U z : ZFSet.{u}) :
    Set (RudimentaryClosureTerm U) :=
  {term | term.eval = z}

theorem representingTerms_nonempty {U z : ZFSet.{u}}
    (hz : z ∈ godelDef U) :
    (representingTerms U z).Nonempty := by
  rcases (mem_godelDef_iff_exists_rudimentaryTerm.mp hz).2 with
    ⟨term, hterm⟩
  exact ⟨term, hterm⟩

/--
The least term representing `z`, relative to a well-order of the generators
`Option (ZFCarrier U)`.
-/
noncomputable def leastRepresentingTerm (U z : ZFSet.{u})
    (hz : z ∈ godelDef U)
    (r : Option (Constructible.ZFCarrier U) ->
      Option (Constructible.ZFCarrier U) -> Prop)
    [IsWellOrder (Option (Constructible.ZFCarrier U)) r] :
    RudimentaryClosureTerm U :=
  letI : IsWellOrder (RudimentaryClosureTerm U) (codeRel r) :=
    codeRel_isWellOrder r
  (IsWellFounded.wf : WellFounded (codeRel r)).min (representingTerms U z)
    (representingTerms_nonempty hz)

@[simp]
theorem eval_leastRepresentingTerm (U z : ZFSet.{u})
    (hz : z ∈ godelDef U)
    (r : Option (Constructible.ZFCarrier U) ->
      Option (Constructible.ZFCarrier U) -> Prop)
    [IsWellOrder (Option (Constructible.ZFCarrier U)) r] :
    (leastRepresentingTerm U z hz r).eval = z := by
  letI : IsWellOrder (RudimentaryClosureTerm U) (codeRel r) :=
    codeRel_isWellOrder r
  exact (IsWellFounded.wf : WellFounded (codeRel r)).min_mem
    (representingTerms U z)
    (representingTerms_nonempty hz)

theorem leastRepresentingTerm_minimal (U z : ZFSet.{u})
    (hz : z ∈ godelDef U)
    (r : Option (Constructible.ZFCarrier U) ->
      Option (Constructible.ZFCarrier U) -> Prop)
    [IsWellOrder (Option (Constructible.ZFCarrier U)) r]
    {term : RudimentaryClosureTerm U} (hterm : term.eval = z) :
    Not (codeRel r term (leastRepresentingTerm U z hz r)) := by
  letI : IsWellOrder (RudimentaryClosureTerm U) (codeRel r) :=
    codeRel_isWellOrder r
  exact (IsWellFounded.wf : WellFounded (codeRel r)).not_lt_min
    (representingTerms U z)
    hterm

/--
Any minimal term representing `z` is the canonical least representing term.

This is the explicit uniqueness interface needed when the structural order on
terms is used to define the canonical order on a constructible stage.
-/
theorem eq_leastRepresentingTerm_of_minimal (U z : ZFSet.{u})
    (hz : z ∈ godelDef U)
    (r : Option (Constructible.ZFCarrier U) ->
      Option (Constructible.ZFCarrier U) -> Prop)
    [IsWellOrder (Option (Constructible.ZFCarrier U)) r]
    {term : RudimentaryClosureTerm U} (hterm : term.eval = z)
    (hminimal : ∀ {other : RudimentaryClosureTerm U}, other.eval = z ->
      Not (codeRel r other term)) :
    term = leastRepresentingTerm U z hz r := by
  letI : IsWellOrder (RudimentaryClosureTerm U) (codeRel r) :=
    codeRel_isWellOrder r
  rcases trichotomous_of (codeRel r) term
      (leastRepresentingTerm U z hz r) with hlt | heq | hgt
  · exact False.elim
      (leastRepresentingTerm_minimal U z hz r hterm hlt)
  · exact heq
  · exact False.elim
      (hminimal (eval_leastRepresentingTerm U z hz r) hgt)

end RudimentaryTerm

end Constructible.Godel
