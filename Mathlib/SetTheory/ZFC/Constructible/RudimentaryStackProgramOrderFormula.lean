/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.IndexedSequenceOrderFormula
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryStackTokenOrderFormula

/-!
# A first-order Shortlex order on postfix stack-program codes

The generic indexed-sequence comparison formula is specialized to the fixed
stack-token formula.  The resulting object-language relation has exactly the
external `stackProgramRel` semantics on genuine program codes.
-/

@[expose] public section

universe u v

namespace Constructible

/-! ## Mapping lemmas for structural list orders -/

theorem listLex_map_iff_of_length_eq {A : Type u} {B : Type v}
    {r : A → A → Prop} {R : B → B → Prop} (f : A → B)
    (hinjective : Function.Injective f)
    (hrel : ∀ x y, R (f x) (f y) ↔ r x y)
    (xs ys : List A) (hlength : xs.length = ys.length) :
    List.Lex R (xs.map f) (ys.map f) ↔ List.Lex r xs ys := by
  rw [listLex_iff_exists_index (by simpa using hlength),
    listLex_iff_exists_index hlength]
  constructor
  · rintro ⟨k, hx, hy, htake, hk⟩
    have hx' : k < xs.length := by simpa using hx
    have hy' : k < ys.length := by simpa using hy
    refine ⟨k, hx', hy', ?_, ?_⟩
    · apply hinjective.list_map
      simpa only [List.map_take] using htake
    · have hk' : R (f (xs.get ⟨k, hx'⟩))
          (f (ys.get ⟨k, hy'⟩)) := by
        simpa only [List.get_eq_getElem, List.getElem_map] using hk
      exact (hrel _ _).mp hk'
  · rintro ⟨k, hx, hy, htake, hk⟩
    refine ⟨k, by simpa using hx, by simpa using hy, ?_, ?_⟩
    · simp only [← List.map_take, htake]
    · have hk' := (hrel _ _).mpr hk
      simpa only [List.get_eq_getElem, List.getElem_map] using hk'

theorem listShortlex_map_iff {A : Type u} {B : Type v}
    {r : A → A → Prop} {R : B → B → Prop} (f : A → B)
    (hinjective : Function.Injective f)
    (hrel : ∀ x y, R (f x) (f y) ↔ r x y)
    (xs ys : List A) :
    List.Shortlex R (xs.map f) (ys.map f) ↔
      List.Shortlex r xs ys := by
  rw [List.shortlex_def, List.shortlex_def]
  simp only [List.length_map]
  constructor
  · rintro (hlength | ⟨hlength, hlex⟩)
    · exact Or.inl hlength
    · exact Or.inr ⟨hlength,
        (listLex_map_iff_of_length_eq f hinjective hrel xs ys hlength).mp hlex⟩
  · rintro (hlength | ⟨hlength, hlex⟩)
    · exact Or.inl hlength
    · exact Or.inr ⟨hlength,
        (listLex_map_iff_of_length_eq f hinjective hrel xs ys hlength).mpr hlex⟩

namespace Godel.RudimentaryTerm

noncomputable section

open IndexedSequenceZF

/-! ## The specialized formula -/

/--
Program comparison layout:

`[U, relation, varTag, appTag, empty, omega, leftProgram, rightProgram]`.
-/
def stackProgramLtFormula : FOFormula 8 :=
  IndexedSequenceZF.shortlexFormula stackTokenLtFormula

/-- The intended raw assignment for two genuine postfix programs. -/
def stackProgramLtAssignment (U relation : ZFSet.{u})
    (left right : List
      (StackToken (Option (Constructible.ZFCarrier U)))) :
    Tuple ZFSet.{u} 8 :=
  ![U, relation, varTag, appTag, ∅, Ordinal.omega0.toZFSet,
    stackProgramZFCode U left, stackProgramZFCode U right]

/-- The structural program-order formula has exact Shortlex semantics. -/
@[simp]
theorem satisfies_stackProgramLtFormula
    (U relation : ZFSet.{u})
    (left right : List
      (StackToken (Option (Constructible.ZFCarrier U)))) :
    FOFormula.Satisfies Delta0Formula.ZFMem stackProgramLtFormula
        (stackProgramLtAssignment U relation left right) ↔
      stackProgramRel (generatorTokenRel U relation) left right := by
  let params : Tuple ZFSet.{u} 5 :=
    ![U, relation, varTag, appTag, ∅]
  let rawTokenRel : ZFSet.{u} → ZFSet.{u} → Prop :=
    fun x y =>
      FOFormula.Satisfies Delta0Formula.ZFMem stackTokenLtFormula
        (snoc (snoc params x) y)
  have hshort :=
    IndexedSequenceZF.satisfies_shortlexFormula_sequenceCode_iff
      stackTokenLtFormula params rawTokenRel
      (fun _ _ => Iff.rfl)
      (left.map (stackTokenZFCode U))
      (right.map (stackTokenZFCode U))
  have htoken : ∀ x y : StackToken
      (Option (Constructible.ZFCarrier U)),
      rawTokenRel (stackTokenZFCode U x) (stackTokenZFCode U y) ↔
        stackTokenRel (generatorTokenRel U relation) x y := by
    intro x y
    change FOFormula.Satisfies Delta0Formula.ZFMem stackTokenLtFormula
      (snoc (snoc params (stackTokenZFCode U x))
        (stackTokenZFCode U y)) ↔
      stackTokenRel (generatorTokenRel U relation) x y
    have hassign :
        snoc (snoc params (stackTokenZFCode U x))
            (stackTokenZFCode U y) =
          ![U, relation, varTag, appTag, ∅,
            stackTokenZFCode U x, stackTokenZFCode U y] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign]
    exact satisfies_stackTokenLtFormula_tokenCodes U relation x y
  have hmap := listShortlex_map_iff (stackTokenZFCode U)
    (stackTokenZFCode_injective U) htoken left right
  have hformula :
      FOFormula.Satisfies Delta0Formula.ZFMem stackProgramLtFormula
          (stackProgramLtAssignment U relation left right) ↔
        List.Shortlex rawTokenRel
          (left.map (stackTokenZFCode U))
          (right.map (stackTokenZFCode U)) := by
    have hassign :
        stackProgramLtAssignment U relation left right =
          snoc
            (snoc (snoc params Ordinal.omega0.toZFSet)
              (sequenceCode (left.map (stackTokenZFCode U))))
            (sequenceCode (right.map (stackTokenZFCode U))) := by
      funext i
      fin_cases i <;> rfl
    rw [hassign]
    simpa only [stackProgramLtFormula] using hshort
  exact hformula.trans hmap

end

end Godel.RudimentaryTerm

end Constructible
