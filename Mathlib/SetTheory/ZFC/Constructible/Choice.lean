/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.ModelTheory.SetTheory.ZFC
public import Mathlib.SetTheory.ZFC.Constructible.ZFModel

/-!
# The Axiom of Choice for the constructible universe

The canonical model-theoretic ZFC API supplies the disjoint-family formulation
of Choice. This file proves that a definable relation giving unique minima to
all nonempty constructible sets produces the required choice sets in `L`.
-/

@[expose] public section

universe u

namespace Constructible

namespace Model

/--
A formula supplies unique minima when every internally nonempty set has a
unique member with no strictly smaller member.
-/
def FormulaHasUniqueMinima {A : Type u} (E : A -> A -> Prop)
    (ltFormula : FOFormula 2) : Prop :=
  forall x : A, (exists y : A, E y x) -> exists y : A,
    (E y x /\ forall z : A, E z x ->
      Not (FOFormula.Satisfies E ltFormula ![z, y])) /\
    forall y' : A,
      (E y' x /\ forall z : A, E z x ->
        Not (FOFormula.Satisfies E ltFormula ![z, y'])) ->
      y' = y

end Model

namespace ChoiceSyntax

/-! ## Selecting minima -/

/-- Place the order formula on the newest variable and coordinate `1`. -/
def leastLtRename : Fin 2 -> Fin 4 :=
  ![Fin.last 3, (1 : Fin 2).castSucc.castSucc]

theorem comp_leastLtRename {A : Type u} (s : Tuple A 2) (x z : A) :
    (fun i => snoc (snoc s x) z (leastLtRename i)) = ![z, s 1] := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change snoc (snoc s x) z (Fin.last 3) = z
    exact snoc_last _ _
  · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    change snoc (snoc s x) z ((1 : Fin 2).castSucc.castSucc) = s 1
    simp only [snoc_castSucc]

/--
With assignment `![a,y]`, this says that `y` is minimal in some member of
the family `a` according to `ltFormula`.
-/
def leastMemberPredicate (ltFormula : FOFormula 2) : FOFormula 2 :=
  .ex
    (.conj
      (.mem (Fin.last 2) (0 : Fin 2).castSucc)
      (.conj
        (.mem (1 : Fin 2).castSucc (Fin.last 2))
        (.all
          (FOFormula.imp
            (.mem (Fin.last 3) (Fin.last 2).castSucc)
            (.neg (FOFormula.rename leastLtRename ltFormula))))))

@[simp]
theorem satisfies_leastMemberPredicate {A : Type u} (E : A -> A -> Prop)
    (ltFormula : FOFormula 2) (s : Tuple A 2) :
    FOFormula.Satisfies E (leastMemberPredicate ltFormula) s <->
      exists x : A, E x (s 0) /\ E (s 1) x /\
        forall z : A, E z x ->
          Not (FOFormula.Satisfies E ltFormula ![z, s 1]) := by
  simp only [leastMemberPredicate, FOFormula.Satisfies,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    FOFormula.satisfies_rename, snoc_last, snoc_castSucc,
    comp_leastLtRename]

end ChoiceSyntax

namespace Model

/--
A formula giving unique minima for all nonempty constructible sets yields the
disjoint-family form of Choice in `L`.
-/
theorem lCarrier_modelsChoice_of_formulaHasUniqueMinima
    (ltFormula : FOFormula 2)
    (hmin : FormulaHasUniqueMinima
      (fun x y : LCarrier.{u} => x.1 ∈ y.1) ltFormula) :
    FirstOrder.SetTheory.ModelsChoice LCarrier.{u} := by
  intro a hnonempty hdisjoint
  let params : Tuple LCarrier.{u} 1 := ![a]
  rcases exists_separationLCarrier
      (ChoiceSyntax.leastMemberPredicate ltFormula)
      params (sUnionLCarrier a) with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro x hxa
  rcases hmin x (hnonempty x hxa) with
    ⟨y, ⟨hyx, hymin⟩, hyunique⟩
  refine ⟨y, hyx, ?_, ?_⟩
  · apply (hc y).mpr
    refine ⟨?_, ?_⟩
    · exact (mem_sUnionLCarrier_iff a y).mpr ⟨x, hxa, hyx⟩
    · apply (ChoiceSyntax.satisfies_leastMemberPredicate
        (fun z w : LCarrier.{u} => z.1 ∈ w.1)
        ltFormula (snoc params y)).mpr
      refine ⟨x, ?_, hyx, hymin⟩
      simpa [params, snoc_eq_finSnoc] using hxa
  · intro z hzx hzc
    have hzSelected := (hc z).mp hzc
    have hzPredicate := hzSelected.2
    rcases (ChoiceSyntax.satisfies_leastMemberPredicate
        (fun q w : LCarrier.{u} => q.1 ∈ w.1)
        ltFormula (snoc params z)).mp hzPredicate with
      ⟨x', hx'a, hzx', hzmin⟩
    have hxx' : x = x' := by
      by_contra hne
      have hxdisjoint := hdisjoint x hxa x'
        (by simpa [params, snoc_eq_finSnoc] using hx'a) hne
      exact hxdisjoint z hzx hzx'
    subst x'
    exact hyunique z ⟨hzx, hzmin⟩

/-- A unique-minimum formula is sufficient for the canonical ZFC model theorem. -/
theorem lCarrier_models_ZFC_of_formulaHasUniqueMinima
    (ltFormula : FOFormula 2)
    (hmin : FormulaHasUniqueMinima
      (fun x y : LCarrier.{u} => x.1 ∈ y.1) ltFormula) :
    LCarrier.{u} ⊨ FirstOrder.Language.Theory.ZFC := by
  rw [FirstOrder.Language.Theory.model_ZFC_iff]
  exact ⟨lCarrier_models_ZF,
    lCarrier_modelsChoice_of_formulaHasUniqueMinima ltFormula hmin⟩

end Model

end Constructible
