/-
Copyright (c) 2026 Sanghyeok Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sanghyeok Park
-/
module

public import Mathlib.Logic.Relation

/-!
# Normal forms for relations

This file develops basic normal form notions for abstract reduction relations.

We represent finite reduction sequences by `Relation.ReflTransGen r`. The assumption
`WellFounded (flip r)` expresses termination of forward reductions.

The main results are:

* existence of normal forms for terminating relations;
* Newman's lemma: for a terminating relation, local confluence implies confluence;
* for terminating relations, confluence is equivalent to uniqueness of normal forms.
-/

@[expose] public section

namespace Relation

variable {α : Type*} {r : α → α → Prop} {a b c : α}

/-- An element is in normal form if it admits no one-step reduction. -/
def IsNormalForm (r : α → α → Prop) (a : α) : Prop :=
  ∀ b, ¬ r a b

/-- An element `b` is a normal form of `a` with respect to `r`. -/
def IsNormalFormOf (r : α → α → Prop) (a b : α) : Prop :=
  ReflTransGen r a b ∧ IsNormalForm r b

/-- A relation has unique normal forms if any two normal forms reachable from the same element by
finite reductions are equal. -/
def UniqueNormalForms (r : α → α → Prop) : Prop :=
  ∀ {a b c : α},
    ReflTransGen r a b →
    ReflTransGen r a c →
    IsNormalForm r b →
    IsNormalForm r c →
    b = c

/-- A relation is locally confluent if any two one-step reductions starting from the same element
can be joined by finite reductions. -/
def LocallyConfluent (r : α → α → Prop) : Prop :=
  ∀ {a b c : α},
    r a b →
    r a c →
    Join (ReflTransGen r) b c

/-- If forward reductions are terminating, then every element has at least one normal form. -/
theorem exists_normalFormOf_of_wellFounded_flip
    (hrwf : WellFounded (flip r)) (a : α) :
    ∃ b : α, IsNormalFormOf r a b := by
  refine hrwf.induction
    (C := fun a : α => ∃ b : α, IsNormalFormOf r a b)
    a
    ?_
  intro a ih
  by_cases hnf : IsNormalForm r a
  · exact ⟨a, ReflTransGen.refl, hnf⟩
  · have hex : ∃ b : α, r a b := by
      exact Classical.byContradiction fun hno =>
        hnf fun b hb => hno ⟨b, hb⟩
    rcases hex with ⟨b, hab⟩
    rcases ih b hab with ⟨c, hbc, hnf_c⟩
    exact ⟨c, (ReflTransGen.single hab).trans hbc, hnf_c⟩

namespace ReflTransGen

/-- If `a` is in normal form and `a` reduces finitely to `b`, then `b = a`. -/
theorem eq_of_isNormalForm (hnf : IsNormalForm r a) (h : ReflTransGen r a b) : b = a :=
  (Relation.reflTransGen_iff_eq hnf).1 h

end ReflTransGen

/-- Confluence implies local confluence. -/
theorem Confluent.locallyConfluent (hc : Confluent r) : LocallyConfluent r := by
  intro _ _ _ hab hac
  exact hc (ReflTransGen.single hab) (ReflTransGen.single hac)

/-- Confluence implies local confluence. -/
theorem locallyConfluent_of_confluent (hc : Confluent r) : LocallyConfluent r :=
  Confluent.locallyConfluent hc

/-- The Church-Rosser property implies local confluence. -/
theorem ChurchRosser.locallyConfluent (hcr : ChurchRosser r) : LocallyConfluent r :=
  Confluent.locallyConfluent (ChurchRosser.confluent hcr)

/-- Newman's lemma, main direction. If `flip r` is well-founded and `r` is locally confluent, then
`r` is confluent. -/
theorem confluent_of_wellFounded_flip_of_locallyConfluent
    (hwf : WellFounded (flip r)) (hlc : LocallyConfluent r) :
    Confluent r := by
  intro a
  refine hwf.induction
    (C := fun a : α =>
      ∀ {b c : α},
        ReflTransGen r a b →
        ReflTransGen r a c →
        Join (ReflTransGen r) b c)
    a
    ?_
  intro a ih b c hab hac
  rcases ReflTransGen.cases_head hab with hEqAB | ⟨b', hab', hb'b⟩
  · cases hEqAB
    exact ⟨c, hac, ReflTransGen.refl⟩
  rcases ReflTransGen.cases_head hac with hEqAC | ⟨c', hac', hc'c⟩
  · cases hEqAC
    exact ⟨b, ReflTransGen.refl, hab⟩
  rcases hlc hab' hac' with ⟨d, hb'd, hc'd⟩
  rcases ih b' hab' hb'b hb'd with ⟨e, hbe, hde⟩
  rcases ih c' hac' hc'c (hc'd.trans hde) with ⟨f, hcf, hef⟩
  exact ⟨f, hbe.trans hef, hcf⟩

/-- Confluence implies unique normal forms. -/
theorem Confluent.uniqueNormalForms (hc : Confluent r) : UniqueNormalForms r := by
  intro _ b c hab hac hnf_b hnf_c
  rcases hc hab hac with ⟨d, hbd, hcd⟩
  have hdb : d = b := ReflTransGen.eq_of_isNormalForm hnf_b hbd
  have hdc : d = c := ReflTransGen.eq_of_isNormalForm hnf_c hcd
  exact hdb.symm.trans hdc

/-- Confluence implies unique normal forms. -/
theorem uniqueNormalForms_of_confluent (hc : Confluent r) : UniqueNormalForms r :=
  Confluent.uniqueNormalForms hc

/-- Under well-foundedness of `flip r`, unique normal forms imply confluence. -/
theorem confluent_of_wellFounded_flip_of_uniqueNormalForms
    (hwf : WellFounded (flip r)) (hunf : UniqueNormalForms r) :
    Confluent r := by
  intro a b c hab hac
  rcases exists_normalFormOf_of_wellFounded_flip hwf b with ⟨b', hb'⟩
  rcases exists_normalFormOf_of_wellFounded_flip hwf c with ⟨c', hc'⟩
  have hEq : b' = c' :=
    hunf
      (hab.trans hb'.1)
      (hac.trans hc'.1)
      hb'.2
      hc'.2
  exact ⟨b', hb'.1, by simpa only [hEq] using hc'.1⟩

end Relation
