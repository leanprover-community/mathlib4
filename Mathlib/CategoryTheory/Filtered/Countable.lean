/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Presentable.Directed

import Mathlib.Data.Set.Countable

/-!
# Countable filtered categories

Every countable filtered category admits a final functor from a countable directed poset
(`IsFiltered.exists_directed_countable`), and hence a final functor from `ℕ`
(`IsFiltered.exists_final_nat`). Dually, every countable cofiltered category admits an initial
functor from a countable codirected poset (`IsCofiltered.exists_codirected_countable`), and hence
an initial functor from `ℕᵒᵖ` (`IsCofiltered.exists_initial_nat`).

We use Deligne's construction from `Mathlib.CategoryTheory.Presentable.Directed`: the finite
diagrams in a countable category form a countable type.
-/

@[expose] public section

universe w

namespace CategoryTheory

namespace IsCardinalFiltered.exists_cardinal_directed

variable (J : Type w) [SmallCategory J]

instance [CountableCategory J] : Countable (Diagram J .aleph0) := by
  have : Countable {s : Set (Arrow J) // s.Finite} := Set.Countable.to_subtype
    Set.Countable.ofPred_finite
  have : Countable {s : Set J // s.Finite} := Set.Countable.to_subtype
    Set.Countable.ofPred_finite
  let f (D : Diagram J .aleph0) :
      {s : Set (Arrow J) // s.Finite} × {s : Set J // s.Finite} :=
    (⟨D.W.toSet, Set.finite_coe_iff.mp ((hasCardinalLT_aleph0_iff _).mp D.hW)⟩,
      ⟨Set.ofPred D.P, Set.finite_coe_iff.mp ((hasCardinalLT_aleph0_iff _).mp D.hP)⟩)
  refine Function.Injective.countable (f := f) ?_
  intro D₁ D₂ h
  have hW : D₁.W.toSet = D₂.W.toSet := congrArg (fun x ↦ x.1.val) h
  have hP : D₁.P = D₂.P := congrArg (fun x ↦ x.2.val) h
  apply Diagram.ext ?_ hP
  ext X Y g
  exact Set.ext_iff.mp hW (Arrow.mk g)

instance [CountableCategory J] : Countable (DiagramWithUniqueTerminal J .aleph0) :=
  Function.Injective.countable (f := fun D ↦ D.toDiagram) (fun _ _ h ↦
    DiagramWithUniqueTerminal.ext _ _ (congrArg Diagram.W h) (congrArg Diagram.P h))

end IsCardinalFiltered.exists_cardinal_directed

open IsCardinalFiltered.exists_cardinal_directed in
attribute [local instance] Cardinal.fact_isRegular_aleph0 in
/-- A countable filtered category admits a final functor from a countable directed poset. -/
lemma IsFiltered.exists_directed_countable (J : Type*) [Category* J]
    [IsFiltered J] [CountableCategory J] :
    ∃ (α : Type) (_ : PartialOrder α) (_ : IsDirectedOrder α) (_ : Nonempty α)
      (_ : Countable α) (F : α ⥤ J), F.Final := by
  let K := CountableCategory.HomAsType J
  have : IsFiltered K := .of_equivalence (CountableCategory.homAsTypeEquiv J).symm
  have : IsCardinalFiltered (K × ℕ) Cardinal.aleph0 :=
    (isCardinalFiltered_aleph0_iff _).2 inferInstance
  have hK (e : K × ℕ) : ∃ (m : K × ℕ) (_ : e ⟶ m), IsEmpty (m ⟶ e) :=
    ⟨(e.1, e.2 + 1), (𝟙 _, homOfLE (Nat.le_succ _)),
      ⟨fun f ↦ (Nat.not_succ_le_self _) (leOfHom f.2)⟩⟩
  let α := DiagramWithUniqueTerminal (K × ℕ) Cardinal.aleph0
  have : IsCardinalFiltered α Cardinal.aleph0 := isCardinalFiltered _ _ hK
  have : IsFiltered α := (isCardinalFiltered_aleph0_iff _).1 inferInstance
  have := final_functor _ Cardinal.aleph0 hK
  exact ⟨α, inferInstance, IsFiltered.isDirectedOrder _, nonempty, inferInstance,
    functor _ _ ⋙ Prod.fst _ _ ⋙ (CountableCategory.homAsTypeEquiv J).functor, inferInstance⟩

/-- A countable cofiltered category admits an initial functor from a countable codirected poset. -/
lemma IsCofiltered.exists_codirected_countable (J : Type*) [Category* J]
    [IsCofiltered J] [CountableCategory J] :
    ∃ (α : Type) (_ : PartialOrder α) (_ : IsCodirectedOrder α) (_ : Nonempty α)
      (_ : Countable α) (F : α ⥤ J), F.Initial := by
  obtain ⟨α, _, _, _, _, F, _⟩ := IsFiltered.exists_directed_countable Jᵒᵖ
  exact ⟨αᵒᵈ, inferInstance, inferInstance, inferInstance, inferInstanceAs (Countable α),
    (orderDualEquivalence α).functor ⋙ F.leftOp, inferInstance⟩

/-- Every countable filtered category admits a final functor from `ℕ`. -/
lemma IsFiltered.exists_final_nat (J : Type*) [Category* J]
    [IsFiltered J] [CountableCategory J] : ∃ (F : ℕ ⥤ J), F.Final := by
  obtain ⟨α, _, _, _, _, F, _⟩ := IsFiltered.exists_directed_countable J
  exact ⟨Limits.IsFiltered.sequentialFunctor α ⋙ F, inferInstance⟩

/-- Every countable cofiltered category admits an initial functor from `ℕᵒᵖ`. -/
lemma IsCofiltered.exists_initial_nat (J : Type*) [Category* J]
    [IsCofiltered J] [CountableCategory J] : ∃ (F : ℕᵒᵖ ⥤ J), F.Initial := by
  obtain ⟨F, _⟩ := IsFiltered.exists_final_nat Jᵒᵖ
  exact ⟨F.leftOp, inferInstance⟩

end CategoryTheory
