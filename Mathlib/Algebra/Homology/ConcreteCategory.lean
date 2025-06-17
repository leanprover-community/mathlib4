/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory

/-!
# Homology of complexes in concrete categories

The homology of short complexes in concrete categories was studied in
`Mathlib/Algebra/Homology/ShortComplex/ConcreteCategory.lean`. In this file,
we introduce specific definitions and lemmas for the homology
of homological complexes in concrete categories. In particular,
we give a computation of the connecting homomorphism of
the homology sequence in terms of (co)cycles.

-/

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC] [HasForget₂ C Ab.{v}]
  [Abelian C] [(forget₂ C Ab).Additive] [(forget₂ C Ab).PreservesHomology]
  {ι : Type*} {c : ComplexShape ι}

namespace HomologicalComplex

variable (K : HomologicalComplex C c)

/-- Constructor for cycles of a homological complex in a concrete category. -/
noncomputable def cyclesMk {i : ι} (x : (forget₂ C Ab).obj (K.X i)) (j : ι) (hj : c.next i = j)
    (hx : ((forget₂ C Ab).map (K.d i j)) x = 0) :
    (forget₂ C Ab).obj (K.cycles i) :=
  (K.sc i).cyclesMk x (by subst hj; exact hx)

@[simp]
lemma i_cyclesMk {i : ι} (x : (forget₂ C Ab).obj (K.X i)) (j : ι) (hj : c.next i = j)
    (hx : ((forget₂ C Ab).map (K.d i j)) x = 0) :
    ((forget₂ C Ab).map (K.iCycles i)) (K.cyclesMk x j hj hx) = x := by
  subst hj
  apply (K.sc i).i_cyclesMk

end HomologicalComplex

namespace CategoryTheory

namespace ShortComplex

namespace ShortExact

variable {S : ShortComplex (HomologicalComplex C c)}
  (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)

lemma δ_apply' (x₃ : (forget₂ C Ab).obj (S.X₃.homology i))
    (x₂ : (forget₂ C Ab).obj (S.X₂.opcycles i))
    (x₁ : (forget₂ C Ab).obj (S.X₁.cycles j))
    (h₂ : (forget₂ C Ab).map (HomologicalComplex.opcyclesMap S.g i) x₂ =
      (forget₂ C Ab).map (S.X₃.homologyι i) x₃)
    (h₁ : (forget₂ C Ab).map (HomologicalComplex.cyclesMap S.f j) x₁ =
      (forget₂ C Ab).map (S.X₂.opcyclesToCycles i j) x₂) :
    (forget₂ C Ab).map (hS.δ i j hij) x₃ = (forget₂ C Ab).map (S.X₁.homologyπ j) x₁ :=
  (HomologicalComplex.HomologySequence.snakeInput hS i j hij).δ_apply' x₃ x₂ x₁ h₂ h₁

lemma δ_apply (x₃ : (forget₂ C Ab).obj (S.X₃.X i))
    (hx₃ : (forget₂ C Ab).map (S.X₃.d i j) x₃ = 0)
    (x₂ : (forget₂ C Ab).obj (S.X₂.X i)) (hx₂ : (forget₂ C Ab).map (S.g.f i) x₂ = x₃)
    (x₁ : (forget₂ C Ab).obj (S.X₁.X j))
    (hx₁ : (forget₂ C Ab).map (S.f.f j) x₁ = (forget₂ C Ab).map (S.X₂.d i j) x₂)
    (k : ι) (hk : c.next j = k) :
    (forget₂ C Ab).map (hS.δ i j hij)
      ((forget₂ C Ab).map (S.X₃.homologyπ i) (S.X₃.cyclesMk x₃ j (c.next_eq' hij) hx₃)) =
        (forget₂ C Ab).map (S.X₁.homologyπ j) (S.X₁.cyclesMk x₁ k hk (by
          have := hS.mono_f
          apply (Preadditive.mono_iff_injective (S.f.f k)).1 inferInstance
          rw [← ConcreteCategory.forget₂_comp_apply, ← HomologicalComplex.Hom.comm,
            ConcreteCategory.forget₂_comp_apply, hx₁, ← ConcreteCategory.forget₂_comp_apply,
            HomologicalComplex.d_comp_d, Functor.map_zero, map_zero]; rfl)) := by
  refine hS.δ_apply' i j hij _ ((forget₂ C Ab).map (S.X₂.pOpcycles i) x₂) _ ?_ ?_
  · rw [← ConcreteCategory.forget₂_comp_apply, ← ConcreteCategory.forget₂_comp_apply,
      HomologicalComplex.p_opcyclesMap, Functor.map_comp, ConcreteCategory.comp_apply,
      HomologicalComplex.homology_π_ι, ConcreteCategory.forget₂_comp_apply, hx₂,
      HomologicalComplex.i_cyclesMk]
  · apply (Preadditive.mono_iff_injective (S.X₂.iCycles j)).1 inferInstance
    conv_lhs =>
      rw [← ConcreteCategory.forget₂_comp_apply, HomologicalComplex.cyclesMap_i,
        ConcreteCategory.forget₂_comp_apply, HomologicalComplex.i_cyclesMk, hx₁]
    conv_rhs =>
      rw [← ConcreteCategory.forget₂_comp_apply, ← ConcreteCategory.forget₂_comp_apply,
        HomologicalComplex.pOpcycles_opcyclesToCycles_assoc, HomologicalComplex.toCycles_i]

end ShortExact

end ShortComplex

end CategoryTheory
