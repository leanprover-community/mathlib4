/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Module.Presentation.PiTensor
import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating

/-!
# Presentation of the exterior power

-/

open Function

namespace ExteriorAlgebra

variable (R : Type*) [CommRing R] (ι : Type*) [DecidableEq ι]
  (n : ℕ) (M : Type*) [AddCommGroup M] [Module R M]

namespace exteriorPower

inductive Rels
  | add (m : ι → M) (i : ι) (x y : M)
  | smul (m : ι → M) (i : ι) (r : R) (x : M)
  | alt (m : ι → M) (i j : ι) (hm : m i = m j) (hij : i ≠ j)

@[simps]
noncomputable def relations : Module.Relations R where
  G := ι → M
  R := Rels R ι M
  relation r := match r with
    | .add m i x y => Finsupp.single ((update m i x)) 1 +
        Finsupp.single ((update m i y)) 1 -
        Finsupp.single ((update m i (x + y))) 1
    | .smul m i r x => Finsupp.single ((update m i (r • x))) 1 -
        r • Finsupp.single ((update m i x)) 1
    | .alt m _ _ _ _ => Finsupp.single m 1

variable (N : Type*) [AddCommGroup N] [Module R N]

variable {R ι M N} in
def relationsSolutionEquiv :
    (relations R ι M).Solution N ≃ AlternatingMap R M N ι where
  toFun s :=
    { toFun := fun m ↦ s.var m
      map_add' := fun m i x y ↦ by
        have := s.linearCombination_var_relation (.add m i x y)
        dsimp at this ⊢
        rw [map_sub, map_add, Finsupp.linearCombination_single, one_smul,
          Finsupp.linearCombination_single, one_smul,
          Finsupp.linearCombination_single, one_smul, sub_eq_zero] at this
        convert this.symm
      map_smul' := fun m i r x ↦ by
        have := s.linearCombination_var_relation (.smul m i r x)
        dsimp at this ⊢
        rw [Finsupp.smul_single, smul_eq_mul, mul_one, map_sub,
          Finsupp.linearCombination_single, one_smul,
          Finsupp.linearCombination_single, sub_eq_zero] at this
        convert this
      map_eq_zero_of_eq' := fun v i j hm hij ↦
        by simpa using s.linearCombination_var_relation (.alt v i j hm hij) }
  invFun f :=
    { var := fun m ↦ f m
      linearCombination_var_relation := by
        rintro (⟨m, i, x, y⟩ | ⟨m, i, r, x⟩ | ⟨v, i, j, hm, hij⟩)
        · simp
        · simp
        · simpa using f.map_eq_zero_of_eq v hm hij }
  left_inv _ := rfl
  right_inv _ := rfl

end exteriorPower

def exteriorProduct : AlternatingMap R M (exteriorPower R n M) (Fin n) where
  toFun m := ⟨ιMulti R n m, ιMulti_range _ _ (by simp)⟩
  map_add' m i x y := Subtype.ext (by simp)
  map_smul' m i c x := Subtype.ext (by simp)
  map_eq_zero_of_eq' v i j hij hij' :=
    Subtype.ext ((ιMulti R (M := M) n).map_eq_zero_of_eq v hij hij')

namespace exteriorPower

def relationsSolution :
    (relations R (Fin n) M).Solution (exteriorPower R n M) :=
  relationsSolutionEquiv.symm (exteriorProduct R n M)

-- the code in https://github.com/leanprover-community/mathlib4/pull/18261 basically shows this
lemma relationsSolution_isPresentation :
    (relationsSolution R n M).IsPresentation := sorry

@[simps!]
noncomputable def presentation : Module.Presentation R (exteriorPower R n M) where
  toSolution := relationsSolution R n M
  toIsPresentation := relationsSolution_isPresentation R n M

end exteriorPower

end ExteriorAlgebra

namespace Module

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

namespace Relations

variable (relation : Presentation R M)


end Relations

end Module
