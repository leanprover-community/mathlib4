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

namespace Function

variable {ι α : Type*} [DecidableEq ι]

lemma update_comp (f : ι → α) (i : ι) (x : α) {β : Type*} (g : α → β) :
    update (g ∘ f) i (g x) = g ∘ update f i x := by
  ext j
  by_cases h : j = i
  · subst h
    simp
  · simp only [update_noteq h, comp_apply]

lemma update_update (f : ι → α) (i j : ι) (a b : α) (hij : i ≠ j) :
    update (update f i a) j b = update (update f j b) i a := by
  ext x
  by_cases h : x = i
  · subst h
    rw [update_same, update_noteq hij, update_same]
  · by_cases h' : x = j
    · subst h'
      rw [update_same, update_noteq hij.symm, update_same]
    · rw [update_noteq h, update_noteq h', update_noteq h, update_noteq h']

variable (f : ι → α) (i j : ι) (k : ι)

def swapValues (f : ι → α) (i j : ι) : ι → α :=
  update (update f i (f j)) j (f i)

lemma swapValues_eq_update_update :
    swapValues f i j = update (update f i (f j)) j (f i) :=
  rfl

@[simp] lemma swapValues_fst : swapValues f i j i = f j := by
  rw [swapValues_eq_update_update]
  by_cases h : i = j
  · subst h
    rw [update_eq_self, update_same]
  · rw [update_update _ _ _ _ _ h, update_same]

@[simp] lemma swapValues_snd : swapValues f i j j = f i := by
  rw [swapValues_eq_update_update, update_same]

lemma swapValues_apply (hi : k ≠ i) (hj : k ≠ j) :
    swapValues f i j k = f k := by
  rw [swapValues_eq_update_update]
  rw [update_noteq hj, update_noteq hi]

lemma swapValues_comp {β : Type*} (g : α → β) :
    swapValues (g.comp f) i j = g ∘ swapValues f i j := by
  simp only [swapValues_eq_update_update, comp_apply, ← update_comp]

end Function

open Function

lemma AlternatingMap.antisymmetry {R M N ι : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [DecidableEq ι]
    (f : AlternatingMap R M N ι) (x : ι → M) (i j : ι) (hij : i ≠ j) :
    f (Function.swapValues x i j) = - f x := by
  have := f.map_eq_zero_of_eq
    (Function.update (Function.update x i (x i + x j)) j (x i + x j))
    (by simp [update_noteq hij]) hij
  rw [map_add, update_update _ _ _ _ _ hij, map_add,
    update_update _ _ _ _ _ hij, map_add] at this
  nth_rw 1 [f.map_eq_zero_of_eq (hij := hij)] at this; swap
  · rw [update_same, update_update _ _ _ _ _ hij.symm, update_same]
  nth_rw 3 [f.map_eq_zero_of_eq (hij := hij)] at this; swap
  · rw [update_same, update_update _ _ _ _ _ hij.symm, update_same]
  rw [zero_add, add_zero, ← eq_neg_iff_add_eq_zero, update_eq_self, update_eq_self] at this
  rw [swapValues_eq_update_update, update_update _ _ _ _ _ hij]
  exact this

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

variable {R}
variable (relation : Relations R) (n : ℕ)

namespace exteriorPower

inductive Rels
  | piTensor (i₀ : Fin n) (r : relation.R) (g : ∀ (i : Fin n) (_ : i ≠ i₀), relation.G)
  | antisymmetry (g : Fin n → relation.G) (i j : Fin n) (hg : i ≠ j)
  | alternate (g : Fin n → relation.G) (i j : Fin n) (hg : g i = g j) (hij : i ≠ j)

end exteriorPower

@[simps]
noncomputable def exteriorPower : Relations R where
  G := Fin n → relation.G
  R := exteriorPower.Rels relation n
  relation x := match x with
    | .piTensor i₀ r g => (piTensor (fun _ ↦ relation)).relation
          (⟨i₀, r, fun ⟨a, ha⟩ ↦ g a ha⟩)
    | .antisymmetry g i j _ => Finsupp.single (swapValues g i j) 1 + Finsupp.single g 1
    | .alternate g _ _ _ _ => Finsupp.single g 1

namespace Solution

variable {relation} {N : Type*} [AddCommGroup N] [Module R N]
  (s : relation.Solution N) (n : ℕ)

def exteriorPower : (relation.exteriorPower n).Solution
    (ExteriorAlgebra.exteriorPower R n N) where
  var g := ExteriorAlgebra.exteriorProduct R n N (s.var ∘ g)
  linearCombination_var_relation := sorry

namespace IsPresentation

variable {s} (h : s.IsPresentation)

include h in
lemma exteriorPower : (s.exteriorPower n).IsPresentation := by
  have := h
  sorry

end IsPresentation

end Solution

end Relations

namespace Presentation

variable {R M} (pres : Presentation R M) (n : ℕ)

@[simps!]
noncomputable def exteriorPower : Presentation R (ExteriorAlgebra.exteriorPower R n M) where
  toSolution := pres.toSolution.exteriorPower n
  toIsPresentation := pres.toIsPresentation.exteriorPower n

end Presentation

end Module
