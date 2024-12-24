/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# `M ⊗ -` and `- ⊗ M` is a right exact functor
-/

suppress_compilation

open CategoryTheory MonoidalCategory ShortComplex.ShortExact ZeroObject

universe u
variable {R : Type u} [CommRing R] (M : ModuleCat.{u} R)

namespace ModuleCat

lemma tensorLeft_preserves_shortExact_right
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) :
    (S.map (tensorLeft M)).Exact ∧ Epi (M ◁ S.g) :=
  ⟨moduleCat_exact_iff_function_exact _ |>.2 $
      lTensor_exact M (moduleCat_exact_iff_function_exact S |>.1 hS.exact)
        (epi_iff_surjective _ |>.1 hS.epi_g),
    have h := ShortComplex.exact_iff_epi (.mk S.g (0 : S.X₃ ⟶ 0) (by simp)) (by simp) |>.2 hS.epi_g
    ShortComplex.exact_iff_epi _ (by simp) |>.1 $ moduleCat_exact_iff_function_exact
      (.mk (M ◁ S.g) (0 : M ⊗ S.X₃ ⟶ 0) (by simp)) |>.2 $
      Function.Injective.comp_exact_iff_exact (i := 0)
      (fun (x y : TensorProduct R M (0 : ModuleCat R)) _ => Subsingleton.elim _ _) |>.2 $
        lTensor_exact M (moduleCat_exact_iff_function_exact _ |>.1 h)
          (epi_iff_surjective _ |>.1 inferInstance)⟩

instance : Limits.PreservesFiniteColimits (tensorLeft M) :=
  let h := Functor.preservesFiniteColimits_tfae (tensorLeft M) |>.out 0 3 |>.1 $
    tensorLeft_preserves_shortExact_right M
  Nonempty.some h

lemma tensorRight_preserves_shortExact_right
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) :
    (S.map (tensorRight M)).Exact ∧ Epi (S.g ▷ M) :=
  ⟨moduleCat_exact_iff_function_exact _ |>.2 $
      rTensor_exact M (moduleCat_exact_iff_function_exact S |>.1 hS.exact)
        (epi_iff_surjective _ |>.1 hS.epi_g),
    have h := ShortComplex.exact_iff_epi (.mk S.g (0 : S.X₃ ⟶ 0) (by simp)) (by simp) |>.2 hS.epi_g
    ShortComplex.exact_iff_epi _ (by simp) |>.1 $ moduleCat_exact_iff_function_exact
      (.mk (S.g ▷ M) (0 : S.X₃ ⊗  M ⟶ 0) (by simp)) |>.2 $
      Function.Injective.comp_exact_iff_exact (i := 0)
      (fun (x y : TensorProduct R (0 : ModuleCat R) M) _ => Subsingleton.elim _ _) |>.2 $
        rTensor_exact M (moduleCat_exact_iff_function_exact _ |>.1 h)
          (epi_iff_surjective _ |>.1 inferInstance)⟩


instance : Limits.PreservesFiniteColimits (tensorRight M) :=
  let h := Functor.preservesFiniteColimits_tfae (tensorRight M) |>.out 0 3 |>.1 $
    tensorRight_preserves_shortExact_right M
  Nonempty.some h

end ModuleCat
