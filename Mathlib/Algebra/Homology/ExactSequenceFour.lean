/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ExactSequence

/-!
# Exact sequences with four terms

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

namespace ComposableArrows

section HasZeroMorphisms

namespace IsComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {n : ℕ} {S : ComposableArrows C (n + 3)}
  (hS : S.IsComplex) (k : ℕ)

/-- If `S : ComposableArrows C (n + 3)` and `k : ℕ` satisfies `k ≤ n`, this is the induced
map from a cokernel of `S.map' k (k + 1)` to a kernel of `S.map' (k + 2) (k + 3)`. -/
def cokerToKer' (hk : k ≤ n) (cc : CokernelCofork (S.map' k (k + 1)))
    (kf : KernelFork (S.map' (k + 2) (k + 3)))
    (hcc : IsColimit cc) (hkf : IsLimit kf) :
  cc.pt ⟶ kf.pt :=
  IsColimit.desc hcc
    (CokernelCofork.ofπ (π := IsLimit.lift hkf (KernelFork.ofι _ (hS.zero (k + 1))))
      (Fork.IsLimit.hom_ext hkf (by simpa using hS.zero k)))

@[reassoc (attr := simp)]
lemma cokerToKer'_fac (hk : k ≤ n) (cc : CokernelCofork (S.map' k (k + 1)))
    (kf : KernelFork (S.map' (k + 2) (k + 3)))
    (hcc : IsColimit cc) (hkf : IsLimit kf) :
    cc.π ≫ hS.cokerToKer' k hk cc kf hcc hkf ≫ kf.ι =
      S.map' (k + 1) (k + 2) := by
  simp [cokerToKer']

/-- If `S : ComposableArrows C (n + 3)` and `k : ℕ` satisfies `k ≤ n`, this is the induced
map from the cokernel of `S.map' k (k + 1)` to the kernel of `S.map' (k + 2) (k + 3)`. -/
noncomputable def cokerToKer (hk : k ≤ n)
  [HasCokernel (S.map' k (k + 1))] [HasKernel (S.map' (k + 2) (k + 3))] :
    cokernel (S.map' k (k + 1) _ _) ⟶ kernel (S.map' (k + 2) (k + 3) _ _) :=
  hS.cokerToKer' k hk (CokernelCofork.ofπ _ (cokernel.condition _))
    (KernelFork.ofι _ (kernel.condition _)) (cokernelIsCokernel _) (kernelIsKernel _)

@[reassoc (attr := simp)]
lemma cokerToKer_fac (hk : k ≤ n)
  [HasCokernel (S.map' k (k + 1))] [HasKernel (S.map' (k + 2) (k + 3))] :
    cokernel.π _ ≫ hS.cokerToKer k hk ≫ kernel.ι _ = S.map' (k + 1) (k + 2)  :=
  hS.cokerToKer'_fac k hk _ _ (cokernelIsCokernel _) (kernelIsKernel _)

end IsComplex

end HasZeroMorphisms

end ComposableArrows

end CategoryTheory
