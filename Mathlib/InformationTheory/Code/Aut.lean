import Mathlib.InformationTheory.Code.Equiv
open Code

section code
variable {α γ T :Type*} (gdist:T) (s:Set α)
variable--? [_Code γ gdist s] =>
  [CompleteLinearOrder γ] [AddCommMonoid γ]
  [CovariantClass γ γ (fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1] [FunLike T α (α → γ)]
  [GPseudoMetricClass T α γ] [Set.IsDelone gdist s]

def CodeAut [_Code γ gdist s] :Type _ := CodeEquiv gdist s gdist s

instance CodeAutGroup [_Code γ gdist s] : Group (CodeAut gdist s) where
  mul := CodeEquiv.trans
  mul_assoc := _
  one := CodeEquiv.refl gdist s
  one_mul := _
  mul_one := _
  inv := CodeEquiv.symm
  mul_left_inv := _

end code

section linearcode

variable {γ Tₖ Tₘ M:Type} (K:Type) [Field K] (gdist_k:Tₖ) (gdist_m:Tₘ)
variable--? [Module K M] =>
  [AddCommMonoid M] [Module K M]
variable (s:Submodule K M)
-- set_option variable?.maxSteps 20
variable--? [_LinearCode γ K gdist_k gdist_m s] =>
  [CompleteLinearOrder γ] [Semiring γ]
  [CovariantClass γ γ (fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1] [FunLike Tₖ K (K → γ)]
  [GPseudoMetricClass Tₖ K γ] [AddGNorm K γ gdist_k] [FunLike Tₘ M (M → γ)]
  [GPseudoMetricClass Tₘ M γ] [AddGNorm M γ gdist_m] [Set.IsDelone gdist_m ↑s] [Nontrivial γ]
  [PosMulMono γ] [MulPosMono γ] [ZeroLEOneClass γ] [StrictModuleGNorm K K gdist_k gdist_k]
  [StrictModuleGNorm K M gdist_k gdist_m]

def LinearCodeAut [_LinearCode γ K gdist_k gdist_m s] := LinearCodeEquiv K gdist_k gdist_m s gdist_m s

-- instance LinearCodeAutGroup [_LinearCode γ K gdist_k gdist_m s] : Group (LinearCodeAut K gdist_k gdist_m s) where
--   mul := LinearCodeEquiv.trans K gdist_k
--   mul_assoc := _
--   one := LinearCodeEquiv.refl K gdist_k
--   one_mul := _
--   mul_one := _
--   inv := LinearCodeEquiv.symm
--   mul_left_inv := _

end linearcode
