import Mathlib.InformationTheory.Code.Linear.Aut
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.GroupAction.DomAct.Basic

instance {G α β : Type*} [Monoid G] [Monoid β] [MulAction G α] :
    MulDistribMulAction (Gᵈᵐᵃ) (α → β) where
  smul_mul _ _ _ := funext fun _ => rfl
  smul_one _ := funext fun _ => rfl

variable {K:Type*} {ι:Type*} [Monoid K]


def f : (ι ≃ ι)ᵐᵒᵖ →* MulAut (ι → Kˣ) := MulDistribMulAction.toMulAut (ι ≃ ι)ᵈᵐᵃ (ι → Kˣ)
