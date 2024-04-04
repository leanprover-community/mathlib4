/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics
/-!
# Asymptotic statements about the operator norm

This file contains lemmas about how operator norm on continuous linear maps interacts with `IsBigO`.

-/

open Asymptotics

set_option linter.uppercaseLean3 false

variable {𝕜 𝕜₂ 𝕜₃ E F G : Type*}
variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]
variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F]  [NormedSpace 𝕜₃ G] {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃}

namespace ContinuousLinearMap

variable [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) (l : Filter E)

theorem isBigOWith_id : IsBigOWith ‖f‖ l f fun x => x :=
  isBigOWith_of_le' _ f.le_opNorm
#align continuous_linear_map.is_O_with_id ContinuousLinearMap.isBigOWith_id

theorem isBigO_id : f =O[l] fun x => x :=
  (f.isBigOWith_id l).isBigO
#align continuous_linear_map.is_O_id ContinuousLinearMap.isBigO_id

theorem isBigOWith_comp [RingHomIsometric σ₂₃] {α : Type*} (g : F →SL[σ₂₃] G) (f : α → F)
    (l : Filter α) : IsBigOWith ‖g‖ l (fun x' => g (f x')) f :=
  (g.isBigOWith_id ⊤).comp_tendsto le_top
#align continuous_linear_map.is_O_with_comp ContinuousLinearMap.isBigOWith_comp

theorem isBigO_comp [RingHomIsometric σ₂₃] {α : Type*} (g : F →SL[σ₂₃] G) (f : α → F)
    (l : Filter α) : (fun x' => g (f x')) =O[l] f :=
  (g.isBigOWith_comp f l).isBigO
#align continuous_linear_map.is_O_comp ContinuousLinearMap.isBigO_comp

theorem isBigOWith_sub (x : E) :
    IsBigOWith ‖f‖ l (fun x' => f (x' - x)) fun x' => x' - x :=
  f.isBigOWith_comp _ l
#align continuous_linear_map.is_O_with_sub ContinuousLinearMap.isBigOWith_sub

theorem isBigO_sub (x : E) :
    (fun x' => f (x' - x)) =O[l] fun x' => x' - x :=
  f.isBigO_comp _ l
#align continuous_linear_map.is_O_sub ContinuousLinearMap.isBigO_sub

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]  (e : E ≃SL[σ₁₂] F)

section

variable [RingHomIsometric σ₁₂]

theorem isBigO_comp {α : Type*} (f : α → E) (l : Filter α) : (fun x' => e (f x')) =O[l] f :=
  (e : E →SL[σ₁₂] F).isBigO_comp f l
#align continuous_linear_equiv.is_O_comp ContinuousLinearEquiv.isBigO_comp

theorem isBigO_sub (l : Filter E) (x : E) : (fun x' => e (x' - x)) =O[l] fun x' => x' - x :=
  (e : E →SL[σ₁₂] F).isBigO_sub l x
#align continuous_linear_equiv.is_O_sub ContinuousLinearEquiv.isBigO_sub

end

section

variable [RingHomIsometric σ₂₁]

theorem isBigO_comp_rev {α : Type*} (f : α → E) (l : Filter α) : f =O[l] fun x' => e (f x') :=
  (e.symm.isBigO_comp _ l).congr_left fun _ => e.symm_apply_apply _
#align continuous_linear_equiv.is_O_comp_rev ContinuousLinearEquiv.isBigO_comp_rev

theorem isBigO_sub_rev (l : Filter E) (x : E) : (fun x' => x' - x) =O[l] fun x' => e (x' - x) :=
  e.isBigO_comp_rev _ _
#align continuous_linear_equiv.is_O_sub_rev ContinuousLinearEquiv.isBigO_sub_rev

end

end ContinuousLinearEquiv
