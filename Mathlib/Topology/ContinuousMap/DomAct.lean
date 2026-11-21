/-
Copyright (c) 2026 Ezequiel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezequiel
-/
module

public import Mathlib.GroupTheory.GroupAction.DomAct.Basic
public import Mathlib.Topology.Algebra.Constructions.DomMulAct
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Action of `Mᵈᵐᵃ` on `C(α, β)`

If `M` acts continuously on `α`, then `Mᵈᵐᵃ` acts on `C(α, β)` by
`(c • f) a = f (mk.symm c • a)`.

## Tags

group action, continuous map, domain action
-/

public section

open ContinuousMap

namespace DomMulAct

variable {M α β N : Type*}
variable [TopologicalSpace α] [TopologicalSpace β]

section SMul

variable [SMul M α] [TopologicalSpace M] [ContinuousConstSMul M α]

instance instSMulContinuousMap : SMul Mᵈᵐᵃ C(α, β) where
  smul c f := ⟨c • (f : α → β), f.continuous.comp (continuous_const_smul (mk.symm c))⟩

omit [TopologicalSpace M] in
@[simp, norm_cast]
theorem coe_smul_continuousMap (c : Mᵈᵐᵃ) (f : C(α, β)) : ⇑(c • f) = c • ⇑f :=
  rfl

omit [TopologicalSpace M] in
theorem smul_continuousMap_apply (c : Mᵈᵐᵃ) (f : C(α, β)) (a : α) :
    (c • f) a = f (mk.symm c • a) :=
  rfl

omit [TopologicalSpace M] in
@[simp]
theorem mk_smul_continuousMap_apply (c : M) (f : C(α, β)) (a : α) : (mk c • f) a = f (c • a) :=
  rfl

variable [SMul N β] [ContinuousConstSMul N β]

instance instSMulCommClass_right : SMulCommClass Mᵈᵐᵃ N C(α, β) where
  smul_comm _ _ _ := ext fun _ => rfl

instance instSMulCommClass_left : SMulCommClass N Mᵈᵐᵃ C(α, β) where
  smul_comm _ _ _ := ext fun _ => rfl

variable [SMul N α] [SMulCommClass M N α] [ContinuousConstSMul N α]

instance instSMulCommClass_dom : SMulCommClass Mᵈᵐᵃ Nᵈᵐᵃ C(α, β) where
  smul_comm _ _ f := ext fun a => congr_arg f (smul_comm _ _ a).symm

end SMul

section MulAction

variable [Monoid M] [MulAction M α] [TopologicalSpace M] [ContinuousConstSMul M α]

instance instMulActionContinuousMap : MulAction Mᵈᵐᵃ C(α, β) where
  smul := (· • ·)
  one_smul f := by ext; simp [smul_continuousMap_apply]
  mul_smul x y f := by ext; simp [smul_continuousMap_apply, mul_smul]

end MulAction

section ContinuousSMul

variable [SMul M α] [TopologicalSpace M] [ContinuousSMul M α] [LocallyCompactSpace α]

instance instContinuousSMulContinuousMap : ContinuousSMul Mᵈᵐᵃ C(α, β) where
  continuous_smul := by
    let h : C(Mᵈᵐᵃ, C(α, α)) :=
      (ContinuousMap.mk (fun p : M × α => p.1 • p.2) continuous_smul).curry.comp (.mk mk.symm)
    refine (continuous_comp'.comp <|
      h.continuous.comp continuous_fst |>.prodMk continuous_snd).congr ?_
    rintro ⟨c, f⟩
    ext a
    change f ((h c) a) = (c • f) a
    rw [smul_continuousMap_apply, comp_apply]
    congr 1

end ContinuousSMul

end DomMulAct
