/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.NormedSpace.Real

#align_import analysis.calculus.diff_cont_on_cl from "leanprover-community/mathlib"@"3bce8d800a6f2b8f63fe1e588fd76a9ff4adcebe"

/-!
# Functions differentiable on a domain and continuous on its closure

Many theorems in complex analysis assume that a function is complex differentiable on a domain and
is continuous on its closure. In this file we define a predicate `DiffContOnCl` that expresses
this property and prove basic facts about this predicate.
-/


open Set Filter Metric

open scoped Topology

variable (𝕜 : Type*) {E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedAddCommGroup G]
  [NormedSpace 𝕜 G] {f g : E → F} {s t : Set E} {x : E}

/-- A predicate saying that a function is differentiable on a set and is continuous on its
closure. This is a common assumption in complex analysis. -/
structure DiffContOnCl (f : E → F) (s : Set E) : Prop where
  protected differentiableOn : DifferentiableOn 𝕜 f s
  protected continuousOn : ContinuousOn f (closure s)
#align diff_cont_on_cl DiffContOnCl

variable {𝕜}

theorem DifferentiableOn.diffContOnCl (h : DifferentiableOn 𝕜 f (closure s)) : DiffContOnCl 𝕜 f s :=
  ⟨h.mono subset_closure, h.continuousOn⟩
#align differentiable_on.diff_cont_on_cl DifferentiableOn.diffContOnCl

theorem Differentiable.diffContOnCl (h : Differentiable 𝕜 f) : DiffContOnCl 𝕜 f s :=
  ⟨h.differentiableOn, h.continuous.continuousOn⟩
#align differentiable.diff_cont_on_cl Differentiable.diffContOnCl

theorem IsClosed.diffContOnCl_iff (hs : IsClosed s) : DiffContOnCl 𝕜 f s ↔ DifferentiableOn 𝕜 f s :=
  ⟨fun h => h.differentiableOn, fun h => ⟨h, hs.closure_eq.symm ▸ h.continuousOn⟩⟩
#align is_closed.diff_cont_on_cl_iff IsClosed.diffContOnCl_iff

theorem diffContOnCl_univ : DiffContOnCl 𝕜 f univ ↔ Differentiable 𝕜 f :=
  isClosed_univ.diffContOnCl_iff.trans differentiableOn_univ
#align diff_cont_on_cl_univ diffContOnCl_univ

theorem diffContOnCl_const {c : F} : DiffContOnCl 𝕜 (fun _ : E => c) s :=
  ⟨differentiableOn_const c, continuousOn_const⟩
#align diff_cont_on_cl_const diffContOnCl_const

namespace DiffContOnCl

theorem comp {g : G → E} {t : Set G} (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g t)
    (h : MapsTo g t s) : DiffContOnCl 𝕜 (f ∘ g) t :=
  ⟨hf.1.comp hg.1 h, hf.2.comp hg.2 <| h.closure_of_continuousOn hg.2⟩
#align diff_cont_on_cl.comp DiffContOnCl.comp

theorem continuousOn_ball [NormedSpace ℝ E] {x : E} {r : ℝ} (h : DiffContOnCl 𝕜 f (ball x r)) :
    ContinuousOn f (closedBall x r) := by
  rcases eq_or_ne r 0 with (rfl | hr)
  · rw [closedBall_zero]
    exact continuousOn_singleton f x
  · rw [← closure_ball x hr]
    exact h.continuousOn
#align diff_cont_on_cl.continuous_on_ball DiffContOnCl.continuousOn_ball

theorem mk_ball {x : E} {r : ℝ} (hd : DifferentiableOn 𝕜 f (ball x r))
    (hc : ContinuousOn f (closedBall x r)) : DiffContOnCl 𝕜 f (ball x r) :=
  ⟨hd, hc.mono <| closure_ball_subset_closedBall⟩
#align diff_cont_on_cl.mk_ball DiffContOnCl.mk_ball

protected theorem differentiableAt (h : DiffContOnCl 𝕜 f s) (hs : IsOpen s) (hx : x ∈ s) :
    DifferentiableAt 𝕜 f x :=
  h.differentiableOn.differentiableAt <| hs.mem_nhds hx
#align diff_cont_on_cl.differentiable_at DiffContOnCl.differentiableAt

theorem differentiableAt' (h : DiffContOnCl 𝕜 f s) (hx : s ∈ 𝓝 x) : DifferentiableAt 𝕜 f x :=
  h.differentiableOn.differentiableAt hx
#align diff_cont_on_cl.differentiable_at' DiffContOnCl.differentiableAt'

protected theorem mono (h : DiffContOnCl 𝕜 f s) (ht : t ⊆ s) : DiffContOnCl 𝕜 f t :=
  ⟨h.differentiableOn.mono ht, h.continuousOn.mono (closure_mono ht)⟩
#align diff_cont_on_cl.mono DiffContOnCl.mono

theorem add (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g s) : DiffContOnCl 𝕜 (f + g) s :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩
#align diff_cont_on_cl.add DiffContOnCl.add

theorem add_const (hf : DiffContOnCl 𝕜 f s) (c : F) : DiffContOnCl 𝕜 (fun x => f x + c) s :=
  hf.add diffContOnCl_const
#align diff_cont_on_cl.add_const DiffContOnCl.add_const

theorem const_add (hf : DiffContOnCl 𝕜 f s) (c : F) : DiffContOnCl 𝕜 (fun x => c + f x) s :=
  diffContOnCl_const.add hf
#align diff_cont_on_cl.const_add DiffContOnCl.const_add

theorem neg (hf : DiffContOnCl 𝕜 f s) : DiffContOnCl 𝕜 (-f) s :=
  ⟨hf.1.neg, hf.2.neg⟩
#align diff_cont_on_cl.neg DiffContOnCl.neg

theorem sub (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g s) : DiffContOnCl 𝕜 (f - g) s :=
  ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩
#align diff_cont_on_cl.sub DiffContOnCl.sub

theorem sub_const (hf : DiffContOnCl 𝕜 f s) (c : F) : DiffContOnCl 𝕜 (fun x => f x - c) s :=
  hf.sub diffContOnCl_const
#align diff_cont_on_cl.sub_const DiffContOnCl.sub_const

theorem const_sub (hf : DiffContOnCl 𝕜 f s) (c : F) : DiffContOnCl 𝕜 (fun x => c - f x) s :=
  diffContOnCl_const.sub hf
#align diff_cont_on_cl.const_sub DiffContOnCl.const_sub

theorem const_smul {R : Type*} [Semiring R] [Module R F] [SMulCommClass 𝕜 R F]
    [ContinuousConstSMul R F] (hf : DiffContOnCl 𝕜 f s) (c : R) : DiffContOnCl 𝕜 (c • f) s :=
  ⟨hf.1.const_smul c, hf.2.const_smul c⟩
#align diff_cont_on_cl.const_smul DiffContOnCl.const_smul

theorem smul {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F]
    [IsScalarTower 𝕜 𝕜' F] {c : E → 𝕜'} {f : E → F} {s : Set E} (hc : DiffContOnCl 𝕜 c s)
    (hf : DiffContOnCl 𝕜 f s) : DiffContOnCl 𝕜 (fun x => c x • f x) s :=
  ⟨hc.1.smul hf.1, hc.2.smul hf.2⟩
#align diff_cont_on_cl.smul DiffContOnCl.smul

theorem smul_const {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
    [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F] {c : E → 𝕜'} {s : Set E} (hc : DiffContOnCl 𝕜 c s)
    (y : F) : DiffContOnCl 𝕜 (fun x => c x • y) s :=
  hc.smul diffContOnCl_const
#align diff_cont_on_cl.smul_const DiffContOnCl.smul_const

theorem inv {f : E → 𝕜} (hf : DiffContOnCl 𝕜 f s) (h₀ : ∀ x ∈ closure s, f x ≠ 0) :
    DiffContOnCl 𝕜 f⁻¹ s :=
  ⟨differentiableOn_inv.comp hf.1 fun _ hx => h₀ _ (subset_closure hx), hf.2.inv₀ h₀⟩
#align diff_cont_on_cl.inv DiffContOnCl.inv

end DiffContOnCl

theorem Differentiable.comp_diffContOnCl {g : G → E} {t : Set G} (hf : Differentiable 𝕜 f)
    (hg : DiffContOnCl 𝕜 g t) : DiffContOnCl 𝕜 (f ∘ g) t :=
  hf.diffContOnCl.comp hg (mapsTo_image _ _)
#align differentiable.comp_diff_cont_on_cl Differentiable.comp_diffContOnCl

theorem DifferentiableOn.diffContOnCl_ball {U : Set E} {c : E} {R : ℝ} (hf : DifferentiableOn 𝕜 f U)
    (hc : closedBall c R ⊆ U) : DiffContOnCl 𝕜 f (ball c R) :=
  DiffContOnCl.mk_ball (hf.mono (ball_subset_closedBall.trans hc)) (hf.continuousOn.mono hc)
#align differentiable_on.diff_cont_on_cl_ball DifferentiableOn.diffContOnCl_ball
