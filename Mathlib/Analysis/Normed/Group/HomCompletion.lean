/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot

! This file was ported from Lean 3 source module analysis.normed.group.hom_completion
! leanprover-community/mathlib commit 17ef379e997badd73e5eabb4d38f11919ab3c4b3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Normed.Group.Hom
import Mathbin.Analysis.Normed.Group.Completion

/-!
# Completion of normed group homs

Given two (semi) normed groups `G` and `H` and a normed group hom `f : normed_add_group_hom G H`,
we build and study a normed group hom
`f.completion  : normed_add_group_hom (completion G) (completion H)` such that the diagram

```
                   f
     G       ----------->     H

     |                        |
     |                        |
     |                        |
     V                        V

completion G -----------> completion H
            f.completion
```

commutes. The map itself comes from the general theory of completion of uniform spaces, but here
we want a normed group hom, study its operator norm and kernel.

The vertical maps in the above diagrams are also normed group homs constructed in this file.

## Main definitions and results:

* `normed_add_group_hom.completion`: see the discussion above.
* `normed_add_comm_group.to_compl : normed_add_group_hom G (completion G)`: the canonical map from
  `G` to its completion, as a normed group hom
* `normed_add_group_hom.completion_to_compl`: the above diagram indeed commutes.
* `normed_add_group_hom.norm_completion`: `‖f.completion‖ = ‖f‖`
* `normed_add_group_hom.ker_le_ker_completion`: the kernel of `f.completion` contains the image of
  the kernel of `f`.
* `normed_add_group_hom.ker_completion`: the kernel of `f.completion` is the closure of the image of
  the kernel of `f` under an assumption that `f` is quantitatively surjective onto its image.
* `normed_add_group_hom.extension` : if `H` is complete, the extension of
  `f : normed_add_group_hom G H` to a `normed_add_group_hom (completion G) H`.
-/


noncomputable section

open Set NormedAddGroupHom UniformSpace

section Completion

variable {G : Type _} [SeminormedAddCommGroup G]

variable {H : Type _} [SeminormedAddCommGroup H]

variable {K : Type _} [SeminormedAddCommGroup K]

/-- The normed group hom induced between completions. -/
def NormedAddGroupHom.completion (f : NormedAddGroupHom G H) :
    NormedAddGroupHom (Completion G) (Completion H) :=
  { f.toAddMonoidHom.Completion f.Continuous with
    bound' := by
      use ‖f‖
      intro y
      apply completion.induction_on y
      ·
        exact
          isClosed_le
            (continuous_norm.comp <| f.to_add_monoid_hom.continuous_completion f.continuous)
            (continuous_const.mul continuous_norm)
      · intro x
        change ‖f.to_add_monoid_hom.completion _ ↑x‖ ≤ ‖f‖ * ‖↑x‖
        rw [f.to_add_monoid_hom.completion_coe f.continuous]
        simp only [completion.norm_coe]
        exact f.le_op_norm x }
#align normed_add_group_hom.completion NormedAddGroupHom.completion

theorem NormedAddGroupHom.completion_def (f : NormedAddGroupHom G H) (x : Completion G) :
    f.Completion x = Completion.map f x :=
  rfl
#align normed_add_group_hom.completion_def NormedAddGroupHom.completion_def

@[simp]
theorem NormedAddGroupHom.completion_coe_to_fun (f : NormedAddGroupHom G H) :
    (f.Completion : Completion G → Completion H) = Completion.map f :=
  by
  ext x
  exact NormedAddGroupHom.completion_def f x
#align normed_add_group_hom.completion_coe_to_fun NormedAddGroupHom.completion_coe_to_fun

@[simp]
theorem NormedAddGroupHom.completion_coe (f : NormedAddGroupHom G H) (g : G) :
    f.Completion g = f g :=
  Completion.map_coe f.UniformContinuous _
#align normed_add_group_hom.completion_coe NormedAddGroupHom.completion_coe

/-- Completion of normed group homs as a normed group hom. -/
@[simps]
def normedAddGroupHomCompletionHom :
    NormedAddGroupHom G H →+ NormedAddGroupHom (Completion G) (Completion H)
    where
  toFun := NormedAddGroupHom.completion
  map_zero' := by
    apply to_add_monoid_hom_injective
    exact AddMonoidHom.completion_zero
  map_add' f g := by
    apply to_add_monoid_hom_injective
    exact f.to_add_monoid_hom.completion_add g.to_add_monoid_hom f.continuous g.continuous
#align normed_add_group_hom_completion_hom normedAddGroupHomCompletionHom

@[simp]
theorem NormedAddGroupHom.completion_id :
    (NormedAddGroupHom.id G).Completion = NormedAddGroupHom.id (Completion G) :=
  by
  ext x
  rw [NormedAddGroupHom.completion_def, NormedAddGroupHom.coe_id, completion.map_id]
  rfl
#align normed_add_group_hom.completion_id NormedAddGroupHom.completion_id

theorem NormedAddGroupHom.completion_comp (f : NormedAddGroupHom G H) (g : NormedAddGroupHom H K) :
    g.Completion.comp f.Completion = (g.comp f).Completion :=
  by
  ext x
  rw [NormedAddGroupHom.coe_comp, NormedAddGroupHom.completion_def,
    NormedAddGroupHom.completion_coe_to_fun, NormedAddGroupHom.completion_coe_to_fun,
    completion.map_comp (NormedAddGroupHom.uniformContinuous _)
      (NormedAddGroupHom.uniformContinuous _)]
  rfl
#align normed_add_group_hom.completion_comp NormedAddGroupHom.completion_comp

theorem NormedAddGroupHom.completion_neg (f : NormedAddGroupHom G H) :
    (-f).Completion = -f.Completion :=
  map_neg (normedAddGroupHomCompletionHom : NormedAddGroupHom G H →+ _) f
#align normed_add_group_hom.completion_neg NormedAddGroupHom.completion_neg

theorem NormedAddGroupHom.completion_add (f g : NormedAddGroupHom G H) :
    (f + g).Completion = f.Completion + g.Completion :=
  normedAddGroupHomCompletionHom.map_add f g
#align normed_add_group_hom.completion_add NormedAddGroupHom.completion_add

theorem NormedAddGroupHom.completion_sub (f g : NormedAddGroupHom G H) :
    (f - g).Completion = f.Completion - g.Completion :=
  map_sub (normedAddGroupHomCompletionHom : NormedAddGroupHom G H →+ _) f g
#align normed_add_group_hom.completion_sub NormedAddGroupHom.completion_sub

@[simp]
theorem NormedAddGroupHom.zero_completion : (0 : NormedAddGroupHom G H).Completion = 0 :=
  normedAddGroupHomCompletionHom.map_zero
#align normed_add_group_hom.zero_completion NormedAddGroupHom.zero_completion

/-- The map from a normed group to its completion, as a normed group hom. -/
def NormedAddCommGroup.toCompl : NormedAddGroupHom G (Completion G)
    where
  toFun := coe
  map_add' := Completion.toCompl.map_add
  bound' := ⟨1, by simp [le_refl]⟩
#align normed_add_comm_group.to_compl NormedAddCommGroup.toCompl

open NormedAddCommGroup

theorem NormedAddCommGroup.norm_toCompl (x : G) : ‖toCompl x‖ = ‖x‖ :=
  Completion.norm_coe x
#align normed_add_comm_group.norm_to_compl NormedAddCommGroup.norm_toCompl

theorem NormedAddCommGroup.denseRange_toCompl : DenseRange (toCompl : G → Completion G) :=
  Completion.denseInducing_coe.dense
#align normed_add_comm_group.dense_range_to_compl NormedAddCommGroup.denseRange_toCompl

@[simp]
theorem NormedAddGroupHom.completion_toCompl (f : NormedAddGroupHom G H) :
    f.Completion.comp toCompl = toCompl.comp f :=
  by
  ext x
  change f.completion x = _
  simpa
#align normed_add_group_hom.completion_to_compl NormedAddGroupHom.completion_toCompl

@[simp]
theorem NormedAddGroupHom.norm_completion (f : NormedAddGroupHom G H) : ‖f.Completion‖ = ‖f‖ :=
  by
  apply f.completion.op_norm_eq_of_bounds (norm_nonneg _)
  · intro x
    apply completion.induction_on x
    · apply isClosed_le
      continuity
    · intro g
      simp [f.le_op_norm g]
  · intro N N_nonneg hN
    apply f.op_norm_le_bound N_nonneg
    intro x
    simpa using hN x
#align normed_add_group_hom.norm_completion NormedAddGroupHom.norm_completion

theorem NormedAddGroupHom.ker_le_ker_completion (f : NormedAddGroupHom G H) :
    (toCompl.comp <| incl f.ker).range ≤ f.Completion.ker :=
  by
  intro a h
  replace h : ∃ y : f.ker, to_compl (y : G) = a; · simpa using h
  rcases h with ⟨⟨g, g_in : g ∈ f.ker⟩, rfl⟩
  rw [f.mem_ker] at g_in
  change f.completion (g : completion G) = 0
  simp [NormedAddGroupHom.mem_ker, f.completion_coe g, g_in, completion.coe_zero]
#align normed_add_group_hom.ker_le_ker_completion NormedAddGroupHom.ker_le_ker_completion

theorem NormedAddGroupHom.ker_completion {f : NormedAddGroupHom G H} {C : ℝ}
    (h : f.SurjectiveOnWith f.range C) :
    (f.Completion.ker : Set <| Completion G) = closure (toCompl.comp <| incl f.ker).range :=
  by
  rcases h.exists_pos with ⟨C', C'_pos, hC'⟩
  apply le_antisymm
  · intro hatg hatg_in
    rw [SeminormedAddCommGroup.mem_closure_iff]
    intro ε ε_pos
    have hCf : 0 ≤ C' * ‖f‖ := (zero_le_mul_left C'_pos).mpr (norm_nonneg f)
    have ineq : 0 < 1 + C' * ‖f‖ := by linarith
    set δ := ε / (1 + C' * ‖f‖)
    have δ_pos : δ > 0 := div_pos ε_pos ineq
    obtain ⟨_, ⟨g : G, rfl⟩, hg : ‖hatg - g‖ < δ⟩ :=
      seminormed_add_comm_group.mem_closure_iff.mp (completion.dense_inducing_coe.dense hatg) δ
        δ_pos
    obtain ⟨g' : G, hgg' : f g' = f g, hfg : ‖g'‖ ≤ C' * ‖f g‖⟩ := hC' (f g) (mem_range_self g)
    have mem_ker : g - g' ∈ f.ker := by rw [f.mem_ker, map_sub, sub_eq_zero.mpr hgg'.symm]
    have : ‖f g‖ ≤ ‖f‖ * ‖hatg - g‖
    calc
      ‖f g‖ = ‖f.completion g‖ := by rw [f.completion_coe, completion.norm_coe]
      _ = ‖f.completion g - 0‖ := by rw [sub_zero _]
      _ = ‖f.completion g - f.completion hatg‖ := by rw [(f.completion.mem_ker _).mp hatg_in]
      _ = ‖f.completion (g - hatg)‖ := by rw [map_sub]
      _ ≤ ‖f.completion‖ * ‖(g : completion G) - hatg‖ := (f.completion.le_op_norm _)
      _ = ‖f‖ * ‖hatg - g‖ := by rw [norm_sub_rev, f.norm_completion]
      
    have : ‖(g' : completion G)‖ ≤ C' * ‖f‖ * ‖hatg - g‖
    calc
      ‖(g' : completion G)‖ = ‖g'‖ := completion.norm_coe _
      _ ≤ C' * ‖f g‖ := hfg
      _ ≤ C' * ‖f‖ * ‖hatg - g‖ := by
        rw [mul_assoc]
        exact (mul_le_mul_left C'_pos).mpr this
      
    refine' ⟨g - g', _, _⟩
    · norm_cast
      rw [NormedAddGroupHom.comp_range]
      apply AddSubgroup.mem_map_of_mem
      simp only [incl_range, mem_ker]
    ·
      calc
        ‖hatg - (g - g')‖ = ‖hatg - g + g'‖ := by abel
        _ ≤ ‖hatg - g‖ + ‖(g' : completion G)‖ := (norm_add_le _ _)
        _ < δ + C' * ‖f‖ * ‖hatg - g‖ := by linarith
        _ ≤ δ + C' * ‖f‖ * δ := (add_le_add_left (mul_le_mul_of_nonneg_left hg.le hCf) δ)
        _ = (1 + C' * ‖f‖) * δ := by ring
        _ = ε := mul_div_cancel' _ ineq.ne.symm
        
  · rw [← f.completion.is_closed_ker.closure_eq]
    exact closure_mono f.ker_le_ker_completion
#align normed_add_group_hom.ker_completion NormedAddGroupHom.ker_completion

end Completion

section Extension

variable {G : Type _} [SeminormedAddCommGroup G]

variable {H : Type _} [SeminormedAddCommGroup H] [SeparatedSpace H] [CompleteSpace H]

/-- If `H` is complete, the extension of `f : normed_add_group_hom G H` to a
`normed_add_group_hom (completion G) H`. -/
def NormedAddGroupHom.extension (f : NormedAddGroupHom G H) : NormedAddGroupHom (Completion G) H :=
  { f.toAddMonoidHom.extension f.Continuous with
    bound' :=
      by
      refine' ⟨‖f‖, fun v => completion.induction_on v (isClosed_le _ _) fun a => _⟩
      · exact Continuous.comp continuous_norm completion.continuous_extension
      · exact Continuous.mul continuous_const continuous_norm
      · rw [completion.norm_coe, AddMonoidHom.toFun_eq_coe, AddMonoidHom.extension_coe]
        exact le_op_norm f a }
#align normed_add_group_hom.extension NormedAddGroupHom.extension

theorem NormedAddGroupHom.extension_def (f : NormedAddGroupHom G H) (v : G) :
    f.extension v = Completion.extension f v :=
  rfl
#align normed_add_group_hom.extension_def NormedAddGroupHom.extension_def

@[simp]
theorem NormedAddGroupHom.extension_coe (f : NormedAddGroupHom G H) (v : G) : f.extension v = f v :=
  AddMonoidHom.extension_coe _ f.Continuous _
#align normed_add_group_hom.extension_coe NormedAddGroupHom.extension_coe

theorem NormedAddGroupHom.extension_coe_to_fun (f : NormedAddGroupHom G H) :
    (f.extension : Completion G → H) = Completion.extension f :=
  rfl
#align normed_add_group_hom.extension_coe_to_fun NormedAddGroupHom.extension_coe_to_fun

theorem NormedAddGroupHom.extension_unique (f : NormedAddGroupHom G H)
    {g : NormedAddGroupHom (Completion G) H} (hg : ∀ v, f v = g v) : f.extension = g :=
  by
  ext v
  rw [NormedAddGroupHom.extension_coe_to_fun,
    completion.extension_unique f.uniform_continuous g.uniform_continuous fun a => hg a]
#align normed_add_group_hom.extension_unique NormedAddGroupHom.extension_unique

end Extension

