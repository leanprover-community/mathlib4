/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.Analysis.Normed.Group.Hom
import Mathlib.Analysis.Normed.Group.Completion

#align_import analysis.normed.group.hom_completion from "leanprover-community/mathlib"@"17ef379e997badd73e5eabb4d38f11919ab3c4b3"

/-!
# Completion of normed group homs

Given two (semi) normed groups `G` and `H` and a normed group hom `f : NormedAddGroupHom G H`,
we build and study a normed group hom
`f.completion : NormedAddGroupHom (completion G) (completion H)` such that the diagram

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

* `NormedAddGroupHom.completion`: see the discussion above.
* `NormedAddCommGroup.toCompl : NormedAddGroupHom G (completion G)`: the canonical map from
  `G` to its completion, as a normed group hom
* `NormedAddGroupHom.completion_toCompl`: the above diagram indeed commutes.
* `NormedAddGroupHom.norm_completion`: `‖f.completion‖ = ‖f‖`
* `NormedAddGroupHom.ker_le_ker_completion`: the kernel of `f.completion` contains the image of
  the kernel of `f`.
* `NormedAddGroupHom.ker_completion`: the kernel of `f.completion` is the closure of the image of
  the kernel of `f` under an assumption that `f` is quantitatively surjective onto its image.
* `NormedAddGroupHom.extension` : if `H` is complete, the extension of
  `f : NormedAddGroupHom G H` to a `NormedAddGroupHom (completion G) H`.
-/


noncomputable section

open Set NormedAddGroupHom UniformSpace

section Completion

variable {G : Type*} [SeminormedAddCommGroup G] {H : Type*} [SeminormedAddCommGroup H]
  {K : Type*} [SeminormedAddCommGroup K]

/-- The normed group hom induced between completions. -/
def NormedAddGroupHom.completion (f : NormedAddGroupHom G H) :
    NormedAddGroupHom (Completion G) (Completion H) :=
  .ofLipschitz (f.toAddMonoidHom.completion f.continuous) f.lipschitz.completion_map
#align normed_add_group_hom.completion NormedAddGroupHom.completion

theorem NormedAddGroupHom.completion_def (f : NormedAddGroupHom G H) (x : Completion G) :
    f.completion x = Completion.map f x :=
  rfl
#align normed_add_group_hom.completion_def NormedAddGroupHom.completion_def

@[simp]
theorem NormedAddGroupHom.completion_coe_to_fun (f : NormedAddGroupHom G H) :
    (f.completion : Completion G → Completion H) = Completion.map f := rfl
#align normed_add_group_hom.completion_coe_to_fun NormedAddGroupHom.completion_coe_to_fun

-- Porting note: `@[simp]` moved to the next lemma
theorem NormedAddGroupHom.completion_coe (f : NormedAddGroupHom G H) (g : G) :
    f.completion g = f g :=
  Completion.map_coe f.uniformContinuous _
#align normed_add_group_hom.completion_coe NormedAddGroupHom.completion_coe

@[simp]
theorem NormedAddGroupHom.completion_coe' (f : NormedAddGroupHom G H) (g : G) :
    Completion.map f g = f g :=
  f.completion_coe g

/-- Completion of normed group homs as a normed group hom. -/
@[simps]
def normedAddGroupHomCompletionHom :
    NormedAddGroupHom G H →+ NormedAddGroupHom (Completion G) (Completion H) where
  toFun := NormedAddGroupHom.completion
  map_zero' := toAddMonoidHom_injective AddMonoidHom.completion_zero
  map_add' f g := toAddMonoidHom_injective <|
    f.toAddMonoidHom.completion_add g.toAddMonoidHom f.continuous g.continuous
#align normed_add_group_hom_completion_hom normedAddGroupHomCompletionHom
#align normed_add_group_hom_completion_hom_apply normedAddGroupHomCompletionHom_apply

@[simp]
theorem NormedAddGroupHom.completion_id :
    (NormedAddGroupHom.id G).completion = NormedAddGroupHom.id (Completion G) := by
  ext x
  rw [NormedAddGroupHom.completion_def, NormedAddGroupHom.coe_id, Completion.map_id]
  rfl
#align normed_add_group_hom.completion_id NormedAddGroupHom.completion_id

theorem NormedAddGroupHom.completion_comp (f : NormedAddGroupHom G H) (g : NormedAddGroupHom H K) :
    g.completion.comp f.completion = (g.comp f).completion := by
  ext x
  rw [NormedAddGroupHom.coe_comp, NormedAddGroupHom.completion_def,
    NormedAddGroupHom.completion_coe_to_fun, NormedAddGroupHom.completion_coe_to_fun,
    Completion.map_comp g.uniformContinuous f.uniformContinuous]
  rfl
#align normed_add_group_hom.completion_comp NormedAddGroupHom.completion_comp

theorem NormedAddGroupHom.completion_neg (f : NormedAddGroupHom G H) :
    (-f).completion = -f.completion :=
  map_neg (normedAddGroupHomCompletionHom : NormedAddGroupHom G H →+ _) f
#align normed_add_group_hom.completion_neg NormedAddGroupHom.completion_neg

theorem NormedAddGroupHom.completion_add (f g : NormedAddGroupHom G H) :
    (f + g).completion = f.completion + g.completion :=
  normedAddGroupHomCompletionHom.map_add f g
#align normed_add_group_hom.completion_add NormedAddGroupHom.completion_add

theorem NormedAddGroupHom.completion_sub (f g : NormedAddGroupHom G H) :
    (f - g).completion = f.completion - g.completion :=
  map_sub (normedAddGroupHomCompletionHom : NormedAddGroupHom G H →+ _) f g
#align normed_add_group_hom.completion_sub NormedAddGroupHom.completion_sub

@[simp]
theorem NormedAddGroupHom.zero_completion : (0 : NormedAddGroupHom G H).completion = 0 :=
  normedAddGroupHomCompletionHom.map_zero
#align normed_add_group_hom.zero_completion NormedAddGroupHom.zero_completion

/-- The map from a normed group to its completion, as a normed group hom. -/
@[simps] -- Porting note: added `@[simps]`
def NormedAddCommGroup.toCompl : NormedAddGroupHom G (Completion G) where
  toFun := (↑)
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
    f.completion.comp toCompl = toCompl.comp f := by ext x; simp
#align normed_add_group_hom.completion_to_compl NormedAddGroupHom.completion_toCompl

@[simp]
theorem NormedAddGroupHom.norm_completion (f : NormedAddGroupHom G H) : ‖f.completion‖ = ‖f‖ :=
  le_antisymm (ofLipschitz_norm_le _ _) <| opNorm_le_bound _ (norm_nonneg _) fun x => by
    simpa using f.completion.le_opNorm x
#align normed_add_group_hom.norm_completion NormedAddGroupHom.norm_completion

theorem NormedAddGroupHom.ker_le_ker_completion (f : NormedAddGroupHom G H) :
    (toCompl.comp <| incl f.ker).range ≤ f.completion.ker := by
  rintro _ ⟨⟨g, h₀ : f g = 0⟩, rfl⟩
  simp [h₀, mem_ker, Completion.coe_zero]
#align normed_add_group_hom.ker_le_ker_completion NormedAddGroupHom.ker_le_ker_completion

theorem NormedAddGroupHom.ker_completion {f : NormedAddGroupHom G H} {C : ℝ}
    (h : f.SurjectiveOnWith f.range C) :
    (f.completion.ker : Set <| Completion G) = closure (toCompl.comp <| incl f.ker).range := by
  refine le_antisymm ?_ (closure_minimal f.ker_le_ker_completion f.completion.isClosed_ker)
  rintro hatg (hatg_in : f.completion hatg = 0)
  rw [SeminormedAddCommGroup.mem_closure_iff]
  intro ε ε_pos
  rcases h.exists_pos with ⟨C', C'_pos, hC'⟩
  rcases exists_pos_mul_lt ε_pos (1 + C' * ‖f‖) with ⟨δ, δ_pos, hδ⟩
  obtain ⟨_, ⟨g : G, rfl⟩, hg : ‖hatg - g‖ < δ⟩ :=
    SeminormedAddCommGroup.mem_closure_iff.mp (Completion.denseInducing_coe.dense hatg) δ δ_pos
  obtain ⟨g' : G, hgg' : f g' = f g, hfg : ‖g'‖ ≤ C' * ‖f g‖⟩ := hC' (f g) (mem_range_self _ g)
  have mem_ker : g - g' ∈ f.ker := by rw [f.mem_ker, map_sub, sub_eq_zero.mpr hgg'.symm]
  refine ⟨_, ⟨⟨g - g', mem_ker⟩, rfl⟩, ?_⟩
  have : ‖f g‖ ≤ ‖f‖ * δ := calc
    ‖f g‖ ≤ ‖f‖ * ‖hatg - g‖ := by simpa [hatg_in] using f.completion.le_opNorm (hatg - g)
    _ ≤ ‖f‖ * δ := by gcongr
  calc ‖hatg - ↑(g - g')‖ = ‖hatg - g + g'‖ := by rw [Completion.coe_sub, sub_add]
    _ ≤ ‖hatg - g‖ + ‖(g' : Completion G)‖ := norm_add_le _ _
    _ = ‖hatg - g‖ + ‖g'‖ := by rw [Completion.norm_coe]
    _ < δ + C' * ‖f g‖ := add_lt_add_of_lt_of_le hg hfg
    _ ≤ δ + C' * (‖f‖ * δ) := by gcongr
    _ < ε := by simpa only [add_mul, one_mul, mul_assoc] using hδ
#align normed_add_group_hom.ker_completion NormedAddGroupHom.ker_completion

end Completion

section Extension

variable {G : Type*} [SeminormedAddCommGroup G]
variable {H : Type*} [SeminormedAddCommGroup H] [T0Space H] [CompleteSpace H]

/-- If `H` is complete, the extension of `f : NormedAddGroupHom G H` to a
`NormedAddGroupHom (completion G) H`. -/
def NormedAddGroupHom.extension (f : NormedAddGroupHom G H) : NormedAddGroupHom (Completion G) H :=
  .ofLipschitz (f.toAddMonoidHom.extension f.continuous) <|
    let _ := MetricSpace.ofT0PseudoMetricSpace H
    f.lipschitz.completion_extension
#align normed_add_group_hom.extension NormedAddGroupHom.extension

theorem NormedAddGroupHom.extension_def (f : NormedAddGroupHom G H) (v : G) :
    f.extension v = Completion.extension f v :=
  rfl
#align normed_add_group_hom.extension_def NormedAddGroupHom.extension_def

@[simp]
theorem NormedAddGroupHom.extension_coe (f : NormedAddGroupHom G H) (v : G) : f.extension v = f v :=
  AddMonoidHom.extension_coe _ f.continuous _
#align normed_add_group_hom.extension_coe NormedAddGroupHom.extension_coe

theorem NormedAddGroupHom.extension_coe_to_fun (f : NormedAddGroupHom G H) :
    (f.extension : Completion G → H) = Completion.extension f :=
  rfl
#align normed_add_group_hom.extension_coe_to_fun NormedAddGroupHom.extension_coe_to_fun

theorem NormedAddGroupHom.extension_unique (f : NormedAddGroupHom G H)
    {g : NormedAddGroupHom (Completion G) H} (hg : ∀ v, f v = g v) : f.extension = g := by
  ext v
  rw [NormedAddGroupHom.extension_coe_to_fun,
    Completion.extension_unique f.uniformContinuous g.uniformContinuous fun a => hg a]
#align normed_add_group_hom.extension_unique NormedAddGroupHom.extension_unique

end Extension
