import Mathlib.Geometry.Euclidean.Inversion

/-!
-/

noncomputable section

open Metric Set EuclideanGeometry AffineSubspace Submodule EuclideanGeometry

variable {V P : Type _} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P]

/-!
### Definition
-/

namespace Equiv

/-- Stereographic projection as a bijective self-map of the ambient space. -/
def stereoProj' (c : P) (R : ℝˣ) (v : sphere c R) : P ≃ V :=
  ((inversion_involutive (v : P) (mul_ne_zero two_ne_zero R.ne_zero)).toPerm _).trans <|
    (vaddConst (pointReflection c v)).symm

theorem stereoProj'_coe (c : P) (R : ℝˣ) (v : sphere c R) :
    stereoProj' c R v = (inversion v.1 (2 * R) · -ᵥ (pointReflection c v)) := rfl

theorem stereoProj'_apply (c : P) (R : ℝˣ) (v : sphere c R) (x : P) :
    stereoProj' c R v x = inversion v.1 (2 * R) x -ᵥ (pointReflection c v) := rfl

theorem stereoProj'_symm_apply (c : P) (R : ℝˣ) (v : sphere c R) (x : V) :
    (stereoProj' c R v).symm x = inversion v.1 (2 * R) (x +ᵥ pointReflection c v) := rfl

theorem stereoProj'_self (c : P) (R : ℝˣ) (v : sphere c R) :
    stereoProj' c R v v = (2 : ℝ) • (v.1 -ᵥ c) := by
  simp [stereoProj'_apply, nsmul_eq_smul_cast ℝ]

theorem stereoProj'_continuousOn (c : P) (R : ℝˣ) (v : sphere c R) :
    ContinuousOn (stereoProj' c R v) ({v.1}ᶜ) :=
  (continuousOn_const.inversion continuousOn_const continuousOn_id <| fun _ ↦ id).vsub
    continuousOn_const

theorem stereoProj'_symm_continuousOn (c : P) (R : ℝˣ) (v : sphere c R) :
    ContinuousOn (stereoProj' c R v).symm ({(2 : ℝ) • (v.1 -ᵥ c)}ᶜ) :=
  continuousOn_const.inversion continuousOn_const (continuousOn_id.vadd continuousOn_const) <|
    fun x ↦ mt fun (hx : x +ᵥ (pointReflection c v) = v.1) ↦ by
      rw [mem_singleton_iff, ← vadd_vsub x (pointReflection c v), hx, right_vsub_pointReflection]
      simp [nsmul_eq_smul_cast ℝ]

@[simp] theorem stereoProj'_pointReflection (c : P) (R : ℝˣ) (v : sphere c R) :
    stereoProj' c R v (pointReflection c v) = 0 :=
  vsub_eq_zero_iff_eq.2 <| inversion_of_mem_sphere <| by
    simp [mem_sphere'.1 v.2, dist_pointReflection_right (𝕜 := ℝ) c v]

@[simp] theorem stereoProj'_symm_zero (c : P) (R : ℝˣ) (v : sphere c R) :
    (stereoProj' c R v).symm 0 = pointReflection c v :=
  (symm_apply_eq _).2 (stereoProj'_pointReflection _ _ _).symm

variable {c x y : P} {R : ℝˣ} {v : sphere c R}

theorem stereoProj'_mem_orthogonal :
    stereoProj' c R v x ∈ (ℝ ∙ (v.1 -ᵥ c))ᗮ ↔ x ∈ sphere c R \ {v.1} :=
  calc
    stereoProj' c R v x ∈ (ℝ ∙ (v.1 -ᵥ c))ᗮ
      ↔ inversion v.1 (2 * R) x ∈ perpBisector v.1 (pointReflection (pointReflection c v) v) := by
      rw [stereoProj'_apply, mem_orthogonal_singleton_iff_inner_left,
        mem_perpBisector_pointReflection_iff_inner_eq_zero,
        right_vsub_pointReflection, nsmul_eq_smul_cast ℝ, inner_smul_right]
      simp
    _ ↔ inversion v.1 (2 * R) x ∈ perpBisector v.1 (inversion v.1 (2 * R) c) := by
      have : (2 ^ 2 : ℝ) = 1 + 1 + 1 + 1 := by norm_num
      convert Iff.rfl using 3
      rw [inversion_mul, inversion_of_mem_sphere (mem_sphere'.1 v.2)]
      simp only [AffineMap.homothety_apply, pointReflection_apply, this, add_smul, one_smul,
        ← vadd_vsub_assoc, ← add_assoc, vsub_vadd, ← add_vadd]
    _ ↔ x ∈ sphere c R \ {v.1} := by
      rw [inversion_mem_perpBisector_inversion_iff' (mul_ne_zero two_ne_zero R.ne_zero)
        (ne_of_mem_sphere v.2 R.ne_zero).symm, mem_sphere'.1 v.2]; rfl

theorem image_stereoProj'_sphere_diff_singleton :
    stereoProj' c R v '' (sphere c R \ {v.1}) = (ℝ ∙ (v.1 -ᵥ c))ᗮ := by
  rw [Equiv.image_eq_preimage]
  ext x
  rw [mem_preimage, ← stereoProj'_mem_orthogonal, apply_symm_apply, SetLike.mem_coe]

/-- Stereographic projection as an equivalence between a punctured sphere and a hyperplane. -/
def stereoProj (c : P) (R : ℝˣ) (v : sphere c R) :
    (sphere c R \ {v.1} : Set P) ≃ (ℝ ∙ (v.1 -ᵥ c))ᗮ :=
  ((stereoProj' c R v).image _).trans <| setCongr image_stereoProj'_sphere_diff_singleton

end Equiv

/-- Stereographic projection as a homeomorphism between a punctured sphere and a hyperplane. -/
def Homeomorph.stereoProj (c : P) (R : ℝˣ) (v : sphere c R) :
    (sphere c R \ {v.1} : Set P) ≃ₜ (ℝ ∙ (v.1 -ᵥ c))ᗮ where
  toEquiv := .stereoProj c R v
  continuous_toFun := .subtype_mk ((Equiv.stereoProj'_continuousOn c R v).comp_continuous
    continuous_subtype_val fun x ↦ x.2.2) _
  continuous_invFun := .subtype_mk ((Equiv.stereoProj'_symm_continuousOn c R v).comp_continuous
    continuous_subtype_val <| by
      rintro ⟨x, hx₀⟩ (rfl : x = (2 : ℝ) • (v.1 -ᵥ c))
      simp [mem_orthogonal_singleton_iff_inner_left, real_inner_smul_left,
        ne_of_mem_sphere v.2 R.ne_zero] at hx₀) _

/-- `Equiv.stereoProj'` as a local homeomorphism. -/
def LocalHomeomorph.stereoProj' (c : P) (R : ℝˣ) (v : sphere c R) : LocalHomeomorph P V where
  toFun := Equiv.stereoProj' c R v
  invFun := (Equiv.stereoProj' c R v).symm
  source := {v.1}ᶜ
  target := {(2 : ℝ) • (v.1 -ᵥ c)}ᶜ
  map_source' _ := mt <| ((Equiv.stereoProj' c R v).injective.eq_iff' <|
    Equiv.stereoProj'_self _ _ _).1
  map_target' _ := mt <| ((Equiv.stereoProj' c R v).symm.injective.eq_iff' <|
    (Equiv.symm_apply_eq _).mpr (Equiv.stereoProj'_self _ _ _).symm).1
  left_inv' _ _ := Equiv.symm_apply_apply _ _
  right_inv' _ _ := Equiv.apply_symm_apply _ _
  open_source := isOpen_compl_singleton
  open_target := isOpen_compl_singleton
  continuous_toFun := Equiv.stereoProj'_continuousOn _ _ _
  continuous_invFun := Equiv.stereoProj'_symm_continuousOn _ _ _

open scoped Classical

open TopologicalSpace in
def LocalHomeomorph.stereoProj (c : P) (R : ℝˣ) (v : sphere c R) :
    LocalHomeomorph (sphere c R) (ℝ ∙ (v.1 -ᵥ c))ᗮ :=
  .transHomeomorph
    (.symm <|
      haveI : Nonempty (sphere c R \ {v.1} : Set P) := (Equiv.stereoProj c R v).nonempty
      OpenEmbedding.toLocalHomeomorph (inclusion <| diff_subset _ _) ⟨embedding_inclusion _, by
        simp only [range_inclusion, mem_diff, Subtype.coe_prop, true_and, mem_singleton_iff,
          Subtype.val_inj]; exact isOpen_compl_singleton⟩)
    <| .stereoProj c R v
