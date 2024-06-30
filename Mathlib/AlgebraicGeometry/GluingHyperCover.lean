/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Joël Riou, Ravi Vakil
-/
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.CategoryTheory.Sites.OneHypercover
import Mathlib.AlgebraicGeometry.Sites.BigZariski

/-!
# Gluing Hypercovers

In this file ...

-/
universe v u

open CategoryTheory Opposite Limits

namespace CategoryTheory

-- this should be moved to CategoryTheory.Limits.Shapes.Types
namespace Limits

variable (I : MulticospanIndex (Type u))

/-- TODO -/
@[ext]
structure MulticospanIndex.sections where
  val (i : I.L) : I.left i
  property (r : I.R) : I.fst r (val _) = I.snd r (val _)

/-- TODO -/
@[simps]
def MulticospanIndex.sectionsEquiv :
    I.sections ≃ I.multicospan.sections where
  toFun s :=
    { val := fun i ↦ match i with
        | .left i => s.val i
        | .right j => I.fst j (s.val _)
      property := by
        rintro _ _ (_|_|r)
        · rfl
        · rfl
        · exact (s.property r).symm }
  invFun s :=
    { val := fun i ↦ s.val (.left i)
      property := fun r ↦ (s.property (.fst r)).trans (s.property (.snd r)).symm }
  left_inv _ := rfl
  right_inv s := by
    ext (_|r)
    · rfl
    · exact s.property (.fst r)

namespace Multifork

variable {I}
variable (c : Multifork I)

/-- TODO -/
@[simps]
def toSections (x : c.pt) : I.sections where
  val i := c.ι i x
  property r := congr_fun (c.condition r) x

lemma toSections_fac : I.sectionsEquiv.symm ∘ Types.sectionOfCone c = c.toSections := rfl

lemma isLimit_types_iff : Nonempty (IsLimit c) ↔ Function.Bijective c.toSections := by
  rw [Types.isLimit_iff_bijective_sectionOfCone, ← toSections_fac, EquivLike.comp_bijective]

namespace IsLimit

variable {c}
variable (hc : IsLimit c)

/-- TODO -/
noncomputable def sectionsEquiv : I.sections ≃ c.pt :=
  (Equiv.ofBijective _ (c.isLimit_types_iff.1 ⟨hc⟩)).symm

@[simp]
lemma sectionsEquiv_symm_apply_val (x : c.pt) (i : I.L) :
    ((sectionsEquiv hc).symm x).val i = c.ι i x := rfl

@[simp]
lemma sectionsEquiv_apply_val (s : I.sections) (i : I.L) :
    c.ι i (sectionsEquiv hc s) = s.val i := by
  obtain ⟨x, rfl⟩ := (sectionsEquiv hc).symm.surjective s
  simp

end IsLimit

end Multifork

end Limits

end CategoryTheory

namespace AlgebraicGeometry.Scheme.GlueData

variable (D : Scheme.GlueData.{u})

/-- TODO -/
@[simps]
noncomputable def oneHypercover : Scheme.zariskiTopology.OneHypercover D.glued where
  I₀ := D.J
  X := D.U
  f := D.ι
  I₁ _ _ := PUnit
  Y i₁ i₂ _ := D.V (i₁, i₂)
  p₁ i₁ i₂ _ := D.f i₁ i₂
  p₂ i₁ i₂ j := D.t i₁ i₂ ≫ D.f i₂ i₁
  w i₁ i₂ _ := by simp only [Category.assoc, Scheme.GlueData.glue_condition]
  mem₀ := by
    refine zariskiTopology.superset_covering ?_ (zariskiTopology_openCover D.openCover)
    rw [Sieve.sets_iff_generate] -- the name of this lemma should be changed!
    rintro W _ ⟨i⟩
    exact ⟨_, 𝟙 _, _, ⟨i⟩, by simp; rfl⟩
  mem₁ i₁ i₂ W p₁ p₂ fac := by
    dsimp at p₁ p₂ fac ⊢
    refine zariskiTopology.superset_covering ?_ (zariskiTopology.top_mem _)
    intro T g _
    dsimp
    have ⟨φ, h₁, h₂⟩ := PullbackCone.IsLimit.lift' (D.vPullbackConeIsLimit i₁ i₂)
      (g ≫ p₁) (g ≫ p₂) (by simpa using g ≫= fac)
    exact ⟨⟨⟩, φ, h₁.symm, h₂.symm⟩

variable {F : Sheaf Scheme.zariskiTopology (Type v)}

section

variable (s : ∀ (j : D.J), F.val.obj (op (D.U j)))
  (h : ∀ (i j : D.J), F.val.map (D.f i j).op (s i) =
    F.val.map ((D.f j i).op ≫ (D.t i j).op) (s j))

/-- TODO -/
noncomputable def sheafValGluedMk : F.val.obj (op D.glued) :=
  Multifork.IsLimit.sectionsEquiv (D.oneHypercover.isLimitMultifork F)
    { val := s
      property := fun _ ↦ h _ _ }

@[simp]
lemma sheafValGluedMk_val (j : D.J) : F.val.map (D.ι j).op (D.sheafValGluedMk s h) = s j :=
  Multifork.IsLimit.sectionsEquiv_apply_val (D.oneHypercover.isLimitMultifork F) _ _

end


end AlgebraicGeometry.Scheme.GlueData
