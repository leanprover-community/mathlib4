/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# Multiequalizers in Type

Given `J : MulticospanShape` and `I : MulticospanIndex J (Type u)`,
we define a type `I.sections`. When `c : Multifork I`, we show
that `c` is a limit iff the canonical map
`c.toSections : c.pt → I.sections` is a bijection.

-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace CategoryTheory.Limits

variable {J : MulticospanShape} (I : MulticospanIndex J (Type u))

/-- Given `I : MulticospanIndex J (Type u)`, this is a type which identifies
to the sections of the functor `I.multicospan`. -/
@[ext]
structure MulticospanIndex.sections where
  /-- The data of an element in `I.left i` for each `i : J.L`. -/
  val (i : J.L) : I.left i
  property (r : J.R) : I.fst r (val _) = I.snd r (val _)

/-- The bijection `I.sections ≃ I.multicospan.sections` when `I : MulticospanIndex (Type u)`
is a multiequalizer diagram in the category of types. -/
@[simps]
def MulticospanIndex.sectionsEquiv :
    I.sections ≃ I.multicospan.sections where
  toFun s :=
    { val := fun i ↦ match i with
        | .left i => s.val i
        | .right j => I.fst j (s.val _)
      property := by
        rintro _ _ (_ | _ | r)
        · rfl
        · rfl
        · exact (s.property r).symm }
  invFun s :=
    { val := fun i ↦ s.val (.left i)
      property := fun r ↦ (s.property (.fst r)).trans (s.property (.snd r)).symm }
  right_inv s := by
    ext (_ | r)
    · rfl
    · exact s.property (.fst r)

namespace Multifork

variable {I}
variable (c : Multifork I)

/-- Given a multiequalizer diagram `I : MulticospanIndex (Type u)` in the category of
types and `c` a multifork for `I`, this is the canonical map `c.pt → I.sections`. -/
@[simps]
def toSections (x : c.pt) : I.sections where
  val i := c.ι i x
  property r := congr_fun (c.condition r) x

lemma toSections_fac : I.sectionsEquiv.symm ∘ Types.sectionOfCone c = c.toSections := rfl

/-- A multifork `c : Multifork I` in the category of types is limit iff the
map `c.toSections : c.pt → I.sections` is a bijection. -/
lemma isLimit_types_iff : Nonempty (IsLimit c) ↔ Function.Bijective c.toSections := by
  rw [Types.isLimit_iff_bijective_sectionOfCone, ← toSections_fac, EquivLike.comp_bijective]

namespace IsLimit

variable {c} (hc : IsLimit c)

/-- The bijection `I.sections ≃ c.pt` when `c : Multifork I` is a limit multifork
in the category of types. -/
noncomputable def sectionsEquiv : I.sections ≃ c.pt :=
  (Equiv.ofBijective _ (c.isLimit_types_iff.1 ⟨hc⟩)).symm

@[simp]
lemma sectionsEquiv_symm_apply_val (x : c.pt) (i : J.L) :
    ((sectionsEquiv hc).symm x).val i = c.ι i x := rfl

@[simp]
lemma sectionsEquiv_apply_val (s : I.sections) (i : J.L) :
    c.ι i (sectionsEquiv hc s) = s.val i := by
  obtain ⟨x, rfl⟩ := (sectionsEquiv hc).symm.surjective s
  simp

end IsLimit

end Multifork

end CategoryTheory.Limits
