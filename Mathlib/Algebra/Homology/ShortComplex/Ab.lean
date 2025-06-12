/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.Kernels
import Mathlib.Algebra.Exact

/-!
# Homology and exactness of short complexes of abelian groups

In this file, the homology of a short complex `S` of abelian groups is identified
with the quotient of `AddMonoidHom.ker S.g` by the image of the morphism
`S.abToCycles : S.X₁ →+ AddMonoidHom.ker S.g` induced by `S.f`.

The definitions are made in the `ShortComplex` namespace so as to enable dot notation.
The names contain the prefix `ab` in order to allow similar constructions for
other categories like `ModuleCat`.

## Main definitions
- `ShortComplex.abHomologyIso` identifies the homology of a short complex of abelian
groups to an explicit quotient.
- `ShortComplex.ab_exact_iff` expresses that a short complex of abelian groups `S`
is exact iff any element in the kernel of `S.g` belongs to the image of `S.f`.

-/

universe u

namespace CategoryTheory

namespace ShortComplex

variable (S : ShortComplex Ab.{u})

@[simp]
lemma ab_zero_apply (x : S.X₁) : S.g (S.f x) = 0 := by
  rw [← ConcreteCategory.comp_apply, S.zero]
  rfl

/-- The canonical additive morphism `S.X₁ →+ AddMonoidHom.ker S.g` induced by `S.f`. -/
@[simps!]
def abToCycles : S.X₁ →+ AddMonoidHom.ker S.g.hom :=
    AddMonoidHom.mk' (fun x => ⟨S.f x, S.ab_zero_apply x⟩) (by aesop)

/-- The explicit left homology data of a short complex of abelian group that is
given by a kernel and a quotient given by the `AddMonoidHom` API. -/
@[simps]
def abLeftHomologyData : S.LeftHomologyData where
  K := AddCommGrp.of (AddMonoidHom.ker S.g.hom)
  H := AddCommGrp.of ((AddMonoidHom.ker S.g.hom) ⧸ AddMonoidHom.range S.abToCycles)
  i := AddCommGrp.ofHom <| (AddMonoidHom.ker S.g.hom).subtype
  π := AddCommGrp.ofHom <| QuotientAddGroup.mk' _
  wi := by
    ext ⟨_, hx⟩
    exact hx
  hi := AddCommGrp.kernelIsLimit _
  wπ := by
    ext (x : S.X₁)
    dsimp
    rw [QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_range]
    apply exists_apply_eq_apply
  hπ := AddCommGrp.cokernelIsColimit (AddCommGrp.ofHom S.abToCycles)

@[simp]
lemma abLeftHomologyData_f' : S.abLeftHomologyData.f' = AddCommGrp.ofHom S.abToCycles := rfl

/-- Given a short complex `S` of abelian groups, this is the isomorphism between
the abstract `S.cycles` of the homology API and the more concrete description as
`AddMonoidHom.ker S.g`. -/
noncomputable def abCyclesIso : S.cycles ≅ AddCommGrp.of (AddMonoidHom.ker S.g.hom) :=
  S.abLeftHomologyData.cyclesIso

-- This was a simp lemma until we made `AddCommGrp.coe_of` a simp lemma,
-- after which the simp normal form linter complains.
-- It was not used a simp lemma in Mathlib.
-- Possible solution: higher priority function coercions that remove the `of`?
-- @[simp]
lemma abCyclesIso_inv_apply_iCycles (x : AddMonoidHom.ker S.g.hom) :
    S.iCycles (S.abCyclesIso.inv x) = x := by
  dsimp only [abCyclesIso]
  rw [← ConcreteCategory.comp_apply, S.abLeftHomologyData.cyclesIso_inv_comp_iCycles]
  rfl

/-- Given a short complex `S` of abelian groups, this is the isomorphism between
the abstract `S.homology` of the homology API and the more explicit
quotient of `AddMonoidHom.ker S.g` by the image of
`S.abToCycles : S.X₁ →+ AddMonoidHom.ker S.g`. -/
noncomputable def abHomologyIso : S.homology ≅
    AddCommGrp.of ((AddMonoidHom.ker S.g.hom) ⧸ AddMonoidHom.range S.abToCycles) :=
  S.abLeftHomologyData.homologyIso

lemma exact_iff_surjective_abToCycles :
    S.Exact ↔ Function.Surjective S.abToCycles := by
  rw [S.abLeftHomologyData.exact_iff_epi_f', abLeftHomologyData_f',
    AddCommGrp.epi_iff_surjective]
  rfl

lemma ab_exact_iff :
    S.Exact ↔ ∀ (x₂ : S.X₂) (_ : S.g x₂ = 0), ∃ (x₁ : S.X₁), S.f x₁ = x₂ := by
  rw [exact_iff_surjective_abToCycles]
  constructor
  · intro h x₂ hx₂
    obtain ⟨x₁, hx₁⟩ := h ⟨x₂, hx₂⟩
    exact ⟨x₁, by simpa only [Subtype.ext_iff, abToCycles_apply_coe] using hx₁⟩
  · rintro h ⟨x₂, hx₂⟩
    obtain ⟨x₁, rfl⟩ := h x₂ hx₂
    exact ⟨x₁, rfl⟩

lemma ab_exact_iff_function_exact :
    S.Exact ↔ Function.Exact S.f S.g := by
  rw [S.ab_exact_iff]
  apply forall_congr'
  intro x₂
  constructor
  · intro h
    refine ⟨h, ?_⟩
    rintro ⟨x₁, rfl⟩
    simp only [ab_zero_apply]
  · tauto

lemma ab_exact_iff_ker_le_range : S.Exact ↔ S.g.hom.ker ≤ S.f.hom.range := S.ab_exact_iff

lemma ab_exact_iff_range_eq_ker : S.Exact ↔ S.f.hom.range = S.g.hom.ker := by
  rw [ab_exact_iff_ker_le_range]
  constructor
  · intro h
    refine le_antisymm ?_ h
    rintro _ ⟨x₁, rfl⟩
    rw [AddMonoidHom.mem_ker, ← ConcreteCategory.comp_apply, S.zero]
    rfl
  · intro h
    rw [h]

variable {S}

lemma ShortExact.ab_injective_f (hS : S.ShortExact) :
    Function.Injective S.f :=
  (AddCommGrp.mono_iff_injective _).1 hS.mono_f

lemma ShortExact.ab_surjective_g (hS : S.ShortExact) :
    Function.Surjective S.g :=
  (AddCommGrp.epi_iff_surjective _).1 hS.epi_g

variable (S)

lemma ShortExact.ab_exact_iff_function_exact :
    S.Exact ↔ Function.Exact S.f S.g := by
  rw [ab_exact_iff_range_eq_ker, AddMonoidHom.exact_iff]
  tauto

end ShortComplex

end CategoryTheory
