/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.GroupCat.Abelian

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
  erw [← comp_apply, S.zero]
  rfl

/-- The canonical additive morphism `S.X₁ →+ AddMonoidHom.ker S.g` induced by `S.f`. -/
@[simps!]
def abToCycles : S.X₁ →+ AddMonoidHom.ker S.g :=
    AddMonoidHom.mk' (fun x => ⟨S.f x, S.ab_zero_apply x⟩) (by aesop)

/-- The explicit left homology data of a short complex of abelian group that is
given by a kernel and a quotient given by the `AddMonoidHom` API. -/
@[simps]
def abLeftHomologyData : S.LeftHomologyData where
  K := AddCommGroupCat.of (AddMonoidHom.ker S.g)
  H := AddCommGroupCat.of ((AddMonoidHom.ker S.g) ⧸ AddMonoidHom.range S.abToCycles)
  i := (AddMonoidHom.ker S.g).subtype
  π := QuotientAddGroup.mk' _
  wi := by
    ext ⟨_, hx⟩
    exact hx
  hi := AddCommGroupCat.kernelIsLimit _
  wπ := by
    ext (x : S.X₁)
    erw [QuotientAddGroup.eq_zero_iff]
    rw [AddMonoidHom.mem_range]
    apply exists_apply_eq_apply
  hπ := AddCommGroupCat.cokernelIsColimit (AddCommGroupCat.ofHom S.abToCycles)

@[simp]
lemma abLeftHomologyData_f' : S.abLeftHomologyData.f' = S.abToCycles := rfl

/-- Given a short complex `S` of abelian groups, this is the isomorphism between
the abstract `S.cycles` of the homology API and the more concrete description as
`AddMonoidHom.ker S.g`. -/
noncomputable def abCyclesIso : S.cycles ≅ AddCommGroupCat.of (AddMonoidHom.ker S.g) :=
  S.abLeftHomologyData.cyclesIso

@[simp]
lemma abCyclesIso_inv_apply_iCycles (x : AddMonoidHom.ker S.g) :
    S.iCycles (S.abCyclesIso.inv x) = x := by
  dsimp only [abCyclesIso]
  erw [← comp_apply, S.abLeftHomologyData.cyclesIso_inv_comp_iCycles]
  rfl

/-- Given a short complex `S` of abelian groups, this is the isomorphism between
the abstract `S.homology` of the homology API and the more explicit
quotient of `AddMonoidHom.ker S.g` by the image of
`S.abToCycles : S.X₁ →+ AddMonoidHom.ker S.g`. -/
noncomputable def abHomologyIso : S.homology ≅
    AddCommGroupCat.of ((AddMonoidHom.ker S.g) ⧸ AddMonoidHom.range S.abToCycles) :=
  S.abLeftHomologyData.homologyIso

lemma exact_iff_surjective_abToCycles :
    S.Exact ↔ Function.Surjective S.abToCycles := by
  rw [S.abLeftHomologyData.exact_iff_epi_f', abLeftHomologyData_f',
    AddCommGroupCat.epi_iff_surjective]
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

lemma ab_exact_iff_ker_le_range : S.Exact ↔ S.g.ker ≤ S.f.range := S.ab_exact_iff

lemma ab_exact_iff_range_eq_ker : S.Exact ↔ S.f.range = S.g.ker := by
  rw [ab_exact_iff_ker_le_range]
  constructor
  · intro h
    refine' le_antisymm _ h
    rintro _ ⟨x₁, rfl⟩
    erw [AddMonoidHom.mem_ker, ← comp_apply, S.zero]
    rfl
  · intro h
    rw [h]

lemma ShortExact.ab_injective_f (hS : S.ShortExact) :
    Function.Injective S.f :=
  (AddCommGroupCat.mono_iff_injective _).1 hS.mono_f

lemma ShortExact.ab_surjective_g (hS : S.ShortExact) :
    Function.Surjective S.g :=
  (AddCommGroupCat.epi_iff_surjective _).1 hS.epi_g

end ShortComplex

end CategoryTheory
