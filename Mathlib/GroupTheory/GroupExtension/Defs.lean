/-
Copyright (c) 2024 Yudai Yamazaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yudai Yamazaki
-/

import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Group Extensions

This file defines extensions of groups and their associated structures such as splittings and
equivalences.

## Main definitions

- `GroupExtension N E G`: structure for extensions of `G` by `N` as short exact sequences
  `1 → N → E → G → 1`
- `GroupExtension.Equiv S S'`: structure for equivalences of two group extensions `S` and `S'` as
  specific homomorphisms `E → E'` such that the diagram below is commutative.

```text
      ↗︎ E  ↘
1 → N   ↓    G → 1
      ↘︎ E' ↗︎️
```

- `GroupExtension.Splitting S`: structure for splittings of a group extension `S` of `G` by `N` as
  section homomorphisms `G → E`
- `SemidirectProduct.toGroupExtension φ`: the group extension associated to the semidirect product
  coming from `φ : G →* MulAut N`, `1 → N → N ⋊[φ] G → G → 1`

## TODO

If `N` is Abelian,

- there is a bijection between `N`-conjugacy classes of
  `(SemidirectProduct.toGroupExtension φ).Splitting` and `groupCohomology.H1`
  (which is available in `GroupTheory/GroupExtension/Abelian.lean` to be added in a later PR).
- there is a bijection between equivalence classes of group extensions and `groupCohomology.H2`
  (which is also stated as a TODO in `RepresentationTheory/GroupCohomology/LowDegree.lean`).
-/

variable (N E G : Type*) [Group N] [Group E] [Group G]

/-- `GroupExtension N E G` is a short exact sequence of groups `1 → N → E → G → 1` -/
structure GroupExtension where
  /-- The inclusion homomorphism `N →* E` -/
  inl : N →* E
  /-- The projection homomorphism `E →* G` -/
  rightHom : E →* G
  /-- The inclusion map is injective -/
  inl_injective : Function.Injective inl
  /-- The range of the inclusion map is equal to the kernel of the projection map -/
  range_inl_eq_ker_rightHom : inl.range = rightHom.ker
  /-- The projection map is surjective -/
  rightHom_surjective : Function.Surjective rightHom

variable {N E G}

namespace GroupExtension

variable (S : GroupExtension N E G)

/-- The range of the inclusion map is a normal subgroup -/
instance normal_inl_range : (S.inl.range).Normal :=
  S.range_inl_eq_ker_rightHom ▸ S.rightHom.normal_ker

theorem rightHom_inl (n : N) : S.rightHom (S.inl n) = 1 := by
  rw [← MonoidHom.mem_ker, ← S.range_inl_eq_ker_rightHom, MonoidHom.mem_range]
  exact exists_apply_eq_apply S.inl n

theorem rightHom_comp_inl : S.rightHom.comp S.inl = 1 := by
  ext n
  rw [MonoidHom.one_apply, MonoidHom.comp_apply]
  exact S.rightHom_inl n

/-- `E` acts on `N` by conjugation -/
noncomputable def conjAct : E →* MulAut N := {
  toFun := fun e ↦ (MonoidHom.ofInjective S.inl_injective).trans <|
    (MulAut.conjNormal e).trans (MonoidHom.ofInjective S.inl_injective).symm
  map_one' := by
    ext _
    simp only [map_one, MulEquiv.trans_apply, MulAut.one_apply, MulEquiv.symm_apply_apply]
  map_mul' := fun _ _ ↦ by
    ext _
    simp only [map_mul, MulEquiv.trans_apply, MulAut.mul_apply, MulEquiv.apply_symm_apply]
}

/-- The inclusion and a conjugation commute -/
theorem inl_conjAct_comm {e : E} {n : N} : S.inl (S.conjAct e n) = e * S.inl n * e⁻¹ := by
  simp only [conjAct, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.trans_apply,
    MonoidHom.apply_ofInjective_symm]
  rfl

/-- `GroupExtension`s are equivalent iff there is a homomorphism making a commuting diagram -/
structure Equiv {E' : Type*} [Group E'] (S' : GroupExtension N E' G) where
  /-- The homomorphism -/
  toMonoidHom : E →* E'
  /-- The left-hand side of the diagram commutes -/
  inl_comm : toMonoidHom.comp S.inl = S'.inl
  /-- The right-hand side of the diagram commutes -/
  rightHom_comm : S'.rightHom.comp toMonoidHom = S.rightHom

/-- `Splitting` of a group extension is a section homomorphism -/
structure Splitting where
  /-- A section homomorphism -/
  sectionHom : G →* E
  /-- The section is a left inverse of the projection map -/
  rightHom_comp_sectionHom : S.rightHom.comp sectionHom = MonoidHom.id G

instance : FunLike (S.Splitting) G E where
  coe s := s.sectionHom
  coe_injective' := by
    intro ⟨_, _⟩ ⟨_, _⟩ h
    congr
    exact DFunLike.coe_injective h

instance : MonoidHomClass (S.Splitting) G E where
  map_mul := fun s ↦ s.sectionHom.map_mul'
  map_one := fun s ↦ s.sectionHom.map_one'

/-- A splitting of an extension `S` is `N`-conjugate to another iff there exists `n : N` such that
the section homomorphism is a conjugate of the other section homomorphism by `S.inl n`. -/
def IsConj (S : GroupExtension N E G) (s s' : S.Splitting) :=
  ∃ n : N, s.sectionHom = fun g ↦ S.inl n * s'.sectionHom g * (S.inl n)⁻¹

end GroupExtension

namespace SemidirectProduct

variable (φ : G →* MulAut N)

/-- The group extension associated to the semidirect product -/
def toGroupExtension : GroupExtension N (N ⋊[φ] G) G where
  inl_injective := inl_injective
  range_inl_eq_ker_rightHom := range_inl_eq_ker_rightHom
  rightHom_surjective := rightHom_surjective

theorem toGroupExtension_inl : (toGroupExtension φ).inl = SemidirectProduct.inl := rfl

theorem toGroupExtension_rightHom : (toGroupExtension φ).rightHom = SemidirectProduct.rightHom :=
  rfl

/-- A canonical splitting -/
def inr_splitting : (toGroupExtension φ).Splitting where
  sectionHom := inr
  rightHom_comp_sectionHom := rightHom_comp_inr

end SemidirectProduct
