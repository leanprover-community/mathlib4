/-
Copyright (c) 2024 Yudai Yamazaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yudai Yamazaki
-/

import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Group Extensions

This file defines extensions of multiplicative and additive groups and their associated structures
such as splittings and equivalences.

## Main definitions

- `(Add?)GroupExtension N E G`: structure for extensions of `G` by `N` as short exact sequences
  `1 → N → E → G → 1` (`0 → N → E → G → 0` for additive groups)
- `(Add?)GroupExtension.Equiv S S'`: structure for equivalences of two group extensions `S` and `S'`
  as specific homomorphisms `E → E'` such that each diagram below is commutative

```text
For multiplicative groups:
      ↗︎ E  ↘
1 → N   ↓    G → 1
      ↘︎ E' ↗︎️

For additive groups:
      ↗︎ E  ↘
0 → N   ↓    G → 0
      ↘︎ E' ↗︎️
```

- `(Add?)GroupExtension.Splitting S`: structure for splittings of a group extension `S` of `G` by
  `N` as section homomorphisms `G → E`
- `SemidirectProduct.toGroupExtension φ`: the multiplicative group extension associated to the
  semidirect product coming from `φ : G →* MulAut N`, `1 → N → N ⋊[φ] G → G → 1`

## TODO

If `N` is abelian,

- there is a bijection between `N`-conjugacy classes of
  `(SemidirectProduct.toGroupExtension φ).Splitting` and `groupCohomology.H1`
  (which will be available in `GroupTheory/GroupExtension/Abelian.lean` to be added in a later PR).
- there is a bijection between equivalence classes of group extensions and `groupCohomology.H2`
  (which is also stated as a TODO in `RepresentationTheory/GroupCohomology/LowDegree.lean`).
-/

variable (N E G : Type*)

/-- `AddGroupExtension N E G` is a short exact sequence of additive groups `0 → N → E → G → 0`. -/
structure AddGroupExtension [AddGroup N] [AddGroup E] [AddGroup G] where
  /-- The inclusion homomorphism `N →+ E` -/
  inl : N →+ E
  /-- The projection homomorphism `E →+ G` -/
  rightHom : E →+ G
  /-- The inclusion map is injective. -/
  inl_injective : Function.Injective inl
  /-- The range of the inclusion map is equal to the kernel of the projection map. -/
  range_inl_eq_ker_rightHom : inl.range = rightHom.ker
  /-- The projection map is surjective. -/
  rightHom_surjective : Function.Surjective rightHom

/-- `GroupExtension N E G` is a short exact sequence of groups `1 → N → E → G → 1`. -/
@[to_additive]
structure GroupExtension [Group N] [Group E] [Group G] where
  /-- The inclusion homomorphism `N →* E` -/
  inl : N →* E
  /-- The projection homomorphism `E →* G` -/
  rightHom : E →* G
  /-- The inclusion map is injective. -/
  inl_injective : Function.Injective inl
  /-- The range of the inclusion map is equal to the kernel of the projection map. -/
  range_inl_eq_ker_rightHom : inl.range = rightHom.ker
  /-- The projection map is surjective. -/
  rightHom_surjective : Function.Surjective rightHom

variable {N E G}

namespace AddGroupExtension

variable [AddGroup N] [AddGroup E] [AddGroup G] (S : AddGroupExtension N E G)

/-- `AddGroupExtension`s are equivalent iff there is a homomorphism making a commuting diagram. -/
structure Equiv {E' : Type*} [AddGroup E'] (S' : AddGroupExtension N E' G) where
  /-- The homomorphism -/
  toAddMonoidHom : E →+ E'
  /-- The left-hand side of the diagram commutes. -/
  inl_comm : toAddMonoidHom.comp S.inl = S'.inl
  /-- The right-hand side of the diagram commutes. -/
  rightHom_comm : S'.rightHom.comp toAddMonoidHom = S.rightHom

/-- `Splitting` of an additive group extension is a section homomorphism. -/
structure Splitting where
  /-- A section homomorphism -/
  sectionHom : G →+ E
  /-- The section is a left inverse of the projection map. -/
  rightHom_comp_sectionHom : S.rightHom.comp sectionHom = AddMonoidHom.id G

end AddGroupExtension

namespace GroupExtension

variable [Group N] [Group E] [Group G] (S : GroupExtension N E G)

/-- The range of the inclusion map is a normal subgroup. -/
@[to_additive "The range of the inclusion map is a normal additive subgroup." ]
instance normal_inl_range : S.inl.range.Normal :=
  S.range_inl_eq_ker_rightHom ▸ S.rightHom.normal_ker

@[to_additive (attr := simp)]
theorem rightHom_inl (n : N) : S.rightHom (S.inl n) = 1 := by
  rw [← MonoidHom.mem_ker, ← S.range_inl_eq_ker_rightHom, MonoidHom.mem_range]
  exact exists_apply_eq_apply S.inl n

@[to_additive (attr := simp)]
theorem rightHom_comp_inl : S.rightHom.comp S.inl = 1 := by
  ext n
  rw [MonoidHom.one_apply, MonoidHom.comp_apply]
  exact S.rightHom_inl n

/-- `E` acts on `N` by conjugation. -/
noncomputable def conjAct : E →* MulAut N where
  toFun e := (MonoidHom.ofInjective S.inl_injective).trans <|
    (MulAut.conjNormal e).trans (MonoidHom.ofInjective S.inl_injective).symm
  map_one' := by
    ext _
    simp only [map_one, MulEquiv.trans_apply, MulAut.one_apply, MulEquiv.symm_apply_apply]
  map_mul' _ _ := by
    ext _
    simp only [map_mul, MulEquiv.trans_apply, MulAut.mul_apply, MulEquiv.apply_symm_apply]

/-- The inclusion and a conjugation commute. -/
theorem inl_conjAct_comm {e : E} {n : N} : S.inl (S.conjAct e n) = e * S.inl n * e⁻¹ := by
  simp only [conjAct, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.trans_apply,
    MonoidHom.apply_ofInjective_symm]
  rfl

/-- `GroupExtension`s are equivalent iff there is a homomorphism making a commuting diagram. -/
@[to_additive]
structure Equiv {E' : Type*} [Group E'] (S' : GroupExtension N E' G) where
  /-- The homomorphism -/
  toMonoidHom : E →* E'
  /-- The left-hand side of the diagram commutes. -/
  inl_comm : toMonoidHom.comp S.inl = S'.inl
  /-- The right-hand side of the diagram commutes. -/
  rightHom_comm : S'.rightHom.comp toMonoidHom = S.rightHom

/-- `Splitting` of a group extension is a section homomorphism. -/
@[to_additive]
structure Splitting where
  /-- A section homomorphism -/
  sectionHom : G →* E
  /-- The section is a left inverse of the projection map. -/
  rightHom_comp_sectionHom : S.rightHom.comp sectionHom = MonoidHom.id G

@[to_additive]
instance : FunLike S.Splitting G E where
  coe s := s.sectionHom
  coe_injective' := by
    intro ⟨_, _⟩ ⟨_, _⟩ h
    congr
    exact DFunLike.coe_injective h

@[to_additive]
instance : MonoidHomClass S.Splitting G E where
  map_mul s := s.sectionHom.map_mul'
  map_one s := s.sectionHom.map_one'

/-- A splitting of an extension `S` is `N`-conjugate to another iff there exists `n : N` such that
the section homomorphism is a conjugate of the other section homomorphism by `S.inl n`. -/
@[to_additive
      "A splitting of an extension `S` is `N`-conjugate to another iff there exists `n : N` such
      that the section homomorphism is a conjugate of the other section homomorphism by `S.inl n`."]
def IsConj (S : GroupExtension N E G) (s s' : S.Splitting) : Prop :=
  ∃ n : N, s.sectionHom = fun g ↦ S.inl n * s'.sectionHom g * (S.inl n)⁻¹

end GroupExtension

namespace SemidirectProduct

variable [Group G] [Group N] (φ : G →* MulAut N)

/-- The group extension associated to the semidirect product -/
def toGroupExtension : GroupExtension N (N ⋊[φ] G) G where
  inl_injective := inl_injective
  range_inl_eq_ker_rightHom := range_inl_eq_ker_rightHom
  rightHom_surjective := rightHom_surjective

theorem toGroupExtension_inl : (toGroupExtension φ).inl = SemidirectProduct.inl := rfl

theorem toGroupExtension_rightHom : (toGroupExtension φ).rightHom = SemidirectProduct.rightHom :=
  rfl

/-- A canonical splitting of the group extension associated to the semidirect product -/
def inr_splitting : (toGroupExtension φ).Splitting where
  sectionHom := inr
  rightHom_comp_sectionHom := rightHom_comp_inr

end SemidirectProduct
