/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.Algebra.Category.GroupCat.EpiMono
import Mathlib.Algebra.Category.GroupCat.ZModuleEquivalence
import Mathlib.Algebra.Category.GroupCat.EquivalenceGroupAddGroup
import Mathlib.Algebra.Module.Injective
import Mathlib.Topology.Instances.AddCircle
import Mathlib.Topology.Instances.Rat
import Mathlib.LinearAlgebra.Isomorphisms

#align_import algebra.category.Group.injective from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Injective objects in the category of abelian groups

In this file we prove that divisible groups are injective object in category of (additive) abelian
groups and that the category of abelian groups has enough injective objects.

## Main results

- `AddCommGroupCat.injective_of_divisible` : a divisible group is also an injective object.
- `AddCommGroupCat.enoughInjectives` : the category of abelian groups (written additively) has
  enough injectives.
- `CommGroupCat.enoughInjectives` : the category of abelian group (written multiplicatively) has
  enough injectives.

## Implementation notes

The details of the proof that the category of abelian groups has enough injectives is hidden
inside the namespace `AddCommGroup.enough_injectives_aux_proofs`. These are not marked `private`,
but are not supposed to be used directly.

-/


open CategoryTheory

open Pointwise

universe u

variable (A : Type u) [AddCommGroup A]

set_option linter.uppercaseLean3 false

namespace AddCommGroupCat

theorem injective_as_module_iff : Injective (⟨A⟩ : ModuleCat ℤ) ↔
    Injective (⟨A,inferInstance⟩ : AddCommGroupCat) :=
  ((forget₂ (ModuleCat ℤ) AddCommGroupCat).asEquivalence.map_injective_iff ⟨A⟩).symm
#noalign AddCommGroup.injective_of_injective_as_module
#noalign AddCommGroup.injective_as_module_of_injective_as_Ab

instance injective_of_divisible [DivisibleBy A ℤ] :
    Injective (⟨A,inferInstance⟩ : AddCommGroupCat) :=
  (injective_as_module_iff A).mp <|
    @Module.injective_object_of_injective_module ℤ _ A _ _ <|
      Module.Baer.injective fun I g ↦ by
        rcases IsPrincipalIdealRing.principal I with ⟨m, rfl⟩
        obtain rfl | h0 := eq_or_ne m 0
        · refine ⟨0, fun n hn ↦ ?_⟩
          rw [Submodule.span_zero_singleton] at hn
          subst hn
          exact (map_zero g).symm
        let gₘ := g ⟨m, Submodule.subset_span (Set.mem_singleton _)⟩
        refine ⟨LinearMap.toSpanSingleton ℤ A (DivisibleBy.div gₘ m), fun n hn ↦ ?_⟩
        rcases Submodule.mem_span_singleton.mp hn with ⟨n, rfl⟩
        rw [map_zsmul, LinearMap.toSpanSingleton_apply, DivisibleBy.div_cancel gₘ h0, ← map_zsmul g,
          SetLike.mk_smul_mk]
#align AddCommGroup.injective_of_divisible AddCommGroupCat.injective_of_divisible

instance injective_ratCircle : Injective <| of <| ULift.{u} <| AddCircle (1 : ℚ) :=
  have : Fact ((0 : ℚ) < 1) := ⟨by norm_num⟩
  injective_of_divisible _

namespace enough_injectives_aux_proofs

variable (A_ : AddCommGroupCat.{u})

/-- The next term of `A`'s injective resolution is `∏_{A →+ ℚ/ℤ}, ℚ/ℤ`. -/
def next : AddCommGroupCat.{u} := of <|
  (A_ ⟶ of <| ULift.{u} <| AddCircle (1 : ℚ)) → ULift.{u} (AddCircle (1 : ℚ))

instance : Injective <| next A_ :=
  have : Fact ((0 : ℚ) < 1) := ⟨by norm_num⟩
  injective_of_divisible _

/-- The map into the next term of `A`'s injective resolution is coordinate-wise evaluation. -/
@[simps] def toNext : A_ ⟶ next A_ where
  toFun a i := i a
  map_zero' := by simp only [map_zero]; rfl
  map_add' _ _ := by simp only [map_add]; rfl

variable {A_} (a : A_)

lemma _root_.LinearMap.toSpanSingleton_ker :
    LinearMap.ker (LinearMap.toSpanSingleton ℤ A_ a) = Ideal.span {(addOrderOf a : ℤ)} := by
  ext1 x
  rw [Ideal.mem_span_singleton, addOrderOf_dvd_iff_zsmul_eq_zero]
  rfl

/-- `ℤ ⧸ ⟨ord(a)⟩ ≃ aℤ` -/
@[simps!] noncomputable def equivZModSpanAddOrderOf :
    (ℤ ∙ a) ≃ₗ[ℤ] ℤ ⧸ Ideal.span {(addOrderOf a : ℤ)} :=
  (LinearEquiv.ofEq _ _ <| LinearMap.span_singleton_eq_range ℤ A_ a).trans <|
    (LinearMap.quotKerEquivRange <| LinearMap.toSpanSingleton ℤ A_ a).symm.trans <|
      Submodule.quotEquivOfEq _ _ <| LinearMap.toSpanSingleton_ker a

lemma equivZModSpanAddOrderOf_apply_self :
    equivZModSpanAddOrderOf a ⟨a, Submodule.mem_span_singleton_self a⟩ = Submodule.Quotient.mk 1 :=
  (LinearEquiv.eq_symm_apply _).mp (one_zsmul _).symm

/-- Given `n : ℕ`, the map `m ↦ m / n`. -/
abbrev divBy (n : ℕ) : ℤ →ₗ[ℤ] AddCircle (1 : ℚ) :=
  LinearMap.toSpanSingleton ℤ _ (QuotientAddGroup.mk (n : ℚ)⁻¹)

lemma divBy_self (n : ℕ) : divBy n n = 0 := by
  obtain rfl | h0 := eq_or_ne n 0
  · apply map_zero
  apply (AddCircle.coe_eq_zero_iff _).mpr ⟨1, _⟩
  simp [mul_inv_cancel (Nat.cast_ne_zero (R := ℚ).mpr h0)]

variable {a}

/-- The map sending `n • a` to `n / 2` when `a` has infinite order,
  and to `n / addOrderOf a` otherwise. -/
@[simps!] noncomputable def toRatCircle : (ℤ ∙ a) →ₗ[ℤ] AddCircle (1 : ℚ) :=
  let e : ℤ ⧸ Ideal.span {(addOrderOf a : ℤ)} →ₗ[ℤ] AddCircle (1 : ℚ) :=
    Submodule.liftQSpanSingleton _ (divBy <| if addOrderOf a = 0 then 2 else addOrderOf a) <| by
      split_ifs with h
      · rw [h, Nat.cast_zero, map_zero]
      · apply divBy_self
  e ∘ₗ equivZModSpanAddOrderOf a

lemma eq_zero_of_toRatCircle_apply_self
    (h : toRatCircle ⟨a, Submodule.mem_span_singleton_self a⟩ = 0) : a = 0 := by
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [toRatCircle, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    equivZModSpanAddOrderOf_apply_self, Submodule.liftQSpanSingleton_apply,
    LinearMap.toSpanSingleton_one, AddCircle.coe_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  apply_fun Rat.den at hn
  rw [zsmul_one, Rat.coe_int_den, Rat.inv_coe_nat_den_of_pos] at hn
  · split_ifs at hn
    · cases hn
    · rwa [eq_comm, AddMonoid.addOrderOf_eq_one_iff] at hn
  · split_ifs with h
    · norm_num
    · exact Nat.pos_of_ne_zero h

variable (A_)

lemma toNext_inj : Function.Injective <| toNext A_ :=
  (injective_iff_map_eq_zero _).mpr fun a h0 ↦
    eq_zero_of_toRatCircle_apply_self <| ULift.up_injective <|
      let f : of (ℤ ∙ a) ⟶ of (ULift.{u} <| AddCircle (1 : ℚ)) :=
        AddMonoidHom.comp ⟨⟨ULift.up, rfl⟩, fun _ _ ↦ rfl⟩ toRatCircle.toAddMonoidHom
      let g : of (ℤ ∙ a) ⟶ A_ := AddSubgroupClass.subtype _
      have : Mono g := (mono_iff_injective _).mpr Subtype.val_injective
      (FunLike.congr_fun (Injective.comp_factorThru f g) _).symm.trans (congr_fun h0 _)

/-- An injective presentation of `A`: `A → ∏_{A →+ ℚ/ℤ}, ℚ/ℤ`. -/
@[simps] def presentation : InjectivePresentation A_ where
  J := next A_
  injective := inferInstance
  f := toNext A_
  mono := (AddCommGroupCat.mono_iff_injective _).mpr <| toNext_inj _

end enough_injectives_aux_proofs

instance enoughInjectives : EnoughInjectives AddCommGroupCat.{u} where
  presentation A_ := ⟨enough_injectives_aux_proofs.presentation A_⟩

end AddCommGroupCat

namespace CommGroupCat

instance enoughInjectives : EnoughInjectives CommGroupCat.{u} :=
  EnoughInjectives.of_equivalence commGroupAddCommGroupEquivalence.functor

end CommGroupCat
