/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Junyan Xu
-/

import Mathlib.Algebra.Module.LinearMap
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.GroupCat.Injective
import Mathlib.Topology.Instances.AddCircle
import Mathlib.Topology.Instances.Rat
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.GroupTheory.GroupAction.DomAct.ActionHom

/-!
# Character module of a module

For commutative ring `R` and an `R`-module `M` and an injective module `D`, its character module
`M⋆` is defined to be `R`-linear maps `M ⟶ D`.

`M⋆` also has an `R`-module structure given by `(r • f) m = f (r • m)`.

## Main results

- `CharacterModuleFunctor` : the contravariant functor of `R`-modules where `M ↦ M⋆` and
an `R`-linear map `l : M ⟶ N` induces an `R`-linear map `l⋆ : f ↦ f ∘ l` where `f : N⋆`.
- `LinearMap.dual_surjective_of_injective` : If `l` is injective then `l⋆` is surjective,
  in another word taking character module as a functor sends monos to epis.
- `CharacterModule.exists_character_apply_ne_zero_of_ne_zero` : for nonzero `a ∈ M`, there is a
  character `c` in `M⋆` such that `c a` is nonzero as well.
- `CharacterModule.homEquiv` : there is a bijection between linear map `Hom(N, M⋆)` and
  `(N ⊗ M)⋆` given by `curry` and `uncurry`.

-/

open CategoryTheory

universe uR uA uB

variable (R : Type uR) [CommRing R]
variable (A : Type uA) [AddCommGroup A]
variable (B : Type uB) [AddCommGroup B]

/--
the character module of abelian group `A` in unit rational circle is `A⋆ := Hom_ℤ(A, ℚ ⧸ ℤ)`
-/
def CharacterModule : Type uA := A →+ (AddCircle (1 : ℚ))

namespace CharacterModule

instance : LinearMapClass (CharacterModule A) ℤ A (AddCircle (1 : ℚ)) where
  coe c := c.toFun
  coe_injective' _ _ _ := by aesop
  map_add := by aesop
  map_smulₛₗ := by aesop

instance : AddCommGroup (CharacterModule A) :=
  inferInstanceAs (AddCommGroup (A →+ _))

section module

variable [Module R A]  [Module R B]

instance : Module R (CharacterModule A) :=
  letI : DistribMulAction Rᵈᵐᵃ (CharacterModule A) :=
    inferInstanceAs <| DistribMulAction Rᵈᵐᵃ (A →+ (AddCircle (1 : ℚ)))
  { smul := fun r l ↦ (DomMulAct.mk r) • l
    one_smul := fun l ↦ DFunLike.ext _ _ <| fun x ↦ show l _ = _ by simp
    mul_smul := fun r₁ r₂ l ↦ DFunLike.ext _ _ <| fun x ↦ show l _ = l _ by
      dsimp; rw [mul_comm, mul_smul]
    smul_zero := fun _ ↦ rfl
    smul_add := fun r l₁ l₂ ↦ DFunLike.ext _ _ fun _ ↦ rfl
    add_smul := fun r₁ r₂ l ↦ DFunLike.ext _ _ fun _ ↦ show l _ = l _ + l _ by simp [add_smul]
    zero_smul := fun l ↦ DFunLike.ext _ _ fun _ ↦ show l _ = 0 by simp }

variable {R A B}

@[simp] lemma smul_apply (c : CharacterModule A) (r : R) (a : A) : (r • c) a = c (r • a) := rfl

/--
Given an abelian group homomorphism `f : A → B`, then `f⋆(L) := L ∘ f` defines a linear map
between `B⋆` and `A⋆`
-/
@[simps] def dual (f : A →ₗ[R] B) : CharacterModule B →ₗ[R] CharacterModule A where
  toFun L := L.comp f.toAddMonoidHom
  map_add' := by aesop
  map_smul' r c := DFunLike.ext _ _ fun x ↦ by
    simp only [RingHom.id_apply, smul_apply]
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, smul_apply]
    erw [smul_apply, f.map_smul]
    rfl

lemma dual_surjective_of_injective (f : A →ₗ[R] B) (hf : Function.Injective f) :
    Function.Surjective <| dual f := by
  have : Fact ((0 : ℚ) < 1) := ⟨by norm_num⟩
  have inst1 : Injective (AddCommGroupCat.of <| ULift.{max uA uB, 0} <| AddCircle (1 : ℚ)) :=
    AddCommGroupCat.injective_of_divisible _

  rintro (g : _ →+ _)
  let g' : AddCommGroupCat.of (ULift.{max uA uB} A) ⟶
      AddCommGroupCat.of (ULift.{max uA uB} (AddCircle (1 : ℚ))) :=
    AddCommGroupCat.ofHom <| (ULift.moduleEquiv (R := ℤ)).symm.toAddMonoidHom.comp g |>.comp
      (ULift.moduleEquiv (R := ℤ)).toAddMonoidHom
  let f' : AddCommGroupCat.of (ULift.{max uA uB} A) ⟶ AddCommGroupCat.of (ULift.{max uA uB} B) :=
    AddCommGroupCat.ofHom <| (ULift.moduleEquiv (R := ℤ)).symm.toAddMonoidHom.comp f |>.comp
      (ULift.moduleEquiv (R := ℤ)).toAddMonoidHom
  have inst2 : Mono f'
  · rw [AddCommGroupCat.mono_iff_injective]
    exact (ULift.moduleEquiv (R := ℤ)).symm.injective.comp hf |>.comp
      (ULift.moduleEquiv (R := ℤ)).injective
  let L := Injective.factorThru g' f'
  refine ⟨(ULift.moduleEquiv (R := ℤ)).toAddMonoidHom.comp L |>.comp
    (ULift.moduleEquiv (R := ℤ)).symm.toAddMonoidHom, AddMonoidHom.ext fun _ ↦
      (ULift.ext_iff _ _).mp <| DFunLike.congr_fun (Injective.comp_factorThru g' f') _⟩

/--
Two isomorphic modules have isomorphic character modules.
-/
def congr (e : A ≃ₗ[R] B) : CharacterModule A ≃ₗ[R] CharacterModule B :=
  LinearEquiv.ofLinear
    (dual e.symm) (dual e)
    (LinearMap.ext fun c ↦ DFunLike.ext _ _ fun a ↦ by
      simp only [LinearMap.coe_comp, Function.comp_apply, dual_apply, LinearMap.id_coe, id_eq]
      rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply]
      erw [e.apply_symm_apply])
    (LinearMap.ext fun c ↦ DFunLike.ext _ _ fun a ↦ by
      simp only [LinearMap.coe_comp, Function.comp_apply, dual_apply, LinearMap.id_coe, id_eq]
      rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply]
      erw [e.symm_apply_apply])

open TensorProduct

/--
Any linear map `L : A → B⋆` induces a character in `(A ⊗ B)⋆` by `a ⊗ b ↦ L a b`
-/
@[simps] noncomputable def curry :
    (A →ₗ[R] CharacterModule B) →ₗ[R] CharacterModule (A ⊗[R] B) where
  toFun c := TensorProduct.liftAddHom c.toAddMonoidHom fun r a b ↦ by
    show c (r • a) b = c a (r • b)
    rw [c.map_smul, smul_apply]
  map_add' c c' := DFunLike.ext _ _ fun x ↦ by
    induction x using TensorProduct.induction_on
    · simp
    · dsimp
      rw [liftAddHom_tmul, AddMonoidHom.add_apply, liftAddHom_tmul, liftAddHom_tmul]
      rfl
    · aesop
  map_smul' r c := DFunLike.ext _ _ fun x ↦ by
    induction' x using TensorProduct.induction_on
    · simp
    · dsimp
      rw [liftAddHom_tmul]
      erw [smul_apply]
      rw [smul_tmul', smul_tmul, liftAddHom_tmul]
      rfl
    · aesop

/--
Any character `c` in `(A ⊗ B)⋆` induces a linear map `A → B⋆` by `a ↦ b ↦ c (a ⊗ b) `
-/
@[simps] noncomputable def uncurry :
    CharacterModule (A ⊗[R] B) →ₗ[R] (A →ₗ[R] CharacterModule B) where
  toFun c :=
  { toFun := fun a ↦ c.comp ((TensorProduct.mk R A B) a).toAddMonoidHom
    map_add' := fun a a' ↦ DFunLike.ext _ _ fun b ↦ by
      rw [AddMonoidHom.add_apply]
      repeat rw [AddMonoidHom.comp_apply]
      simp
    map_smul' := fun r a ↦ DFunLike.ext _ _ fun b ↦ by
      simp only [map_smul, RingHom.id_apply, smul_apply]
      repeat rw [AddMonoidHom.comp_apply]
      simp }
  map_add' c c' := DFunLike.ext _ _ fun a ↦ DFunLike.ext _ _ fun b ↦ by
    dsimp
    repeat rw [AddMonoidHom.add_apply]
    repeat rw [AddMonoidHom.comp_apply]
    simp only [LinearMap.toAddMonoidHom_coe, mk_apply]
    rfl
  map_smul' r c := DFunLike.ext _ _ fun a ↦ DFunLike.ext _ _ fun b ↦ by
    dsimp
    repeat rw [AddMonoidHom.comp_apply]
    simp only [LinearMap.toAddMonoidHom_coe, mk_apply, map_smul]
    rw [smul_apply]

/--
Linear maps into a character module are exactly characters of tensor product.
-/
@[simps!] noncomputable def homEquiv :
    (A →ₗ[R] CharacterModule B) ≃ₗ[R] CharacterModule (A ⊗[R] B) :=
  LinearEquiv.ofLinear curry uncurry
    (LinearMap.ext fun c ↦ DFunLike.ext _ _ fun z ↦ by
      refine z.induction_on ?_ ?_ ?_ <;> aesop)
    (LinearMap.ext fun l ↦ DFunLike.ext _ _ fun _ ↦ by aesop)

end module
/--
`ℤ⋆`, the character module of `ℤ` in rational circle
-/
protected abbrev int : Type := CharacterModule ℤ

/-- Given `n : ℕ`, the map `m ↦ m / n`. -/
protected abbrev int.divByNat (n : ℕ) : CharacterModule.int  :=
  LinearMap.toSpanSingleton ℤ _ (QuotientAddGroup.mk (n : ℚ)⁻¹) |>.toAddMonoidHom

protected lemma int.divByNat_self (n : ℕ) :
    int.divByNat n n = 0 := by
  obtain rfl | h0 := eq_or_ne n 0
  · apply map_zero
  exact (AddCircle.coe_eq_zero_iff _).mpr
    ⟨1, by simp [mul_inv_cancel (Nat.cast_ne_zero (R := ℚ).mpr h0)]⟩

variable {A}

/-- `ℤ ⧸ ⟨ord(a)⟩ ≃ aℤ` -/
@[simps!] noncomputable def equivZModSpanAddOrderOf (a : A) :
    (ℤ ∙ a) ≃ₗ[ℤ] ℤ ⧸ Ideal.span {(addOrderOf a : ℤ)} :=
  (LinearEquiv.ofEq _ _ <| LinearMap.span_singleton_eq_range ℤ A a).trans <|
    (LinearMap.quotKerEquivRange <| LinearMap.toSpanSingleton ℤ A a).symm.trans <|
      Submodule.quotEquivOfEq _ _ <| by
        ext1 x; rw [Ideal.mem_span_singleton, addOrderOf_dvd_iff_zsmul_eq_zero]; rfl

lemma equivZModSpanAddOrderOf_apply_self (a : A) :
    equivZModSpanAddOrderOf a ⟨a, Submodule.mem_span_singleton_self a⟩ =
    Submodule.Quotient.mk 1 :=
  (LinearEquiv.eq_symm_apply _).mp <| Subtype.ext <| Eq.symm <| one_zsmul _

/--
For an abelian group `M` and an element `a ∈ M`, there is a character `c : ℤ ∙ a → ℚ⧸ℤ` given by
`m • a ↦ m / n` where `n` is the smallest natural number such that `na = 0` and when such `n` does
not exist, `c` is defined by `m • a ↦ m / 2`
-/
noncomputable def ofSpanSingleton (a : A) : CharacterModule (ℤ ∙ a) :=
  let l' :  ℤ ⧸ Ideal.span {(addOrderOf a : ℤ)} →ₗ[ℤ] (AddCircle (1 : ℚ)):=
    Submodule.liftQSpanSingleton _
      (CharacterModule.int.divByNat <|
        if addOrderOf a = 0 then 2 else addOrderOf a).toIntLinearMap <| by
        simp only [CharacterModule.int.divByNat, Nat.cast_ite, Nat.cast_ofNat,
          LinearMap.toSpanSingleton_apply, coe_nat_zsmul, Nat.isUnit_iff,
          AddMonoid.addOrderOf_eq_one_iff]
        by_cases h : addOrderOf a = 0
        · rw [h]; simp
        · rw [if_neg h]
          apply CharacterModule.int.divByNat_self
  l' ∘ₗ (equivZModSpanAddOrderOf a) |>.toAddMonoidHom

lemma eq_zero_of_ofSpanSingleton_apply_self (a : A)
    (h : ofSpanSingleton a ⟨a, Submodule.mem_span_singleton_self a⟩ = 0) : a = 0 := by
  erw [ofSpanSingleton, LinearMap.comp_apply,
    equivZModSpanAddOrderOf_apply_self, Submodule.liftQSpanSingleton_apply,
    LinearMap.toAddMonoidHom_coe, int.divByNat, LinearMap.toSpanSingleton_one,
    AddCircle.coe_eq_zero_iff] at h
  rcases h with ⟨n, hn⟩
  apply_fun Rat.den at hn
  rw [zsmul_one, Rat.coe_int_den, Rat.inv_coe_nat_den_of_pos] at hn
  · split_ifs at hn
    · cases hn
    · rwa [eq_comm, AddMonoid.addOrderOf_eq_one_iff] at hn
  · split_ifs with h
    · norm_num
    · exact Nat.pos_of_ne_zero h

lemma exists_character_apply_ne_zero_of_ne_zero {a : A} (ne_zero : a ≠ 0) :
    ∃ (c : CharacterModule A), c a ≠ 0 := by
  let L := AddCommGroupCat.ofHom <|
    ((ULift.moduleEquiv (R := ℤ)).symm.toLinearMap.toAddMonoidHom.comp <|
      CharacterModule.ofSpanSingleton a)
  let ι : AddCommGroupCat.of (ℤ ∙ a) ⟶ AddCommGroupCat.of A :=
    AddCommGroupCat.ofHom (Submodule.subtype _).toAddMonoidHom
  have : Mono ι := (AddCommGroupCat.mono_iff_injective _).mpr Subtype.val_injective
  refine ⟨(ULift.moduleEquiv (R := ℤ)).toLinearMap.toAddMonoidHom.comp <|
    Injective.factorThru L ι, ?_⟩
  intro rid
  erw [AddMonoidHom.comp_apply, DFunLike.congr_fun (Injective.comp_factorThru L ι)
    ⟨a, Submodule.mem_span_singleton_self _⟩] at rid
  exact ne_zero <| eq_zero_of_ofSpanSingleton_apply_self a rid

end CharacterModule
