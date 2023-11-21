/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.Algebra.Category.GroupCat.EpiMono
import Mathlib.Algebra.Category.GroupCat.ZModuleEquivalence
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
- `AddCommGroupCat.enoughInjectives` : the category of abelian groups has enough injectives.

## Implementation notes

The details of the proof that the category of abelian groups has enough injectives is hidden
inside the namespace `AddCommGroup.enough_injectives_aux_proofs`. These are not marked `private`,
but are not supposed to be used directly.

-/


open CategoryTheory

open Pointwise

universe u v w w'

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

end AddCommGroupCat

section injective_character

variable (R : Type u) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M]
variable (N : Type w') [AddCommGroup N] [Module R N]

def CharacterModule : Type w :=
M →ₗ[ℤ] (ULift.{w} <| AddCircle (1 : ℚ))

instance : FunLike (CharacterModule M) M (fun _ => ULift <| AddCircle (1 : ℚ)) where
  coe (f : M →ₗ[ℤ] ULift <| AddCircle (1 : ℚ)) m := f m
  coe_injective' _ _ h := LinearMap.ext fun _ => congr_fun h _

instance : AddMonoidHomClass (CharacterModule M) M (ULift <| AddCircle (1 : ℚ)) where
  coe f := f
  coe_injective' _ _ h := FunLike.ext _ _ fun _ => congr_fun h _
  map_add f := f.map_add
  map_zero f := f.map_zero

instance : AddCommGroup (CharacterModule M) := by
  delta CharacterModule
  infer_instance

instance : Module R (CharacterModule M) where
  smul r l :=
  { toFun := fun x => l (r • x)
    map_add' := fun x y => by dsimp; rw [smul_add, map_add]
    map_smul' := fun s x => by dsimp; rw [← smul_comm, l.map_smul] }
  one_smul l := LinearMap.ext fun x => show l _ = _ by rw [one_smul]
  mul_smul r₁ r₂ l := LinearMap.ext fun x => show l _ = l _ by rw [mul_smul, smul_comm]
  smul_zero r := rfl
  smul_add r l₁ l₂ := LinearMap.ext fun x => show (l₁ + _) _ = _ by
    rw [LinearMap.add_apply, LinearMap.add_apply]; rfl
  add_smul r₁ r₂ l := LinearMap.ext fun x => show l _ = l _ + l _ by
    rw [add_smul, map_add]
  zero_smul l := LinearMap.ext fun x => show l _ = 0 by rw [zero_smul, map_zero]

@[simp] lemma CharacterModule.smul_apply (f : CharacterModule M) (r : R) (m : M) :
    (r • f) m = f (r • m) := rfl

variable {R}
@[simps] def LinearMap.characterfy
    (L : M →ₗ[R] N) :
    CharacterModule N →ₗ[R] CharacterModule M where
  toFun f := ⟨⟨ULift.up ∘ ULift.down, by aesop⟩, by aesop⟩ ∘ₗ f ∘ₗ L.toAddMonoidHom.toIntLinearMap
  map_add' _ _ := FunLike.ext _ _ fun _ => by aesop
  map_smul' _ _ := FunLike.ext _ _ fun _ => by
    ext
    simp only [RingHom.id_apply, CharacterModule.smul_apply]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    simp only [AddMonoidHom.coe_toIntLinearMap, LinearMap.toAddMonoidHom_coe, LinearMap.coe_mk,
      AddHom.coe_mk, Function.comp_apply, map_smul]
    rfl

variable {M N} in
lemma LinearMap.charaterfy_surjective_of_injective
    (L : M →ₗ[R] N) (inj : Function.Injective L) :
    Function.Surjective L.characterfy := by
  rintro (g : _ →ₗ[_] _)
  let g'' : (ULift.{max w w'} M) →ₗ[ℤ] (ULift.{max w w'} (AddCircle (1 : ℚ))) :=
    ⟨⟨ULift.up ∘ ULift.down, by aesop⟩, by aesop⟩ ∘ₗ g ∘ₗ ⟨⟨ULift.down, by aesop⟩, by aesop⟩
  let L'' : ULift.{max w w'} M →ₗ[R] ULift.{max w w'} N :=
    ⟨⟨ULift.up, by aesop⟩, by aesop⟩ ∘ₗ L ∘ₗ ⟨⟨ULift.down, by aesop⟩, by aesop⟩
  let L' := AddCommGroupCat.ofHom L''.toAddMonoidHom
  have m1 : Mono <| L'
  · rw [AddCommGroupCat.mono_iff_injective]
    exact fun _ _ h => ULift.ext _ _ <| inj ((ULift.ext_iff _ _).mp h)
  have : Fact ((0 : ℚ) < 1) := ⟨by norm_num⟩
  have i1 : Injective (AddCommGroupCat.of <| ULift.{max w w'} <| AddCircle (1 : ℚ)) :=
    AddCommGroupCat.injective_of_divisible _
  let g' := AddCommGroupCat.ofHom g''.toAddMonoidHom
  refine ⟨⟨⟨ULift.up ∘ ULift.down, by aesop⟩, by aesop⟩ ∘ₗ
    (Injective.factorThru g' L').toIntLinearMap ∘ₗ ⟨⟨ULift.up, by aesop⟩, by aesop⟩,
    LinearMap.ext fun x => ?_⟩
  ext
  convert (ULift.ext_iff _ _).mp <| FunLike.congr_fun (Injective.comp_factorThru g' L') (ULift.up x)

variable (R)
@[simps]
def CharacterModuleFunctor :
    (ModuleCat R)ᵒᵖ ⥤ ModuleCat R where
  obj M := ModuleCat.of R <| CharacterModule M.unop
  map L := L.unop.characterfy
  map_id {_} := LinearMap.ext fun _ => LinearMap.ext fun _ => rfl
  map_comp _ _ := LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

namespace CharacterModuleFunctor

lemma map_surjective_of_injective_unop {M N : (ModuleCat.{w, u} R)ᵒᵖ}
    (L : M ⟶ N) (hL : Function.Injective L.unop) :
    Function.Surjective <| (CharacterModuleFunctor R).map L :=
  L.unop.charaterfy_surjective_of_injective hL

end CharacterModuleFunctor

/-- Given `n : ℕ`, the map `m ↦ m / n`. -/
abbrev IntCharacterModule.divByNat (n : ℕ) : CharacterModule ℤ :=
  LinearMap.toSpanSingleton ℤ _ (ULift.up <| QuotientAddGroup.mk (n : ℚ)⁻¹)

lemma IntCharacterModule.divByNat_self (n : ℕ) : IntCharacterModule.divByNat n n = 0 := by
  obtain rfl | h0 := eq_or_ne n 0
  · apply map_zero
  exact ULift.ext (divByNat n n) 0 <| (AddCircle.coe_eq_zero_iff _).mpr
    ⟨1, by simp [mul_inv_cancel (Nat.cast_ne_zero (R := ℚ).mpr h0)]⟩

variable {M}
/-- `ℤ ⧸ ⟨ord(a)⟩ ≃ aℤ` -/
@[simps!] noncomputable def equivZModSpanAddOrderOf (a : M) :
    (ℤ ∙ a) ≃ₗ[ℤ] ℤ ⧸ Ideal.span {(addOrderOf a : ℤ)} :=
  (LinearEquiv.ofEq _ _ <| LinearMap.span_singleton_eq_range ℤ M a).trans <|
    (LinearMap.quotKerEquivRange <| LinearMap.toSpanSingleton ℤ M a).symm.trans <|
      Submodule.quotEquivOfEq _ _ <| by
        ext1 x; rw [Ideal.mem_span_singleton, addOrderOf_dvd_iff_zsmul_eq_zero]; rfl

lemma equivZModSpanAddOrderOf_apply_self (a : M) :
    equivZModSpanAddOrderOf a ⟨a, Submodule.mem_span_singleton_self a⟩ = Submodule.Quotient.mk 1 :=
  (LinearEquiv.eq_symm_apply _).mp (one_zsmul _).symm

noncomputable def CharacterModule.ofSpanSingleton (a : M) : CharacterModule (ℤ ∙ a) :=
let l' :  CharacterModule <| ℤ ⧸ Ideal.span {(addOrderOf a : ℤ)} :=
    Submodule.liftQSpanSingleton _
      (IntCharacterModule.divByNat <| if addOrderOf a = 0 then 2 else addOrderOf a) <| by
        split_ifs with h
        · rw [h, Nat.cast_zero, map_zero]
        · apply IntCharacterModule.divByNat_self
  LinearMap.characterfy (R := ℤ) _ _ (equivZModSpanAddOrderOf a).toLinearMap l'

lemma CharacterModule.eq_zero_of_ofSpanSingleton_apply_self (a : M)
    (h : ofSpanSingleton a ⟨a, Submodule.mem_span_singleton_self a⟩ = 0) : a = 0 := by
  erw [ofSpanSingleton, LinearMap.comp_apply, LinearMap.coe_mk,  AddHom.coe_mk, Function.comp_apply,
    LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.coe_toIntLinearMap,
    LinearEquiv.coe_toLinearMap, equivZModSpanAddOrderOf_apply_self, ULift.ext_iff, ULift.zero_down,
    QuotientAddGroup.lift_mk, LinearMap.toAddMonoidHom_coe, IntCharacterModule.divByNat,
    LinearMap.toSpanSingleton_one, AddCircle.coe_eq_zero_iff] at h
  rcases h with ⟨n, hn⟩
  apply_fun Rat.den at hn
  rw [zsmul_one, Rat.coe_int_den, Rat.inv_coe_nat_den_of_pos] at hn
  · split_ifs at hn
    · cases hn
    · rwa [eq_comm, AddMonoid.addOrderOf_eq_one_iff] at hn
  · split_ifs with h
    · norm_num
    · exact Nat.pos_of_ne_zero h

lemma CharacterModule.exists_character_apply_ne_zero_of_ne_zero {a : M} (ne_zero : a ≠ 0) :
    ∃ (c : CharacterModule M), c a ≠ 0 := by
  let L := AddCommGroupCat.ofHom <| (ofSpanSingleton a).toAddMonoidHom
  let ι : AddCommGroupCat.of (ℤ ∙ a) ⟶ AddCommGroupCat.of M :=
    AddCommGroupCat.ofHom (Submodule.subtype _).toAddMonoidHom
  have : Mono ι := (AddCommGroupCat.mono_iff_injective _).mpr Subtype.val_injective
  use (Injective.factorThru L ι).toIntLinearMap
  erw [FunLike.congr_fun (Injective.comp_factorThru L ι) ⟨a, Submodule.mem_span_singleton_self _⟩]
  intro rid
  rw [ULift.ext_iff, AddCommGroupCat.ofHom_apply, ULift.zero_down] at rid
  exact ne_zero <| eq_zero_of_ofSpanSingleton_apply_self a (ULift.ext _ _ rid)

open TensorProduct

variable (M)

@[simps!]
noncomputable def CharacterModule.uncurry (f : N →ₗ[R] CharacterModule M) :
    CharacterModule (N ⊗[R] M) :=
  AddMonoidHom.toIntLinearMap <|
    TensorProduct.liftAddHom
      (⟨⟨fun x => AddMonoidHom.comp ⟨⟨ULift.up ∘ ULift.down, by aesop⟩, by aesop⟩
        (f x).toAddMonoidHom , by aesop⟩,  by aesop⟩) fun r n m => by aesop

@[simps]
noncomputable def CharacterModule.curry (c : CharacterModule (N ⊗[R] M)):
    (N →ₗ[R] CharacterModule M) where
  toFun n := ⟨⟨ULift.up ∘ ULift.down, by aesop⟩, by aesop⟩  ∘ₗ c ∘ₗ (TensorProduct.mk R N M n)
  map_add' _ _ := LinearMap.ext <| by aesop
  map_smul' r n := LinearMap.ext fun m => ULift.ext _ _ <| show (c _).down = (c _).down by aesop

@[simps]
noncomputable def CharacterModule.homEquiv : (N →ₗ[R] CharacterModule M) ≃ CharacterModule (N ⊗[R] M) :=
{ toFun := CharacterModule.uncurry R M N
  invFun := CharacterModule.curry R M N
  left_inv := fun _ => LinearMap.ext fun _ => LinearMap.ext fun _ => by simp
  right_inv := fun _ => LinearMap.ext fun z => by refine z.induction_on ?_ ?_ ?_ <;> aesop }

@[simps!]
def CharacterModule.cong (e : M ≃ₗ[R] N) : CharacterModule M ≃ₗ[R] CharacterModule N := by
  refine LinearEquiv.ofLinear e.symm.toLinearMap.characterfy e.toLinearMap.characterfy ?_ ?_ <;>
  refine LinearMap.ext <| fun _ => LinearMap.ext fun _ => ?_ <;>
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.characterfy_apply,
    AddMonoidHom.coe_toIntLinearMap, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, LinearMap.id_coe, id_eq] <;>
  aesop

end injective_character

namespace AddCommGroupCat

namespace enough_injectives_aux_proofs

variable (A_ : AddCommGroupCat.{u})

/-- The next term of `A`'s injective resolution is `∏_{A →+ ℚ/ℤ}, ℚ/ℤ`. -/
def next : AddCommGroupCat.{u} := of <| (CharacterModule A_) → ULift.{u} (AddCircle (1 : ℚ))

instance : Injective <| next A_ :=
  have : Fact ((0 : ℚ) < 1) := ⟨by norm_num⟩
  injective_of_divisible _

/-- The map into the next term of `A`'s injective resolution is coordinate-wise evaluation. -/
@[simps] def toNext : A_ ⟶ next A_ where
  toFun a i := i a
  map_zero' := by simp only [map_zero]; rfl
  map_add' _ _ := by simp only [map_add]; rfl

variable {A_} (a : A_)

variable {a}

/-- The map sending `n • a` to `n / 2` when `a` has infinite order,
  and to `n / addOrderOf a` otherwise. -/
@[simps!] noncomputable def toRatCircle : CharacterModule (ℤ ∙ a) :=
  CharacterModule.ofSpanSingleton a

lemma eq_zero_of_toRatCircle_apply_self
    (h : toRatCircle ⟨a, Submodule.mem_span_singleton_self a⟩ = 0) : a = 0 :=
  CharacterModule.eq_zero_of_ofSpanSingleton_apply_self a h

variable (A_)

lemma toNext_inj : Function.Injective <| toNext A_ :=
  (injective_iff_map_eq_zero _).mpr fun a h0 ↦
    eq_zero_of_toRatCircle_apply_self <| -- <| ULift.up_injective <| _
      let f : of (ℤ ∙ a) ⟶ of (ULift.{u} <| AddCircle (1 : ℚ)) := toRatCircle.toAddMonoidHom
      let g : of (ℤ ∙ a) ⟶ A_ := AddSubgroupClass.subtype _
      have : Mono g := (mono_iff_injective _).mpr Subtype.val_injective
      (FunLike.congr_fun (Injective.comp_factorThru f g) _).symm.trans <|
        ULift.ext _ _ <| (ULift.ext_iff _ _).mp <| congr_fun h0 (Injective.factorThru f g).toIntLinearMap

/-- An injective presentation of `A`: `A → ∏_{A →+ ℚ/ℤ}, ℚ/ℤ`. -/
@[simps] def presentation : InjectivePresentation A_ where
  J := next A_
  injective := inferInstance
  f := toNext A_
  mono := (AddCommGroupCat.mono_iff_injective _).mpr <| toNext_inj _

end enough_injectives_aux_proofs

instance enoughInjectives : EnoughInjectives (AddCommGroupCat.{u}) where
  presentation A_ := ⟨enough_injectives_aux_proofs.presentation A_⟩

end AddCommGroupCat
