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

/-!
# Character module of a module

For commutative ring `R` and an `R`-module `M`, its character module `M⋆` is defined to be
`ℤ`-linear maps `M ⟶ ℚ ⧸ ℤ`.

`M⋆` also has an `R`-module structure given by `(r • f) m = f (r • m)`.

## Main results

- `CharacterModuleFunctor` : the contravariant functor of `R`-modules where `M ↦ M⋆` and
an `R`-lineara map `l : M ⟶ N` induces an `R`-linear map `l⋆ : f ↦ l ∘ f` where `f : N⋆`.
- `LinearMap.charaterfy_surjective_of_injective` : If `l` is injective then `l⋆` is surjective,
  in another word taking character module as a functor sends monos to epis.
- `CharacterModule.exists_character_apply_ne_zero_of_ne_zero` : for nonzero `a ∈ M`, there is a
  character `c` in `M⋆` such that `c a` is nonzero as well.
- `CharacterModule.homEquiv` : there is a bijection between linear map `Hom(N, M⋆)` and
  `(N ⊗ M)⋆` given by `curry` and `uncurry`.

-/

open CategoryTheory

universe u w w'
variable (R : Type u) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M]
variable (D : Type w) [AddCommGroup D] [Module R D]
variable (N : Type w') [AddCommGroup N] [Module R N]

/--
If `M` is an abelian group, its character module is defined to be the `Hom_ℤ(M, ℚ/ℤ)`
-/
def CharacterModule : Type w := M →ₗ[ℤ] (ULift.{w} <| AddCircle (1 : ℚ))

instance : FunLike (CharacterModule M) M (fun _ ↦ ULift <| AddCircle (1 : ℚ)) where
  coe (f : M →ₗ[ℤ] ULift <| AddCircle (1 : ℚ)) m := f m
  coe_injective' _ _ h := LinearMap.ext fun _ ↦ congr_fun h _

instance : AddMonoidHomClass (CharacterModule M) M (ULift <| AddCircle (1 : ℚ)) where
  coe f := f
  coe_injective' _ _ h := FunLike.ext _ _ fun _ ↦ congr_fun h _
  map_add f := f.map_add
  map_zero f := f.map_zero

instance : AddCommGroup (CharacterModule M) :=
  inferInstanceAs <| AddCommGroup <| M →ₗ[ℤ] ULift.{w} <| AddCircle (1 : ℚ)

instance : Module R (CharacterModule M) where
  smul r l :=
  { toFun := fun x ↦ l (r • x)
    map_add' := fun x y ↦ by dsimp; rw [smul_add, map_add]
    map_smul' := fun s x ↦ by dsimp; rw [← smul_comm, l.map_smul] }
  one_smul l := LinearMap.ext fun x ↦ show l _ = _ by rw [one_smul]
  mul_smul r₁ r₂ l := LinearMap.ext fun x ↦ show l _ = l _ by rw [mul_smul, smul_comm]
  smul_zero r := rfl
  smul_add r l₁ l₂ := LinearMap.ext fun x ↦ show (l₁ + _) _ = _ by
    rw [LinearMap.add_apply, LinearMap.add_apply]; rfl
  add_smul r₁ r₂ l := LinearMap.ext fun x ↦ show l _ = l _ + l _ by
    rw [add_smul, map_add]
  zero_smul l := LinearMap.ext fun _ ↦ show l _ = 0 by rw [zero_smul, map_zero]

@[simp] lemma CharacterModule.smul_apply (f : CharacterModule M) (r : R) (m : M) :
    (r • f) m = f (r • m) := rfl

variable {R}

/--
For a linear map `L : M → N`, `(· ∘ L)` defines map from `CharacterModule N` to `CharacterModule M`
-/
@[simps] def LinearMap.characterify
    (L : M →ₗ[R] N) :
    CharacterModule N →ₗ[R] CharacterModule M where
  toFun f := ULift.moduleEquiv'.toLinearMap ∘ₗ f ∘ₗ L.toAddMonoidHom.toIntLinearMap
  map_add' _ _ := by aesop
  map_smul' _ _ := FunLike.ext _ _ fun _ ↦ by
    ext
    dsimp
    repeat rw [LinearMap.comp_apply]
    aesop

variable {M N} in
lemma LinearMap.characterify_surjective_of_injective
    (L : M →ₗ[R] N) (inj : Function.Injective L) :
    Function.Surjective L.characterify := by
  rintro (g : _ →ₗ[_] _)
  let g'' : (ULift.{max w w'} M) →ₗ[ℤ] (ULift.{max w w'} (AddCircle (1 : ℚ))) :=
    ULift.moduleEquiv'.toLinearMap ∘ₗ g ∘ₗ ULift.moduleEquiv.toLinearMap
  let L'' : ULift.{max w w'} M →ₗ[R] ULift.{max w w'} N :=
    ULift.moduleEquiv.symm.toLinearMap ∘ₗ L ∘ₗ ULift.moduleEquiv.toLinearMap
  let L' := AddCommGroupCat.ofHom L''.toAddMonoidHom
  have m1 : Mono <| L'
  · rw [AddCommGroupCat.mono_iff_injective]
    exact fun _ _ h ↦ ULift.ext _ _ <| inj ((ULift.ext_iff _ _).mp h)
  have : Fact ((0 : ℚ) < 1) := ⟨by norm_num⟩
  have i1 : Injective (AddCommGroupCat.of <| ULift.{max w w'} <| AddCircle (1 : ℚ)) :=
    AddCommGroupCat.injective_of_divisible _
  let g' := AddCommGroupCat.ofHom g''.toAddMonoidHom
  refine ⟨ULift.moduleEquiv'.toLinearMap ∘ₗ
    (Injective.factorThru g' L').toIntLinearMap ∘ₗ ULift.moduleEquiv.symm.toLinearMap,
    LinearMap.ext fun x ↦ ?_⟩
  ext
  convert (ULift.ext_iff _ _).mp <| FunLike.congr_fun (Injective.comp_factorThru g' L') (ULift.up x)

variable (R)
/--
If `R` is a commutative ring, `M ↦ CharacterModule M` and `L ↦ (· ∘ L)` defines a contravariant
endofunctor on `R`-modules.
-/
@[simps]
def CharacterModuleFunctor :
    (ModuleCat R)ᵒᵖ ⥤ ModuleCat R where
  obj M := ModuleCat.of R <| CharacterModule M.unop
  map L := L.unop.characterify
  map_id {_} := LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ rfl
  map_comp _ _ := LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ rfl

namespace CharacterModuleFunctor

lemma map_surjective_of_injective_unop {M N : (ModuleCat.{w, u} R)ᵒᵖ}
    (L : M ⟶ N) (hL : Function.Injective L.unop) :
    Function.Surjective <| (CharacterModuleFunctor R).map L :=
  L.unop.characterify_surjective_of_injective hL

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

/--
For an abelian group `M` and an element `a ∈ M`, there is a character `c : ℤ ∙ a → ℚ⧸ℤ` given by
`m • a ↦ m / n` where `n` is the smallest natural number such that `na = 0` and when such `n` does
not exist, `c` is defined by `m • a ↦ m / 2`
-/
noncomputable def CharacterModule.ofSpanSingleton (a : M) : CharacterModule (ℤ ∙ a) :=
let l' :  CharacterModule <| ℤ ⧸ Ideal.span {(addOrderOf a : ℤ)} :=
    Submodule.liftQSpanSingleton _
      (IntCharacterModule.divByNat <| if addOrderOf a = 0 then 2 else addOrderOf a) <| by
        split_ifs with h
        · rw [h, Nat.cast_zero, map_zero]
        · apply IntCharacterModule.divByNat_self
  LinearMap.characterify (R := ℤ) _ _ (equivZModSpanAddOrderOf a).toLinearMap l'

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

/--
for a linear map `f : N → CharacterModule M`, i.e. `f : N → M → ℚ/ℤ`, we can uncurry it into
`(N ⊗ M) → ℚ/ℤ`, i.e. a character in `CharacterModule (N ⊗[R] M)`.
-/
@[simps!]
noncomputable def CharacterModule.uncurry (f : N →ₗ[R] CharacterModule M) :
    CharacterModule (N ⊗[R] M) :=
  AddMonoidHom.toIntLinearMap <|
    TensorProduct.liftAddHom
      (⟨⟨fun x ↦ AddMonoidHom.comp ⟨⟨ULift.up ∘ ULift.down, by aesop⟩, by aesop⟩
        (f x).toAddMonoidHom , by aesop⟩,  by aesop⟩) fun r n m ↦ by aesop

/--
for a character in `CharacterModule (N ⊗[R] M)` i.e. `N ⊗ M → ℚ/ℤ`, we can curry it into
`N → M → ℚ/ℤ`, i.e. a linear map `N → CharacterModule M`
-/
@[simps]
noncomputable def CharacterModule.curry (c : CharacterModule (N ⊗[R] M)):
    (N →ₗ[R] CharacterModule M) where
  toFun n := ⟨⟨ULift.up ∘ ULift.down, by aesop⟩, by aesop⟩  ∘ₗ c ∘ₗ (TensorProduct.mk R N M n)
  map_add' _ _ := LinearMap.ext <| by aesop
  map_smul' r n := LinearMap.ext fun m ↦ ULift.ext _ _ <| show (c _).down = (c _).down by aesop

/--
`CharacterModule.uncurry` and `CharacterModule.curry` defines a bijection between linear map
`Hom(N, CharacterModule M)` and `CharacterModule(N ⊗ M)`
-/
@[simps]
noncomputable def CharacterModule.homEquiv :
  (N →ₗ[R] CharacterModule M) ≃ CharacterModule (N ⊗[R] M) :=
{ toFun := CharacterModule.uncurry R M N
  invFun := CharacterModule.curry R M N
  left_inv := fun _ ↦ LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ by simp
  right_inv := fun _ ↦ LinearMap.ext fun z ↦ by refine z.induction_on ?_ ?_ ?_ <;> aesop }

/--
Equivalent modules have equivalent character modules
-/
@[simps!]
def CharacterModule.cong (e : M ≃ₗ[R] N) : CharacterModule M ≃ₗ[R] CharacterModule N := by
  refine LinearEquiv.ofLinear e.symm.toLinearMap.characterify e.toLinearMap.characterify ?_ ?_ <;>
  refine LinearMap.ext <| fun _ ↦ LinearMap.ext fun _ ↦ ?_ <;>
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.characterify_apply,
    AddMonoidHom.coe_toIntLinearMap, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, LinearMap.id_coe, id_eq] <;>
  aesop
