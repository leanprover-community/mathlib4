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

/-!
# Character module of a module

For commutative ring `R` and an `R`-module `M` and an injective module `D`, its character module
`M⋆` is defined to be `R`-linear maps `M ⟶ D`.

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

universe uR uM uN uD
variable (R : Type uR) [CommRing R]
variable (M : Type (max uR uM)) [AddCommGroup M] [Module R M]
variable (N : Type (max uR uN)) [AddCommGroup N] [Module R N]
variable (D : Type (max uR uD)) [AddCommGroup D] [Module R D]
variable [injective_dual : Injective <| ModuleCat.of R D]

/--
If `M` is an `R`-module, its `D`-character module is defined to be the `Hom_R(M, D)`
-/
def CharacterModule : Type (max uR uM uD) := M →ₗ[R] D

instance : FunLike (CharacterModule.{uR, uM, uD} R M D) M (fun _ ↦ D) where
  coe (f : M →ₗ[R] D) m := f m
  coe_injective' _ _ h := LinearMap.ext fun _ ↦ congr_fun h _

instance : AddMonoidHomClass (CharacterModule.{uR, uM, uD} R M D) M D where
  coe f := f
  coe_injective' _ _ h := FunLike.ext _ _ fun _ ↦ congr_fun h _
  map_add f := f.map_add
  map_zero f := f.map_zero

instance : AddCommGroup (CharacterModule.{uR, uM, uD} R M D) :=
  inferInstanceAs <| AddCommGroup <| M →ₗ[R] D

instance : Module R (CharacterModule.{uR, uM, uD} R M D) :=
  LinearMap.module
  -- smul r l :=
  -- { toFun := fun x ↦ l (r • x)
  --   map_add' := fun x y ↦ by dsimp; rw [smul_add, map_add]
  --   map_smul' := fun s x ↦ by dsimp; rw [← smul_comm, l.map_smul] }
  -- one_smul l := LinearMap.ext fun x ↦ show l _ = _ by rw [one_smul]
  -- mul_smul r₁ r₂ l := LinearMap.ext fun x ↦ show l _ = l _ by rw [mul_smul, smul_comm]
  -- smul_zero r := rfl
  -- smul_add r l₁ l₂ := LinearMap.ext fun x ↦ show (l₁ + _) _ = _ by
  --   rw [LinearMap.add_apply, LinearMap.add_apply]; rfl
  -- add_smul r₁ r₂ l := LinearMap.ext fun x ↦ show l _ = l _ + l _ by
  --   rw [add_smul, map_add]
  -- zero_smul l := LinearMap.ext fun _ ↦ show l _ = 0 by rw [zero_smul, map_zero]

@[simp] lemma CharacterModule.smul_apply (f : CharacterModule.{uR, uM, uD} R M D) (r : R) (m : M) :
    (r • f) m = f (r • m) := by
  rw [LinearMap.smul_apply, f.map_smul]

variable {R M N}

/--
For a linear map `L : M → N`, `(· ∘ L)` defines map from `CharacterModule N` to `CharacterModule M`
-/
@[simps]
def LinearMap.characterify
    (L : M →ₗ[R] N)  :
    CharacterModule.{uR, uN, uD} R N D →ₗ[R] CharacterModule.{uR, uM, uD} R M D where
  toFun f := f ∘ₗ L
  map_add' _ _ := LinearMap.ext fun m ↦ by aesop
  map_smul' r c := LinearMap.ext fun m ↦ by
    simp only [coe_comp, coe_restrictScalars, Function.comp_apply, RingHom.id_apply]
    rw [CharacterModule.smul_apply, CharacterModule.smul_apply, LinearMap.comp_apply, c.map_smul,
      L.map_smul, c.map_smul]

lemma LinearMap.characterify_surjective_of_injective
    (L : M →ₗ[R] N)
    (inj : Function.Injective L) :
    Function.Surjective <| LinearMap.characterify.{uR, uM, uN, uD} D L := by

  rintro (g : _ →ₗ[_] _)
  let g'' : (ULift.{max uM uN uD uR} M) →ₗ[R] (ULift.{max uM uN uD uR} D) :=
    ULift.moduleEquiv.symm.toLinearMap ∘ₗ g ∘ₗ ULift.moduleEquiv.toLinearMap
  let L'' : ULift.{max uM uN uD uR} M →ₗ[R] ULift.{max uM uN uD uR} N :=
    ULift.moduleEquiv.symm.toLinearMap ∘ₗ L ∘ₗ ULift.moduleEquiv.toLinearMap
  let L' := ModuleCat.ofHom L''
  have m1 : Mono <| L'
  · rw [ModuleCat.mono_iff_injective]
    intro _ _ h
    exact ULift.down_inj |>.mp <| inj <| ULift.ext_iff _ _ |>.mp h

  let g' := ModuleCat.ofHom g''
  have : Injective (ModuleCat.of R <| ULift.{max uM uN uD uR} D)
  · exact ModuleCat.injective_ulift.{uR, max uR uD, max uM uN uR uD} R D
  exact ⟨ULift.moduleEquiv.toLinearMap ∘ₗ Injective.factorThru g' L' ∘ₗ
    ULift.moduleEquiv.symm.toLinearMap, FunLike.ext _ _ fun _ ↦ ULift.ext_iff _ _ |>.mp <|
      FunLike.congr_fun (Injective.comp_factorThru g' L') _⟩

variable (R)

/--
If `R` is a commutative ring, `M ↦ CharacterModule M` and `L ↦ (· ∘ L)` defines a contravariant
endofunctor on `R`-modules.
-/
@[simps!]
def CharacterModuleFunctor :
    (ModuleCat.{max uM uR, uR} R)ᵒᵖ ⥤ ModuleCat.{max uM uD uR, uR} R where
  obj M := ModuleCat.of R <| CharacterModule.{uR, uM, uD} R M.unop D
  map L := LinearMap.characterify.{uR, uM, uM, uD} D L.unop
  map_id {_} := LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ rfl
  map_comp _ _ := LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ rfl

namespace CharacterModuleFunctor

lemma map_surjective_of_injective_unop
    {M N : (ModuleCat.{max uM uR, uR} R)ᵒᵖ}
    (L : M ⟶ N) (hL : Function.Injective L.unop) :
    Function.Surjective <| (CharacterModuleFunctor.{uR, uM, uD} R D).map L :=
  LinearMap.characterify_surjective_of_injective.{uR, uM, uM, uD} D L.unop hL

end CharacterModuleFunctor

open TensorProduct

variable (M N)

/--
for a linear map `f : N → CharacterModule M`, i.e. `f : N → M → D`, we can uncurry it into
`(N ⊗ M) → D`, i.e. a character in `CharacterModule (N ⊗[R] M)`.
-/
@[simps!]
noncomputable def CharacterModule.uncurry :
    (N →ₗ[R] CharacterModule.{uR, uM, uD} R M D) →ₗ[R]
    CharacterModule.{uR, max uN uM, uD} R (N ⊗[R] M) D :=
  TensorProduct.uncurry _ _ _ _

-- !FIXME Simply `TensorProduct.curry` doesn't work because of universe levels
/--
for a character in `CharacterModule (N ⊗[R] M)` i.e. `N ⊗ M → ℚ/ℤ`, we can curry it into
`N → M → ℚ/ℤ`, i.e. a linear map `N → CharacterModule M`
-/
@[simps!]
noncomputable def CharacterModule.curry :
    CharacterModule.{uR, max uN uM, uD} R (N ⊗[R] M) D →ₗ[R]
    N →ₗ[R] CharacterModule.{uR, uM, uD} R M D :=
  { toFun := fun c ↦ TensorProduct.curry (R := R) (M := N) (N := M) (P := D) c,
    map_add' := map_add _
    map_smul' := map_smul _ }


/--
`CharacterModule.uncurry` and `CharacterModule.curry` defines a bijection between linear map
`Hom(N, CharacterModule M)` and `CharacterModule(N ⊗ M)`
-/
@[simps]
noncomputable def CharacterModule.homEquiv :
  (N →ₗ[R] CharacterModule.{uR, uM, uD} R M D) ≃ CharacterModule.{uR, max uM uN, uD} R (N ⊗[R] M) D :=
{ toFun := CharacterModule.uncurry.{uR, uM, uN, uD} R M N D
  invFun := CharacterModule.curry.{uR, uM, uN, uD} R M N D
  left_inv := fun _ ↦ LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ by aesop
  right_inv := fun _ ↦ LinearMap.ext fun z ↦ by refine z.induction_on ?_ ?_ ?_ <;> aesop }

/--
Equivalent modules have equivalent character modules
-/
@[simps!]
def CharacterModule.cong (e : M ≃ₗ[R] N) :
    CharacterModule.{uR, uM, uD} R M D ≃ₗ[R] CharacterModule.{uR, uN, uD} R N D := by
  refine LinearEquiv.ofLinear
    (e.symm.toLinearMap.characterify D) (e.toLinearMap.characterify D) ?_ ?_ <;>
  refine LinearMap.ext <| fun _ ↦ LinearMap.ext fun _ ↦ ?_ <;>
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.characterify_apply,
    AddMonoidHom.coe_toIntLinearMap, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, LinearMap.id_coe, id_eq]
  aesop

namespace CharacterModule

universe uA
variable (A : Type uA) [AddCommGroup A]

/--
the character module of abelian group `A` in unit rational circle is `A⋆ := Hom_ℤ(A, ℚ ⧸ ℤ)`
-/
abbrev unitRationalCircle : Type uA :=
  CharacterModule ℤ A (AddCircle (1 : ℚ))

namespace unitRationalCircle
/--
`ℤ⋆`, the character module of `ℤ` in rational circle
-/
protected abbrev int : Type :=
  CharacterModule.unitRationalCircle ℤ

/-- Given `n : ℕ`, the map `m ↦ m / n`. -/
protected abbrev int.divByNat (n : ℕ) : CharacterModule.unitRationalCircle ℤ :=
  LinearMap.toSpanSingleton ℤ _ (QuotientAddGroup.mk (n : ℚ)⁻¹)

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
noncomputable def ofSpanSingleton (a : A) : unitRationalCircle (ℤ ∙ a) :=
  let l' :  unitRationalCircle (ℤ ⧸ Ideal.span {(addOrderOf a : ℤ)}) :=
    Submodule.liftQSpanSingleton _
      (unitRationalCircle.int.divByNat <| if addOrderOf a = 0 then 2 else addOrderOf a) <| by
        simp only [unitRationalCircle.int.divByNat, Nat.cast_ite, Nat.cast_ofNat,
          LinearMap.toSpanSingleton_apply, coe_nat_zsmul, Nat.isUnit_iff,
          AddMonoid.addOrderOf_eq_one_iff]
        by_cases h : addOrderOf a = 0
        · rw [h, zero_smul]
        · rw [if_neg h]
          apply unitRationalCircle.int.divByNat_self
  (equivZModSpanAddOrderOf a).characterify (R := ℤ) (D := AddCircle (1 : ℚ)) l'

lemma eq_zero_of_ofSpanSingleton_apply_self (a : A)
    (h : ofSpanSingleton a ⟨a, Submodule.mem_span_singleton_self a⟩ = 0) : a = 0 := by
  -- simp? [ofSpanSingleton] at h
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
    ∃ (c : unitRationalCircle A), c a ≠ 0 := by
  let L := AddCommGroupCat.ofHom <|
    (ULift.moduleEquiv.symm.toLinearMap ∘ₗ unitRationalCircle.ofSpanSingleton a).toAddMonoidHom
  let ι : AddCommGroupCat.of (ℤ ∙ a) ⟶ AddCommGroupCat.of A :=
    AddCommGroupCat.ofHom (Submodule.subtype _).toAddMonoidHom
  have : Mono ι := (AddCommGroupCat.mono_iff_injective _).mpr Subtype.val_injective
  refine ⟨ULift.moduleEquiv.toLinearMap ∘ₗ (Injective.factorThru L ι).toIntLinearMap, ?_⟩
  intro rid
  erw [LinearMap.comp_apply, FunLike.congr_fun (Injective.comp_factorThru L ι)
    ⟨a, Submodule.mem_span_singleton_self _⟩] at rid
  exact ne_zero <| unitRationalCircle.eq_zero_of_ofSpanSingleton_apply_self a rid

end unitRationalCircle

end CharacterModule
