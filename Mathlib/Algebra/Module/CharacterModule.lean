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
an `R`-lineara map `l : M ⟶ N` induces an `R`-linear map `l⋆ : f ↦ f ∘ l` where `f : N⋆`.
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
variable (M : Type uM) [AddCommGroup M] [Module R M]
variable (N : Type uN) [AddCommGroup N] [Module R N]
variable (D : Type uD) [AddCommGroup D] [Module R D]

-- we really want to consider only injective modules
/--
If `M` is an `R`-module, its `D`-character module is defined to be the `Hom_R(M, D)`
-/
def CharacterModule := M →ₗ[R] D

instance : FunLike (CharacterModule R M D) M (fun _ ↦ D) :=
  inferInstanceAs <| FunLike (M →ₗ[R] D) M _

instance : AddCommGroup (CharacterModule R M D) :=
  inferInstanceAs <| AddCommGroup <| M →ₗ[R] D

instance : Module R (CharacterModule R M D) :=
  LinearMap.module

instance : LinearMapClass (CharacterModule R M D) R M D :=
  inferInstanceAs <| LinearMapClass (M →ₗ[R] D) R M D

@[simp] lemma CharacterModule.smul_apply (f : CharacterModule R M D) (r : R) (m : M) :
    (r • f) m = f (r • m) := by
  rw [LinearMap.smul_apply, f.map_smul]

variable {R M N}

/--
For a linear map `L : M → N`, `(· ∘ L)` defines map from `CharacterModule N` to `CharacterModule M`
-/
@[simps]
def LinearMap.characterify
    (L : M →ₗ[R] N)  :
    CharacterModule R N D →ₗ[R] CharacterModule R M D where
  toFun f := f ∘ₗ L
  map_add' _ _ := LinearMap.ext fun m ↦ by aesop
  map_smul' r c := LinearMap.ext fun m ↦ by
    simp only [coe_comp, coe_restrictScalars, Function.comp_apply, RingHom.id_apply]
    rw [CharacterModule.smul_apply, CharacterModule.smul_apply, LinearMap.comp_apply, c.map_smul,
      L.map_smul, c.map_smul]

lemma LinearMap.characterify_surjective_of_injective
    [UnivLE.{uR, uD}] [injective_dual : Module.Injective R D]
    (L : M →ₗ[R] N)
    (inj : Function.Injective L) :
    Function.Surjective <| LinearMap.characterify D L :=
  Module.Baer.iff_injective.mpr injective_dual |>.extension_property L inj

variable (R)

/--
If `R` is a commutative ring, `M ↦ CharacterModule M` and `L ↦ (· ∘ L)` defines a contravariant
endofunctor on `R`-modules.
-/
@[simps!]
def CharacterModuleFunctor :
    (ModuleCat R)ᵒᵖ ⥤ ModuleCat R where
  obj M := ModuleCat.of R <| CharacterModule R M.unop D
  map L := LinearMap.characterify D L.unop
  map_id {_} := LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ rfl
  map_comp _ _ := LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ rfl

namespace CharacterModuleFunctor

lemma map_surjective_of_injective_unop [UnivLE.{uR, uD}] [Module.Injective R D]
    {M N : (ModuleCat R)ᵒᵖ} {L : M ⟶ N} (hL : Function.Injective L.unop) :
    Function.Surjective <| (CharacterModuleFunctor R D).map L :=
  L.unop.characterify_surjective_of_injective D hL

end CharacterModuleFunctor

namespace CharacterModule

/--
Equivalent modules have equivalent character modules
-/
@[simps!]
def cong (e : M ≃ₗ[R] N) :
    CharacterModule R M D ≃ₗ[R] CharacterModule R N D := by
  refine LinearEquiv.ofLinear
    (e.symm.toLinearMap.characterify D) (e.toLinearMap.characterify D) ?_ ?_ <;>
  refine LinearMap.ext <| fun _ ↦ LinearMap.ext fun _ ↦ ?_ <;> aesop

end CharacterModule


namespace CharacterModule

open TensorProduct

variable (M N)

/--
for a linear map `f : N → CharacterModule M`, i.e. `f : N → M → D`, we can uncurry it into
`(N ⊗ M) → D`, i.e. a character in `CharacterModule (N ⊗[R] M)`.
-/
@[simps!]
noncomputable def uncurry :
    (N →ₗ[R] CharacterModule.{uR, uM, uD} R M D) →ₗ[R]
    CharacterModule.{uR, max uN uM, uD} R (N ⊗[R] M) D :=
  TensorProduct.uncurry _ _ _ _

-- !FIXME Simply `TensorProduct.curry` doesn't work because of universe levels
/--
for a character in `CharacterModule (N ⊗[R] M)` i.e. `N ⊗ M → ℚ/ℤ`, we can curry it into
`N → M → ℚ/ℤ`, i.e. a linear map `N → CharacterModule M`
-/
@[simps!]
noncomputable def curry :
    CharacterModule.{uR, max uN uM, uD} R (N ⊗[R] M) D →ₗ[R]
    N →ₗ[R] CharacterModule.{uR, uM, uD} R M D :=
  { toFun := fun c ↦ TensorProduct.curry (R := R) (M := N) (N := M) (P := D) c,
    map_add' := map_add _
    map_smul' := map_smul _ }


/--
`CharacterModule.uncurry` and `CharacterModule.curry` defines a bijection between linear map
`Hom(N, CharacterModule M)` and `CharacterModule(N ⊗ M)`
-/
@[simps!]
noncomputable def homEquiv :
    (N →ₗ[R] CharacterModule.{uR, uM, uD} R M D) ≃ₗ[R]
    CharacterModule.{uR, max uM uN, uD} R (N ⊗[R] M) D :=
LinearEquiv.ofLinear
  (uncurry.{uR, uM, uN, uD} R M N D)
  (curry.{uR, uM, uN, uD} R M N D)
  (LinearMap.ext fun _ ↦ TensorProduct.ext <| by aesop)
  (LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ by aesop)

section addCommGroup

universe uA uB
variable (A : Type uA) [AddCommGroup A]
variable (B : Type uB) [AddCommGroup B]

/--
the character module of abelian group `A` in unit rational circle is `A⋆ := Hom_ℤ(A, ℚ ⧸ ℤ)`
-/
abbrev unitRationalCircle : Type uA :=
  CharacterModule ℤ A (AddCircle (1 : ℚ))

namespace unitRationalCircle

section module

variable (R : Type*) [CommRing R] [Module R A] [Module R B]

instance domModule : Module R (unitRationalCircle A) where
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

@[simp] lemma domModule_smul_apply (r : R) (c : unitRationalCircle A) (a : A) :
  (r • c) a = c (r • a) := rfl

@[simps!]
noncomputable def uncurry :
    (B →ₗ[R] unitRationalCircle A) →ₗ[R] unitRationalCircle (B ⊗[R] A) where
  toFun c := (liftAddHom
      { toFun := fun b => c b
        map_zero' := by aesop
        map_add' := by aesop } <| by aesop).toIntLinearMap
  map_add' _ _ := LinearMap.ext fun z ↦ by
    refine z.induction_on ?_ ?_ ?_ <;> aesop
  map_smul' r c := LinearMap.ext fun z ↦ by
    refine z.induction_on ?_ ?_ ?_
    · aesop
    · intro b a
      dsimp
      set c' : unitRationalCircle (B ⊗[R] A) := (liftAddHom _ _).toIntLinearMap
      change _ = (r • c') (b ⊗ₜ[R] a)
      simp only [domModule_smul_apply]
      erw [AddMonoidHom.coe_toIntLinearMap, liftAddHom_tmul]
      simp
    · aesop

@[simps!]
noncomputable def curry :
    unitRationalCircle (B ⊗[R] A) →ₗ[R] (B →ₗ[R] unitRationalCircle A) where
  toFun c :=
  { toFun := fun b ↦
    { toFun := fun a ↦ c (b ⊗ₜ a)
      map_add' := by simp [tmul_add]
      map_smul' := by simp }
    map_add' := fun _ _ ↦ LinearMap.ext fun _ ↦ by
      simp only [add_tmul, map_add, LinearMap.coe_mk, AddHom.coe_mk]; rfl
    map_smul' := fun r _ ↦ LinearMap.ext fun _ ↦ by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply]
      set c' : unitRationalCircle A := _
      change _ = (r • c') _
      simp only [domModule_smul_apply]
      rw [LinearMap.coe_mk, AddHom.coe_mk, smul_tmul] }
  map_add' _ _ := LinearMap.ext fun _ ↦ by aesop
  map_smul' r x := LinearMap.ext fun y ↦ LinearMap.ext fun z ↦ by
    simp only [domModule_smul_apply, LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply,
      LinearMap.smul_apply]
    set c' : unitRationalCircle A := _
    change _ = (r • c') _
    simp only [domModule_smul_apply]
    rw [LinearMap.coe_mk, AddHom.coe_mk, smul_tmul', ← smul_tmul]

@[simps!]
noncomputable def homEquiv :
    unitRationalCircle (B ⊗[R] A) ≃ₗ[R] (B →ₗ[R] unitRationalCircle A) :=
  LinearEquiv.ofLinear
    (curry (R := R) (A := A) (B := B))
    (uncurry (R := R) (A := A) (B := B))
    (LinearMap.ext fun _ ↦ by aesop)
    (LinearMap.ext fun _ ↦ LinearMap.ext fun z ↦ by
      refine z.induction_on ?_ ?_ ?_ <;> aesop)

@[simps!]
def cong (e : A ≃ₗ[R] B) : unitRationalCircle A ≃ₗ[R] unitRationalCircle B :=
  LinearEquiv.ofLinear
    { __ := e.symm.toLinearMap.toAddMonoidHom.toIntLinearMap.characterify (AddCircle (1 : ℚ))
      map_smul' := fun r c ↦ LinearMap.ext fun b ↦ by
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.characterify_apply,
          LinearMap.coe_comp, AddMonoidHom.coe_toIntLinearMap, LinearMap.toAddMonoidHom_coe,
          LinearEquiv.coe_coe, Function.comp_apply, RingHom.id_apply]
        set c' : unitRationalCircle B := _
        change _ = (r • c') _
        simp only [domModule_smul_apply]
        rw [LinearMap.comp_apply, domModule_smul_apply (r := r) (c := c)]
        aesop }
    { __ := e.toLinearMap.toAddMonoidHom.toIntLinearMap.characterify (AddCircle (1 : ℚ))
      map_smul' := fun r c ↦ LinearMap.ext fun b ↦ by
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.characterify_apply,
          LinearMap.coe_comp, AddMonoidHom.coe_toIntLinearMap, LinearMap.toAddMonoidHom_coe,
          LinearEquiv.coe_coe, Function.comp_apply, RingHom.id_apply]
        set c' : unitRationalCircle A := _
        change _ = (r • c') _
        simp only [domModule_smul_apply]
        rw [LinearMap.comp_apply, domModule_smul_apply (r := r) (c := c)]
        aesop }
    (LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ by aesop)
    (LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ by aesop)

end module

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

end addCommGroup

end CharacterModule
