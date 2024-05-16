/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Junyan Xu
-/

import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.GroupCat.Injective
import Mathlib.Topology.Instances.AddCircle
import Mathlib.Topology.Instances.Rat
import Mathlib.LinearAlgebra.Isomorphisms

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
- `CharacterModule.homEquiv` : there is a bijection between linear map `Hom(N, M⋆)` and
  `(N ⊗ M)⋆` given by `curry` and `uncurry`.

-/

open CategoryTheory

universe uR uA uB

variable (R : Type uR) [CommRing R]
variable (A : Type uA) [AddCommGroup A]
variable (A' : Type*) [AddCommGroup A']
variable (B : Type uB) [AddCommGroup B]

/--
The character module of an abelian group `A` in the unit rational circle is `A⋆ := Hom_ℤ(A, ℚ ⧸ ℤ)`.
-/
def CharacterModule : Type uA := A →+ AddCircle (1 : ℚ)

namespace CharacterModule

instance : FunLike (CharacterModule A) A (AddCircle (1 : ℚ)) where
  coe c := c.toFun
  coe_injective' _ _ _ := by aesop

instance : LinearMapClass (CharacterModule A) ℤ A (AddCircle (1 : ℚ)) where
  map_add _ _ _ := by rw [AddMonoidHom.map_add]
  map_smulₛₗ _ _ _ := by rw [AddMonoidHom.map_zsmul, RingHom.id_apply]

instance : AddCommGroup (CharacterModule A) :=
  inferInstanceAs (AddCommGroup (A →+ _))

@[ext] theorem ext {c c' : CharacterModule A} (h : ∀ x, c x = c' x) : c = c' := DFunLike.ext _ _ h

section module

variable [Module R A] [Module R A'] [Module R B]

instance : Module R (CharacterModule A) :=
  Module.compHom (A →+ _) (RingEquiv.toOpposite _ |>.toRingHom : R →+* Rᵈᵐᵃ)

variable {R A B}

@[simp] lemma smul_apply (c : CharacterModule A) (r : R) (a : A) : (r • c) a = c (r • a) := rfl

/--
Given an abelian group homomorphism `f : A → B`, `f⋆(L) := L ∘ f` defines a linear map
from `B⋆` to `A⋆`.
-/
@[simps] def dual (f : A →ₗ[R] B) : CharacterModule B →ₗ[R] CharacterModule A where
  toFun L := L.comp f.toAddMonoidHom
  map_add' := by aesop
  map_smul' r c := by ext x; exact congr(c $(f.map_smul r x)).symm

lemma dual_surjective_of_injective (f : A →ₗ[R] B) (hf : Function.Injective f) :
    Function.Surjective (dual f) :=
  (Module.Baer.of_divisible _).extension_property_addMonoidHom _ hf

/--
Two isomorphic modules have isomorphic character modules.
-/
def congr (e : A ≃ₗ[R] B) : CharacterModule A ≃ₗ[R] CharacterModule B :=
  .ofLinear (dual e.symm) (dual e)
    (by ext c _; exact congr(c $(e.right_inv _)))
    (by ext c _; exact congr(c $(e.left_inv _)))

open TensorProduct

/--
Any linear map `L : A → B⋆` induces a character in `(A ⊗ B)⋆` by `a ⊗ b ↦ L a b`.
-/
@[simps] noncomputable def uncurry :
    (A →ₗ[R] CharacterModule B) →ₗ[R] CharacterModule (A ⊗[R] B) where
  toFun c := TensorProduct.liftAddHom c.toAddMonoidHom fun r a b ↦ congr($(c.map_smul r a) b)
  map_add' c c' := DFunLike.ext _ _ fun x ↦ by refine x.induction_on ?_ ?_ ?_ <;> aesop
  map_smul' r c := DFunLike.ext _ _ fun x ↦ x.induction_on
    (by simp_rw [map_zero]) (fun a b ↦ congr($(c.map_smul r a) b).symm) (by aesop)

/--
Any character `c` in `(A ⊗ B)⋆` induces a linear map `A → B⋆` by `a ↦ b ↦ c (a ⊗ b)`.
-/
@[simps] noncomputable def curry :
    CharacterModule (A ⊗[R] B) →ₗ[R] (A →ₗ[R] CharacterModule B) where
  toFun c :=
  { toFun := (c.comp <| TensorProduct.mk R A B ·)
    map_add' := fun a a' ↦ DFunLike.ext _ _ fun b ↦
      congr(c <| $(map_add (mk R A B) _ _) b).trans (c.map_add _ _)
    map_smul' := fun r a ↦ by ext; exact congr(c $(TensorProduct.tmul_smul _ _ _)).symm }
  map_add' c c' := rfl
  map_smul' r c := by ext; exact congr(c $(TensorProduct.tmul_smul _ _ _)).symm

/--
Linear maps into a character module are exactly characters of the tensor product.
-/
@[simps!] noncomputable def homEquiv :
    (A →ₗ[R] CharacterModule B) ≃ₗ[R] CharacterModule (A ⊗[R] B) :=
  .ofLinear uncurry curry (by ext _ z; refine z.induction_on ?_ ?_ ?_ <;> aesop) (by aesop)

theorem dual_rTensor_conj_homEquiv (f : A →ₗ[R] A') :
    homEquiv.symm.toLinearMap ∘ₗ dual (f.rTensor B) ∘ₗ homEquiv.toLinearMap = f.lcomp R _ := rfl

end module

/--
`ℤ⋆`, the character module of `ℤ` in the unit rational circle.
-/
protected abbrev int : Type := CharacterModule ℤ

/-- Given `n : ℕ`, the map `m ↦ m / n`. -/
protected abbrev int.divByNat (n : ℕ) : CharacterModule.int :=
  LinearMap.toSpanSingleton ℤ _ (QuotientAddGroup.mk (n : ℚ)⁻¹) |>.toAddMonoidHom

protected lemma int.divByNat_self (n : ℕ) :
    int.divByNat n n = 0 := by
  obtain rfl | h0 := eq_or_ne n 0
  · apply map_zero
  exact (AddCircle.coe_eq_zero_iff _).mpr
    ⟨1, by simp [mul_inv_cancel (Nat.cast_ne_zero (R := ℚ).mpr h0)]⟩

variable {A}

/-- The `ℤ`-submodule spanned by a single element `a` is isomorphic to the quotient of `ℤ`
by the ideal generated by the order of `a`. -/
@[simps!] noncomputable def intSpanEquivQuotAddOrderOf (a : A) :
    (ℤ ∙ a) ≃ₗ[ℤ] ℤ ⧸ Ideal.span {(addOrderOf a : ℤ)} :=
  LinearEquiv.ofEq _ _ (LinearMap.span_singleton_eq_range ℤ A a) ≪≫ₗ
  (LinearMap.quotKerEquivRange <| LinearMap.toSpanSingleton ℤ A a).symm ≪≫ₗ
  Submodule.quotEquivOfEq _ _ (by
    ext1 x
    rw [Ideal.mem_span_singleton, addOrderOf_dvd_iff_zsmul_eq_zero, LinearMap.mem_ker,
      LinearMap.toSpanSingleton_apply])

lemma intSpanEquivQuotAddOrderOf_apply_self (a : A) :
    intSpanEquivQuotAddOrderOf a ⟨a, Submodule.mem_span_singleton_self a⟩ =
    Submodule.Quotient.mk 1 :=
  (LinearEquiv.eq_symm_apply _).mp <| Subtype.ext (one_zsmul _).symm

/--
For an abelian group `A` and an element `a ∈ A`, there is a character `c : ℤ ∙ a → ℚ ⧸ ℤ` given by
`m • a ↦ m / n` where `n` is the smallest positive integer such that `n • a = 0` and when such `n`
does not exist, `c` is defined by `m • a ↦ m / 2`.
-/
noncomputable def ofSpanSingleton (a : A) : CharacterModule (ℤ ∙ a) :=
  let l :  ℤ ⧸ Ideal.span {(addOrderOf a : ℤ)} →ₗ[ℤ] AddCircle (1 : ℚ) :=
    Submodule.liftQSpanSingleton _
      (CharacterModule.int.divByNat <|
        if addOrderOf a = 0 then 2 else addOrderOf a).toIntLinearMap <| by
        split_ifs with h
        · rw [h, Nat.cast_zero, map_zero]
        · apply CharacterModule.int.divByNat_self
  l ∘ₗ intSpanEquivQuotAddOrderOf a |>.toAddMonoidHom

lemma eq_zero_of_ofSpanSingleton_apply_self (a : A)
    (h : ofSpanSingleton a ⟨a, Submodule.mem_span_singleton_self a⟩ = 0) : a = 0 := by
  erw [ofSpanSingleton, LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply,
     intSpanEquivQuotAddOrderOf_apply_self, Submodule.liftQSpanSingleton_apply,
    AddMonoidHom.coe_toIntLinearMap, int.divByNat, LinearMap.toSpanSingleton_one,
    AddCircle.coe_eq_zero_iff] at h
  rcases h with ⟨n, hn⟩
  apply_fun Rat.den at hn
  rw [zsmul_one, Rat.den_intCast, Rat.inv_natCast_den_of_pos] at hn
  · split_ifs at hn
    · cases hn
    · rwa [eq_comm, AddMonoid.addOrderOf_eq_one_iff] at hn
  · split_ifs with h
    · norm_num
    · exact Nat.pos_of_ne_zero h

lemma exists_character_apply_ne_zero_of_ne_zero {a : A} (ne_zero : a ≠ 0) :
    ∃ (c : CharacterModule A), c a ≠ 0 :=
  have ⟨c, hc⟩ := dual_surjective_of_injective _ (Submodule.injective_subtype _) (ofSpanSingleton a)
  ⟨c, fun h ↦ ne_zero <| eq_zero_of_ofSpanSingleton_apply_self a <| by rwa [← hc]⟩

lemma eq_zero_of_character_apply {a : A} (h : ∀ c : CharacterModule A, c a = 0) : a = 0 := by
  contrapose! h; exact exists_character_apply_ne_zero_of_ne_zero h

variable [Module R A] [Module R A'] [Module R B] {R A' B}

lemma dual_surjective_iff_injective {f : A →ₗ[R] A'} :
    Function.Surjective (dual f) ↔ Function.Injective f :=
  ⟨fun h ↦ (injective_iff_map_eq_zero _).2 fun a h0 ↦ eq_zero_of_character_apply fun c ↦ by
    obtain ⟨c, rfl⟩ := h c; exact congr(c $h0).trans c.map_zero,
  dual_surjective_of_injective f⟩

theorem _root_.rTensor_injective_iff_lcomp_surjective {f : A →ₗ[R] A'} :
    Function.Injective (f.rTensor B) ↔ Function.Surjective (f.lcomp R <| CharacterModule B) := by
  simp [← dual_rTensor_conj_homEquiv, dual_surjective_iff_injective]

end CharacterModule
