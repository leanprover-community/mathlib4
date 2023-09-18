import Mathlib.Algebra.Category.ModuleCat.TensorProduct
import Mathlib.Algebra.Category.GroupCat.Injective
import Mathlib.Topology.Instances.AddCircle
import Mathlib.Topology.Instances.Rat

open CategoryTheory

universe u v w w'

variable (R : Type u) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M]


def CharacterModule : Type w :=
M →ₗ[ℤ] (AddCircle (1 : ℚ))

instance : FunLike (CharacterModule M) M (fun _ => AddCircle (1 : ℚ)) where
  coe (f : M →ₗ[ℤ] (AddCircle (1 : ℚ))) m := f m
  coe_injective' _ _ h := LinearMap.ext fun _ => congr_fun h _

instance : AddCommGroup (CharacterModule M) := by
  delta CharacterModule
  infer_instance

open Bimodule
instance : Module R (CharacterModule M) := by
  delta CharacterModule
  infer_instance

@[simps]
def CharacterModuleFunctor :
    (ModuleCat.{max u v} R)ᵒᵖ ⥤ ModuleCat.{max u v} R where
  obj M := ModuleCat.of R <| CharacterModule M.unop
  map {X Y} L :=
  { toFun := (. ∘ₗ L.unop.toAddMonoidHom.toIntLinearMap)
    map_add' := fun _ _ => LinearMap.ext fun _ => rfl
    map_smul' := fun _ _ => LinearMap.ext fun _ => by
      simp only [LinearMap.coe_comp, AddMonoidHom.coe_toIntLinearMap, LinearMap.toAddMonoidHom_coe,
        Function.comp_apply, RingHom.id_apply]
      rw [LinearMap.bimodule_smul_apply, LinearMap.bimodule_smul_apply, LinearMap.comp_apply]
      simp only [AddMonoidHom.coe_toIntLinearMap, LinearMap.toAddMonoidHom_coe, map_smul] }
  map_id {_} := LinearMap.ext fun _ => LinearMap.ext fun _ => rfl
  map_comp _ _ := LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

namespace CharacterModuleFunctor

lemma map_surjective_of_injective_unop {M N : (ModuleCat R)ᵒᵖ}
    (L : M ⟶ N) (hL : Function.Injective L.unop) :
    Function.Surjective <| (CharacterModuleFunctor R).map L := by
  rintro (g : _ →ₗ[_] _)
  let L' := AddCommGroupCat.ofHom L.unop.toAddMonoidHom
  have m1 : Mono <| L'
  · rw [AddCommGroupCat.mono_iff_injective]
    exact hL
  have : Fact ((0 : ℚ) < 1) := ⟨by norm_num⟩
  have i1 : Injective (AddCommGroupCat.of <| ULift <| AddCircle (1 : ℚ)) :=
    AddCommGroupCat.injective_of_divisible _
  let g' := AddCommGroupCat.ofHom
      (⟨⟨ULift.up, by intros; rfl⟩, by intros; rfl⟩ ∘ₗ g).toAddMonoidHom
  exact ⟨⟨⟨ULift.down, by intros; rfl⟩, by intros; rfl⟩ ∘ₗ
    (Injective.factorThru g' L').toIntLinearMap, LinearMap.ext fun _ => congr_arg ULift.down <|
      FunLike.congr_fun (Injective.comp_factorThru g' L') _⟩

end CharacterModuleFunctor

lemma exists_character_apply_ne_zero_of_ne_zero {m : M} (ne_zero : m ≠ 0) :
    ∃ (c : CharacterModule M), c m ≠ 0 := by
  let M' : Submodule ℤ M := ℤ ∙ m
  let L := AddCommGroupCat.ofHom
    (⟨⟨ULift.up, by intros; rfl⟩, by intros; rfl⟩ ∘ₗ
      AddCommGroupCat.enough_injectives_aux_proofs.toRatCircle
        (A_ := AddCommGroupCat.of M) (a := m)).toAddMonoidHom
  let ι : AddCommGroupCat.of M' ⟶ AddCommGroupCat.of M := (Submodule.subtype _).toAddMonoidHom
  have : Mono ι
  · rw [AddCommGroupCat.mono_iff_injective]
    exact Subtype.val_injective
  use ⟨⟨ULift.down, by intros; rfl⟩, by intros; rfl⟩ ∘ₗ (Injective.factorThru L ι).toIntLinearMap
  rw [LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
  -- rintro (r : _ = ULift.down _)
  -- rw [ULift.down_inj, AddMonoidHom.coe_toIntLinearMap] at r
  have eq1 := FunLike.congr_fun (Injective.comp_factorThru L ι)
    ⟨m, Submodule.mem_span_singleton_self _⟩
  simp only at eq1
  rw [comp_apply, AddCommGroupCat.ofHom_apply, LinearMap.toAddMonoidHom_coe,
    LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk,
    Submodule.subtype_apply, Subtype.coe_mk] at eq1
  have eq2 := (ULift.ext_iff _ _).mp eq1
  dsimp only at eq2
  erw [eq2]
  apply AddCommGroupCat.enough_injectives_aux_proofs.toRatCircle_apply_self_ne_zero
  assumption
