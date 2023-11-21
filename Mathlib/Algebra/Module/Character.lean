import Mathlib.Algebra.Category.GroupCat.Injective
import Mathlib.Topology.Instances.AddCircle
import Mathlib.Topology.Instances.Rat

open CategoryTheory

universe u v w w'

variable (R : Type u) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M]
variable (N : Type w) [AddCommGroup N] [Module R N]


def CharacterModule : Type w :=
M →ₗ[ℤ] (AddCircle (1 : ℚ))

instance : FunLike (CharacterModule M) M (fun _ => AddCircle (1 : ℚ)) where
  coe (f : M →ₗ[ℤ] (AddCircle (1 : ℚ))) m := f m
  coe_injective' _ _ h := LinearMap.ext fun _ => congr_fun h _

instance : AddMonoidHomClass (CharacterModule M) M (AddCircle (1 : ℚ)) where
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
@[simps] def LinearMap.characterfy {M N : Type w}
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (L : M →ₗ[R] N) : CharacterModule N →ₗ[R] CharacterModule M where
  toFun := (. ∘ₗ L.toAddMonoidHom.toIntLinearMap)
  map_add' _ _ := FunLike.ext _ _ fun _ => rfl
  map_smul' _ _ := FunLike.ext _ _ fun _ => by
    rw [RingHom.id_apply, CharacterModule.smul_apply, LinearMap.comp_apply,
      CharacterModule.smul_apply, LinearMap.comp_apply]
    simp only [AddMonoidHom.coe_toIntLinearMap, LinearMap.toAddMonoidHom_coe, map_smul]

lemma LinearMap.charaterfy_surjective_of_injective {M N : Type w}
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (L : M →ₗ[R] N) (inj : Function.Injective L) :
    Function.Surjective L.characterfy := by
  rintro (g : _ →ₗ[_] _)
  let L' := AddCommGroupCat.ofHom L.toAddMonoidHom
  have m1 : Mono <| L'
  · rw [AddCommGroupCat.mono_iff_injective]
    exact inj
  have : Fact ((0 : ℚ) < 1) := ⟨by norm_num⟩
  have i1 : Injective (AddCommGroupCat.of <| ULift <| AddCircle (1 : ℚ)) :=
    AddCommGroupCat.injective_of_divisible _
  let g' := AddCommGroupCat.ofHom
      (⟨⟨ULift.up, by intros; rfl⟩, by intros; rfl⟩ ∘ₗ g).toAddMonoidHom
  exact ⟨⟨⟨ULift.down, by intros; rfl⟩, by intros; rfl⟩ ∘ₗ
    (Injective.factorThru g' L').toIntLinearMap, LinearMap.ext fun _ => congr_arg ULift.down <|
      FunLike.congr_fun (Injective.comp_factorThru g' L') _⟩

variable (R)
@[simps]
def CharacterModuleFunctor :
    (ModuleCat.{max u v} R)ᵒᵖ ⥤ ModuleCat.{max u v} R where
  obj M := ModuleCat.of R <| CharacterModule M.unop
  map L := L.unop.characterfy
  map_id {_} := LinearMap.ext fun _ => LinearMap.ext fun _ => rfl
  map_comp _ _ := LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

namespace CharacterModuleFunctor

lemma map_surjective_of_injective_unop {M N : (ModuleCat R)ᵒᵖ}
    (L : M ⟶ N) (hL : Function.Injective L.unop) :
    Function.Surjective <| (CharacterModuleFunctor R).map L :=
  L.unop.charaterfy_surjective_of_injective hL

end CharacterModuleFunctor

lemma exists_character_apply_ne_zero_of_ne_zero {m : M} (ne_zero : m ≠ 0) :
    ∃ (c : CharacterModule M), c m ≠ 0 := by
  let L := AddCommGroupCat.ofHom
    (⟨⟨ULift.up, by aesop⟩, by aesop⟩ ∘ₗ
      AddCommGroupCat.enough_injectives_aux_proofs.toRatCircle
        (A_ := AddCommGroupCat.of M) (a := m)).toAddMonoidHom
  let ι : AddCommGroupCat.of (ℤ ∙ m) ⟶ AddCommGroupCat.of M :=
    AddCommGroupCat.ofHom (Submodule.subtype _).toAddMonoidHom
  have : Mono ι := (AddCommGroupCat.mono_iff_injective _).mpr Subtype.val_injective
  use ⟨⟨ULift.down, by aesop⟩, by aesop⟩ ∘ₗ (Injective.factorThru L ι).toIntLinearMap
  rw [LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
  erw [(ULift.ext_iff _ _).mp <| FunLike.congr_fun (Injective.comp_factorThru L ι)
    ⟨m, Submodule.mem_span_singleton_self _⟩]
  exact fun rid => (ne_zero <|
    AddCommGroupCat.enough_injectives_aux_proofs.eq_zero_of_toRatCircle_apply_self rid).elim

open TensorProduct

@[simps!]
noncomputable def CharacterModule.uncurry (f : N →ₗ[R] CharacterModule M) :
    CharacterModule (N ⊗[R] M) :=
  AddMonoidHom.toIntLinearMap <|
    TensorProduct.liftAddHom (⟨⟨(f ·), by aesop⟩,  by aesop⟩) fun r n m => by aesop

@[simps]
noncomputable def CharacterModule.curry (c : CharacterModule (N ⊗[R] M)):
    (N →ₗ[R] CharacterModule M) where
  toFun n := c ∘ₗ (TensorProduct.mk R N M n)
  map_add' _ _ := LinearMap.ext <| by aesop
  map_smul' r n := LinearMap.ext fun m => show c _ = c _ by aesop

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
    LinearEquiv.apply_symm_apply, LinearMap.id_coe, id_eq]
  aesop
