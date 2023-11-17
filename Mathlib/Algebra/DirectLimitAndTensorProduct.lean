import Mathlib.Algebra.DirectLimit

/-!
Tensor product and direct limits communicate with each other.

-/

open TensorProduct

universe u v w

variable {R : Type u} [CommRing R]
variable {ι : Type v}
variable [DecidableEq ι] [Preorder ι]
variable {G : ι → Type w}

namespace Module

variable [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]

variable (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)
variable (M : Type w) [AddCommGroup M] [Module R M]

/-- limᵢ (G i ⊗ M) -/
local notation "Lim_G_tensor" =>
  (DirectLimit (fun i => G i ⊗[R] M) <| fun i j h => TensorProduct.map (f _ _ h) LinearMap.id)

/-- lim G -/
local notation "Lim_G" => (DirectLimit G f)

noncomputable def directLimitOfTensorProductToTensorProductWithDirectLimit :
  Lim_G_tensor →ₗ[R] Lim_G ⊗[R] M :=
DirectLimit.lift _ _ _ _ (fun i => TensorProduct.map (DirectLimit.of _ _ _ _ _) LinearMap.id) <|
  fun i j h x => x.induction_on (by simp only [map_zero])
    (fun g m => by simp only [map_tmul, LinearMap.id_coe, id_eq, DirectLimit.of_f])
    (fun x y hx hy => by
      dsimp only at hx hy ⊢
      rw [map_add, map_add, hx, hy, map_add])

variable {M}
lemma directLimitOfTensorProductToTensorProductWithDirectLimit_apply_of_tmul
    {i : ι} (g : G i) (m : M) :
    directLimitOfTensorProductToTensorProductWithDirectLimit f M
      (DirectLimit.of _ _ _ _ i (g ⊗ₜ m) : Lim_G_tensor) =
    (DirectLimit.of _ _ _ _ i g : Lim_G) ⊗ₜ m := by
  dsimp only [directLimitOfTensorProductToTensorProductWithDirectLimit]
  rw [DirectLimit.lift_of (R := R) (ι := ι) (G := fun i => G i ⊗[R] M)
        (f := fun i j h => TensorProduct.map (f _ _ h) LinearMap.id) (i := i)
        (P := Lim_G ⊗[R] M) _ _ (g ⊗ₜ m)]
  rfl

variable (M)
noncomputable def tensorProductWithDirectLimitToDirectLimitOfTensorProduct :
  Lim_G ⊗[R] M →ₗ[R] Lim_G_tensor :=
TensorProduct.lift <| DirectLimit.lift _ _ _ _
  (fun i =>
    { toFun := fun g =>
      { toFun := fun m => DirectLimit.of R ι (fun i => G i ⊗[R] M)
          (fun i j h => TensorProduct.map (f _ _ h) LinearMap.id) i (g ⊗ₜ m)
        map_add' := fun _ _ => by dsimp only; rw [tmul_add, map_add]
        map_smul' := fun r x => by
          dsimp only
          rw [RingHom.id_apply, ← smul_tmul, ← smul_tmul', LinearMap.map_smul] }
      map_add' := fun _ _ => FunLike.ext _ _ fun _ => by
        dsimp only
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
        rw [add_tmul, map_add]
      map_smul' := fun _ _ => FunLike.ext _ _ fun _ => by
        dsimp only
        simp only [LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply]
        rw [← smul_tmul', LinearMap.map_smul] }) fun i j h g => FunLike.ext _ _ fun m =>
  DirectLimit.of_f (R := R) (ι := ι) (G := fun i => G i ⊗[R] M)
    (f := fun i j h => TensorProduct.map (f _ _ h) LinearMap.id) (i := i) (j := j) (hij := h)
    (x := g ⊗ₜ m)

variable {M}
lemma tensorProductWithDirectLimitToDirectLimitOfTensorProduct_apply_of_tmul
    {i : ι} (g : G i) (m : M) :
    (tensorProductWithDirectLimitToDirectLimitOfTensorProduct f M <|
      (DirectLimit.of _ _ _ _ i g : Lim_G) ⊗ₜ m)=
    (DirectLimit.of _ _ _ _ i (g ⊗ₜ m) : Lim_G_tensor) := by
  delta tensorProductWithDirectLimitToDirectLimitOfTensorProduct
  dsimp only
  simp only [lift.tmul]
  rw [DirectLimit.lift_of]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]

variable (M)

variable [IsDirected ι (. ≤ .)] [Nonempty ι]

set_option maxHeartbeats 800000 in
@[simps!]
noncomputable def directLimitCommutesTensorProduct :
    Lim_G_tensor ≃ₗ[R] Lim_G ⊗[R] M :=
  LinearEquiv.ofLinear
    (directLimitOfTensorProductToTensorProductWithDirectLimit f M)
    (tensorProductWithDirectLimitToDirectLimitOfTensorProduct f M)
    (TensorProduct.ext <| FunLike.ext _ _ fun g => FunLike.ext _ _ fun m => by
      dsimp only [LinearMap.compr₂_apply, mk_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.id_coe, id_eq]
      induction' g using DirectLimit.induction_on with i g
      rw [tensorProductWithDirectLimitToDirectLimitOfTensorProduct_apply_of_tmul,
        directLimitOfTensorProductToTensorProductWithDirectLimit_apply_of_tmul])
    (FunLike.ext _ _ fun x => DirectLimit.induction_on x fun i g => g.induction_on
      (by simp only [map_zero])
      (fun g m => by rw [LinearMap.comp_apply,
        directLimitOfTensorProductToTensorProductWithDirectLimit_apply_of_tmul f g m,
        tensorProductWithDirectLimitToDirectLimitOfTensorProduct_apply_of_tmul f g m,
        LinearMap.id_apply])
      (fun x y hx hy => by rw [map_add, map_add, hx, hy, map_add]))

section injective

universe u₁

variable {P : Type u₁} [AddCommGroup P] [Module R P] (g : ∀ i, G i →ₗ[R] P)
variable (compatible : ∀ i j hij x, g j (f i j hij x) = g i x)
variable (injective : ∀ i, Function.Injective <| g i)

variable (R ι G)

lemma DirectLimit.lift_inj :
  Function.Injective $ DirectLimit.lift R ι G f g compatible := by
  simp_rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff, LinearMap.mem_ker] at injective ⊢
  intros z hz
  induction' z using DirectLimit.induction_on with i gi
  rw [DirectLimit.lift_of] at hz
  specialize injective i gi hz
  rw [injective]
  simp only [map_zero]

end injective

end Module
