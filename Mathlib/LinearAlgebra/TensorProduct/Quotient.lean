import Mathlib.RingTheory.Ideal.Operations
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Quotient
import Mathlib.LinearAlgebra.Prod

namespace TensorProduct

variable {R M N : Type*} [CommRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

attribute [local ext high] ext LinearMap.prod_ext

noncomputable def quotientTensorQuotientEquiv (m : Submodule R M) (n : Submodule R N) :
    (M ⧸ (m : Submodule R M)) ⊗[R] (N ⧸ (n : Submodule R N)) ≃ₗ[R]
    (M ⊗[R] N) ⧸
      (LinearMap.range (map m.subtype LinearMap.id) ⊔
        LinearMap.range (map LinearMap.id n.subtype)) :=
  LinearEquiv.ofLinear
    (lift <| Submodule.liftQ _ (LinearMap.flip <| Submodule.liftQ _
      ((mk R (M := M) (N := N)).flip.compr₂ (Submodule.mkQ _)) fun x hx => by
      ext y
      simp only [LinearMap.compr₂_apply, LinearMap.flip_apply, mk_apply, Submodule.mkQ_apply,
        LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_sup_right ⟨y ⊗ₜ ⟨x, hx⟩, rfl⟩) fun x hx => by
      ext y
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearMap.flip_apply,
        Submodule.liftQ_apply, LinearMap.compr₂_apply, mk_apply, LinearMap.zero_comp,
        LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_sup_left ⟨⟨x, hx⟩ ⊗ₜ y, rfl⟩)
    (Submodule.liftQ _ (map (Submodule.mkQ _) (Submodule.mkQ _)) fun x hx => by
      rw [Submodule.mem_sup] at hx
      rcases hx with ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
      simp only [LinearMap.mem_ker, map_add]
      set f := (map m.mkQ n.mkQ) ∘ₗ (map m.subtype LinearMap.id)
      set g := (map m.mkQ n.mkQ) ∘ₗ (map LinearMap.id n.subtype)
      have eq : LinearMap.coprod f g = 0 := by
        ext x y
        · simp [f, Submodule.Quotient.mk_eq_zero _ |>.2 x.2]
        · simp [g, Submodule.Quotient.mk_eq_zero _ |>.2 y.2]
      exact congr($eq (a, b)))
    (by ext; simp) (by ext; simp)

@[simp]
lemma quotientTensorQuotientEquiv_apply_tmul_mk_tmul_mk
    (m : Submodule R M) (n : Submodule R N) (x : M) (y : N) :
    quotientTensorQuotientEquiv m n
      (Submodule.Quotient.mk x ⊗ₜ[R] Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (x ⊗ₜ y) := rfl

@[simp]
lemma quotientTensorQuotientEquiv_symm_apply_mk_tmul
    (m : Submodule R M) (n : Submodule R N) (x : M) (y : N) :
    (quotientTensorQuotientEquiv m n).symm (Submodule.Quotient.mk (x ⊗ₜ y)) =
      Submodule.Quotient.mk x ⊗ₜ[R] Submodule.Quotient.mk y := rfl

variable (N) in
noncomputable def quotientTensorEquiv (m : Submodule R M) :
    (M ⧸ (m : Submodule R M)) ⊗[R] N ≃ₗ[R]
    (M ⊗[R] N) ⧸ (LinearMap.range (map m.subtype (LinearMap.id : N →ₗ[R] N))) :=
  congr (LinearEquiv.refl _ _) ((Submodule.quotEquivOfEqBot _ rfl).symm) ≪≫ₗ
  quotientTensorQuotientEquiv (N := N) m ⊥ ≪≫ₗ
  Submodule.Quotient.equiv _ _ (LinearEquiv.refl _ _) (by
    simp only [Submodule.map_sup]
    erw [Submodule.map_id, Submodule.map_id]
    simp only [sup_eq_left]
    rw [map_range_eq_span_tmul, map_range_eq_span_tmul]
    aesop)

@[simp]
lemma quotientTensorEquiv_apply_tmul_mk (m : Submodule R M) (x : M) (y : N) :
    quotientTensorEquiv N m (Submodule.Quotient.mk x ⊗ₜ[R] y) =
    Submodule.Quotient.mk (x ⊗ₜ y) :=
  rfl

@[simp]
lemma quotientTensorEquiv_symm_apply_mk_tmul (m : Submodule R M) (x : M) (y : N) :
    (quotientTensorEquiv N m).symm (Submodule.Quotient.mk (x ⊗ₜ y)) =
    Submodule.Quotient.mk x ⊗ₜ[R] y :=
  rfl

variable (M) in
noncomputable def tensorQuotientEquiv (n : Submodule R N) :
    M ⊗[R] (N ⧸ (n : Submodule R N)) ≃ₗ[R]
    (M ⊗[R] N) ⧸ (LinearMap.range (map (LinearMap.id : M →ₗ[R] M) n.subtype)) :=
  congr ((Submodule.quotEquivOfEqBot _ rfl).symm) (LinearEquiv.refl _ _)  ≪≫ₗ
  quotientTensorQuotientEquiv (⊥ : Submodule R M) n ≪≫ₗ
  Submodule.Quotient.equiv _ _ (LinearEquiv.refl _ _) (by
    simp only [Submodule.map_sup]
    erw [Submodule.map_id, Submodule.map_id]
    simp only [sup_eq_right]
    rw [map_range_eq_span_tmul, map_range_eq_span_tmul]
    aesop)

@[simp]
lemma tensorQuotientEquiv_apply_mk_tmul (n : Submodule R N) (x : M) (y : N) :
    tensorQuotientEquiv M n (x ⊗ₜ[R] Submodule.Quotient.mk y) =
    Submodule.Quotient.mk (x ⊗ₜ y) :=
  rfl

@[simp]
lemma tensorQuotientEquiv_symm_apply_tmul_mk (n : Submodule R N) (x : M) (y : N) :
    (tensorQuotientEquiv M n).symm (Submodule.Quotient.mk (x ⊗ₜ y)) =
    x ⊗ₜ[R] Submodule.Quotient.mk y :=
  rfl

variable (M) in
noncomputable def quotientRingTensorEquiv (I : Ideal R) :
    ((R ⧸ I) ⊗[R] M) ≃ₗ[R] M ⧸ (I • (⊤ : Submodule R M)) :=
  quotientTensorEquiv M I ≪≫ₗ
  Submodule.Quotient.equiv (M := R ⊗[R] M) (N := M) (f := TensorProduct.lid R M) (hf := rfl) ≪≫ₗ
  Submodule.Quotient.equiv _ _ (LinearEquiv.refl R M) (by
    erw [Submodule.map_id]
    rw [TensorProduct.map_range_eq_span_tmul, Submodule.map_span]
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.map₂_le.2 ?_)
    · rintro _ ⟨_, ⟨r, m, rfl⟩, rfl⟩
      simp only [Submodule.coe_subtype, LinearMap.id_coe, id_eq, lid_tmul, SetLike.mem_coe]
      apply Submodule.apply_mem_map₂ <;> aesop
    · rintro r hr m -
      simp only [Submodule.coe_subtype, LinearMap.id_coe, id_eq, Subtype.exists, exists_prop,
        LinearMap.lsmul_apply]
      refine Submodule.subset_span ?_
      simp only [Set.mem_image, Set.mem_setOf_eq]
      exact ⟨r ⊗ₜ m, ⟨r, hr, m, rfl⟩, rfl⟩)

@[simp]
lemma quotientRingTensorEquiv_apply_mk_tmul (I : Ideal R) (r : R) (m : M) :
    quotientRingTensorEquiv M I (Submodule.Quotient.mk r ⊗ₜ[R] m) =
    Submodule.Quotient.mk (r • m) :=
  rfl

@[simp]
lemma quotientRingTensorEquiv_symm_apply_mk (I : Ideal R) (m : M) :
    (quotientRingTensorEquiv M I).symm (Submodule.Quotient.mk m) =
    Submodule.Quotient.mk 1 ⊗ₜ[R] m :=
  rfl

variable (M) in
noncomputable def tensorQuotientIdealEquiv (I : Ideal R) :
    (M ⊗[R] (R ⧸ I)) ≃ₗ[R] M ⧸ (I • (⊤ : Submodule R M)) :=
  TensorProduct.comm _ _ _ ≪≫ₗ quotientRingTensorEquiv M I

@[simp]
lemma tensorQuotientIdealEquiv_apply_tmul_mk (I : Ideal R) (m : M) (r : R) :
    tensorQuotientIdealEquiv M I (m ⊗ₜ[R] Submodule.Quotient.mk r) =
    Submodule.Quotient.mk (r • m) :=
  rfl

@[simp]
lemma tensorQuotientIdealEquiv_symm_apply_mk (I : Ideal R) (m : M) :
    (tensorQuotientIdealEquiv M I).symm (Submodule.Quotient.mk m) =
    m ⊗ₜ Submodule.Quotient.mk 1 :=
  rfl

end TensorProduct
