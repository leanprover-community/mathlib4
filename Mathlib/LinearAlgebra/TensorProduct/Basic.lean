/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro
-/
import Mathlib.Algebra.Module.Submodule.Bilinear
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.Tactic.Abel

/-!
# Basic properties of the tensor product of modules over commutative semirings.
-/

suppress_compilation

section Semiring

variable {R : Type*} [CommSemiring R]
variable {R' : Type*} [Monoid R']
variable {R'' : Type*} [Semiring R'']
variable {A M N P Q S T : Type*}
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
variable [AddCommMonoid Q] [AddCommMonoid S] [AddCommMonoid T]
variable [Module R M] [Module R N] [Module R Q] [Module R S] [Module R T]
variable [DistribMulAction R' M]
variable [Module R'' M]
variable (M N)

namespace TensorProduct

section Module

variable {M N}
variable [SMulCommClass R R' M] [SMulCommClass R R'' M]

theorem ite_tmul (x₁ : M) (x₂ : N) (P : Prop) [Decidable P] :
    (if P then x₁ else 0) ⊗ₜ[R] x₂ = if P then x₁ ⊗ₜ x₂ else 0 := by split_ifs <;> simp

theorem tmul_ite (x₁ : M) (x₂ : N) (P : Prop) [Decidable P] :
    (x₁ ⊗ₜ[R] if P then x₂ else 0) = if P then x₁ ⊗ₜ x₂ else 0 := by split_ifs <;> simp

lemma tmul_single {ι : Type*} [DecidableEq ι] {M : ι → Type*} [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)] (i : ι) (x : N) (m : M i) (j : ι) :
    x ⊗ₜ[R] Pi.single i m j = (Pi.single i (x ⊗ₜ[R] m) : ∀ i, N ⊗[R] M i) j := by
  by_cases h : i = j <;> aesop

lemma single_tmul {ι : Type*} [DecidableEq ι] {M : ι → Type*} [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)] (i : ι) (x : N) (m : M i) (j : ι) :
    Pi.single i m j ⊗ₜ[R] x = (Pi.single i (m ⊗ₜ[R] x) : ∀ i, M i ⊗[R] N) j := by
  by_cases h : i = j <;> aesop

section

theorem sum_tmul {α : Type*} (s : Finset α) (m : α → M) (n : N) :
    (∑ a ∈ s, m a) ⊗ₜ[R] n = ∑ a ∈ s, m a ⊗ₜ[R] n := by
  classical
    induction' s using Finset.induction with a s has ih h
    · simp
    · simp [Finset.sum_insert has, add_tmul, ih]

theorem tmul_sum (m : M) {α : Type*} (s : Finset α) (n : α → N) :
    (m ⊗ₜ[R] ∑ a ∈ s, n a) = ∑ a ∈ s, m ⊗ₜ[R] n a := by
  classical
    induction' s using Finset.induction with a s has ih h
    · simp
    · simp [Finset.sum_insert has, tmul_add, ih]

end

variable (R M N)

/-- The simple (aka pure) elements span the tensor product. -/
theorem span_tmul_eq_top : Submodule.span R { t : M ⊗[R] N | ∃ m n, m ⊗ₜ n = t } = ⊤ := by
  ext t; simp only [Submodule.mem_top, iff_true]
  refine t.induction_on ?_ ?_ ?_
  · exact Submodule.zero_mem _
  · intro m n
    apply Submodule.subset_span
    use m, n
  · intro t₁ t₂ ht₁ ht₂
    exact Submodule.add_mem _ ht₁ ht₂

@[simp]
theorem map₂_mk_top_top_eq_top : Submodule.map₂ (mk R M N) ⊤ ⊤ = ⊤ := by
  rw [← top_le_iff, ← span_tmul_eq_top, Submodule.map₂_eq_span_image2]
  exact Submodule.span_mono fun _ ⟨m, n, h⟩ => ⟨m, trivial, n, trivial, h⟩

theorem exists_eq_tmul_of_forall (x : TensorProduct R M N)
    (h : ∀ (m₁ m₂ : M) (n₁ n₂ : N), ∃ m n, m₁ ⊗ₜ n₁ + m₂ ⊗ₜ n₂ = m ⊗ₜ[R] n) :
    ∃ m n, x = m ⊗ₜ n := by
  induction x with
  | zero =>
    use 0, 0
    rw [TensorProduct.zero_tmul]
  | tmul m n => use m, n
  | add x y h₁ h₂ =>
    obtain ⟨m₁, n₁, rfl⟩ := h₁
    obtain ⟨m₂, n₂, rfl⟩ := h₂
    apply h

end Module

variable [Module R P]

section UMP

variable {M N}
variable {f : M →ₗ[R] N →ₗ[R] P}

attribute [local ext high] ext

example : M → N → (M → N → P) → P := fun m => flip fun f => f m

variable (R M N P)

@[simp]
theorem lift.equiv_apply (f : M →ₗ[R] N →ₗ[R] P) (m : M) (n : N) :
    lift.equiv R M N P f (m ⊗ₜ n) = f m n :=
  uncurry_apply f m n

@[simp]
theorem lift.equiv_symm_apply (f : M ⊗[R] N →ₗ[R] P) (m : M) (n : N) :
    (lift.equiv R M N P).symm f m n = f (m ⊗ₜ n) :=
  rfl

variable {R M N P}

theorem curry_injective : Function.Injective (curry : (M ⊗[R] N →ₗ[R] P) → M →ₗ[R] N →ₗ[R] P) :=
  fun _ _ H => ext H

theorem ext_threefold {g h : (M ⊗[R] N) ⊗[R] P →ₗ[R] Q}
    (H : ∀ x y z, g (x ⊗ₜ y ⊗ₜ z) = h (x ⊗ₜ y ⊗ₜ z)) : g = h := by
  ext x y z
  exact H x y z

@[deprecated (since := "2024-10-18")] alias ext₃ := ext_threefold

-- We'll need this one for checking the pentagon identity!
theorem ext_fourfold {g h : ((M ⊗[R] N) ⊗[R] P) ⊗[R] Q →ₗ[R] S}
    (H : ∀ w x y z, g (w ⊗ₜ x ⊗ₜ y ⊗ₜ z) = h (w ⊗ₜ x ⊗ₜ y ⊗ₜ z)) : g = h := by
  ext w x y z
  exact H w x y z

/-- Two linear maps (M ⊗ N) ⊗ (P ⊗ Q) → S which agree on all elements of the
form (m ⊗ₜ n) ⊗ₜ (p ⊗ₜ q) are equal. -/
theorem ext_fourfold' {φ ψ : (M ⊗[R] N) ⊗[R] P ⊗[R] Q →ₗ[R] S}
    (H : ∀ w x y z, φ (w ⊗ₜ x ⊗ₜ (y ⊗ₜ z)) = ψ (w ⊗ₜ x ⊗ₜ (y ⊗ₜ z))) : φ = ψ := by
  ext m n p q
  exact H m n p q

end UMP

variable {M N}

@[simp]
theorem lid_tmul (m : M) (r : R) : (TensorProduct.lid R M : R ⊗ M → M) (r ⊗ₜ m) = r • m :=
  rfl

@[simp]
theorem lid_symm_apply (m : M) : (TensorProduct.lid R M).symm m = 1 ⊗ₜ m :=
  rfl

section

variable (R M N)

@[simp]
theorem comm_tmul (m : M) (n : N) : (TensorProduct.comm R M N) (m ⊗ₜ n) = n ⊗ₜ m :=
  rfl

@[simp]
theorem comm_symm_tmul (m : M) (n : N) : (TensorProduct.comm R M N).symm (n ⊗ₜ m) = m ⊗ₜ n :=
  rfl

lemma lift_comp_comm_eq (f : M →ₗ[R] N →ₗ[R] P) :
    lift f ∘ₗ TensorProduct.comm R N M = lift f.flip :=
  ext rfl
end

@[simp]
theorem rid_tmul (m : M) (r : R) : (TensorProduct.rid R M) (m ⊗ₜ r) = r • m :=
  rfl

@[simp]
theorem rid_symm_apply (m : M) : (TensorProduct.rid R M).symm m = m ⊗ₜ 1 :=
  rfl

variable (R) in
theorem lid_eq_rid : TensorProduct.lid R R = TensorProduct.rid R R :=
  LinearEquiv.toLinearMap_injective <| ext' mul_comm

section CompatibleSMul

variable (R A M N) [CommSemiring A] [Module A M] [Module A N] [SMulCommClass R A M]
  [CompatibleSMul R A M N]

theorem mapOfCompatibleSMul_surjective : Function.Surjective (mapOfCompatibleSMul R A M N) :=
  fun x ↦ x.induction_on (⟨0, map_zero _⟩) (fun m n ↦ ⟨_, mapOfCompatibleSMul_tmul ..⟩)
    fun _ _ ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x + y, by simpa using congr($hx + $hy)⟩

omit [SMulCommClass R A M]

variable [Module R A] [SMulCommClass R A A] [CompatibleSMul R A A M] [CompatibleSMul A R A M]

theorem lidOfCompatibleSMul_tmul (a m) : lidOfCompatibleSMul R A M (a ⊗ₜ[R] m) = a • m := rfl

end CompatibleSMul

open LinearMap

@[simp]
theorem assoc_tmul (m : M) (n : N) (p : P) :
    (TensorProduct.assoc R M N P) (m ⊗ₜ n ⊗ₜ p) = m ⊗ₜ (n ⊗ₜ p) :=
  rfl

@[simp]
theorem assoc_symm_tmul (m : M) (n : N) (p : P) :
    (TensorProduct.assoc R M N P).symm (m ⊗ₜ (n ⊗ₜ p)) = m ⊗ₜ n ⊗ₜ p :=
  rfl

/-- Given linear maps `f : M → P`, `g : N → Q`, if we identify `M ⊗ N` with `N ⊗ M` and `P ⊗ Q`
with `Q ⊗ P`, then this lemma states that `f ⊗ g = g ⊗ f`. -/
lemma map_comp_comm_eq (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    map f g ∘ₗ TensorProduct.comm R N M = TensorProduct.comm R Q P ∘ₗ map g f :=
  ext rfl

lemma map_comm (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (x : N ⊗[R] M) :
    map f g (TensorProduct.comm R N M x) = TensorProduct.comm R Q P (map g f x) :=
  DFunLike.congr_fun (map_comp_comm_eq _ _) _

/-- Given linear maps `f : M → Q`, `g : N → S`, and `h : P → T`, if we identify `(M ⊗ N) ⊗ P`
with `M ⊗ (N ⊗ P)` and `(Q ⊗ S) ⊗ T` with `Q ⊗ (S ⊗ T)`, then this lemma states that
`f ⊗ (g ⊗ h) = (f ⊗ g) ⊗ h`. -/
lemma map_map_comp_assoc_eq (f : M →ₗ[R] Q) (g : N →ₗ[R] S) (h : P →ₗ[R] T) :
    map f (map g h) ∘ₗ TensorProduct.assoc R M N P =
      TensorProduct.assoc R Q S T ∘ₗ map (map f g) h :=
  ext <| ext <| LinearMap.ext fun _ => LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

lemma map_map_assoc (f : M →ₗ[R] Q) (g : N →ₗ[R] S) (h : P →ₗ[R] T) (x : (M ⊗[R] N) ⊗[R] P) :
    map f (map g h) (TensorProduct.assoc R M N P x) =
      TensorProduct.assoc R Q S T (map (map f g) h x) :=
  DFunLike.congr_fun (map_map_comp_assoc_eq _ _ _) _

/-- Given linear maps `f : M → Q`, `g : N → S`, and `h : P → T`, if we identify `M ⊗ (N ⊗ P)`
with `(M ⊗ N) ⊗ P` and `Q ⊗ (S ⊗ T)` with `(Q ⊗ S) ⊗ T`, then this lemma states that
`(f ⊗ g) ⊗ h = f ⊗ (g ⊗ h)`. -/
lemma map_map_comp_assoc_symm_eq (f : M →ₗ[R] Q) (g : N →ₗ[R] S) (h : P →ₗ[R] T) :
    map (map f g) h ∘ₗ (TensorProduct.assoc R M N P).symm =
      (TensorProduct.assoc R Q S T).symm ∘ₗ map f (map g h) :=
  ext <| LinearMap.ext fun _ => ext <| LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

lemma map_map_assoc_symm (f : M →ₗ[R] Q) (g : N →ₗ[R] S) (h : P →ₗ[R] T) (x : M ⊗[R] (N ⊗[R] P)) :
    map (map f g) h ((TensorProduct.assoc R M N P).symm x) =
      (TensorProduct.assoc R Q S T).symm (map f (map g h) x) :=
  DFunLike.congr_fun (map_map_comp_assoc_symm_eq _ _ _) _

theorem map_range_eq_span_tmul (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    range (map f g) = Submodule.span R { t | ∃ m n, f m ⊗ₜ g n = t } := by
  simp only [← Submodule.map_top, ← span_tmul_eq_top, Submodule.map_span, Set.mem_image,
    Set.mem_setOf_eq]
  congr; ext t
  constructor
  · rintro ⟨_, ⟨⟨m, n, rfl⟩, rfl⟩⟩
    use m, n
    simp only [map_tmul]
  · rintro ⟨m, n, rfl⟩
    refine ⟨_, ⟨⟨m, n, rfl⟩, ?_⟩⟩
    simp only [map_tmul]

lemma range_mapIncl (p : Submodule R P) (q : Submodule R Q) :
    LinearMap.range (mapIncl p q) = Submodule.span R (Set.image2 (· ⊗ₜ ·) p q) := by
  rw [mapIncl, map_range_eq_span_tmul]
  congr; ext; simp

theorem map₂_eq_range_lift_comp_mapIncl (f : P →ₗ[R] Q →ₗ[R] M)
    (p : Submodule R P) (q : Submodule R Q) :
    Submodule.map₂ f p q = LinearMap.range (lift f ∘ₗ mapIncl p q) := by
  simp_rw [LinearMap.range_comp, range_mapIncl, Submodule.map_span,
    Set.image_image2, Submodule.map₂_eq_span_image2, lift.tmul]

section

variable {P' Q' : Type*}
variable [AddCommMonoid P'] [Module R P']
variable [AddCommMonoid Q'] [Module R Q']

theorem map_comp (f₂ : P →ₗ[R] P') (f₁ : M →ₗ[R] P) (g₂ : Q →ₗ[R] Q') (g₁ : N →ₗ[R] Q) :
    map (f₂.comp f₁) (g₂.comp g₁) = (map f₂ g₂).comp (map f₁ g₁) :=
  ext' fun _ _ => rfl

lemma range_mapIncl_mono {p p' : Submodule R P} {q q' : Submodule R Q} (hp : p ≤ p') (hq : q ≤ q') :
    LinearMap.range (mapIncl p q) ≤ LinearMap.range (mapIncl p' q') := by
  simp_rw [range_mapIncl]
  exact Submodule.span_mono (Set.image2_subset hp hq)

theorem lift_comp_map (i : P →ₗ[R] Q →ₗ[R] Q') (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    (lift i).comp (map f g) = lift ((i.comp f).compl₂ g) :=
  ext' fun _ _ => rfl

attribute [local ext high] ext

@[simp]
theorem map_id : map (id : M →ₗ[R] M) (id : N →ₗ[R] N) = .id := by
  ext
  simp only [mk_apply, id_coe, compr₂_apply, _root_.id, map_tmul]

@[simp]
protected theorem map_one : map (1 : M →ₗ[R] M) (1 : N →ₗ[R] N) = 1 :=
  map_id

protected theorem map_mul (f₁ f₂ : M →ₗ[R] M) (g₁ g₂ : N →ₗ[R] N) :
    map (f₁ * f₂) (g₁ * g₂) = map f₁ g₁ * map f₂ g₂ :=
  map_comp f₁ f₂ g₁ g₂

@[simp]
protected theorem map_pow (f : M →ₗ[R] M) (g : N →ₗ[R] N) (n : ℕ) :
    map f g ^ n = map (f ^ n) (g ^ n) := by
  induction n with
  | zero => simp only [pow_zero, TensorProduct.map_one]
  | succ n ih => simp only [pow_succ', ih, TensorProduct.map_mul]

@[simp]
theorem mapBilinear_apply (f : M →ₗ[R] P) (g : N →ₗ[R] Q) : mapBilinear R M N P Q f g = map f g :=
  rfl

@[simp]
theorem lTensorHomToHomLTensor_apply (p : P) (f : M →ₗ[R] Q) (m : M) :
    lTensorHomToHomLTensor R M P Q (p ⊗ₜ f) m = p ⊗ₜ f m :=
  rfl

@[simp]
theorem rTensorHomToHomRTensor_apply (f : M →ₗ[R] P) (q : Q) (m : M) :
    rTensorHomToHomRTensor R M P Q (f ⊗ₜ q) m = f m ⊗ₜ q :=
  rfl

@[simp]
theorem homTensorHomMap_apply (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    homTensorHomMap R M N P Q (f ⊗ₜ g) = map f g :=
  rfl

@[simp]
theorem map₂_apply_tmul (f : M →ₗ[R] P →ₗ[R] Q) (g : N →ₗ[R] S →ₗ[R] T) (m : M) (n : N) :
    map₂ f g (m ⊗ₜ n) = map (f m) (g n) := rfl

@[simp]
theorem map_zero_left (g : N →ₗ[R] Q) : map (0 : M →ₗ[R] P) g = 0 :=
  (mapBilinear R M N P Q).map_zero₂ _

@[simp]
theorem map_zero_right (f : M →ₗ[R] P) : map f (0 : N →ₗ[R] Q) = 0 :=
  (mapBilinear R M N P Q _).map_zero

end

@[simp]
theorem congr_tmul (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) (m : M) (n : N) :
    congr f g (m ⊗ₜ n) = f m ⊗ₜ g n :=
  rfl

@[simp]
theorem congr_symm_tmul (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) (p : P) (q : Q) :
    (congr f g).symm (p ⊗ₜ q) = f.symm p ⊗ₜ g.symm q :=
  rfl

theorem congr_symm (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) : (congr f g).symm = congr f.symm g.symm := rfl

@[simp] theorem congr_refl_refl : congr (.refl R M) (.refl R N) = .refl R _ :=
  LinearEquiv.toLinearMap_injective <| ext' fun _ _ ↦ rfl

theorem congr_trans (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) (f' : P ≃ₗ[R] S) (g' : Q ≃ₗ[R] T) :
    congr (f ≪≫ₗ f') (g ≪≫ₗ g') = congr f g ≪≫ₗ congr f' g' :=
  LinearEquiv.toLinearMap_injective <| map_comp _ _ _ _

theorem congr_mul (f : M ≃ₗ[R] M) (g : N ≃ₗ[R] N) (f' : M ≃ₗ[R] M) (g' : N ≃ₗ[R] N) :
    congr (f * f') (g * g') = congr f g * congr f' g' := congr_trans _ _ _ _

@[simp] theorem congr_pow (f : M ≃ₗ[R] M) (g : N ≃ₗ[R] N) (n : ℕ) :
    congr f g ^ n = congr (f ^ n) (g ^ n) := by
  induction n with
  | zero => exact congr_refl_refl.symm
  | succ n ih => simp_rw [pow_succ, ih, congr_mul]

@[simp] theorem congr_zpow (f : M ≃ₗ[R] M) (g : N ≃ₗ[R] N) (n : ℤ) :
    congr f g ^ n = congr (f ^ n) (g ^ n) := by
  induction n with
  | ofNat n => exact congr_pow _ _ _
  | negSucc n => simp_rw [zpow_negSucc, congr_pow]; exact congr_symm _ _

variable (R)

@[simp]
theorem leftComm_tmul (m : M) (n : N) (p : P) : leftComm R M N P (m ⊗ₜ (n ⊗ₜ p)) = n ⊗ₜ (m ⊗ₜ p) :=
  rfl

@[simp]
theorem leftComm_symm_tmul (m : M) (n : N) (p : P) :
    (leftComm R M N P).symm (n ⊗ₜ (m ⊗ₜ p)) = m ⊗ₜ (n ⊗ₜ p) :=
  rfl

@[simp]
theorem tensorTensorTensorComm_tmul (m : M) (n : N) (p : P) (q : Q) :
    tensorTensorTensorComm R M N P Q (m ⊗ₜ n ⊗ₜ (p ⊗ₜ q)) = m ⊗ₜ p ⊗ₜ (n ⊗ₜ q) :=
  rfl

-- Porting note: the proof here was `rfl` but that caused a timeout.
@[simp]
theorem tensorTensorTensorComm_symm :
    (tensorTensorTensorComm R M N P Q).symm = tensorTensorTensorComm R M P N Q := by
  ext; rfl

@[simp]
theorem tensorTensorTensorAssoc_tmul (m : M) (n : N) (p : P) (q : Q) :
    tensorTensorTensorAssoc R M N P Q (m ⊗ₜ n ⊗ₜ (p ⊗ₜ q)) = m ⊗ₜ (n ⊗ₜ p) ⊗ₜ q :=
  rfl

@[simp]
theorem tensorTensorTensorAssoc_symm_tmul (m : M) (n : N) (p : P) (q : Q) :
    (tensorTensorTensorAssoc R M N P Q).symm (m ⊗ₜ (n ⊗ₜ p) ⊗ₜ q) = m ⊗ₜ n ⊗ₜ (p ⊗ₜ q) :=
  rfl

end TensorProduct

open scoped TensorProduct

variable [Module R P]

namespace LinearMap

variable {N}

variable (g : P →ₗ[R] Q) (f : N →ₗ[R] P)

@[simp]
theorem lTensor_comp_mk (m : M) :
    f.lTensor M ∘ₗ TensorProduct.mk R M N m = TensorProduct.mk R M P m ∘ₗ f :=
  rfl

@[simp]
theorem rTensor_comp_flip_mk (m : M) :
    f.rTensor M ∘ₗ (TensorProduct.mk R N M).flip m = (TensorProduct.mk R P M).flip m ∘ₗ f :=
  rfl

lemma comm_comp_rTensor_comp_comm_eq (g : N →ₗ[R] P) :
    TensorProduct.comm R P Q ∘ₗ rTensor Q g ∘ₗ TensorProduct.comm R Q N =
      lTensor Q g :=
  TensorProduct.ext rfl

theorem rTensor_tensor : rTensor (M ⊗[R] N) g =
    TensorProduct.assoc R Q M N ∘ₗ rTensor N (rTensor M g) ∘ₗ (TensorProduct.assoc R P M N).symm :=
  TensorProduct.ext <| LinearMap.ext fun _ ↦ TensorProduct.ext rfl

lemma comm_comp_lTensor_comp_comm_eq (g : N →ₗ[R] P) :
    TensorProduct.comm R Q P ∘ₗ lTensor Q g ∘ₗ TensorProduct.comm R N Q =
      rTensor Q g :=
  TensorProduct.ext rfl

/-- Given a linear map `f : N → P`, `f ⊗ M` is injective if and only if `M ⊗ f` is injective. -/
theorem lTensor_inj_iff_rTensor_inj :
    Function.Injective (lTensor M f) ↔ Function.Injective (rTensor M f) := by
  simp [← comm_comp_rTensor_comp_comm_eq]

/-- Given a linear map `f : N → P`, `f ⊗ M` is surjective if and only if `M ⊗ f` is surjective. -/
theorem lTensor_surj_iff_rTensor_surj :
    Function.Surjective (lTensor M f) ↔ Function.Surjective (rTensor M f) := by
  simp [← comm_comp_rTensor_comp_comm_eq]

/-- Given a linear map `f : N → P`, `f ⊗ M` is bijective if and only if `M ⊗ f` is bijective. -/
theorem lTensor_bij_iff_rTensor_bij :
    Function.Bijective (lTensor M f) ↔ Function.Bijective (rTensor M f) := by
  simp [← comm_comp_rTensor_comp_comm_eq]

open TensorProduct

attribute [local ext high] TensorProduct.ext

@[simp]
theorem coe_lTensorHom : (lTensorHom M : (N →ₗ[R] P) → M ⊗[R] N →ₗ[R] M ⊗[R] P) = lTensor M :=
  rfl

@[simp]
theorem coe_rTensorHom : (rTensorHom M : (N →ₗ[R] P) → N ⊗[R] M →ₗ[R] P ⊗[R] M) = rTensor M :=
  rfl

@[simp]
theorem lTensor_add (f g : N →ₗ[R] P) : (f + g).lTensor M = f.lTensor M + g.lTensor M :=
  (lTensorHom M).map_add f g

@[simp]
theorem rTensor_add (f g : N →ₗ[R] P) : (f + g).rTensor M = f.rTensor M + g.rTensor M :=
  (rTensorHom M).map_add f g

@[simp]
theorem lTensor_zero : lTensor M (0 : N →ₗ[R] P) = 0 :=
  (lTensorHom M).map_zero

@[simp]
theorem rTensor_zero : rTensor M (0 : N →ₗ[R] P) = 0 :=
  (rTensorHom M).map_zero

@[simp]
theorem lTensor_smul (r : R) (f : N →ₗ[R] P) : (r • f).lTensor M = r • f.lTensor M :=
  (lTensorHom M).map_smul r f

@[simp]
theorem rTensor_smul (r : R) (f : N →ₗ[R] P) : (r • f).rTensor M = r • f.rTensor M :=
  (rTensorHom M).map_smul r f

theorem lTensor_comp : (g.comp f).lTensor M = (g.lTensor M).comp (f.lTensor M) := by
  ext m n
  simp only [compr₂_apply, mk_apply, comp_apply, lTensor_tmul]

theorem lTensor_comp_apply (x : M ⊗[R] N) :
    (g.comp f).lTensor M x = (g.lTensor M) ((f.lTensor M) x) := by rw [lTensor_comp, coe_comp]; rfl

theorem rTensor_comp : (g.comp f).rTensor M = (g.rTensor M).comp (f.rTensor M) := by
  ext m n
  simp only [compr₂_apply, mk_apply, comp_apply, rTensor_tmul]

theorem rTensor_comp_apply (x : N ⊗[R] M) :
    (g.comp f).rTensor M x = (g.rTensor M) ((f.rTensor M) x) := by rw [rTensor_comp, coe_comp]; rfl

theorem lTensor_mul (f g : Module.End R N) : (f * g).lTensor M = f.lTensor M * g.lTensor M :=
  lTensor_comp M f g

theorem rTensor_mul (f g : Module.End R N) : (f * g).rTensor M = f.rTensor M * g.rTensor M :=
  rTensor_comp M f g

variable (N)

@[simp]
theorem lTensor_id : (id : N →ₗ[R] N).lTensor M = id :=
  map_id

-- `simp` can prove this.
theorem lTensor_id_apply (x : M ⊗[R] N) : (LinearMap.id : N →ₗ[R] N).lTensor M x = x := by
  rw [lTensor_id, id_coe, _root_.id]

@[simp]
theorem rTensor_id : (id : N →ₗ[R] N).rTensor M = id :=
  map_id

-- `simp` can prove this.
theorem rTensor_id_apply (x : N ⊗[R] M) : (LinearMap.id : N →ₗ[R] N).rTensor M x = x := by
  rw [rTensor_id, id_coe, _root_.id]

@[simp]
theorem lTensor_smul_action (r : R) :
    (DistribMulAction.toLinearMap R N r).lTensor M =
      DistribMulAction.toLinearMap R (M ⊗[R] N) r :=
  (lTensor_smul M r LinearMap.id).trans (congrArg _ (lTensor_id M N))

@[simp]
theorem rTensor_smul_action (r : R) :
    (DistribMulAction.toLinearMap R N r).rTensor M =
      DistribMulAction.toLinearMap R (N ⊗[R] M) r :=
  (rTensor_smul M r LinearMap.id).trans (congrArg _ (rTensor_id M N))

variable {N}

theorem lid_comp_rTensor (f : N →ₗ[R] R) :
    (TensorProduct.lid R M).comp (rTensor M f) = lift ((lsmul R M).comp f) := ext' fun _ _ ↦ rfl

@[simp]
theorem lTensor_comp_rTensor (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    (g.lTensor P).comp (f.rTensor N) = map f g := by
  simp only [lTensor, rTensor, ← map_comp, id_comp, comp_id]

@[simp]
theorem rTensor_comp_lTensor (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    (f.rTensor Q).comp (g.lTensor M) = map f g := by
  simp only [lTensor, rTensor, ← map_comp, id_comp, comp_id]

@[simp]
theorem map_comp_rTensor (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (f' : S →ₗ[R] M) :
    (map f g).comp (f'.rTensor _) = map (f.comp f') g := by
  simp only [lTensor, rTensor, ← map_comp, id_comp, comp_id]

@[simp]
theorem map_comp_lTensor (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (g' : S →ₗ[R] N) :
    (map f g).comp (g'.lTensor _) = map f (g.comp g') := by
  simp only [lTensor, rTensor, ← map_comp, id_comp, comp_id]

@[simp]
theorem rTensor_comp_map (f' : P →ₗ[R] S) (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    (f'.rTensor _).comp (map f g) = map (f'.comp f) g := by
  simp only [lTensor, rTensor, ← map_comp, id_comp, comp_id]

@[simp]
theorem lTensor_comp_map (g' : Q →ₗ[R] S) (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    (g'.lTensor _).comp (map f g) = map f (g'.comp g) := by
  simp only [lTensor, rTensor, ← map_comp, id_comp, comp_id]

variable {M}

@[simp]
theorem rTensor_pow (f : M →ₗ[R] M) (n : ℕ) : f.rTensor N ^ n = (f ^ n).rTensor N := by
  have h := TensorProduct.map_pow f (id : N →ₗ[R] N) n
  rwa [id_pow] at h

@[simp]
theorem lTensor_pow (f : N →ₗ[R] N) (n : ℕ) : f.lTensor M ^ n = (f ^ n).lTensor M := by
  have h := TensorProduct.map_pow (id : M →ₗ[R] M) f n
  rwa [id_pow] at h

end LinearMap

namespace LinearEquiv

variable {N}

/-- `LinearEquiv.lTensor M f : M ⊗ N ≃ₗ M ⊗ P` is the natural linear equivalence
induced by `f : N ≃ₗ P`. -/
def lTensor (f : N ≃ₗ[R] P) : M ⊗[R] N ≃ₗ[R] M ⊗[R] P := TensorProduct.congr (refl R M) f

/-- `LinearEquiv.rTensor M f : N₁ ⊗ M ≃ₗ N₂ ⊗ M` is the natural linear equivalence
induced by `f : N₁ ≃ₗ N₂`. -/
def rTensor (f : N ≃ₗ[R] P) : N ⊗[R] M ≃ₗ[R] P ⊗[R] M := TensorProduct.congr f (refl R M)

variable (g : P ≃ₗ[R] Q) (f : N ≃ₗ[R] P) (m : M) (n : N) (p : P) (x : M ⊗[R] N) (y : N ⊗[R] M)

@[simp] theorem coe_lTensor : lTensor M f = (f : N →ₗ[R] P).lTensor M := rfl

@[simp] theorem coe_lTensor_symm : (lTensor M f).symm = (f.symm : P →ₗ[R] N).lTensor M := rfl

@[simp] theorem coe_rTensor : rTensor M f = (f : N →ₗ[R] P).rTensor M := rfl

@[simp] theorem coe_rTensor_symm : (rTensor M f).symm = (f.symm : P →ₗ[R] N).rTensor M := rfl

@[simp] theorem lTensor_tmul : f.lTensor M (m ⊗ₜ n) = m ⊗ₜ f n := rfl

@[simp] theorem lTensor_symm_tmul : (f.lTensor M).symm (m ⊗ₜ p) = m ⊗ₜ f.symm p := rfl

@[simp] theorem rTensor_tmul : f.rTensor M (n ⊗ₜ m) = f n ⊗ₜ m := rfl

@[simp] theorem rTensor_symm_tmul : (f.rTensor M).symm (p ⊗ₜ m) = f.symm p ⊗ₜ m := rfl

lemma comm_trans_rTensor_trans_comm_eq (g : N ≃ₗ[R] P) :
    TensorProduct.comm R Q N ≪≫ₗ rTensor Q g ≪≫ₗ TensorProduct.comm R P Q = lTensor Q g :=
  toLinearMap_injective <| TensorProduct.ext rfl

lemma comm_trans_lTensor_trans_comm_eq (g : N ≃ₗ[R] P) :
    TensorProduct.comm R N Q ≪≫ₗ lTensor Q g ≪≫ₗ TensorProduct.comm R Q P = rTensor Q g :=
  toLinearMap_injective <| TensorProduct.ext rfl

theorem lTensor_trans : (f ≪≫ₗ g).lTensor M = f.lTensor M ≪≫ₗ g.lTensor M :=
  toLinearMap_injective <| LinearMap.lTensor_comp M _ _

theorem lTensor_trans_apply : (f ≪≫ₗ g).lTensor M x = g.lTensor M (f.lTensor M x) :=
  LinearMap.lTensor_comp_apply M _ _ x

theorem rTensor_trans : (f ≪≫ₗ g).rTensor M = f.rTensor M ≪≫ₗ g.rTensor M :=
  toLinearMap_injective <| LinearMap.rTensor_comp M _ _

theorem rTensor_trans_apply : (f ≪≫ₗ g).rTensor M y = g.rTensor M (f.rTensor M y) :=
  LinearMap.rTensor_comp_apply M _ _ y

theorem lTensor_mul (f g : N ≃ₗ[R] N) : (f * g).lTensor M = f.lTensor M * g.lTensor M :=
  lTensor_trans M f g

theorem rTensor_mul (f g : N ≃ₗ[R] N) : (f * g).rTensor M = f.rTensor M * g.rTensor M :=
  rTensor_trans M f g

variable (N)

@[simp] theorem lTensor_refl : (refl R N).lTensor M = refl R _ := TensorProduct.congr_refl_refl

theorem lTensor_refl_apply : (refl R N).lTensor M x = x := by rw [lTensor_refl, refl_apply]

@[simp] theorem rTensor_refl : (refl R N).rTensor M = refl R _ := TensorProduct.congr_refl_refl

theorem rTensor_refl_apply : (refl R N).rTensor M y = y := by rw [rTensor_refl, refl_apply]

variable {N}

@[simp] theorem rTensor_trans_lTensor (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) :
    f.rTensor N ≪≫ₗ g.lTensor P = TensorProduct.congr f g :=
  toLinearMap_injective <| LinearMap.lTensor_comp_rTensor M _ _

@[simp] theorem lTensor_trans_rTensor (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) :
    g.lTensor M ≪≫ₗ f.rTensor Q = TensorProduct.congr f g :=
  toLinearMap_injective <| LinearMap.rTensor_comp_lTensor M _ _

@[simp] theorem rTensor_trans_congr (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) (f' : S ≃ₗ[R] M) :
    f'.rTensor _ ≪≫ₗ TensorProduct.congr f g = TensorProduct.congr (f' ≪≫ₗ f) g :=
  toLinearMap_injective <| LinearMap.map_comp_rTensor M _ _ _

@[simp] theorem lTensor_trans_congr (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) (g' : S ≃ₗ[R] N) :
    g'.lTensor _ ≪≫ₗ TensorProduct.congr f g = TensorProduct.congr f (g' ≪≫ₗ g) :=
  toLinearMap_injective <| LinearMap.map_comp_lTensor M _ _ _

@[simp] theorem congr_trans_rTensor (f' : P ≃ₗ[R] S) (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) :
    TensorProduct.congr f g ≪≫ₗ f'.rTensor _ = TensorProduct.congr (f ≪≫ₗ f') g :=
  toLinearMap_injective <| LinearMap.rTensor_comp_map M _ _ _

@[simp] theorem congr_trans_lTensor (g' : Q ≃ₗ[R] S) (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) :
    TensorProduct.congr f g ≪≫ₗ g'.lTensor _ = TensorProduct.congr f (g ≪≫ₗ g') :=
  toLinearMap_injective <| LinearMap.lTensor_comp_map M _ _ _

variable {M}

@[simp] theorem rTensor_pow (f : M ≃ₗ[R] M) (n : ℕ) : f.rTensor N ^ n = (f ^ n).rTensor N := by
  simpa only [one_pow] using TensorProduct.congr_pow f (1 : N ≃ₗ[R] N) n

@[simp] theorem rTensor_zpow (f : M ≃ₗ[R] M) (n : ℤ) : f.rTensor N ^ n = (f ^ n).rTensor N := by
  simpa only [one_zpow] using TensorProduct.congr_zpow f (1 : N ≃ₗ[R] N) n

@[simp] theorem lTensor_pow (f : N ≃ₗ[R] N) (n : ℕ) : f.lTensor M ^ n = (f ^ n).lTensor M := by
  simpa only [one_pow] using TensorProduct.congr_pow (1 : M ≃ₗ[R] M) f n

@[simp] theorem lTensor_zpow (f : N ≃ₗ[R] N) (n : ℤ) : f.lTensor M ^ n = (f ^ n).lTensor M := by
  simpa only [one_zpow] using TensorProduct.congr_zpow (1 : M ≃ₗ[R] M) f n

end LinearEquiv

end Semiring

section Ring

variable {R : Type*} [CommSemiring R]
variable {M : Type*} {N : Type*} {P : Type*} {Q : Type*} {S : Type*}
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q] [AddCommGroup S]
variable [Module R M] [Module R N] [Module R P] [Module R Q] [Module R S]

namespace TensorProduct

open TensorProduct

open LinearMap

variable (R)

/-- Auxiliary function to defining negation multiplication on tensor product. -/
def Neg.aux : M ⊗[R] N →ₗ[R] M ⊗[R] N :=
  lift <| (mk R M N).comp (-LinearMap.id)

variable {R}

instance neg : Neg (M ⊗[R] N) where
  neg := Neg.aux R

protected theorem neg_add_cancel (x : M ⊗[R] N) : -x + x = 0 :=
  x.induction_on
    (by rw [add_zero]; apply (Neg.aux R).map_zero)
    (fun x y => by convert (add_tmul (R := R) (-x) x y).symm; rw [neg_add_cancel, zero_tmul])
    fun x y hx hy => by
    suffices -x + x + (-y + y) = 0 by
      rw [← this]
      unfold Neg.neg neg
      simp only
      rw [map_add]
      abel
    rw [hx, hy, add_zero]

instance addCommGroup : AddCommGroup (M ⊗[R] N) :=
  { TensorProduct.addCommMonoid with
    neg := Neg.neg
    sub := _
    sub_eq_add_neg := fun _ _ => rfl
    neg_add_cancel := fun x => TensorProduct.neg_add_cancel x
    zsmul := fun n v => n • v
    zsmul_zero' := by simp [TensorProduct.zero_smul]
    zsmul_succ' := by simp [add_comm, TensorProduct.one_smul, TensorProduct.add_smul]
    zsmul_neg' := fun n x => by
      change (-n.succ : ℤ) • x = -(((n : ℤ) + 1) • x)
      rw [← zero_add (_ • x), ← TensorProduct.neg_add_cancel ((n.succ : ℤ) • x), add_assoc,
        ← add_smul, ← sub_eq_add_neg, sub_self, zero_smul, add_zero]
      rfl }

theorem neg_tmul (m : M) (n : N) : (-m) ⊗ₜ n = -m ⊗ₜ[R] n :=
  rfl

theorem tmul_neg (m : M) (n : N) : m ⊗ₜ (-n) = -m ⊗ₜ[R] n :=
  (mk R M N _).map_neg _

theorem tmul_sub (m : M) (n₁ n₂ : N) : m ⊗ₜ (n₁ - n₂) = m ⊗ₜ[R] n₁ - m ⊗ₜ[R] n₂ :=
  (mk R M N _).map_sub _ _

theorem sub_tmul (m₁ m₂ : M) (n : N) : (m₁ - m₂) ⊗ₜ n = m₁ ⊗ₜ[R] n - m₂ ⊗ₜ[R] n :=
  (mk R M N).map_sub₂ _ _ _

/-- While the tensor product will automatically inherit a ℤ-module structure from
`AddCommGroup.toIntModule`, that structure won't be compatible with lemmas like `tmul_smul` unless
we use a `ℤ-Module` instance provided by `TensorProduct.left_module`.

When `R` is a `Ring` we get the required `TensorProduct.compatible_smul` instance through
`IsScalarTower`, but when it is only a `Semiring` we need to build it from scratch.
The instance diamond in `compatible_smul` doesn't matter because it's in `Prop`.
-/
instance CompatibleSMul.int : CompatibleSMul R ℤ M N :=
  ⟨fun r m n =>
    Int.induction_on r (by simp) (fun r ih => by simpa [add_smul, tmul_add, add_tmul] using ih)
      fun r ih => by simpa [sub_smul, tmul_sub, sub_tmul] using ih⟩

instance CompatibleSMul.unit {S} [Monoid S] [DistribMulAction S M] [DistribMulAction S N]
    [CompatibleSMul R S M N] : CompatibleSMul R Sˣ M N :=
  ⟨fun s m n => CompatibleSMul.smul_tmul (s : S) m n⟩

end TensorProduct

namespace LinearMap

@[simp]
theorem lTensor_sub (f g : N →ₗ[R] P) : (f - g).lTensor M = f.lTensor M - g.lTensor M := by
  simp_rw [← coe_lTensorHom]
  exact (lTensorHom (R := R) (N := N) (P := P) M).map_sub f g

@[simp]
theorem rTensor_sub (f g : N →ₗ[R] P) : (f - g).rTensor M = f.rTensor M - g.rTensor M := by
  simp only [← coe_rTensorHom]
  exact (rTensorHom (R := R) (N := N) (P := P) M).map_sub f g

@[simp]
theorem lTensor_neg (f : N →ₗ[R] P) : (-f).lTensor M = -f.lTensor M := by
  simp only [← coe_lTensorHom]
  exact (lTensorHom (R := R) (N := N) (P := P) M).map_neg f

@[simp]
theorem rTensor_neg (f : N →ₗ[R] P) : (-f).rTensor M = -f.rTensor M := by
  simp only [← coe_rTensorHom]
  exact (rTensorHom (R := R) (N := N) (P := P) M).map_neg f

end LinearMap

end Ring

