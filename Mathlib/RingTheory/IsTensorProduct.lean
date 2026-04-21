/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The characteristic predicate of tensor product

## Main definitions

- `IsTensorProduct`: A predicate on `f : M₁ →ₗ[R] M₂ →ₗ[R] M` expressing that `f` realizes `M` as
  the tensor product of `M₁ ⊗[R] M₂`. This is defined by requiring the lift `M₁ ⊗[R] M₂ → M` to be
  bijective.
- `IsBaseChange`: A predicate on an `R`-algebra `S` and a map `f : M →ₗ[R] N` with `N` being an
  `S`-module, expressing that `f` realizes `N` as the base change of `M` along `R → S`.
- `Algebra.IsPushout`: A predicate on the following diagram of scalar towers
  ```
    R  →  S
    ↓     ↓
    R' →  S'
  ```
  asserting that is a pushout diagram (i.e. `S' = S ⊗[R] R'`)

## Main results
- `TensorProduct.isBaseChange`: `S ⊗[R] M` is the base change of `M` along `R → S`.

-/

@[expose] public section



universe u v₁ v₂ v₃ v₄

open TensorProduct

section IsTensorProduct

variable {R : Type*} [CommSemiring R]
variable {M₁ M₂ M M' : Type*}
variable [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M] [AddCommMonoid M']
variable [Module R M₁] [Module R M₂] [Module R M] [Module R M']
variable (f : M₁ →ₗ[R] M₂ →ₗ[R] M)
variable {N₁ N₂ N : Type*} [AddCommMonoid N₁] [AddCommMonoid N₂] [AddCommMonoid N]
variable [Module R N₁] [Module R N₂] [Module R N]
variable {g : N₁ →ₗ[R] N₂ →ₗ[R] N}

/-- Given a bilinear map `f : M₁ →ₗ[R] M₂ →ₗ[R] M`, `IsTensorProduct f` means that
`M` is the tensor product of `M₁` and `M₂` via `f`.
This is defined by requiring the lift `M₁ ⊗[R] M₂ → M` to be bijective.
-/
def IsTensorProduct : Prop :=
  Function.Bijective (TensorProduct.lift f)

variable (R M N) {f}

theorem TensorProduct.isTensorProduct : IsTensorProduct (TensorProduct.mk R M N) := by
  delta IsTensorProduct
  convert_to Function.Bijective (LinearMap.id : M ⊗[R] N →ₗ[R] M ⊗[R] N) using 2
  · apply TensorProduct.ext'
    simp
  · exact Function.bijective_id

namespace IsTensorProduct

variable {R M N}

/-- If `M` is the tensor product of `M₁` and `M₂`, it is linearly equivalent to `M₁ ⊗[R] M₂`. -/
@[simps! apply]
noncomputable def equiv (h : IsTensorProduct f) : M₁ ⊗[R] M₂ ≃ₗ[R] M :=
  LinearEquiv.ofBijective _ h

@[simp]
theorem equiv_toLinearMap (h : IsTensorProduct f) :
    h.equiv.toLinearMap = TensorProduct.lift f :=
  rfl

@[simp]
theorem equiv_symm_apply (h : IsTensorProduct f) (x₁ : M₁) (x₂ : M₂) :
    h.equiv.symm (f x₁ x₂) = x₁ ⊗ₜ x₂ := by
  apply h.equiv.injective
  refine (h.equiv.apply_symm_apply _).trans ?_
  simp

/-- If `M` is the tensor product of `M₁` and `M₂`, we may lift a bilinear map `M₁ →ₗ[R] M₂ →ₗ[R] M'`
to a `M →ₗ[R] M'`. -/
noncomputable def lift (h : IsTensorProduct f) (f' : M₁ →ₗ[R] M₂ →ₗ[R] M') :
    M →ₗ[R] M' :=
  (TensorProduct.lift f').comp h.equiv.symm.toLinearMap

theorem lift_eq (h : IsTensorProduct f) (f' : M₁ →ₗ[R] M₂ →ₗ[R] M') (x₁ : M₁)
    (x₂ : M₂) : h.lift f' (f x₁ x₂) = f' x₁ x₂ := by
  simp [lift]

/-- The tensor product of a pair of linear maps between modules. -/
noncomputable def map (hf : IsTensorProduct f) (hg : IsTensorProduct g)
    (i₁ : M₁ →ₗ[R] N₁) (i₂ : M₂ →ₗ[R] N₂) : M →ₗ[R] N :=
  hg.equiv.toLinearMap.comp ((TensorProduct.map i₁ i₂).comp hf.equiv.symm.toLinearMap)

@[simp]
theorem map_eq (hf : IsTensorProduct f) (hg : IsTensorProduct g) (i₁ : M₁ →ₗ[R] N₁)
    (i₂ : M₂ →ₗ[R] N₂) (x₁ : M₁) (x₂ : M₂) : hf.map hg i₁ i₂ (f x₁ x₂) = g (i₁ x₁) (i₂ x₂) := by
  simp [map]

@[elab_as_elim]
theorem inductionOn (h : IsTensorProduct f) {motive : M → Prop} (m : M)
    (zero : motive 0) (tmul : ∀ x y, motive (f x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive m := by
  rw [← h.equiv.right_inv m]
  generalize h.equiv.invFun m = y
  change motive (TensorProduct.lift f y)
  induction y with
  | zero => rwa [map_zero]
  | tmul _ _ =>
    rw [TensorProduct.lift.tmul]
    apply tmul
  | add _ _ _ _ =>
    rw [map_add]
    apply add <;> assumption

lemma of_equiv (e : M₁ ⊗[R] M₂ ≃ₗ[R] M) (he : ∀ x y, e (x ⊗ₜ y) = f x y) :
    IsTensorProduct f := by
  have : TensorProduct.lift f = e := by
    ext x y
    simp [he]
  simpa [IsTensorProduct, this] using e.bijective

section map

variable {P₁ P₂ P : Type*} [AddCommMonoid P₁] [AddCommMonoid P₂]
  [AddCommMonoid P] [Module R P₁] [Module R P₂] [Module R P] {p : P₁ →ₗ[R] P₂ →ₗ[R] P}
  (hf : IsTensorProduct f) (hg : IsTensorProduct g) (hp : IsTensorProduct p)
  (i₁ : N₁ →ₗ[R] P₁) (j₁ : M₁ →ₗ[R] N₁) (i₂ : N₂ →ₗ[R] P₂) (j₂ : M₂ →ₗ[R] N₂)

theorem map_comp : hf.map hp (i₁ ∘ₗ j₁) (i₂ ∘ₗ j₂) = hg.map hp i₁ i₂ ∘ₗ hf.map hg j₁ j₂ :=
  LinearMap.ext <| fun x ↦ hf.inductionOn x (by simp) (by simp) (fun _ _ h₁ h₂ ↦ by simp [h₁, h₂])

theorem map_map (x : M) :
    hg.map hp i₁ i₂ ((hf.map hg j₁ j₂) x) = hf.map hp (i₁ ∘ₗ j₁) (i₂ ∘ₗ j₂) x :=
  DFunLike.congr_fun (hf.map_comp hg hp i₁ j₁ i₂ j₂).symm x

@[simp]
theorem map_id :
    hf.map hf (LinearMap.id : M₁ →ₗ[R] M₁) (LinearMap.id : M₂ →ₗ[R] M₂) = LinearMap.id :=
  LinearMap.ext <| fun x ↦ hf.inductionOn x (by simp) (by simp) (fun _ _ h₁ h₂ ↦ by simp [h₁, h₂])

@[simp]
protected theorem map_one : hf.map hf (1 : M₁ →ₗ[R] M₁) (1 : M₂ →ₗ[R] M₂) = 1 :=
  hf.map_id

protected theorem map_mul (i₁ i₂ : M₁ →ₗ[R] M₁) (j₁ j₂ : M₂ →ₗ[R] M₂) :
    hf.map hf (i₁ * i₂) (j₁ * j₂) = hf.map hf i₁ j₁ * hf.map hf i₂ j₂ :=
  hf.map_comp hf hf i₁ i₂ j₁ j₂

protected theorem map_pow (i : M₁ →ₗ[R] M₁) (j : M₂ →ₗ[R] M₂) (n : ℕ) :
    hf.map hf i j ^ n = hf.map hf (i ^ n) (j ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [pow_succ, ih, hf.map_mul]

end map


section

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
 {M₁ M₂ M₃ M₁₂ M₂₃ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
 [AddCommMonoid M₁₂] [AddCommMonoid M₂₃]
 [Module R M₁]
 [Module R M₂] [Module S M₂] [IsScalarTower R S M₂]
 [Module R M₃] [Module S M₃] [IsScalarTower R S M₃]
 [Module R M₁₂] [Module S M₁₂] [IsScalarTower R S M₁₂]
 [Module R M₂₃] [Module S M₂₃] [IsScalarTower R S M₂₃]

set_option backward.defeqAttrib.useBackward true in
/-- (Implementation): Use the more linear `IsTensorProduct.assoc`. -/
private noncomputable def assocAux
    (f : M₁ →ₗ[R] M₂ →ₗ[S] M₁₂) (hf : IsTensorProduct (f.restrictScalars₁₂ R R))
    (g : M₂ →ₗ[S] M₃ →ₗ[S] M₂₃) (hg : IsTensorProduct g) :
    M₁₂ ⊗[S] M₃ ≃ₗ[R] M₁ ⊗[R] M₂₃ :=
  letI : Module S (M₁ ⊗[R] M₂) :=
    AddEquiv.module S hf.equiv.toAddEquiv
  haveI heq (s : S) (y : M₁) (x : M₂) : s • y ⊗ₜ[R] x = y ⊗ₜ[R] (s • x) := by
    change hf.equiv.symm (s • _) = _
    dsimp
    rw [← map_smul]
    apply hf.equiv_symm_apply
  haveI : IsScalarTower R S (M₁ ⊗[R] M₂) := hf.equiv.isScalarTower S
  letI e₀ : M₂ ⊗[R] M₁ ≃ₗ[S] M₁ ⊗[R] M₂ :=
    { __ := TensorProduct.comm R M₂ M₁
      map_smul' s x := by induction x <;> simp_all [TensorProduct.smul_tmul'] }
  LinearEquiv.symm <|
    TensorProduct.congr (.refl _ _) (hg.equiv.symm.restrictScalars R) ≪≫ₗ
    TensorProduct.comm _ _ _ ≪≫ₗ
    (AlgebraTensorModule.congr (TensorProduct.comm _ _ _) (.refl _ _)).restrictScalars R ≪≫ₗ
    (AlgebraTensorModule.assoc R S S M₃ M₂ M₁).restrictScalars R ≪≫ₗ
    (TensorProduct.comm _ _ _).restrictScalars R ≪≫ₗ
    (TensorProduct.congr e₀ (.refl _ _)).restrictScalars R ≪≫ₗ
    (TensorProduct.congr (hf.equiv.linearEquiv S) (.refl _ _)).restrictScalars R

variable (f : M₁ →ₗ[R] M₂ →ₗ[S] M₁₂) (hf : IsTensorProduct (f.restrictScalars₁₂ R R))
  (g : M₂ →ₗ[S] M₃ →ₗ[S] M₂₃) (hg : IsTensorProduct g)

@[simp]
private lemma assocAux_symm_tmul (x₁ : M₁) (x₂ : M₂) (x₃ : M₃) :
    (IsTensorProduct.assocAux f hf g hg).symm (x₁ ⊗ₜ g x₂ x₃) = f x₁ x₂ ⊗ₜ x₃ := by
  simp [IsTensorProduct.assocAux]

@[simp]
private lemma assocAux_tmul (x₁ : M₁) (x₂ : M₂) (x₃ : M₃) :
    IsTensorProduct.assocAux f hf g hg (f x₁ x₂ ⊗ₜ x₃) = x₁ ⊗ₜ g x₂ x₃ := by
  have : hf.equiv.symm (f x₁ x₂) = x₁ ⊗ₜ x₂ := hf.equiv_symm_apply _ _
  simp [IsTensorProduct.assocAux, this]

set_option backward.defeqAttrib.useBackward true in
/--
This is the canonical isomorphism `(M₁ ⊗[R] M₂) ⊗[S] M₃ ≃ₗ[T] M₁ ⊗[R] (M₂ ⊗[S] M₃)`.
We state this for a general `M₁₂ = M₁ ⊗[R] M₂` and `M₂₃ = M₂ ⊗[R] M₃`.
For the version where `R` and `S` are flipped, see `TensorProduct.AlgebraTensorModule.assoc`.
-/
@[no_expose]
noncomputable def assoc {T : Type*} [CommSemiring T] [Algebra R T] [Module T M₁]
    [IsScalarTower R T M₁] [Module T M₁₂] [SMulCommClass S T M₁₂] [IsScalarTower R T M₁₂]
    (f : M₁ →ₗ[T] M₂ →ₗ[S] M₁₂) (hf : IsTensorProduct (f.restrictScalars₁₂ R R))
    (g : M₂ →ₗ[S] M₃ →ₗ[S] M₂₃) (hg : IsTensorProduct g) :
    M₁₂ ⊗[S] M₃ ≃ₗ[T] M₁ ⊗[R] M₂₃ where
  toAddEquiv := IsTensorProduct.assocAux (f.restrictScalars₁₂ R S) hf g hg
  map_smul' t x := by
    induction x with
    | zero => simp
    | add x y _ _ => simp_all
    | tmul x y =>
    obtain ⟨x, rfl⟩ := hf.equiv.surjective x
    induction x with
    | zero => simp
    | add x y _ _ => simp_all [add_tmul]
    | tmul x z =>
      have : t • (f x) z = f (t • x) z := by simp
      dsimp
      rw [smul_tmul', this, ← f.restrictScalars₁₂_apply_apply R S,
        ← f.restrictScalars₁₂_apply_apply R S, IsTensorProduct.assocAux_tmul,
        IsTensorProduct.assocAux_tmul, TensorProduct.smul_tmul']

variable {T : Type*} [CommSemiring T] [Algebra R T] [Module T M₁] [IsScalarTower R T M₁]
  [Module T M₁₂] [SMulCommClass S T M₁₂] [IsScalarTower R T M₁₂]
  (f : M₁ →ₗ[T] M₂ →ₗ[S] M₁₂) (hf : IsTensorProduct (f.restrictScalars₁₂ R R))
  (g : M₂ →ₗ[S] M₃ →ₗ[S] M₂₃) (hg : IsTensorProduct g)

@[simp]
lemma assoc_tmul (x₁ : M₁) (x₂ : M₂) (x₃ : M₃) :
    assoc f hf g hg (f x₁ x₂ ⊗ₜ x₃) = x₁ ⊗ₜ g x₂ x₃ :=
  assocAux_tmul (f.restrictScalars₁₂ R S) hf g hg _ _ _

@[simp]
lemma assoc_symm_tmul (x₁ : M₁) (x₂ : M₂) (x₃ : M₃) :
    (assoc f hf g hg).symm (x₁ ⊗ₜ g x₂ x₃) = f x₁ x₂ ⊗ₜ x₃ :=
  assocAux_symm_tmul (f.restrictScalars₁₂ R S) hf g hg _ _ _

/-- Variant of `IsTensorProduct.assoc` taking an `R`-bilinear map `f` and proofs that
`f` is `T` linear in the first and `S`-linear in the second argument. -/
noncomputable def assocOfMapSMul (f : M₁ →ₗ[R] M₂ →ₗ[R] M₁₂) (hf : IsTensorProduct f)
    (g : M₂ →ₗ[S] M₃ →ₗ[S] M₂₃) (hg : IsTensorProduct g)
    (h₁ : ∀ (t : T) (x : M₁) (y : M₂), f (t • x) y = t • f x y)
    (h₂ : ∀ (s : S) (x : M₁) (y : M₂), f x (s • y) = s • f x y) :
    M₁₂ ⊗[S] M₃ ≃ₗ[T] M₁ ⊗[R] M₂₃ :=
  IsTensorProduct.assoc (.mk₂' _ _ (f ·) (by simp) (by simp [h₁]) (by simp) (by simp [h₂])) hf g hg

variable (f : M₁ →ₗ[R] M₂ →ₗ[R] M₁₂) (hf : IsTensorProduct f)
  (g : M₂ →ₗ[S] M₃ →ₗ[S] M₂₃) (hg : IsTensorProduct g)
  (h₁ : ∀ (t : T) (x : M₁) (y : M₂), f (t • x) y = t • f x y)
  (h₂ : ∀ (s : S) (x : M₁) (y : M₂), f x (s • y) = s • f x y)

@[simp]
lemma assocOfMapSMul_tmul (x₁ : M₁) (x₂ : M₂) (x₃ : M₃) :
    assocOfMapSMul f hf g hg h₁ h₂ (f x₁ x₂ ⊗ₜ x₃) = x₁ ⊗ₜ g x₂ x₃ :=
  IsTensorProduct.assoc_tmul ..

@[simp]
lemma assocOfMapSMul_symm_tmul (x₁ : M₁) (x₂ : M₂) (x₃ : M₃) :
    (assocOfMapSMul f hf g hg h₁ h₂).symm (x₁ ⊗ₜ g x₂ x₃) = f x₁ x₂ ⊗ₜ x₃ :=
  IsTensorProduct.assoc_symm_tmul ..

end

end IsTensorProduct

end IsTensorProduct

section IsBaseChange

variable {R : Type*} {M : Type v₁} {N : Type v₂} (S : Type v₃)
variable [AddCommMonoid M] [AddCommMonoid N] [CommSemiring R]
variable [CommSemiring S] [Algebra R S] [Module R M] [Module R N] [Module S N] [IsScalarTower R S N]
variable (f : M →ₗ[R] N)

/-- Given an `R`-algebra `S` and an `R`-module `M`, an `S`-module `N` together with a map
`f : M →ₗ[R] N` is the base change of `M` to `S` if the map `S × M → N, (s, m) ↦ s • f m` is the
tensor product. -/
def IsBaseChange : Prop :=
  IsTensorProduct
    (((Algebra.linearMap S <| Module.End S (M →ₗ[R] N)).flip f).restrictScalars R)

variable {S f} (h : IsBaseChange S f)
variable {P Q : Type*} [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module S Q]

section

variable [Module R Q] [IsScalarTower R S Q]

/-- Suppose `f : M →ₗ[R] N` is the base change of `M` along `R → S`. Then any `R`-linear map from
`M` to an `S`-module factors through `f`. -/
noncomputable nonrec def IsBaseChange.lift (g : M →ₗ[R] Q) : N →ₗ[S] Q :=
  { h.lift
      (((Algebra.linearMap S <| Module.End S (M →ₗ[R] Q)).flip g).restrictScalars R) with
    map_smul' := fun r x => by
      let F := ((Algebra.linearMap S <| Module.End S (M →ₗ[R] Q)).flip g).restrictScalars R
      have hF : ∀ (s : S) (m : M), h.lift F (s • f m) = s • g m := h.lift_eq F
      change h.lift F (r • x) = r • h.lift F x
      induction x using h.inductionOn with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | tmul s m =>
        change h.lift F (r • s • f m) = r • h.lift F (s • f m)
        rw [← mul_smul, hF, hF, mul_smul]
      | add x₁ x₂ e₁ e₂ => rw [map_add, smul_add, map_add, smul_add, e₁, e₂] }

nonrec theorem IsBaseChange.lift_eq (g : M →ₗ[R] Q) (x : M) : h.lift g (f x) = g x := by
  have hF : ∀ (s : S) (m : M), h.lift g (s • f m) = s • g m := h.lift_eq _
  convert hF 1 x <;> rw [one_smul]

theorem IsBaseChange.lift_comp (g : M →ₗ[R] Q) : ((h.lift g).restrictScalars R).comp f = g :=
  LinearMap.ext (h.lift_eq g)

end

section
include h

@[elab_as_elim]
nonrec theorem IsBaseChange.inductionOn (x : N) (motive : N → Prop) (zero : motive 0)
    (tmul : ∀ m : M, motive (f m)) (smul : ∀ (s : S) (n), motive n → motive (s • n))
    (add : ∀ n₁ n₂, motive n₁ → motive n₂ → motive (n₁ + n₂)) : motive x :=
  h.inductionOn x zero (fun _ _ => smul _ _ (tmul _)) add

theorem IsBaseChange.algHom_ext (g₁ g₂ : N →ₗ[S] Q) (e : ∀ x, g₁ (f x) = g₂ (f x)) : g₁ = g₂ := by
  ext x
  refine h.inductionOn x _ ?_ ?_ ?_ ?_
  · rw [map_zero, map_zero]
  · assumption
  · intro s n e'
    rw [g₁.map_smul, g₂.map_smul, e']
  · intro x y e₁ e₂
    rw [map_add, map_add, e₁, e₂]

theorem IsBaseChange.algHom_ext' [Module R Q] [IsScalarTower R S Q] (g₁ g₂ : N →ₗ[S] Q)
    (e : (g₁.restrictScalars R).comp f = (g₂.restrictScalars R).comp f) : g₁ = g₂ :=
  h.algHom_ext g₁ g₂ (LinearMap.congr_fun e)

end

variable (R M N S)

theorem TensorProduct.isBaseChange : IsBaseChange S (TensorProduct.mk R S M 1) := by
  delta IsBaseChange
  convert TensorProduct.isTensorProduct R S M using 1
  ext s x
  change s • (1 : S) ⊗ₜ[R] x = s ⊗ₜ[R] x
  rw [TensorProduct.smul_tmul']
  congr 1
  exact mul_one _

variable {R M N S}

/-- The base change of `M` along `R → S` is linearly equivalent to `S ⊗[R] M`. -/
noncomputable nonrec def IsBaseChange.equiv : S ⊗[R] M ≃ₗ[S] N :=
  { h.equiv with
    map_smul' := fun r x => by
      change h.equiv (r • x) = r • h.equiv x
      refine TensorProduct.induction_on x ?_ ?_ ?_
      · rw [smul_zero, map_zero, smul_zero]
      · intro x y
        simp [smul_tmul', Algebra.linearMap_apply, smul_comm r x]
      · intro x y hx hy
        rw [map_add, smul_add, map_add, smul_add, hx, hy] }

@[simp]
theorem IsBaseChange.equiv_tmul (s : S) (m : M) : h.equiv (s ⊗ₜ m) = s • f m :=
  rfl

@[simp]
theorem IsBaseChange.equiv_symm_apply (m : M) : h.equiv.symm (f m) = 1 ⊗ₜ m := by
  rw [h.equiv.symm_apply_eq, h.equiv_tmul, one_smul]

lemma IsBaseChange.of_equiv (e : S ⊗[R] M ≃ₗ[S] N) (he : ∀ x, e (1 ⊗ₜ x) = f x) :
    IsBaseChange S f := by
  apply IsTensorProduct.of_equiv (e.restrictScalars R)
  intro x y
  simp [show x ⊗ₜ[R] y = x • (1 ⊗ₜ[R] y) by simp [smul_tmul'], he]

variable (R S) in
theorem IsBaseChange.linearMap : IsBaseChange S (Algebra.linearMap R S) :=
  of_equiv (AlgebraTensorModule.rid R S S) fun x ↦ by
    simpa using (Algebra.algebraMap_eq_smul_one x).symm

section

variable (A : Type*) [CommSemiring A]
variable [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable [Module S M] [IsScalarTower R S M]
variable [Module A N] [IsScalarTower S A N] [IsScalarTower R A N]

/-- If `N` is the base change of `M` to `A`, then `N ⊗[R] P` is the base change
of `M ⊗[R] P` to `A`. This is simply the isomorphism
`A ⊗[S] (M ⊗[R] P) ≃ₗ[A] (A ⊗[S] M) ⊗[R] P`. -/
lemma isBaseChange_tensorProduct_map {f : M →ₗ[S] N} (hf : IsBaseChange A f) :
    IsBaseChange A (AlgebraTensorModule.map f (LinearMap.id (R := R) (M := P))) := by
  let e : A ⊗[S] (M ⊗[R] P) ≃ₗ[A] N ⊗[R] P := (AlgebraTensorModule.assoc R S A A M P).symm.trans
    (AlgebraTensorModule.congr hf.equiv (LinearEquiv.refl R P))
  refine IsBaseChange.of_equiv e (fun x ↦ ?_)
  induction x with
  | zero => simp
  | tmul => simp [e, IsBaseChange.equiv_tmul]
  | add _ _ h1 h2 => simp [tmul_add, h1, h2]

end

variable (f) in
theorem IsBaseChange.of_lift_unique
    (h : ∀ (Q : Type max v₁ v₂ v₃) [AddCommMonoid Q],
      ∀ [Module R Q] [Module S Q], ∀ [IsScalarTower R S Q],
        ∀ g : M →ₗ[R] Q, ∃! g' : N →ₗ[S] Q, (g'.restrictScalars R).comp f = g) :
    IsBaseChange S f := by
  obtain ⟨g, hg, -⟩ :=
    h (ULift.{v₂} <| S ⊗[R] M)
      (ULift.moduleEquiv.symm.toLinearMap.comp <| TensorProduct.mk R S M 1)
  let f' : S ⊗[R] M →ₗ[R] N :=
    TensorProduct.lift (((LinearMap.flip (AlgHom.toLinearMap (Algebra.ofId S
      (Module.End S (M →ₗ[R] N))))) f).restrictScalars R)
  change Function.Bijective f'
  let f'' : S ⊗[R] M →ₗ[S] N := by
    refine
      { f' with
        map_smul' := fun s x =>
          TensorProduct.induction_on x ?_ (fun s' y => smul_assoc s s' _) fun x y hx hy => ?_ }
    · dsimp; rw [map_zero, smul_zero, map_zero, smul_zero]
    · dsimp at *; rw [smul_add, map_add, map_add, smul_add, hx, hy]
  simp_rw [DFunLike.ext_iff, LinearMap.comp_apply, LinearMap.restrictScalars_apply] at hg
  let fe : S ⊗[R] M ≃ₗ[S] N :=
    LinearEquiv.ofLinear f'' (ULift.moduleEquiv.toLinearMap.comp g) ?_ ?_
  · exact fe.bijective
  · rw [← LinearMap.cancel_left (ULift.moduleEquiv : ULift.{max v₁ v₃} N ≃ₗ[S] N).symm.injective]
    refine (h (ULift.{max v₁ v₃} N) <| ULift.moduleEquiv.symm.toLinearMap.comp f).unique ?_ rfl
    ext x
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, hg]
    apply one_smul
  · ext x
    change (g <| (1 : S) • f x).down = _
    rw [one_smul, hg]
    rfl

theorem IsBaseChange.iff_lift_unique :
    IsBaseChange S f ↔
      ∀ (Q : Type max v₁ v₂ v₃) [AddCommMonoid Q],
        ∀ [Module R Q] [Module S Q],
          ∀ [IsScalarTower R S Q],
            ∀ g : M →ₗ[R] Q, ∃! g' : N →ₗ[S] Q, (g'.restrictScalars R).comp f = g :=
  ⟨fun h => by
    intro Q _ _ _ _ g
    exact ⟨h.lift g, h.lift_comp g, fun g' e => h.algHom_ext' _ _ (e.trans (h.lift_comp g).symm)⟩,
    IsBaseChange.of_lift_unique f⟩

set_option backward.isDefEq.respectTransparency false in
theorem IsBaseChange.ofEquiv (e : M ≃ₗ[R] N) : IsBaseChange R e.toLinearMap := by
  apply IsBaseChange.of_lift_unique
  intro Q I₁ I₂ I₃ I₄ g
  have : I₂ = I₃ := by
    ext r q
    change (by let _ := I₂; exact r • q) = (by let _ := I₃; exact r • q)
    dsimp
    rw [← one_smul R q, smul_smul, ← @smul_assoc _ _ _ (id _) (id _) (id _) I₄, smul_eq_mul]
  cases this
  refine
    ⟨g.comp e.symm.toLinearMap, by
      ext
      simp, ?_⟩
  rintro y (rfl : _ = _)
  ext
  simp

variable {T O : Type*} [CommSemiring T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable [AddCommMonoid O] [Module R O] [Module S O] [Module T O] [IsScalarTower S T O]
variable [IsScalarTower R S O] [IsScalarTower R T O]

theorem IsBaseChange.comp {f : M →ₗ[R] N} (hf : IsBaseChange S f) {g : N →ₗ[S] O}
    (hg : IsBaseChange T g) : IsBaseChange T ((g.restrictScalars R).comp f) := by
  apply IsBaseChange.of_lift_unique
  intro Q _ _ _ _ i
  letI := Module.compHom Q (algebraMap S T)
  haveI : IsScalarTower S T Q :=
    ⟨fun x y z => by
      rw [Algebra.smul_def, mul_smul]
      rfl⟩
  have : IsScalarTower R S Q := IsScalarTower.to₁₂₄ _ _ T _
  refine
    ⟨hg.lift (hf.lift i), by
      ext
      simp [IsBaseChange.lift_eq], ?_⟩
  rintro g' (e : _ = _)
  refine hg.algHom_ext' _ _ (hf.algHom_ext' _ _ ?_)
  rw [IsBaseChange.lift_comp, IsBaseChange.lift_comp, ← e]
  ext
  rfl

/-- If `N` is the base change of `M` to `S` and `O` the base change of `M` to `T`, then
`O` is the base change of `N` to `T`. -/
lemma IsBaseChange.of_comp {f : M →ₗ[R] N} (hf : IsBaseChange S f) {h : N →ₗ[S] O}
    (hc : IsBaseChange T ((h : N →ₗ[R] O) ∘ₗ f)) :
    IsBaseChange T h := by
  apply IsBaseChange.of_lift_unique
  intro Q _ _ _ _ r
  letI : Module R Q := .restrictScalars R S Q
  haveI : IsScalarTower R S Q := .restrictScalars R S Q
  haveI : IsScalarTower R T Q := IsScalarTower.of_algebraMap_smul fun r x ↦ by
    simp [IsScalarTower.algebraMap_apply R S T]
  let r' : M →ₗ[R] Q := r ∘ₗ f
  let q : O →ₗ[T] Q := hc.lift r'
  refine ⟨q, ?_, ?_⟩
  · apply hf.algHom_ext'
    simp [r', q, LinearMap.comp_assoc, hc.lift_comp]
  · intro q' hq'
    apply hc.algHom_ext'
    apply_fun LinearMap.restrictScalars R at hq'
    rw [← LinearMap.comp_assoc]
    rw [show q'.restrictScalars R ∘ₗ h.restrictScalars R = _ from hq', hc.lift_comp]

/-- If `N` is the base change `M` to `S`, then `O` is the base change of `M` to `T` if and
only if `O` is the base change of `N` to `T`. -/
lemma IsBaseChange.comp_iff {f : M →ₗ[R] N} (hf : IsBaseChange S f) {h : N →ₗ[S] O} :
    IsBaseChange T ((h : N →ₗ[R] O) ∘ₗ f) ↔ IsBaseChange T h :=
  ⟨fun hc ↦ IsBaseChange.of_comp hf hc, fun hh ↦ IsBaseChange.comp hf hh⟩

/-- Let `R` be a commutative ring, `S` be an `R`-algebra, `M` be an `R`-module, `P` be an `S`
  module, `N` be the base change of `M` to `S`, then `P ⊗[S] N` is isomorphic to `P ⊗[R] M`
  as `S`-modules. -/
noncomputable def IsBaseChange.tensorEquiv {f : M →ₗ[R] N} (hf : IsBaseChange S f) (P : Type*)
    [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P] : P ⊗[S] N ≃ₗ[S] P ⊗[R] M :=
  LinearEquiv.lTensor P hf.equiv.symm ≪≫ₗ AlgebraTensorModule.cancelBaseChange R S S P M

theorem IsBaseChange.map_id_lsmul_eq_lsmul_algebraMap
    {f : M →ₗ[R] N} (hf : IsBaseChange S f) (x : R) :
    hf.map hf LinearMap.id (LinearMap.lsmul R M x) = LinearMap.lsmul S N (algebraMap R S x) := by
  ext y
  refine IsTensorProduct.inductionOn hf y (by simp) ?_ (fun _ _ ha hb ↦ by simp [ha, hb])
  intro s m
  rw [hf.map_eq hf]
  simpa using smul_comm x s (f m)

variable {R' S' : Type*} [CommSemiring R'] [CommSemiring S']
variable [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S']
variable [IsScalarTower R R' S'] [IsScalarTower R S S']

open IsScalarTower (toAlgHom algebraMap_apply)

variable (R S R' S')

/-- A type-class stating that the following diagram of scalar towers
```
R  →  S
↓     ↓
R' →  S'
```
is a pushout diagram (i.e. `S' = S ⊗[R] R'`)
-/
@[mk_iff]
class Algebra.IsPushout : Prop where
  out : IsBaseChange S (toAlgHom R R' S').toLinearMap

/-- The isomorphism `S' ≃ S ⊗[R] R` given `Algebra.IsPushout R S R' S'`. -/
noncomputable
def Algebra.IsPushout.equiv [h : Algebra.IsPushout R S R' S'] : S ⊗[R] R' ≃ₐ[S] S' where
  __ := h.out.equiv
  map_mul' x y := by
    dsimp
    induction x with
    | zero => simp
    | add x y _ _ => simp [*, add_mul]
    | tmul a b =>
      induction y with
      | zero => simp
      | add x y _ _ => simp [*, mul_add]
      | tmul x y => simp [IsBaseChange.equiv_tmul, Algebra.smul_def, mul_mul_mul_comm]
  commutes' := by simp [IsBaseChange.equiv_tmul, Algebra.smul_def]

lemma Algebra.IsPushout.equiv_tmul [h : Algebra.IsPushout R S R' S'] (a : S) (b : R') :
    equiv R S R' S' (a ⊗ₜ b) = algebraMap _ _ a * algebraMap _ _ b :=
  (h.out.equiv_tmul _ _).trans (Algebra.smul_def _ _)

lemma Algebra.IsPushout.equiv_symm_algebraMap_left [Algebra.IsPushout R S R' S'] (a : S) :
    (equiv R S R' S').symm (algebraMap S S' a) = a ⊗ₜ 1 := by
  rw [(equiv R S R' S').symm_apply_eq, equiv_tmul, map_one, mul_one]

lemma Algebra.IsPushout.equiv_symm_algebraMap_right [Algebra.IsPushout R S R' S'] (a : R') :
    (equiv R S R' S').symm (algebraMap R' S' a) = 1 ⊗ₜ a := by
  rw [(equiv R S R' S').symm_apply_eq, equiv_tmul, map_one, one_mul]

variable {R S R' S'}

@[symm]
theorem Algebra.IsPushout.symm (h : Algebra.IsPushout R S R' S') : Algebra.IsPushout R R' S S' where
  out := .of_equiv
    { __ := (TensorProduct.comm R ..).toAddEquiv.trans (equiv R S R' S').toAddEquiv,
      map_smul' _ x := x.induction_on (by simp) (fun _ _ ↦ by
        simp [equiv_tmul, Algebra.smul_def, mul_left_comm]) (by simp +contextual) }
    fun _ ↦ by simp [equiv_tmul]

variable (R S R' S')

theorem Algebra.IsPushout.comm : Algebra.IsPushout R S R' S' ↔ Algebra.IsPushout R R' S S' :=
  ⟨Algebra.IsPushout.symm, Algebra.IsPushout.symm⟩

instance : Algebra.IsPushout R R S S where
  out := .of_equiv (TensorProduct.lid R S) fun _ ↦ by simp

instance : Algebra.IsPushout R S R S := .symm inferInstance

variable {R S R'}

attribute [local instance] Algebra.TensorProduct.rightAlgebra

instance TensorProduct.isPushout {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]
    [Algebra R S] [Algebra R T] : Algebra.IsPushout R S T (S ⊗[R] T) :=
  ⟨TensorProduct.isBaseChange R T S⟩

instance TensorProduct.isPushout' {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]
    [Algebra R S] [Algebra R T] : Algebra.IsPushout R T S (S ⊗[R] T) :=
  Algebra.IsPushout.symm inferInstance

lemma Algebra.IsPushout.tensorProduct_tensorProduct
    (R S A B : Type*) [CommSemiring R] [CommSemiring S] [CommSemiring A] [CommSemiring B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [Algebra R S]
    {_ : Algebra (A ⊗[R] S) (B ⊗[R] S)} {_ : IsScalarTower A (A ⊗[R] S) (B ⊗[R] S)}
    (H : (algebraMap (A ⊗[R] S) (B ⊗[R] S)).comp Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom) :
    Algebra.IsPushout A B (A ⊗[R] S) (B ⊗[R] S) := by
  constructor
  convert isBaseChange_tensorProduct_map (R := R) (P := S) _ (IsBaseChange.linearMap A B)
  ext s
  simpa using congr($H s)

/-- If `S' = S ⊗[R] R'`, then any pair of `R`-algebra homomorphisms `f : S → A` and `g : R' → A`
such that `f x` and `g y` commutes for all `x, y` descends to a (unique) homomorphism `S' → A`.
-/
@[simps! -isSimp apply]
noncomputable def Algebra.pushoutDesc [H : Algebra.IsPushout R S R' S'] {A : Type*} [Semiring A]
    [Algebra R A] (f : S →ₐ[R] A) (g : R' →ₐ[R] A) (hf : ∀ x y, f x * g y = g y * f x) :
    S' →ₐ[R] A :=
  (Algebra.TensorProduct.lift f g hf).comp
    ((Algebra.IsPushout.equiv R S R' S').symm.toAlgHom.restrictScalars R)

@[simp]
theorem Algebra.pushoutDesc_left [Algebra.IsPushout R S R' S'] {A : Type*} [Semiring A]
    [Algebra R A] (f : S →ₐ[R] A) (g : R' →ₐ[R] A) (H) (x : S) :
    Algebra.pushoutDesc S' f g H (algebraMap S S' x) = f x := by
  simp [Algebra.pushoutDesc_apply]

theorem Algebra.lift_algHom_comp_left [Algebra.IsPushout R S R' S'] {A : Type*} [Semiring A]
    [Algebra R A] (f : S →ₐ[R] A) (g : R' →ₐ[R] A) (H) :
    (Algebra.pushoutDesc S' f g H).comp (toAlgHom R S S') = f :=
  AlgHom.ext fun x => (Algebra.pushoutDesc_left S' f g H x :)

@[simp]
theorem Algebra.pushoutDesc_right [Algebra.IsPushout R S R' S'] {A : Type*} [Semiring A]
    [Algebra R A] (f : S →ₐ[R] A) (g : R' →ₐ[R] A) (H) (x : R') :
    Algebra.pushoutDesc S' f g H (algebraMap R' S' x) = g x := by
  simp [Algebra.pushoutDesc_apply, Algebra.IsPushout.equiv_symm_algebraMap_right]

theorem Algebra.lift_algHom_comp_right [Algebra.IsPushout R S R' S'] {A : Type*} [Semiring A]
    [Algebra R A] (f : S →ₐ[R] A) (g : R' →ₐ[R] A) (H) :
    (Algebra.pushoutDesc S' f g H).comp (toAlgHom R R' S') = g :=
  AlgHom.ext fun x => (Algebra.pushoutDesc_right S' f g H x :)

@[ext (iff := false)]
theorem Algebra.IsPushout.algHom_ext [H : Algebra.IsPushout R S R' S'] {A : Type*} [Semiring A]
    [Algebra R A] {f g : S' →ₐ[R] A} (h₁ : f.comp (toAlgHom R R' S') = g.comp (toAlgHom R R' S'))
    (h₂ : f.comp (toAlgHom R S S') = g.comp (toAlgHom R S S')) : f = g := by
  ext x
  refine H.1.inductionOn x _ ?_ ?_ ?_ ?_
  · simp only [map_zero]
  · exact AlgHom.congr_fun h₁
  · intro s s' e
    rw [Algebra.smul_def, map_mul, map_mul, e]
    congr 1
    exact (AlgHom.congr_fun h₂ s :)
  · intro s₁ s₂ e₁ e₂
    rw [map_add, map_add, e₁, e₂]

variable (R S R')
/--
Let the following be a commutative diagram of rings
```
  R  →  S  →  T
  ↓     ↓     ↓
  R' →  S' →  T'
```
where the left-hand square is a pushout. Then the following are equivalent:
- the big rectangle is a pushout.
- the right-hand square is a pushout.

Note that this is essentially the isomorphism `T ⊗[S] (S ⊗[R] R') ≃ₐ[T] T ⊗[R] R'`.
-/
lemma Algebra.IsPushout.comp_iff {T' : Type*} [CommSemiring T'] [Algebra R T']
    [Algebra S' T'] [Algebra S T'] [Algebra T T'] [Algebra R' T']
    [IsScalarTower R T T'] [IsScalarTower S T T'] [IsScalarTower S S' T']
    [IsScalarTower R R' T'] [IsScalarTower R S' T'] [IsScalarTower R' S' T']
    [Algebra.IsPushout R S R' S'] :
    Algebra.IsPushout R T R' T' ↔ Algebra.IsPushout S T S' T' := by
  let f : R' →ₗ[R] S' := (IsScalarTower.toAlgHom R R' S').toLinearMap
  haveI : IsScalarTower R S T' := .of_algebraMap_eq fun x ↦ by
    rw [algebraMap_apply R S' T', algebraMap_apply R S S', ← algebraMap_apply S S' T']
  have heq : (toAlgHom S S' T').toLinearMap.restrictScalars R ∘ₗ f =
      (toAlgHom R R' T').toLinearMap := by
    ext x
    simp [f, ← IsScalarTower.algebraMap_apply]
  rw [isPushout_iff, isPushout_iff, ← heq, IsBaseChange.comp_iff]
  exact Algebra.IsPushout.out

variable {R R' S S'} in
lemma Algebra.IsPushout.of_equiv [h : IsPushout R R' S S']
    {T : Type*} [CommSemiring T] [Algebra R' T] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [IsScalarTower R R' T] (e : S' ≃ₐ[R'] T)
    (he : e.toRingHom.comp (algebraMap S S') = algebraMap S T) :
    IsPushout R R' S T := by
  rw [isPushout_iff] at h ⊢
  refine IsBaseChange.of_equiv (h.equiv ≪≫ₗ e.toLinearEquiv) fun x ↦ ?_
  simpa [h.equiv_tmul] using DFunLike.congr_fun he x

namespace Algebra

variable (A B : Type*)
  [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]
variable (M : Type*) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- (Implementation) If `B = S ⊗[R] A`, this is the canonical `R`-isomorphism:
`B ⊗[A] M ≃ₗ[S] S ⊗[R] M`. See `IsPushout.cancelBaseChange` for the `S`-linear version. -/
noncomputable
def IsPushout.cancelBaseChangeAux : B ⊗[A] M ≃ₗ[R] S ⊗[R] M :=
  have : IsPushout R A S B := IsPushout.symm inferInstance
  (AlgebraTensorModule.congr ((IsPushout.equiv R A S B).toLinearEquiv).symm
      (LinearEquiv.refl _ _)).restrictScalars R ≪≫ₗ
    (_root_.TensorProduct.comm _ _ _).restrictScalars R ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange _ _ A _ _).restrictScalars R ≪≫ₗ
    (_root_.TensorProduct.comm _ _ _).restrictScalars R

@[simp]
lemma IsPushout.cancelBaseChangeAux_symm_tmul (s : S) (m : M) :
    (IsPushout.cancelBaseChangeAux R S A B M).symm (s ⊗ₜ m) = algebraMap S B s ⊗ₜ m := by
  simp [IsPushout.cancelBaseChangeAux, IsPushout.equiv_tmul]

/-- If `B = S ⊗[R] A`, this is the canonical `S`-isomorphism: `B ⊗[A] M ≃ₗ[S] S ⊗[R] M`.
This is the cancelling on the left version of
`TensorProduct.AlgebraTensorModule.cancelBaseChange`. -/
noncomputable
def IsPushout.cancelBaseChange : B ⊗[A] M ≃ₗ[S] S ⊗[R] M :=
  LinearEquiv.symm <|
  AddEquiv.toLinearEquiv (IsPushout.cancelBaseChangeAux R S A B M).symm <| by
    intro s x
    induction x with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul s' m => simp [Algebra.smul_def, TensorProduct.smul_tmul']

@[simp]
lemma IsPushout.cancelBaseChange_tmul (m : M) :
    IsPushout.cancelBaseChange R S A B M (1 ⊗ₜ m) = 1 ⊗ₜ m := by
  change ((cancelBaseChangeAux R S A B M).symm).symm (1 ⊗ₜ[A] m) = 1 ⊗ₜ[R] m
  simp [cancelBaseChangeAux, TensorProduct.one_def]

@[simp]
lemma IsPushout.cancelBaseChange_symm_tmul (s : S) (m : M) :
    (IsPushout.cancelBaseChange R S A B M).symm (s ⊗ₜ m) = algebraMap S B s ⊗ₜ m :=
  IsPushout.cancelBaseChangeAux_symm_tmul R S A B M s m

variable (C : Type*) [CommRing C] [Algebra R C] [Algebra A C] [IsScalarTower R A C]

/-- Algebra version of `IsPushout.cancelBaseChange`. -/
noncomputable def IsPushout.cancelBaseChangeAlg : B ⊗[A] C ≃ₐ[S] S ⊗[R] C := by
  refine AlgEquiv.symm
    (AlgEquiv.ofLinearEquiv (IsPushout.cancelBaseChange R S A B C).symm ?_ ?_)
  · simp [TensorProduct.one_def]
  · apply LinearMap.map_mul_of_map_mul_tmul
    simp

@[simp]
lemma IsPushout.toLinearEquiv_cancelBaseChangeAlg :
    (IsPushout.cancelBaseChangeAlg R S A B C).toLinearEquiv =
      IsPushout.cancelBaseChange R S A B C := by
  rfl

@[simp]
lemma IsPushout.cancelBaseChangeAlg_tmul (c : C) :
    IsPushout.cancelBaseChangeAlg R S A B C (1 ⊗ₜ c) = 1 ⊗ₜ c := by
  simp [cancelBaseChangeAlg]

@[simp]
lemma IsPushout.cancelBaseChangeAlg_symm_tmul (s : S) (c : C) :
    (IsPushout.cancelBaseChangeAlg R S A B C).symm (s ⊗ₜ c) = algebraMap S B s ⊗ₜ c := by
  simp [cancelBaseChangeAlg]

variable (S : Type*) [CommRing S] [Algebra R S] [Algebra S B] [IsScalarTower R S B]
  [Algebra.IsPushout R S A B]

attribute [local instance] TensorProduct.rightAlgebra in
lemma IsPushout.cancelBaseChange_symm_comp_lTensor :
    AlgHom.comp (IsPushout.cancelBaseChangeAlg R S A (S ⊗[R] A) C).symm.toAlgHom
      (TensorProduct.lTensor _ (IsScalarTower.toAlgHom R A C)) =
      TensorProduct.includeLeft := by
  ext
  simp [← TensorProduct.one_def, ← TensorProduct.tmul_one_eq_one_tmul, RingHom.algebraMap_toAlgebra]

end Algebra

end IsBaseChange
