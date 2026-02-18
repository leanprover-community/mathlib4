/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import Mathlib.LinearAlgebra.SModEq.Pointwise
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Algebra.DirectSum.Finsupp

/-!
# Functoriality of adic completions

In this file we establish functorial properties of the adic completion.

## Main definitions

- `AdicCauchySequence.map I f`: the linear map on `I`-adic Cauchy sequences induced by `f`
- `AdicCompletion.map I f`: the linear map on `I`-adic completions induced by `f`

## Main results

- `sumEquivOfFintype`: adic completion commutes with finite sums
- `piEquivOfFintype`: adic completion commutes with finite products

-/

@[expose] public section

suppress_compilation

variable {R : Type*} [CommRing R] (I : Ideal R)
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {P : Type*} [AddCommGroup P] [Module R P]
variable {T : Type*} [AddCommGroup T] [Module (AdicCompletion I R) T]

namespace LinearMap

set_option backward.privateInPublic true in
/-- `R`-linear version of `reduceModIdeal`. -/
private def reduceModIdealAux (f : M →ₗ[R] N) :
    M ⧸ (I • ⊤ : Submodule R M) →ₗ[R] N ⧸ (I • ⊤ : Submodule R N) :=
  Submodule.mapQ (I • ⊤ : Submodule R M) (I • ⊤ : Submodule R N) f
    (fun x hx ↦ by
      refine Submodule.smul_induction_on hx (fun r hr x _ ↦ ?_) (fun x y hx hy ↦ ?_)
      · simp [Submodule.smul_mem_smul hr Submodule.mem_top]
      · simp [Submodule.add_mem _ hx hy])

@[local simp]
private theorem reduceModIdealAux_apply (f : M →ₗ[R] N) (x : M) :
    (f.reduceModIdealAux I) (Submodule.Quotient.mk (p := (I • ⊤ : Submodule R M)) x) =
      Submodule.Quotient.mk (p := (I • ⊤ : Submodule R N)) (f x) :=
  rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The induced linear map on the quotients mod `I • ⊤`. -/
def reduceModIdeal (f : M →ₗ[R] N) :
    M ⧸ (I • ⊤ : Submodule R M) →ₗ[R ⧸ I] N ⧸ (I • ⊤ : Submodule R N) where
  toFun := f.reduceModIdealAux I
  map_add' := by simp
  map_smul' r x := by
    refine Quotient.inductionOn' r (fun r ↦ ?_)
    refine Quotient.inductionOn' x (fun x ↦ ?_)
    simp only [Submodule.Quotient.mk''_eq_mk, Ideal.Quotient.mk_eq_mk, Module.Quotient.mk_smul_mk,
      Submodule.Quotient.mk_smul, LinearMapClass.map_smul, reduceModIdealAux_apply,
      RingHomCompTriple.comp_apply]

@[simp]
theorem reduceModIdeal_apply (f : M →ₗ[R] N) (x : M) :
    (f.reduceModIdeal I) (Submodule.Quotient.mk (p := (I • ⊤ : Submodule R M)) x) =
      Submodule.Quotient.mk (p := (I • ⊤ : Submodule R N)) (f x) :=
  rfl

end LinearMap

namespace AdicCompletion

open LinearMap

theorem transitionMap_comp_reduceModIdeal (f : M →ₗ[R] N) {m n : ℕ}
    (hmn : m ≤ n) : transitionMap I N hmn ∘ₗ f.reduceModIdeal (I ^ n) =
      (f.reduceModIdeal (I ^ m) : _ →ₗ[R] _) ∘ₗ transitionMap I M hmn := by
  ext x
  simp

namespace AdicCauchySequence

/-- A linear map induces a linear map on adic Cauchy sequences. -/
@[simps]
def map (f : M →ₗ[R] N) : AdicCauchySequence I M →ₗ[R] AdicCauchySequence I N where
  toFun a := ⟨fun n ↦ f (a n), fun {m n} hmn ↦ by
    have hm : Submodule.map f (I ^ m • ⊤ : Submodule R M) ≤ (I ^ m • ⊤ : Submodule R N) := by
      rw [Submodule.map_smul'']
      exact smul_mono_right _ le_top
    apply SModEq.mono hm
    apply SModEq.map (a.property hmn) f⟩
  map_add' a b := by ext n; simp
  map_smul' r a := by ext n; simp

variable (M) in
@[simp]
theorem map_id : map I (LinearMap.id (M := M)) = LinearMap.id :=
  rfl

theorem map_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    map I g ∘ₗ map I f = map I (g ∘ₗ f) :=
  rfl

theorem map_comp_apply (f : M →ₗ[R] N) (g : N →ₗ[R] P) (a : AdicCauchySequence I M) :
    map I g (map I f a) = map I (g ∘ₗ f) a :=
  rfl

@[simp]
theorem map_zero : map I (0 : M →ₗ[R] N) = 0 :=
  rfl

end AdicCauchySequence

set_option backward.privateInPublic true in
/-- `R`-linear version of `adicCompletion`. -/
private def adicCompletionAux (f : M →ₗ[R] N) :
    AdicCompletion I M →ₗ[R] AdicCompletion I N :=
  AdicCompletion.lift I (fun n ↦ reduceModIdeal (I ^ n) f ∘ₗ AdicCompletion.eval I M n)
    (fun {m n} hmn ↦ by rw [← comp_assoc, AdicCompletion.transitionMap_comp_reduceModIdeal,
        comp_assoc, transitionMap_comp_eval])

@[local simp]
private theorem adicCompletionAux_val_apply (f : M →ₗ[R] N) {n : ℕ} (x : AdicCompletion I M) :
    (adicCompletionAux I f x).val n = f.reduceModIdeal (I ^ n) (x.val n) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- A linear map induces a map on adic completions. -/
def map (f : M →ₗ[R] N) :
    AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I N where
  toFun := adicCompletionAux I f
  map_add' := by simp
  map_smul' r x := by
    ext n
    simp only [adicCompletionAux_val_apply, smul_eval, smul_eq_mul, RingHom.id_apply]
    rw [val_smul_eq_evalₐ_smul, val_smul_eq_evalₐ_smul, map_smul]

@[simp]
theorem map_val_apply (f : M →ₗ[R] N) {n : ℕ} (x : AdicCompletion I M) :
    (map I f x).val n = f.reduceModIdeal (I ^ n) (x.val n) :=
  rfl

/-- Equality of maps out of an adic completion can be checked on Cauchy sequences. -/
theorem map_ext {N} {f g : AdicCompletion I M → N}
    (h : ∀ (a : AdicCauchySequence I M),
      f (AdicCompletion.mk I M a) = g (AdicCompletion.mk I M a)) :
    f = g := by
  ext x
  apply induction_on I M x h

/-- Equality of linear maps out of an adic completion can be checked on Cauchy sequences. -/
@[ext]
theorem map_ext' {f g : AdicCompletion I M →ₗ[AdicCompletion I R] T}
    (h : ∀ (a : AdicCauchySequence I M),
      f (AdicCompletion.mk I M a) = g (AdicCompletion.mk I M a)) :
    f = g := by
  ext x
  apply induction_on I M x h

/-- Equality of linear maps out of an adic completion can be checked on Cauchy sequences. -/
@[ext]
theorem map_ext'' {f g : AdicCompletion I M →ₗ[R] N}
    (h : f.comp (AdicCompletion.mk I M) = g.comp (AdicCompletion.mk I M)) :
    f = g := by
  ext x
  apply induction_on I M x (fun a ↦ LinearMap.ext_iff.mp h a)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- A linear map induces a map on adic completions. -/
def map : (M →ₗ[R] N) →ₗ[R] AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I N where
  toFun f :=
    { toFun := adicCompletionAux I f
      map_add' := by simp
      map_smul' r x := by
        ext n
        simp only [adicCompletionAux_val_apply, smul_eval, smul_eq_mul, RingHom.id_apply]
        rw [val_smul_eq_evalₐ_smul, val_smul_eq_evalₐ_smul, map_smul] }
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

@[simp]
theorem map_val_apply (f : M →ₗ[R] N) {n : ℕ} (x : AdicCompletion I M) :
    (map I f x).val n = f.reduceModIdeal (I ^ n) (x.val n) :=
  rfl

variable (M) in
@[simp]
theorem map_id :
    map I (LinearMap.id (M := M)) =
      LinearMap.id (R := AdicCompletion I R) (M := AdicCompletion I M) := by
  ext a n
  simp

theorem map_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    map I g ∘ₗ map I f = map I (g ∘ₗ f) := by
  ext
  simp

theorem map_comp_apply (f : M →ₗ[R] N) (g : N →ₗ[R] P) (x : AdicCompletion I M) :
    map I g (map I f x) = map I (g ∘ₗ f) x := by
  change (map I g ∘ₗ map I f) x = map I (g ∘ₗ f) x
  rw [map_comp]

@[simp]
theorem map_mk (f : M →ₗ[R] N) (a : AdicCauchySequence I M) :
    map I f (AdicCompletion.mk I M a) =
      AdicCompletion.mk I N (AdicCauchySequence.map I f a) :=
  rfl

@[simp]
theorem map_zero : map I (0 : M →ₗ[R] N) = 0 := by
  ext
  simp

theorem map_of (f : M →ₗ[R] N) (x : M) : map I f (of I M x) = of I N (f x) :=
  rfl

/-- A linear equiv induces a linear equiv on adic completions. -/
def congr (f : M ≃ₗ[R] N) :
    AdicCompletion I M ≃ₗ[AdicCompletion I R] AdicCompletion I N :=
  LinearEquiv.ofLinear (map I f)
    (map I f.symm) (by simp [map_comp]) (by simp [map_comp])

@[simp]
theorem congr_apply (f : M ≃ₗ[R] N) (x : AdicCompletion I M) :
    congr I f x = map I f x :=
  rfl

@[simp]
theorem congr_symm_apply (f : M ≃ₗ[R] N) (x : AdicCompletion I N) :
    (congr I f).symm x = map I f.symm x :=
  rfl

section Families

/-! ### Adic completion in families

In this section we consider a family `M : ι → Type*` of `R`-modules. Purely from
the formal properties of adic completions we obtain two canonical maps

- `AdicCompletion I (∀ j, M j) →ₗ[R] ∀ j, AdicCompletion I (M j)`
- `(⨁ j, (AdicCompletion I (M j))) →ₗ[R] AdicCompletion I (⨁ j, M j)`

If `ι` is finite, both are isomorphisms and, modulo
the equivalence `⨁ j, (AdicCompletion I (M j)` and `∀ j, AdicCompletion I (M j)`,
inverse to each other.

-/

variable {ι : Type*} (M : ι → Type*) [∀ i, AddCommGroup (M i)]
  [∀ i, Module R (M i)]

section Pi

/-- The canonical map from the adic completion of the product to the product of the
adic completions. -/
@[simps!]
def pi : AdicCompletion I (∀ j, M j) →ₗ[AdicCompletion I R] ∀ j, AdicCompletion I (M j) :=
  LinearMap.pi (fun j ↦ map I (LinearMap.proj j))

end Pi

section Sum

open DirectSum

set_option backward.isDefEq.respectTransparency false in
/-- The canonical map from the sum of the adic completions to the adic completion
of the sum. -/
def sum [DecidableEq ι] :
    (⨁ j, (AdicCompletion I (M j))) →ₗ[AdicCompletion I R] AdicCompletion I (⨁ j, M j) :=
  toModule (AdicCompletion I R) ι (AdicCompletion I (⨁ j, M j))
    (fun j ↦ map I (lof R ι M j))

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem sum_lof [DecidableEq ι] (j : ι) (x : AdicCompletion I (M j)) :
    sum I M ((DirectSum.lof (AdicCompletion I R) ι (fun i ↦ AdicCompletion I (M i)) j) x) =
      map I (lof R ι M j) x := by
  simp [sum]

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem sum_of [DecidableEq ι] (j : ι) (x : AdicCompletion I (M j)) :
    sum I M ((DirectSum.of (fun i ↦ AdicCompletion I (M i)) j) x) =
      map I (lof R ι M j) x := by
  rw [← lof_eq_of R]
  apply sum_lof

variable [Fintype ι]

set_option backward.isDefEq.respectTransparency false in
/-- If `ι` is finite, we use the equivalence of sum and product to obtain an inverse for
`AdicCompletion.sum` from `AdicCompletion.pi`. -/
def sumInv : AdicCompletion I (⨁ j, M j) →ₗ[AdicCompletion I R] (⨁ j, (AdicCompletion I (M j))) :=
  letI f := map I (linearEquivFunOnFintype R ι M)
  letI g := linearEquivFunOnFintype (AdicCompletion I R) ι (fun j ↦ AdicCompletion I (M j))
  g.symm.toLinearMap ∘ₗ pi I M ∘ₗ f

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem component_sumInv (x : AdicCompletion I (⨁ j, M j)) (j : ι) :
    component (AdicCompletion I R) ι _ j (sumInv I M x) =
      map I (component R ι _ j) x := by
  apply induction_on I _ x (fun x ↦ ?_)
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem sumInv_apply (x : AdicCompletion I (⨁ j, M j)) (j : ι) :
    (sumInv I M x) j = map I (component R ι _ j) x := by
  apply induction_on I _ x (fun x ↦ ?_)
  rfl

variable [DecidableEq ι]

set_option backward.isDefEq.respectTransparency false in
theorem sumInv_comp_sum : sumInv I M ∘ₗ sum I M = LinearMap.id := by
  ext j x : 2
  apply DirectSum.ext_component (AdicCompletion I R) (fun i ↦ ?_)
  ext n
  simp only [LinearMap.coe_comp, Function.comp_apply, sum_lof, map_mk, component_sumInv,
    mk_apply_coe, AdicCauchySequence.map_apply_coe, Submodule.mkQ_apply, LinearMap.id_comp]
  rw [DirectSum.component.of, DirectSum.component.of]
  split
  · next h => subst h; simp
  · simp

set_option backward.isDefEq.respectTransparency false in
theorem sum_comp_sumInv : sum I M ∘ₗ sumInv I M = LinearMap.id := by
  ext f n
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq, mk_apply_coe,
    Submodule.mkQ_apply]
  rw [← DirectSum.sum_univ_of (((sumInv I M) ((AdicCompletion.mk I (⨁ (j : ι), M j)) f)))]
  simp only [sumInv_apply, map_mk, map_sum, sum_of, val_sum_apply, mk_apply_coe,
    AdicCauchySequence.map_apply_coe]
  simp only [← Submodule.mkQ_apply, ← map_sum, ← apply_eq_component, lof_eq_of,
    DirectSum.sum_univ_of]

set_option backward.isDefEq.respectTransparency false in
/-- If `ι` is finite, `sum` has `sumInv` as inverse. -/
def sumEquivOfFintype :
    (⨁ j, (AdicCompletion I (M j))) ≃ₗ[AdicCompletion I R] AdicCompletion I (⨁ j, M j) :=
  LinearEquiv.ofLinear (sum I M) (sumInv I M) (sum_comp_sumInv I M) (sumInv_comp_sum I M)

@[simp]
theorem sumEquivOfFintype_apply (x : ⨁ j, (AdicCompletion I (M j))) :
    sumEquivOfFintype I M x = sum I M x :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem sumEquivOfFintype_symm_apply (x : AdicCompletion I (⨁ j, M j)) :
    (sumEquivOfFintype I M).symm x = sumInv I M x :=
  rfl

end Sum

section Pi

open DirectSum

variable [DecidableEq ι] [Fintype ι]

set_option backward.isDefEq.respectTransparency false in
/-- If `ι` is finite, `pi` is a linear equiv. -/
def piEquivOfFintype :
    AdicCompletion I (∀ j, M j) ≃ₗ[AdicCompletion I R] ∀ j, AdicCompletion I (M j) :=
  letI f := (congr I (linearEquivFunOnFintype R ι M)).symm
  letI g := (linearEquivFunOnFintype (AdicCompletion I R) ι (fun j ↦ AdicCompletion I (M j)))
  f.trans ((sumEquivOfFintype I M).symm.trans g)

@[simp]
theorem piEquivOfFintype_apply (x : AdicCompletion I (∀ j, M j)) :
    piEquivOfFintype I M x = pi I M x := by
  simp [piEquivOfFintype, sumInv, map_comp_apply]

/-- Adic completion of `R^n` is `(AdicCompletion I R)^n`. -/
def piEquivFin (n : ℕ) :
    AdicCompletion I (Fin n → R) ≃ₗ[AdicCompletion I R] Fin n → AdicCompletion I R :=
  piEquivOfFintype I (ι := Fin n) (fun _ : Fin n ↦ R)

@[simp]
theorem piEquivFin_apply (n : ℕ) (x : AdicCompletion I (Fin n → R)) :
    piEquivFin I n x = pi I (fun _ : Fin n ↦ R) x := by
  simp only [piEquivFin, piEquivOfFintype_apply]

end Pi

end Families

open Submodule

variable {I}

theorem exists_smodEq_pow_add_one_smul {f : M →ₗ[R] N}
    (h : Function.Surjective (mkQ (I • ⊤) ∘ₗ f)) {y : N} {n : ℕ}
    (hy : y ∈ (I ^ n • ⊤ : Submodule R N)) :
    ∃ x ∈ (I ^ n • ⊤ : Submodule R M), f x ≡ y [SMOD (I ^ (n + 1) • ⊤ : Submodule R N)] := by
  induction hy using smul_induction_on' with
  | smul r hr y _ =>
    obtain ⟨x, hx⟩ := h (mkQ _ y)
    use r • x, smul_mem_smul hr mem_top
    simp only [coe_comp, Function.comp_apply, mkQ_apply, ← SModEq.def, map_smul] at ⊢ hx
    rw [pow_succ, ← smul_smul]
    exact SModEq.smul' hx hr
  | add y1 hy1 y2 hy2 ih1 ih2 =>
    obtain ⟨x1, hx1, hx1'⟩ := ih1
    obtain ⟨x2, hx2, hx2'⟩ := ih2
    use x1 + x2, add_mem hx1 hx2
    simp only [map_add]
    exact SModEq.add hx1' hx2'

theorem exists_smodEq_pow_smul_top_and_smodEq_pow_add_one_smul_top {f : M →ₗ[R] N}
    (h : Function.Surjective (mkQ (I • ⊤) ∘ₗ f)) {x : M} {y : N} {n : ℕ}
    (hxy : f x ≡ y [SMOD (I ^ n • ⊤ : Submodule R N)]) :
    ∃ x' : M, x ≡ x' [SMOD (I ^ n • ⊤ : Submodule R M)] ∧
    f x' ≡ y [SMOD (I ^ (n + 1) • ⊤ : Submodule R N)] := by
  obtain ⟨z, hz, hz'⟩ :=
    exists_smodEq_pow_add_one_smul h (y := y - f x) (SModEq.sub_mem.mp hxy.symm)
  use x + z
  constructor
  · simpa [SModEq.sub_mem]
  · simpa [SModEq.sub_mem, sub_sub_eq_add_sub, add_comm] using hz'

theorem exists_smodEq_pow_smul_top_and_mkQ_eq {f : M →ₗ[R] N}
    (h : Function.Surjective (mkQ (I • ⊤) ∘ₗ f)) {x : M} {n : ℕ}
    {y : N ⧸ (I ^ n • ⊤ : Submodule R N)} {y' : N ⧸ (I ^ (n + 1) • ⊤ : Submodule R N)}
    (hyy' : factor (pow_smul_top_le I N n.le_succ) y' = y) (hxy : mkQ _ (f x) = y) :
    ∃ x' : M, x ≡ x' [SMOD (I ^ n • ⊤ : Submodule R M)] ∧ mkQ _ (f x') = y' := by
  obtain ⟨y0, hy0⟩ := mkQ_surjective _ y'
  have : f x ≡ y0 [SMOD (I ^ n • ⊤ : Submodule R N)] := by
    rw [SModEq, ← mkQ_apply, ← mkQ_apply, ← factor_mk (pow_smul_top_le I N n.le_succ) y0,
        hy0, hyy', hxy]
  obtain ⟨x', hxx', hx'y0⟩ :=
    exists_smodEq_pow_smul_top_and_smodEq_pow_add_one_smul_top h this
  use x', hxx'
  rwa [mkQ_apply, hx'y0]

theorem map_surjective_of_mkQ_comp_surjective {f : M →ₗ[R] N}
    (h : Function.Surjective (mkQ (I • ⊤) ∘ₗ f)) : Function.Surjective (map I f) := by
  intro y
  suffices h : ∃ x : ℕ → M, ∀ n, x n ≡ x (n + 1) [SMOD (I ^ n • ⊤ : Submodule R M)] ∧
      Submodule.Quotient.mk (f (x n)) = eval I _ n y by
    obtain ⟨x, hx⟩ := h
    use AdicCompletion.mk I M ⟨x, fun h ↦
        eq_factor_of_eq_factor_succ (fun _ _ ↦ pow_smul_top_le I M) _ (fun n ↦ (hx n).1) h⟩
    ext n
    simp [hx n]
  let x : (n : ℕ) → {m : M // Submodule.Quotient.mk (f m) = eval I _ n y} := fun n ↦ by
    induction n with
    | zero =>
      use 0
      apply_fun (Submodule.Quotient.equiv (I ^ 0 • ⊤) ⊤ (.refl R N) (by simp)).toEquiv
      exact Subsingleton.elim _ _
    | succ n xn =>
      choose z hz using exists_smodEq_pow_smul_top_and_mkQ_eq h
          (y' := eval _ _ (n + 1) y) (by simp) xn.2
      exact ⟨z, hz.2⟩
  exact ⟨fun n ↦ (x n).val, fun n ↦ ⟨(Classical.choose_spec (exists_smodEq_pow_smul_top_and_mkQ_eq
      h (y' := eval I _ (n + 1) y) (by simp) (x n).2)).1, (x n).property⟩⟩

section finsuppSum

open Finsupp

variable {σ : Type*}

variable (σ M I) in
/-- The canonical map from the finitely supported functions of adic completions to
the adic completion of finitely supported functions. This is an isomorphism if `σ` is finite. -/
def finsuppSum : (σ →₀ (AdicCompletion I M)) →ₗ[AdicCompletion I R] AdicCompletion I (σ →₀ M) :=
  lsum (AdicCompletion I R) fun i ↦ map I (lsingle i)

@[simp]
theorem finsuppSum_single_of (i : σ) (m : M) : finsuppSum I M σ (single i (of I M m)) =
    of I (σ →₀ M) (single i m) := by
  ext; simp [finsuppSum]

theorem map_finsuppLEquivDirectSum_comp_finsuppSum [DecidableEq σ] :
    map I (finsuppLEquivDirectSum R M σ) ∘ₗ finsuppSum I M σ = sum I (fun _ : σ ↦ M) ∘ₗ
      (finsuppLEquivDirectSum (AdicCompletion I R) (AdicCompletion I M) σ) := by
  ext; simp [finsuppSum]

variable [Fintype σ]

variable (σ M I) in
/-- If `σ` is finite, `AdicCompletion.finsuppSumInv` is
an inverse for `AdicCompletion.finsuppSum`. -/
def finsuppSumInv : AdicCompletion I (σ →₀ M) →ₗ[AdicCompletion I R] (σ →₀ (AdicCompletion I M)) :=
  (linearEquivFunOnFinite (AdicCompletion I R) (AdicCompletion I M) σ).symm ∘ₗ
    .pi (fun i ↦ map I (lapply i))

theorem finsuppSumInv_comp_sum : finsuppSumInv I M σ ∘ₗ finsuppSum I M σ = .id := by
  classical
  ext
  -- simp [finsuppSum, finsuppSumInv, single_apply]
  simp only [finsuppSumInv, finsuppSum, coe_comp, LinearEquiv.coe_coe, coe_lsum,
    Function.comp_apply, lsingle_apply, _root_.map_zero, sum_single_index, map_mk,
    linearEquivFunOnFinite_symm_apply, pi_apply, mk_apply_coe,
    AdicCauchySequence.map_apply_coe, lapply_apply, Finsupp.single_apply, mkQ_apply,
    id_comp]
  split <;> simp

theorem finsuppSum_comp_sumInv : finsuppSum I M σ ∘ₗ finsuppSumInv I M σ = .id := by
  refine LinearMap.ext fun _ ↦ ?_
  simp [finsuppSum, finsuppSumInv, sum_fintype, map_comp_apply]
  simp [← LinearMap.sum_apply, ← map_sum, sum_lsingle_comp_lapply]

@[simp]
theorem finsuppSumInv_single_of (i : σ) (m : M) :
    finsuppSumInv I M σ (of I (σ →₀ M) (single i m)) = single i (of I M m) := by
  simp [← finsuppSum_single_of, ← comp_apply, finsuppSumInv_comp_sum]

end finsuppSum

end AdicCompletion

open AdicCompletion Submodule

variable {I}

theorem surjective_of_mkQ_comp_surjective [IsPrecomplete I M] [IsHausdorff I N]
    {f : M →ₗ[R] N} (h : Function.Surjective (mkQ (I • ⊤) ∘ₗ f)) : Function.Surjective f := by
  intro y
  obtain ⟨x', hx'⟩ := AdicCompletion.map_surjective_of_mkQ_comp_surjective h (of I N y)
  obtain ⟨x, hx⟩ := of_surjective I M x'
  use x
  rwa [← of_inj (I := I), ← map_of, hx]

variable {S : Type*} [CommRing S] (f : R →+* S)

theorem surjective_of_mk_map_comp_surjective [IsPrecomplete I R] [haus : IsHausdorff (I.map f) S]
    (h : Function.Surjective ((Ideal.Quotient.mk (I.map f)).comp f)) :
    Function.Surjective f := by
  let _ := f.toAlgebra
  let fₗ := (Algebra.ofId R S).toLinearMap
  change Function.Surjective ((restrictScalars R (I.map f)).mkQ ∘ₗ fₗ) at h
  have : I • ⊤ = restrictScalars R (Ideal.map f I) := by
    simp only [Ideal.smul_top_eq_map, restrictScalars_inj]
    rfl
  have _ := IsHausdorff.map_algebraMap_iff.mp haus
  apply surjective_of_mkQ_comp_surjective (I := I) (f := fₗ)
  rwa [Ideal.smul_top_eq_map]
