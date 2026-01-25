/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yaël Dillies
-/
module
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Coalgebra.Basic
public import Mathlib.RingTheory.Coalgebra.SimpAttr

/-!
# Tactic to reassociate comultiplication in a coalgebra

`coassoc_simps` is a simp set useful to prove tautologies on coalgebras.

The general algorithm it follows is to push the associators `TensorProduct.assoc` and
commutators `TensorProduct.comm` inwards (to the right) until they cancel against
co-multiplications.

The simp set makes the following choice of normal form
* It regards `TensorProduct.map`, `TensorProduct.assoc`, `TensorProduct.comm` as the primitive
  constructions and rewrites everything else such as `lTensor`, `leftComm` using them.
* It rewrites both sides into a right associated composition of linear maps.
  In particular `LinearMap.comp_assoc` and `LinearEquiv.coe_trans` are tagged.
* It rewrites `(f₂ ⊗ g₂) ∘ (f₁ ⊗ g₁)` into `(f₂ ∘ f₁) ⊗ (g₂ ∘ g₁)`.

## Notes

- It is not confluent with `(ε ⊗ₘ id) ∘ₗ δ = λ⁻¹`.
  It is often useful to `trans` (or `calc`) with a term containing
  `(ε ⊗ₘ _) ∘ₗ δ` or `(_ ⊗ₘ ε) ∘ₗ δ`,
  and use one of `map_counit_comp_comul_left` `map_counit_comp_comul_right`
  `map_counit_comp_comul_left_assoc` `map_counit_comp_comul_right_assoc` to continue.

- Some lemmas (e.g. `lid_comp_map : λ ∘ₗ (f ⊗ₘ g) = g ∘ₗ λ ∘ₗ (f ⊗ₘ id)`) loops when tagged as simp,
  so we wrap it inside a rudimentary simproc that only fires when `g ≠ id`.
-/

@[expose] public section

open TensorProduct

open LinearMap (id)
open Coalgebra

open Qq
namespace CoassocSimps

variable {R A M N P M' N' P' Q Q' : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
    [Coalgebra R A]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]
    [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']
    [AddCommMonoid P'] [Module R P'] [AddCommMonoid Q] [Module R Q] [AddCommMonoid Q'] [Module R Q']
    {M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [AddCommMonoid M₁]
    [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid N₁] [AddCommMonoid N₂] [AddCommMonoid N₃]
    [Module R M₁] [Module R M₂] [Module R M₃] [Module R N₁] [Module R N₂] [Module R N₃]

local notation3 "α" => (TensorProduct.assoc R _ _ _).toLinearMap
local notation3 "α⁻¹" => (TensorProduct.assoc R _ _ _).symm.toLinearMap
local notation3 "λ" => (TensorProduct.lid R _).toLinearMap
local notation3 "λ⁻¹" => (TensorProduct.lid R _).symm.toLinearMap
local notation3 "ρ" => (TensorProduct.rid R _).toLinearMap
local notation3 "ρ⁻¹" => (TensorProduct.rid R _).symm.toLinearMap
local notation3 "β" => (TensorProduct.comm R _ _).toLinearMap
local infix:90 " ⊗ₘ " => TensorProduct.map
local notation3 "δ" => comul (R := R)
local notation3 "ε" => counit (R := R)

attribute [coassoc_simps] LinearMap.comp_id LinearMap.id_comp TensorProduct.map_id
  LinearMap.lTensor_def LinearMap.rTensor_def LinearMap.comp_assoc
  LinearEquiv.coe_trans LinearEquiv.trans_symm
  LinearEquiv.refl_toLinearMap TensorProduct.toLinearMap_congr
  LinearEquiv.comp_symm LinearEquiv.symm_comp LinearEquiv.symm_symm
  LinearEquiv.coe_lTensor LinearEquiv.coe_lTensor_symm
  LinearEquiv.coe_rTensor LinearEquiv.coe_rTensor_symm
  IsCocomm.comm_comp_comul TensorProduct.AlgebraTensorModule.map_eq
  TensorProduct.AlgebraTensorModule.assoc_eq TensorProduct.AlgebraTensorModule.rightComm_eq
  TensorProduct.tensorTensorTensorComm TensorProduct.AlgebraTensorModule.tensorTensorTensorComm
  TensorProduct.AlgebraTensorModule.congr_eq LinearEquiv.comp_symm_assoc
  LinearEquiv.symm_comp_assoc TensorProduct.rightComm_def TensorProduct.leftComm_def
  TensorProduct.comm_symm TensorProduct.comm_comp_comm TensorProduct.comm_comp_comm_assoc

attribute [coassoc_simps← ] TensorProduct.map_comp TensorProduct.map_map_comp_assoc_eq
  TensorProduct.map_map_comp_assoc_symm_eq

@[coassoc_simps]
lemma TensorProduct.map_comp_assoc
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (f' : M' →ₗ[R] N') (g' : N' →ₗ[R] P') (φ : M₁ →ₗ[R] M ⊗[R] M') :
    map g g' ∘ₗ map f f' ∘ₗ φ = map (g ∘ₗ f) (g' ∘ₗ f') ∘ₛₗ φ := by
  rw [← LinearMap.comp_assoc, TensorProduct.map_comp]

@[coassoc_simps← ]
lemma TensorProduct.map_map_comp_assoc_eq_assoc
    (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂) (f₃ : M₃ →ₗ[R] N₃) (f : M →ₗ[R] M₁ ⊗[R] M₂ ⊗[R] M₃) :
    f₁ ⊗ₘ (f₂ ⊗ₘ f₃) ∘ₗ α ∘ₗ f = α ∘ₗ ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ∘ₗ f := by
  rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc, TensorProduct.map_map_comp_assoc_eq]

@[coassoc_simps← ]
lemma TensorProduct.map_map_comp_assoc_symm_eq_assoc
    (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂) (f₃ : M₃ →ₗ[R] N₃) (f : M →ₗ[R] M₁ ⊗[R] (M₂ ⊗[R] M₃)) :
    (f₁ ⊗ₘ f₂) ⊗ₘ f₃ ∘ₗ α⁻¹ ∘ₗ f = α⁻¹ ∘ₗ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃)) ∘ₗ f := by
  rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc, TensorProduct.map_map_comp_assoc_symm_eq]

@[coassoc_simps]
lemma assoc_comp_map_map_comp
    (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂) (f₃ : M₃ →ₗ[R] N₃) (f₁₂ : M →ₗ[R] M₁ ⊗[R] M₂) :
    α ∘ₗ (((f₁ ⊗ₘ f₂) ∘ₗ f₁₂) ⊗ₘ f₃) = (f₁ ⊗ₘ (f₂ ⊗ₘ f₃)) ∘ₗ α ∘ₗ (f₁₂ ⊗ₘ id) := by
  rw [← LinearMap.comp_assoc, map_map_comp_assoc_eq]
  ext
  rfl

@[coassoc_simps]
lemma assoc_comp_map_map_comp_assoc
    (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂) (f₃ : M₃ →ₗ[R] N₃) (f₁₂ : M →ₗ[R] M₁ ⊗[R] M₂)
    (f : M →ₗ[R] M ⊗[R] M₃) :
    α ∘ₗ (((f₁ ⊗ₘ f₂) ∘ₗ f₁₂) ⊗ₘ f₃) ∘ₗ f =
      (f₁ ⊗ₘ (f₂ ⊗ₘ f₃)) ∘ₗ α ∘ₗ (f₁₂ ⊗ₘ id) ∘ₗ f := by
  simp only [← LinearMap.comp_assoc, assoc_comp_map_map_comp]

-- This loops when tagged as a simp lemma,
-- so we turn it into a simproc that only fires when `f₃ ≠ id`.
lemma assoc_comp_map (f₃ : M₃ →ₗ[R] N₃) (f₁₂ : M →ₗ[R] M₁ ⊗[R] M₂) :
    α ∘ₗ (f₁₂ ⊗ₘ f₃) = (id ⊗ₘ (id ⊗ₘ f₃)) ∘ₗ α ∘ₗ (f₁₂ ⊗ₘ id) := by
  rw [← LinearMap.comp_assoc, map_map_comp_assoc_eq]
  simp only [coassoc_simps]

/-- Simproc version of `assoc_comp_map` that only fires when `f₃ ≠ id`. -/
simproc_decl assoc_comp_map_simproc
    ((TensorProduct.assoc _ _ _ _).toLinearMap ∘ₗ (_ ⊗ₘ _)) := .ofQ fun _ t e ↦ do
  match_expr t with
  | LinearMap R _ _ _ _ T₁ T₂ _ _ _ _ =>
    match_expr T₁ with
    | TensorProduct _ instR M M₃ instM instM₃ instRM instRM₃ =>
      match_expr T₂ with
      | TensorProduct _ _ M₁ T₃ instM₁ _ instRM₁ _ =>
        match_expr T₃ with
        | TensorProduct _ _ M₂ N₃ instM₂ instN₃ instRM₂ instRN₃ =>
          let .succ u₁ := (← Lean.Meta.inferType R).sortLevel! | return .continue
          let .succ u₂ := (← Lean.Meta.inferType M).sortLevel! | return .continue
          let .succ u₃ := (← Lean.Meta.inferType M₁).sortLevel! | return .continue
          let .succ u₄ := (← Lean.Meta.inferType M₂).sortLevel! | return .continue
          let .succ u₅ := (← Lean.Meta.inferType M₃).sortLevel! | return .continue
          let .succ u₆ := (← Lean.Meta.inferType N₃).sortLevel! | return .continue
          have R  : Q(Type u₁) := R
          have M  : Q(Type u₂) := M
          have M₁ : Q(Type u₃) := M₁
          have M₂ : Q(Type u₄) := M₂
          have M₃ : Q(Type u₅) := M₃
          have N₃ : Q(Type u₆) := N₃
          have : Q(CommSemiring $R) := instR
          have : Q(AddCommMonoid $M) := instM
          have : Q(AddCommMonoid $M₁) := instM₁
          have : Q(AddCommMonoid $M₂) := instM₂
          have : Q(AddCommMonoid $M₃) := instM₃
          have : Q(AddCommMonoid $N₃) := instN₃
          have : Q(Module $R $M) := instRM
          have : Q(Module $R $M₁) := instRM₁
          have : Q(Module $R $M₂) := instRM₂
          have : Q(Module $R $M₃) := instRM₃
          have : Q(Module $R $N₃) := instRN₃
          have e : Q($M ⊗[$R] $M₃ →ₗ[$R] $M₁ ⊗[$R] ($M₂ ⊗[$R] $N₃)) := e
          match e with
          | ~q((TensorProduct.assoc «$R» «$M₁» «$M₂» «$N₃»).toLinearMap ∘ₗ ($f₁₂ ⊗ₘ $f₃)) =>
            match_expr f₃ with
            | LinearMap.id _ _ _ _ _ => return .continue
            | _ => return .visit (e := e) (.mk q((id ⊗ₘ (id ⊗ₘ $f₃)) ∘ₗ
                  (TensorProduct.assoc _ _ _ _).toLinearMap ∘ₗ ($f₁₂ ⊗ₘ id))
                (some q(assoc_comp_map ..)))
          | _ => return Lean.Meta.Simp.StepQ.continue
        | _ => return Lean.Meta.Simp.StepQ.continue
      | _ => return Lean.Meta.Simp.StepQ.continue
    | _ => return Lean.Meta.Simp.StepQ.continue
  | _ => return .continue

attribute [coassoc_simps] assoc_comp_map_simproc

-- This loops when tagged as a simp lemma,
-- so we turn it into a simproc that only fires when `f₃ ≠ id`.
lemma assoc_comp_map_assoc (f₃ : M₃ →ₗ[R] N₃)
    (f₁₂ : M →ₗ[R] M₁ ⊗[R] M₂) (f : P →ₗ[R] M ⊗[R] M₃) :
    α ∘ₗ (f₁₂ ⊗ₘ f₃) ∘ₗ f = (id ⊗ₘ (id ⊗ₘ f₃)) ∘ₗ α ∘ₗ (f₁₂ ⊗ₘ id) ∘ₗ f := by
  rw [← LinearMap.comp_assoc, assoc_comp_map]
  simp only [coassoc_simps]

/-- Simproc version of `assoc_comp_map_assoc` that only fires when `f₃ ≠ id`. -/
simproc_decl assoc_comp_map_assoc_simproc
    ((TensorProduct.assoc _ _ _ _).toLinearMap ∘ₗ (_ ⊗ₘ _) ∘ₗ _) := .ofQ fun _ _ e ↦ do
  match_expr e with
  | LinearMap.comp R _ _ P _ T₂ _ _ _ instP _ _ instRP _ _ _ _ _ _ _ e' => do
    match_expr e' with
    | LinearMap.comp _ _ _ _ T₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => do
      match_expr T₁ with
      | TensorProduct _ instR M M₃ instM instM₃ instRM instRM₃ =>
        match_expr T₂ with
        | TensorProduct _ _ M₁ T₃ instM₁ _ instRM₁ _ =>
          match_expr T₃ with
          | TensorProduct _ _ M₂ N₃ instM₂ instN₃ instRM₂ instRN₃ =>
            let .succ u₁ := (← Lean.Meta.inferType R).sortLevel! | return .continue
            let .succ u₂ := (← Lean.Meta.inferType M).sortLevel! | return .continue
            let .succ u₃ := (← Lean.Meta.inferType M₁).sortLevel! | return .continue
            let .succ u₄ := (← Lean.Meta.inferType M₂).sortLevel! | return .continue
            let .succ u₅ := (← Lean.Meta.inferType M₃).sortLevel! | return .continue
            let .succ u₆ := (← Lean.Meta.inferType N₃).sortLevel! | return .continue
            let .succ u₇ := (← Lean.Meta.inferType P).sortLevel! | return .continue
            have R  : Q(Type u₁) := R
            have M  : Q(Type u₂) := M
            have M₁ : Q(Type u₃) := M₁
            have M₂ : Q(Type u₄) := M₂
            have M₃ : Q(Type u₅) := M₃
            have N₃ : Q(Type u₆) := N₃
            have P  : Q(Type u₇) := P
            have : Q(CommSemiring $R) := instR
            have : Q(AddCommMonoid $M) := instM
            have : Q(AddCommMonoid $M₁) := instM₁
            have : Q(AddCommMonoid $M₂) := instM₂
            have : Q(AddCommMonoid $M₃) := instM₃
            have : Q(AddCommMonoid $N₃) := instN₃
            have : Q(AddCommMonoid $P)  := instP
            have : Q(Module $R $M) := instRM
            have : Q(Module $R $M₁) := instRM₁
            have : Q(Module $R $M₂) := instRM₂
            have : Q(Module $R $M₃) := instRM₃
            have : Q(Module $R $N₃) := instRN₃
            have : Q(Module $R $P) := instRP
            have e : Q($P →ₗ[$R] $M₁ ⊗[$R] ($M₂ ⊗[$R] $N₃)) := e
            match e with
            | ~q((TensorProduct.assoc «$R» «$M₁» «$M₂» «$N₃»).toLinearMap ∘ₗ
                ($f₁₂ ⊗ₘ $f₃) ∘ₗ ($f : _ →ₗ[_] «$M» ⊗ «$M₃»)) =>
              match_expr f₃ with
              | LinearMap.id _ _ _ _ _ => return .continue
              | _ => return .visit (e := e) (.mk q((id ⊗ₘ (id ⊗ₘ $f₃)) ∘ₗ
                    (TensorProduct.assoc _ _ _ _).toLinearMap ∘ₗ ($f₁₂ ⊗ₘ id) ∘ₗ $f)
                  (some q(assoc_comp_map_assoc ..)))
            | _ => return Lean.Meta.Simp.StepQ.continue
          | _ => return Lean.Meta.Simp.StepQ.continue
        | _ => return Lean.Meta.Simp.StepQ.continue
      | _ => return Lean.Meta.Simp.StepQ.continue
    | _ => return Lean.Meta.Simp.StepQ.continue
  | _ => return .continue

attribute [coassoc_simps] assoc_comp_map_assoc_simproc

-- This loops when tagged as a simp lemma,
-- so we turn it into a simproc that only fires when `f₁ ≠ id`.
lemma asssoc_symm_comp_map
    (f₁ : M₁ →ₗ[R] N₁) (f₂₃ : M →ₗ[R] M₂ ⊗[R] M₃) :
    α⁻¹ ∘ₗ (f₁ ⊗ₘ f₂₃) = ((f₁ ⊗ₘ .id) ⊗ₘ .id) ∘ₗ α⁻¹ ∘ₗ (.id ⊗ₘ f₂₃) := by
  rw [← LinearMap.comp_assoc, map_map_comp_assoc_symm_eq]
  simp only [coassoc_simps]

/-- Simproc version of `asssoc_symm_comp_map` that only fires when `f₁ ≠ id`. -/
simproc_decl asssoc_symm_comp_map_simproc
    ((TensorProduct.assoc _ _ _ _).symm.toLinearMap ∘ₗ (_ ⊗ₘ _)) := .ofQ fun _ t e ↦ do
  match_expr t with
  | LinearMap R _ _ _ _ T₁ T₂ _ _ _ _ =>
    match_expr T₁ with
    | TensorProduct _ instR M₁ M instM₁ instM instRM₁ instRM =>
      match_expr T₂ with
      | TensorProduct _ _ T₃ M₃ _ instM₃ _ instRM₃ =>
        match_expr T₃ with
        | TensorProduct _ _ N₁ M₂ instN₁ instM₂ instRN₁ instRM₂ =>
          let .succ u₁ := (← Lean.Meta.inferType R).sortLevel! | return .continue
          let .succ u₂ := (← Lean.Meta.inferType M).sortLevel! | return .continue
          let .succ u₃ := (← Lean.Meta.inferType M₁).sortLevel! | return .continue
          let .succ u₄ := (← Lean.Meta.inferType M₂).sortLevel! | return .continue
          let .succ u₅ := (← Lean.Meta.inferType M₃).sortLevel! | return .continue
          let .succ u₆ := (← Lean.Meta.inferType N₁).sortLevel! | return .continue
          have R  : Q(Type u₁) := R
          have M  : Q(Type u₂) := M
          have M₁ : Q(Type u₃) := M₁
          have M₂ : Q(Type u₄) := M₂
          have M₃ : Q(Type u₅) := M₃
          have N₁ : Q(Type u₆) := N₁
          have : Q(CommSemiring $R) := instR
          have : Q(AddCommMonoid $M) := instM
          have : Q(AddCommMonoid $M₁) := instM₁
          have : Q(AddCommMonoid $M₂) := instM₂
          have : Q(AddCommMonoid $M₃) := instM₃
          have : Q(AddCommMonoid $N₁) := instN₁
          have : Q(Module $R $M) := instRM
          have : Q(Module $R $M₁) := instRM₁
          have : Q(Module $R $M₂) := instRM₂
          have : Q(Module $R $M₃) := instRM₃
          have : Q(Module $R $N₁) := instRN₁
          have e : Q($M₁ ⊗[$R] $M →ₗ[$R] $N₁ ⊗[$R] $M₂ ⊗[$R] $M₃) := e
          match e with
          | ~q((TensorProduct.assoc «$R» «$N₁» «$M₂» «$M₃»).symm.toLinearMap ∘ₗ ($f₁ ⊗ₘ $f₂₃)) =>
            match_expr f₁ with
            | LinearMap.id _ _ _ _ _ => return .continue
            | _ => return .visit (e := e) (.mk q((($f₁ ⊗ₘ id) ⊗ₘ id) ∘ₗ
                  (TensorProduct.assoc _ _ _ _).symm.toLinearMap ∘ₗ (id ⊗ₘ $f₂₃))
                (some q(asssoc_symm_comp_map ..)))
          | _ => return Lean.Meta.Simp.StepQ.continue
        | _ => return Lean.Meta.Simp.StepQ.continue
      | _ => return Lean.Meta.Simp.StepQ.continue
    | _ => return Lean.Meta.Simp.StepQ.continue
  | _ => return .continue

attribute [coassoc_simps] asssoc_symm_comp_map_simproc

-- This loops when tagged as a simp lemma,
-- so we turn it into a simproc that only fires when `f₁ ≠ id`.
lemma asssoc_symm_comp_map_assoc (f₁ : M₁ →ₗ[R] N₁)
    (f₂₃ : M →ₗ[R] M₂ ⊗[R] M₃) (f : P →ₗ[R] M₁ ⊗[R] M) :
    α⁻¹ ∘ₗ (f₁ ⊗ₘ f₂₃) ∘ₗ f = ((f₁ ⊗ₘ .id) ⊗ₘ .id) ∘ₗ α⁻¹ ∘ₗ (.id ⊗ₘ f₂₃) ∘ₗ f := by
  rw [← LinearMap.comp_assoc, asssoc_symm_comp_map]
  simp only [coassoc_simps]

/-- Simproc version of `asssoc_symm_comp_map_assoc` that only fires when `f₁ ≠ id`. -/
simproc_decl asssoc_symm_comp_map_assoc_simproc
    ((TensorProduct.assoc _ _ _ _).symm.toLinearMap ∘ₗ (_ ⊗ₘ _) ∘ₗ _) := .ofQ fun _ _ e ↦ do
  match_expr e with
  | LinearMap.comp R _ _ P _ T₂ _ _ _ instP _ _ instRP _ _ _ _ _ _ _ e' => do
    match_expr e' with
    | LinearMap.comp _ _ _ _ T₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => do
      match_expr T₁ with
      | TensorProduct _ instR M₁ M instM₁ instM instRM₁ instRM => do
        match_expr T₂ with
        | TensorProduct _ _ T₃ M₃ _ instM₃ _ instRM₃ => do
          match_expr T₃ with
          | TensorProduct _ _ N₁ M₂ instN₁ instM₂ instRN₁ instRM₂ => do
            let .succ u₁ := (← Lean.Meta.inferType R).sortLevel! | return .continue
            let .succ u₂ := (← Lean.Meta.inferType M).sortLevel! | return .continue
            let .succ u₃ := (← Lean.Meta.inferType M₁).sortLevel! | return .continue
            let .succ u₄ := (← Lean.Meta.inferType M₂).sortLevel! | return .continue
            let .succ u₅ := (← Lean.Meta.inferType M₃).sortLevel! | return .continue
            let .succ u₆ := (← Lean.Meta.inferType N₁).sortLevel! | return .continue
            let .succ u₇ := (← Lean.Meta.inferType P).sortLevel! | return .continue
            have R  : Q(Type u₁) := R
            have M  : Q(Type u₂) := M
            have M₁ : Q(Type u₃) := M₁
            have M₂ : Q(Type u₄) := M₂
            have M₃ : Q(Type u₅) := M₃
            have N₁ : Q(Type u₆) := N₁
            have P  : Q(Type u₇) := P
            have : Q(CommSemiring $R) := instR
            have : Q(AddCommMonoid $M) := instM
            have : Q(AddCommMonoid $M₁) := instM₁
            have : Q(AddCommMonoid $M₂) := instM₂
            have : Q(AddCommMonoid $M₃) := instM₃
            have : Q(AddCommMonoid $N₁) := instN₁
            have : Q(AddCommMonoid $P)  := instP
            have : Q(Module $R $M) := instRM
            have : Q(Module $R $M₁) := instRM₁
            have : Q(Module $R $M₂) := instRM₂
            have : Q(Module $R $M₃) := instRM₃
            have : Q(Module $R $N₁) := instRN₁
            have : Q(Module $R $P) := instRP
            have e : Q($P →ₗ[$R] $N₁ ⊗[$R] $M₂ ⊗[$R] $M₃) := e
            match e with
            | ~q((TensorProduct.assoc «$R» «$N₁» «$M₂» «$M₃»).symm.toLinearMap ∘ₗ
                ($f₁ ⊗ₘ $f₂₃) ∘ₗ ($f : _ →ₗ[_] «$M₁» ⊗ «$M»)) =>
              match_expr f₁ with
              | LinearMap.id _ _ _ _ _ => return .continue
              | _ => return .visit (e := e) (.mk q((($f₁ ⊗ₘ id) ⊗ₘ id) ∘ₗ
                    (TensorProduct.assoc _ _ _ _).symm.toLinearMap ∘ₗ (id ⊗ₘ $f₂₃) ∘ₗ $f)
                  (some q(asssoc_symm_comp_map_assoc ..)))
            | _ => return Lean.Meta.Simp.StepQ.continue
          | _ => return Lean.Meta.Simp.StepQ.continue
        | _ => return Lean.Meta.Simp.StepQ.continue
      | _ => return Lean.Meta.Simp.StepQ.continue
    | _ => return Lean.Meta.Simp.StepQ.continue
  | _ => return .continue

attribute [coassoc_simps] asssoc_symm_comp_map_assoc_simproc

@[coassoc_simps]
lemma assoc_symm_comp_map_map_comp
    (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂) (f₃ : M₃ →ₗ[R] N₃) (f₂₃ : M →ₗ[R] M₂ ⊗[R] M₃) :
    α⁻¹ ∘ₗ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃ ∘ₗ f₂₃)) = ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ∘ₗ α⁻¹ ∘ₗ (id ⊗ₘ f₂₃) := by
  rw [← LinearMap.comp_assoc, map_map_comp_assoc_symm_eq]
  ext
  rfl

@[coassoc_simps]
lemma assoc_symm_comp_map_map_comp_assoc
    (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂) (f₃ : M₃ →ₗ[R] N₃) (f₂₃ : M →ₗ[R] M₂ ⊗[R] M₃)
    (f : N →ₗ[R] M₁ ⊗[R] M) :
    α⁻¹ ∘ₗ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃ ∘ₗ f₂₃)) ∘ₗ f = ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ∘ₗ α⁻¹ ∘ₗ (id ⊗ₘ f₂₃) ∘ₗ f := by
  simp only [← LinearMap.comp_assoc, assoc_symm_comp_map_map_comp]

@[coassoc_simps]
lemma assoc_symm_comp_lid_symm :
    (α⁻¹ ∘ₗ λ⁻¹ : M ⊗[R] N →ₗ[R] _) = λ⁻¹ ⊗ₘ id := rfl

@[coassoc_simps]
lemma assoc_symm_comp_lid_symm_assoc (f : P →ₗ[R] M ⊗[R] N) :
    α⁻¹ ∘ₗ λ⁻¹ ∘ₗ f = λ⁻¹ ⊗ₘ id ∘ₗ f := rfl

@[coassoc_simps]
lemma assoc_symm_comp_map_lid_symm (f : M →ₗ[R] M') :
    α⁻¹ ∘ₗ f ⊗ₘ λ⁻¹ = (f ⊗ₘ id ∘ₗ ρ⁻¹) ⊗ₘ id (M := N) := by
  ext; rfl

@[coassoc_simps]
lemma assoc_symm_comp_map_lid_symm_assoc (f : M →ₗ[R] M') (g : P →ₗ[R] M ⊗[R] N) :
    α⁻¹ ∘ₗ f ⊗ₘ λ⁻¹ ∘ₗ g = (f ⊗ₘ id ∘ₗ ρ⁻¹) ⊗ₘ id ∘ₗ g := by
  simp_rw [← LinearMap.comp_assoc, ← assoc_symm_comp_map_lid_symm]

@[coassoc_simps]
lemma assoc_symm_comp_map_rid_symm (f : M →ₗ[R] M') :
    α⁻¹ ∘ₗ f ⊗ₘ ρ⁻¹ = (f ⊗ₘ id (M := N)) ⊗ₘ id ∘ₗ ρ⁻¹ := by
  ext; rfl

@[coassoc_simps]
lemma assoc_symm_comp_map_rid_symm_assoc (f : M →ₗ[R] M') (g : P →ₗ[R] M ⊗[R] N) :
    α⁻¹ ∘ₗ f ⊗ₘ ρ⁻¹ ∘ₗ g = (f ⊗ₘ id) ⊗ₘ id ∘ₗ ρ⁻¹ ∘ₗ g := by
  simp_rw [← LinearMap.comp_assoc, ← assoc_symm_comp_map_rid_symm]

@[coassoc_simps]
lemma assoc_comp_rid_symm :
    (α ∘ₗ ρ⁻¹ : M ⊗[R] N →ₗ[R] _) = id ⊗ₘ ρ⁻¹ := by ext; rfl

@[coassoc_simps]
lemma assoc_comp_rid_symm_assoc (f : P →ₗ[R] M ⊗[R] N) :
    α ∘ₗ ρ⁻¹ ∘ₗ f = id ⊗ₘ ρ⁻¹ ∘ₗ f := by
  simp_rw [← assoc_comp_rid_symm, LinearMap.comp_assoc]

@[coassoc_simps]
lemma assoc_comp_map_lid_symm (f : N →ₗ[R] N') :
    α ∘ₗ λ⁻¹ ⊗ₘ f = (id ⊗ₘ (id (M := M) ⊗ₘ f)) ∘ₗ λ⁻¹ := by
  ext; rfl

@[coassoc_simps]
lemma assoc_comp_map_lid_symm_assoc (f : N →ₗ[R] N') (g : P →ₗ[R] M ⊗[R] N) :
    α ∘ₗ λ⁻¹ ⊗ₘ f ∘ₗ g = (id ⊗ₘ (id ⊗ₘ f)) ∘ₗ λ⁻¹ ∘ₗ g := by
  simp_rw [← LinearMap.comp_assoc, ← assoc_comp_map_lid_symm]

@[coassoc_simps]
lemma assoc_comp_map_rid_symm (f : N →ₗ[R] N') :
    α ∘ₗ ρ⁻¹ ⊗ₘ f = id (M := M) ⊗ₘ ((id ⊗ₘ f) ∘ₗ λ⁻¹) := by
  ext; rfl

@[coassoc_simps]
lemma assoc_comp_map_rid_symm_assoc (f : N →ₗ[R] N') (g : P →ₗ[R] M ⊗[R] N) :
    α ∘ₗ ρ⁻¹ ⊗ₘ f ∘ₗ g = id ⊗ₘ ((id ⊗ₘ f) ∘ₗ λ⁻¹) ∘ₗ g := by
  simp_rw [← LinearMap.comp_assoc, ← assoc_comp_map_rid_symm]

-- This loops when tagged as a simp lemma,
-- so we turn it into a simproc that only fires when `g ≠ id`.
lemma lid_comp_map (f : M →ₗ[R] R) (g : N →ₗ[R] M') :
    λ ∘ₗ (f ⊗ₘ g) = g ∘ₗ λ ∘ₗ (f ⊗ₘ id) := by
  ext; simp

/-- Simproc version of `lid_comp_map` that only fires when `g ≠ id`. -/
simproc_decl lid_comp_map_simproc
    ((TensorProduct.lid _ _).toLinearMap ∘ₗ (_ ⊗ₘ _)) := .ofQ fun _ t e ↦ do
  match_expr t with
  | LinearMap R _ _ _ _ T₁ M' _ instM' _ instRM' => do
    match_expr T₁ with
    | TensorProduct _ instR M N instM instN instRM instRN => do
      let .succ u₁ := (← Lean.Meta.inferType R).sortLevel! | return .continue
      let .succ u₂ := (← Lean.Meta.inferType M).sortLevel! | return .continue
      let .succ u₃ := (← Lean.Meta.inferType M').sortLevel! | return .continue
      let .succ u₄ := (← Lean.Meta.inferType N).sortLevel! | return .continue
      have R  : Q(Type u₁) := R
      have M  : Q(Type u₂) := M
      have M' : Q(Type u₃) := M'
      have N  : Q(Type u₄) := N
      have : Q(CommSemiring $R)   := instR
      have : Q(AddCommMonoid $M)  := instM
      have : Q(AddCommMonoid $M') := instM'
      have : Q(AddCommMonoid $N)  := instN
      have : Q(Module $R $M)  := instRM
      have : Q(Module $R $M') := instRM'
      have : Q(Module $R $N)  := instRN
      have e : Q($M ⊗[$R] $N →ₗ[$R] $M') := e
      match e with
      | ~q((TensorProduct.lid «$R» «$M'»).toLinearMap ∘ₗ ($f ⊗ₘ $g)) =>
        match_expr g with
        | LinearMap.id _ _ _ _ _ => return .continue
        | _ => return .visit (e := e)
                (.mk q($g ∘ₗ (TensorProduct.lid $R _).toLinearMap ∘ₗ ($f ⊗ₘ .id))
                (some q(lid_comp_map ..)))
      | _ => return Lean.Meta.Simp.StepQ.continue
    | _ => return Lean.Meta.Simp.StepQ.continue
  | _ => return .continue

attribute [coassoc_simps] lid_comp_map_simproc

-- This loops when tagged as a simp lemma,
-- so we turn it into a simproc that only fires when `g ≠ id`.
lemma lid_comp_map_assoc (f : M →ₗ[R] R) (g : N →ₗ[R] M') (h : P →ₗ[R] M ⊗[R] N) :
    λ ∘ₗ (f ⊗ₘ g) ∘ₗ h = g ∘ₗ λ ∘ₗ (f ⊗ₘ id) ∘ₗ h := by
  simp only [← LinearMap.comp_assoc, lid_comp_map _ g]

/-- Simproc version of `lid_comp_map_assoc` that only fires when `g ≠ id`. -/
simproc_decl lid_comp_map_assoc_simproc
    ((TensorProduct.lid _ _).toLinearMap ∘ₗ (_ ⊗ₘ _) ∘ₗ _) := .ofQ fun _ _ e ↦ do
  match_expr e with
  | LinearMap.comp R _ _ P _ M' _ _ _ instP _ instM' instRP _ instRM' _ _ _ _ _ e' => do
    match_expr e' with
    | LinearMap.comp _ _ _ _ T₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => do
      match_expr T₁ with
      | TensorProduct _ instR M N instM instN instRM instRN => do
        let .succ u₁ := (← Lean.Meta.inferType R).sortLevel! | return .continue
        let .succ u₂ := (← Lean.Meta.inferType M).sortLevel! | return .continue
        let .succ u₃ := (← Lean.Meta.inferType M').sortLevel! | return .continue
        let .succ u₄ := (← Lean.Meta.inferType N).sortLevel! | return .continue
        let .succ u₅ := (← Lean.Meta.inferType P).sortLevel! | return .continue
        have R  : Q(Type u₁) := R
        have M  : Q(Type u₂) := M
        have M' : Q(Type u₃) := M'
        have N  : Q(Type u₄) := N
        have P  : Q(Type u₅) := P
        have : Q(CommSemiring $R)   := instR
        have : Q(AddCommMonoid $M)  := instM
        have : Q(AddCommMonoid $M') := instM'
        have : Q(AddCommMonoid $N)  := instN
        have : Q(AddCommMonoid $P)  := instP
        have : Q(Module $R $M)  := instRM
        have : Q(Module $R $M') := instRM'
        have : Q(Module $R $N)  := instRN
        have : Q(Module $R $P)  := instRP
        have e : Q($P →ₗ[$R] $M') := e
        match e with
        | ~q((TensorProduct.lid «$R» «$M'»).toLinearMap ∘ₗ ($f ⊗ₘ $g) ∘ₗ
            ($h : «$P» →ₗ[«$R»] «$M» ⊗[«$R»] «$N»)) =>
          match_expr g with
          | LinearMap.id _ _ _ _ _ => return .continue
          | _ => return .visit (e := e)
                  (.mk q($g ∘ₗ (TensorProduct.lid $R _).toLinearMap ∘ₗ ($f ⊗ₘ .id) ∘ₗ $h)
                  (some q(lid_comp_map_assoc ..)))
        | _ => return Lean.Meta.Simp.StepQ.continue
      | _ => return Lean.Meta.Simp.StepQ.continue
    | _ => return Lean.Meta.Simp.StepQ.continue
  | _ => return Lean.Meta.Simp.StepQ.continue

attribute [coassoc_simps] lid_comp_map_assoc_simproc

-- This loops when tagged as a simp lemma,
-- so we turn it into a simproc that only fires when `f ≠ id`.
lemma rid_comp_map (f : M →ₗ[R] M') (g : N →ₗ[R] R) :
    ρ ∘ₗ (f ⊗ₘ g) = f ∘ₗ ρ ∘ₗ (.id ⊗ₘ g) := by
  ext; simp

/-- Simproc version of `rid_comp_map` that only fires when `g ≠ id`. -/
simproc_decl rid_comp_map_simproc
    ((TensorProduct.rid _ _).toLinearMap ∘ₗ (_ ⊗ₘ _)) := .ofQ fun _ t e ↦ do
  match_expr t with
  | LinearMap R _ _ _ _ T₁ M' _ instM' _ instRM' => do
    match_expr T₁ with
    | TensorProduct _ instR M N instM instN instRM instRN => do
      let .succ u₁ := (← Lean.Meta.inferType R).sortLevel! | return .continue
      let .succ u₂ := (← Lean.Meta.inferType M).sortLevel! | return .continue
      let .succ u₃ := (← Lean.Meta.inferType M').sortLevel! | return .continue
      let .succ u₄ := (← Lean.Meta.inferType N).sortLevel! | return .continue
      have R  : Q(Type u₁) := R
      have M  : Q(Type u₂) := M
      have M' : Q(Type u₃) := M'
      have N  : Q(Type u₄) := N
      have : Q(CommSemiring $R)   := instR
      have : Q(AddCommMonoid $M)  := instM
      have : Q(AddCommMonoid $M') := instM'
      have : Q(AddCommMonoid $N)  := instN
      have : Q(Module $R $M)  := instRM
      have : Q(Module $R $M') := instRM'
      have : Q(Module $R $N)  := instRN
      have e : Q($M ⊗[$R] $N →ₗ[$R] $M') := e
      match e with
      | ~q((TensorProduct.rid «$R» «$M'»).toLinearMap ∘ₗ ($f ⊗ₘ $g)) =>
        match_expr f with
        | LinearMap.id _ _ _ _ _ => return .continue
        | _ => return .visit (e := e)
                (.mk q($f ∘ₗ (TensorProduct.rid $R _).toLinearMap ∘ₗ (.id ⊗ₘ $g))
                (some q(rid_comp_map ..)))
      | _ => return Lean.Meta.Simp.StepQ.continue
    | _ => return Lean.Meta.Simp.StepQ.continue
  | _ => return .continue

attribute [coassoc_simps] rid_comp_map_simproc

-- This loops when tagged as a simp lemma,
-- so we turn it into a simproc that only fires when `f ≠ id`.
lemma rid_comp_map_assoc (f : M →ₗ[R] M') (g : N →ₗ[R] R) (h : P →ₗ[R] M ⊗[R] N) :
    ρ ∘ₗ (f ⊗ₘ g) ∘ₗ h = f ∘ₗ ρ ∘ₗ (.id ⊗ₘ g) ∘ₗ h := by
  simp only [← LinearMap.comp_assoc, rid_comp_map f]

/-- Simproc version of `rid_comp_map_assoc` that only fires when `f ≠ id`. -/
simproc_decl rid_comp_map_assoc_simproc
    ((TensorProduct.rid _ _).toLinearMap ∘ₗ (_ ⊗ₘ _) ∘ₗ _) := .ofQ fun _ _ e ↦ do
  match_expr e with
  | LinearMap.comp R _ _ P _ M' _ _ _ instP _ instM' instRP _ instRM' _ _ _ _ _ e' => do
    match_expr e' with
    | LinearMap.comp _ _ _ _ T₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => do
      match_expr T₁ with
      | TensorProduct _ instR M N instM instN instRM instRN => do
        let .succ u₁ := (← Lean.Meta.inferType R).sortLevel! | return .continue
        let .succ u₂ := (← Lean.Meta.inferType M).sortLevel! | return .continue
        let .succ u₃ := (← Lean.Meta.inferType M').sortLevel! | return .continue
        let .succ u₄ := (← Lean.Meta.inferType N).sortLevel! | return .continue
        let .succ u₅ := (← Lean.Meta.inferType P).sortLevel! | return .continue
        have R  : Q(Type u₁) := R
        have M  : Q(Type u₂) := M
        have M' : Q(Type u₃) := M'
        have N  : Q(Type u₄) := N
        have P  : Q(Type u₅) := P
        have : Q(CommSemiring $R)   := instR
        have : Q(AddCommMonoid $M)  := instM
        have : Q(AddCommMonoid $M') := instM'
        have : Q(AddCommMonoid $N)  := instN
        have : Q(AddCommMonoid $P)  := instP
        have : Q(Module $R $M)  := instRM
        have : Q(Module $R $M') := instRM'
        have : Q(Module $R $N)  := instRN
        have : Q(Module $R $P)  := instRP
        have e : Q($P →ₗ[$R] $M') := e
        match e with
        | ~q((TensorProduct.rid «$R» «$M'»).toLinearMap ∘ₗ ($f ⊗ₘ $g) ∘ₗ
            ($h : «$P» →ₗ[«$R»] «$M» ⊗[«$R»] «$N»)) =>
          match_expr f with
          | LinearMap.id _ _ _ _ _ => return .continue
          | _ => return .visit (e := e)
                  (.mk q($f ∘ₗ (TensorProduct.rid $R _).toLinearMap ∘ₗ (.id ⊗ₘ $g) ∘ₗ $h)
                  (some q(rid_comp_map_assoc ..)))
        | _ => return Lean.Meta.Simp.StepQ.continue
      | _ => return Lean.Meta.Simp.StepQ.continue
    | _ => return Lean.Meta.Simp.StepQ.continue
  | _ => return Lean.Meta.Simp.StepQ.continue

attribute [coassoc_simps] rid_comp_map_assoc_simproc

@[coassoc_simps]
lemma lid_symm_comp (f : M →ₗ[R] M') :
    λ⁻¹ ∘ₗ f = (id ⊗ₘ f) ∘ₗ λ⁻¹ := by
  ext; rfl

@[coassoc_simps]
lemma rid_symm_comp (f : M →ₗ[R] M') :
    ρ⁻¹ ∘ₗ f = (f ⊗ₘ id) ∘ₗ ρ⁻¹ := by
  ext; rfl

@[coassoc_simps]
lemma symm_comp_lid_symm :
    (β ∘ₗ λ⁻¹ : M →ₗ[R] _) = ρ⁻¹ := rfl

@[coassoc_simps]
lemma symm_comp_lid_symm_assoc (f : M →ₗ[R] M') :
    β ∘ₗ λ⁻¹ ∘ₗ f = ρ⁻¹ ∘ₗ f := rfl

@[coassoc_simps]
lemma symm_comp_rid_symm :
    (β ∘ₗ ρ⁻¹ : M →ₗ[R] _) = λ⁻¹ := rfl

@[coassoc_simps]
lemma symm_comp_rid_symm_assoc (f : M →ₗ[R] M') :
    β ∘ₗ ρ⁻¹ ∘ₗ f = λ⁻¹ ∘ₗ f := rfl

@[coassoc_simps]
lemma symm_comp_map (f : M →ₗ[R] M') (g : N →ₗ[R] N') :
    β ∘ₗ (f ⊗ₘ g) = (g ⊗ₘ f) ∘ₗ β := by ext; rfl

@[coassoc_simps]
lemma symm_comp_map_assoc (f : M →ₗ[R] M') (g : N →ₗ[R] N') (h : P →ₗ[R] M ⊗[R] N) :
    β ∘ₗ (f ⊗ₘ g) ∘ₗ h = (g ⊗ₘ f) ∘ₗ β ∘ₗ h := by
  simp only [← LinearMap.comp_assoc, symm_comp_map]

@[coassoc_simps]
lemma coassoc_left [Coalgebra R M] (f : M →ₗ[R] M') :
    α ∘ₗ (δ ⊗ₘ f) ∘ₗ δ = (id ⊗ₘ (id ⊗ₘ f)) ∘ₗ (id ⊗ₘ δ) ∘ₗ δ := by
  simp_rw [← LinearMap.lTensor_def, ← coassoc, ← LinearMap.comp_assoc, LinearMap.lTensor_def,
    map_map_comp_assoc_eq]
  simp only [coassoc_simps]

@[coassoc_simps]
lemma coassoc_left_assoc [Coalgebra R M] (f : M →ₗ[R] M') (g : N →ₗ[R] M) :
    α ∘ₗ (δ ⊗ₘ f) ∘ₗ δ ∘ₗ g = (id ⊗ₘ (id ⊗ₘ f)) ∘ₗ (id ⊗ₘ δ) ∘ₗ δ ∘ₗ g := by
  simp only [← LinearMap.comp_assoc]
  congr 1
  simp only [coassoc_simps]

@[coassoc_simps]
lemma coassoc_right [Coalgebra R M] (f : M →ₗ[R] M') :
    α⁻¹ ∘ₗ (f ⊗ₘ δ) ∘ₗ δ = ((f ⊗ₘ id) ⊗ₘ id) ∘ₗ (δ ⊗ₘ id) ∘ₗ δ := by
  simp_rw [← LinearMap.rTensor_def, ← coassoc_symm, ← LinearMap.comp_assoc, LinearMap.rTensor_def,
    map_map_comp_assoc_symm_eq]
  simp only [coassoc_simps]

@[coassoc_simps]
lemma coassoc_right_assoc [Coalgebra R M] (f : M →ₗ[R] M') (g : N →ₗ[R] M) :
    α⁻¹ ∘ₗ (f ⊗ₘ δ) ∘ₗ δ ∘ₗ g = ((f ⊗ₘ id) ⊗ₘ id) ∘ₗ (δ ⊗ₘ id) ∘ₗ δ ∘ₗ g := by
  simp only [← LinearMap.comp_assoc]
  congr 1
  simp only [coassoc_simps]

lemma map_counit_comp_comul_left [Coalgebra R M] (f : M →ₗ[R] M') :
    (ε ⊗ₘ f) ∘ₗ δ = (id ⊗ₘ f) ∘ₗ λ⁻¹ := by
  rw [← LinearMap.lTensor_comp_rTensor, LinearMap.comp_assoc, Coalgebra.rTensor_counit_comp_comul]
  rfl

lemma map_counit_comp_comul_left_assoc [Coalgebra R M] (f : M →ₗ[R] M') (g : P →ₗ[R] M) :
    (ε ⊗ₘ f) ∘ₗ δ ∘ₗ g = (id ⊗ₘ f) ∘ₗ λ⁻¹ ∘ₗ g := by
  simp_rw [← LinearMap.comp_assoc, map_counit_comp_comul_left]

lemma map_counit_comp_comul_right [Coalgebra R M] (f : M →ₗ[R] M') :
    (f ⊗ₘ ε) ∘ₗ δ = (f ⊗ₘ id) ∘ₗ ρ⁻¹ := by
  rw [← LinearMap.rTensor_comp_lTensor, LinearMap.comp_assoc, Coalgebra.lTensor_counit_comp_comul]
  rfl

lemma map_counit_comp_comul_right_assoc [Coalgebra R M] (f : M →ₗ[R] M') (g : P →ₗ[R] M) :
    (f ⊗ₘ ε) ∘ₗ δ ∘ₗ g = (f ⊗ₘ id) ∘ₗ ρ⁻¹ ∘ₗ g := by
  simp_rw [← LinearMap.comp_assoc, map_counit_comp_comul_right]

@[coassoc_simps]
lemma assoc_comp_map_comm_comp_comul_comp_comul [Coalgebra R M] (f : M →ₗ[R] N) :
    α ∘ₗ ((β ∘ₗ δ) ⊗ₘ f) ∘ₗ δ = (id ⊗ₘ ((id ⊗ₘ f) ∘ₗ β)) ∘ₗ α ∘ₗ δ ⊗ₘ id ∘ₗ β ∘ₗ δ := by
  rw [← symm_comp_map_assoc, ← LinearMap.lTensor_def, ← LinearMap.lTensor_def,
    ← LinearMap.lTensor_def, ← Coalgebra.coassoc, ← f.comp_id,
    TensorProduct.map_comp, ← LinearMap.rTensor_def]
  simp only [← LinearMap.comp_assoc]
  congr 2
  ext
  rfl

@[coassoc_simps]
lemma assoc_comp_map_comm_comp_comul_comp_comul_assoc
    [Coalgebra R M] (f : M →ₗ[R] N) (h : Q →ₗ[R] M) :
    α ∘ₗ ((β ∘ₗ δ) ⊗ₘ f) ∘ₗ δ ∘ₗ h = (id ⊗ₘ ((id ⊗ₘ f) ∘ₗ β)) ∘ₗ α ∘ₗ δ ⊗ₘ id ∘ₗ β ∘ₗ δ ∘ₗ h := by
  simp_rw [← LinearMap.comp_assoc]
  congr 1
  simp only [LinearMap.comp_assoc, assoc_comp_map_comm_comp_comul_comp_comul]

end CoassocSimps
