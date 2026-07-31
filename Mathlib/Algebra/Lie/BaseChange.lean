/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.Algebra.Lie.TensorProduct

meta import Lean.PostprocessTraces

/-!
# Extension and restriction of scalars for Lie algebras and Lie modules

Lie algebras and their representations have a well-behaved theory of extension and restriction of
scalars.

## Main definitions

* `LieAlgebra.ExtendScalars.instLieAlgebra`
* `LieAlgebra.ExtendScalars.instLieModule`
* `LieAlgebra.RestrictScalars.lieAlgebra`

## Tags

lie ring, lie algebra, extension of scalars, restriction of scalars, base change
-/

open Lean.PostprocessTraces

@[expose] public section

open scoped TensorProduct

variable (R A L M : Type*)

namespace LieAlgebra

namespace ExtendScalars

variable [CommRing R] [CommRing A] [Algebra R A] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

set_option backward.privateInPublic true in
/-- The Lie bracket on the extension of a Lie algebra `L` over `R` by an algebra `A` over `R`. -/
private def bracket' : A ⊗[R] L →ₗ[A] A ⊗[R] M →ₗ[A] A ⊗[R] M :=
  TensorProduct.curry <|
    TensorProduct.AlgebraTensorModule.map
        (LinearMap.mul' A A) (LieModule.toModuleHom R L M : L ⊗[R] M →ₗ[R] M) ∘ₗ
      (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R A A A L A M).toLinearMap

@[simp]
private theorem bracket'_tmul (s t : A) (x : L) (m : M) :
    bracket' R A L M (s ⊗ₜ[R] x) (t ⊗ₜ[R] m) = (s * t) ⊗ₜ ⁅x, m⁆ := rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : Bracket (A ⊗[R] L) (A ⊗[R] M) where bracket x m := bracket' R A L M x m

private theorem bracket_def (x : A ⊗[R] L) (m : A ⊗[R] M) : ⁅x, m⁆ = bracket' R A L M x m :=
  rfl

@[simp]
theorem bracket_tmul (s t : A) (x : L) (y : M) : ⁅s ⊗ₜ[R] x, t ⊗ₜ[R] y⁆ = (s * t) ⊗ₜ ⁅x, y⁆ := rfl

set_option backward.privateInPublic true in
private theorem bracket_lie_self (x : A ⊗[R] L) : ⁅x, x⁆ = 0 := by
  simp only [bracket_def]
  refine x.induction_on ?_ ?_ ?_
  · simp only [map_zero]
  · intro a l
    simp only [bracket'_tmul, TensorProduct.tmul_zero, lie_self]
  · intro z₁ z₂ h₁ h₂
    suffices bracket' R A L L z₁ z₂ + bracket' R A L L z₂ z₁ = 0 by
      rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, h₁, h₂,
        zero_add, add_zero, add_comm, this]
    refine z₁.induction_on ?_ ?_ ?_
    · simp only [map_zero, add_zero, LinearMap.zero_apply]
    · intro a₁ l₁; refine z₂.induction_on ?_ ?_ ?_
      · simp only [map_zero, add_zero, LinearMap.zero_apply]
      · intro a₂ l₂
        simp only [← lie_skew l₂ l₁, mul_comm a₁ a₂, TensorProduct.tmul_neg, bracket'_tmul,
          add_neg_cancel]
      · intro y₁ y₂ hy₁ hy₂
        simp only [hy₁, hy₂, add_add_add_comm, add_zero, LinearMap.add_apply, map_add]
    · intro y₁ y₂ hy₁ hy₂
      simp only [add_add_add_comm, hy₁, hy₂, add_zero, LinearMap.add_apply, map_add]

set_option backward.privateInPublic true in
private theorem bracket_leibniz_lie (x y : A ⊗[R] L) (z : A ⊗[R] M) :
    ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆ := by
  simp only [bracket_def]
  refine x.induction_on ?_ ?_ ?_
  · simp only [map_zero, add_zero, LinearMap.zero_apply]
  · intro a₁ l₁
    refine y.induction_on ?_ ?_ ?_
    · simp only [map_zero, add_zero, LinearMap.zero_apply]
    · intro a₂ l₂
      refine z.induction_on ?_ ?_ ?_
      · simp only [map_zero, add_zero]
      · intro a₃ l₃; simp only [bracket'_tmul]
        rw [mul_left_comm a₂ a₁ a₃, mul_assoc, leibniz_lie, TensorProduct.tmul_add]
      · grind
    · grind [LinearMap.add_apply]
  · grind [LinearMap.add_apply]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance instLieRing : LieRing (A ⊗[R] L) where
  add_lie x y z := by simp only [bracket_def, LinearMap.add_apply, map_add]
  lie_add x y z := by simp only [bracket_def, map_add]
  lie_self := bracket_lie_self R A L
  leibniz_lie := bracket_leibniz_lie R A L L

instance instBaseLieAlgebra : LieAlgebra R (A ⊗[R] L) where lie_smul := by simp [bracket_def]

instance instLieAlgebra : LieAlgebra A (A ⊗[R] L) where lie_smul _a _x _y := map_smul _ _ _

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance instLieRingModule : LieRingModule (A ⊗[R] L) (A ⊗[R] M) where
  add_lie x y z := by simp only [bracket_def, LinearMap.add_apply, map_add]
  lie_add x y z := by simp only [bracket_def, map_add]
  leibniz_lie := bracket_leibniz_lie R A L M

set_option backward.isDefEq.respectTransparency false in
instance instLieModule : LieModule A (A ⊗[R] L) (A ⊗[R] M) where
  smul_lie t x m := by simp only [bracket_def, map_smul, LinearMap.smul_apply]
  lie_smul _ _ _ := map_smul _ _ _

/-- The Lie algebra homomorphism induced by an algebra map. -/
def map {R A B L L' : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L'] (f : A →ₐ[R] B) (g : L →ₗ⁅R⁆ L') :
    A ⊗[R] L →ₗ⁅R⁆ B ⊗[R] L' :=
  { TensorProduct.map f.toLinearMap g with
    map_lie' {x y} := by
      simp only [bracket_def, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
      refine x.induction_on (by simp) ?_ ?_
      · intro _ _
        refine y.induction_on (by simp) (fun _ _ ↦ by simp) (fun _ _ h1 h2 ↦ by simp [h1, h2])
      · intro _ _
        refine y.induction_on (by simp) (fun _ _ h ↦ by simp [h]) (by simp_all) }

@[simp]
lemma map_apply_tmul {R A B L L' : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B]
    [Algebra R B] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L'] {f : A →ₐ[R] B}
    {g : L →ₗ⁅R⁆ L'} (a : A) (x : L) :
    map f g (a ⊗ₜ x) = (f a) ⊗ₜ (g x) :=
  rfl

end ExtendScalars

namespace RestrictScalars

variable [h : LieRing L]

instance : LieRing (RestrictScalars R A L) :=
  h

variable [CommRing A] [LieAlgebra A L]

/-! # Issue -/

set_option backward.isDefEq.respectTransparency false in
instance lieAlgebra [CommRing R] [Algebra R A] : LieAlgebra R (RestrictScalars R A L) where
  lie_smul t x y := (lie_smul (algebraMap R A t) (RestrictScalars.addEquiv R A L x)
    (RestrictScalars.addEquiv R A L y) :)

/-! ## Explanation -/

private meta partial def elideBelow (p : TracePattern) : TracePostprocessor :=
  fun trees => trees.mapM go
where
  go (t : TraceTree) : Lean.CoreM TraceTree := do
    match t with
    | .leaf msg => return .leaf msg
    | .node data msg children wrap =>
      if ← p t then
        return .node data m!"{msg} (truncated)" #[] wrap
      else
        return .node data msg (← children.mapM go) wrap

-- The dual of `filterSubtrees`: drop matching subtrees (used to remove `onFailure` duplicates).
private meta partial def dropSubtrees (p : TracePattern) : TracePostprocessor :=
  fun trees => trees.filterMapM go
where
  go (t : TraceTree) : Lean.CoreM (Option TraceTree) := do
    if ← p t then
      return none
    match t with
    | .leaf msg => return some (.leaf msg)
    | .node data msg children wrap => return some (.node data msg (← children.filterMapM go) wrap)

-- `RestrictScalars R A L := L` is a semireducible synonym carrying a *different* `Module R`
-- structure. Synthesizing the `Module R (RestrictScalars R A L)` parent of `LieAlgebra` via
-- `RestrictScalars.module` assigns its `AddCommMonoid` argument across the synonym: the direct
-- `.instances` type check `AddCommMonoid L =?= AddCommMonoid (RestrictScalars R A L)` fails (the
-- synonym does not unfold there). Under `markOrSynth` the fallback synthesizes the mvar's own
-- type (`✅ AddCommMonoid L`) and unifies the candidate with it at `.default`, which succeeds and
-- rescues the assignment. Under plain `mark` there is no fallback and the structure elaborator
-- reports `Fields missing: add_smul, zero_smul`.
set_option linter.style.longLine false in
/--
trace: [Meta.synthInstance] ✅️ Module R (RestrictScalars R A L)
  [Meta.synthInstance.apply] ✅️ apply RestrictScalars.module to Module R (RestrictScalars R A L)
    [Meta.synthInstance.tryResolve] ✅️ Module R (RestrictScalars R A L) ≟ Module R (RestrictScalars R A L)
      [Meta.isDefEq] ✅️ [instances] Module R
            (RestrictScalars R A L) =?= Module ?m.12 (RestrictScalars ?m.12 ?m.13 ?m.14)
        [Meta.isDefEq] ✅️ [default] (instLieRingRestrictScalars R A
                L).toAddCommMonoid =?= instAddCommMonoidRestrictScalars R A L
          [Meta.isDefEq] ✅️ [default] { toAddMonoid := (instLieRingRestrictScalars R A L).toAddMonoid,
                add_comm := ⋯ } =?= ?m.16
            [Meta.isDefEq.assign.checkTypes] ✅️ (?m.16 : AddCommMonoid
                  L) := ({ toAddMonoid := (instLieRingRestrictScalars R A L).toAddMonoid,
                  add_comm := ⋯ } : AddCommMonoid (RestrictScalars R A L))
              [Meta.isDefEq] ❌️ [instances] AddCommMonoid L =?= AddCommMonoid (RestrictScalars R A L)
                [Meta.isDefEq] ❌️ [instances] L =?= RestrictScalars R A L
              [Meta.synthInstance] ✅️ AddCommMonoid L (truncated)
              [Meta.isDefEq] ✅️ [default] { toAddMonoid := (instLieRingRestrictScalars R A L).toAddMonoid,
                    add_comm := ⋯ } =?= h.toAddCommMonoid (truncated)
---
warning: Setting options starting with 'debug', 'pp', 'profiler', 'trace' is only intended for development and not for final code. If you intend to submit this contribution to the Mathlib project, please remove 'set_option trace.Meta.isDefEq'.

Note: This linter can be disabled with `set_option linter.style.setOption false`
-/
#guard_msgs in
postprocess_traces
  filterSubtrees (fun x => (ofClass `Meta.synthInstance.apply x) <&&>
    (containsString "RestrictScalars.module" x))
  >=> filterSubtrees (fun x => (ofClass `Meta.isDefEq.assign.checkTypes x) <&&>
    (containsString "AddCommMonoid" x))
  >=> elideBelow (fun x => (ofClass `Meta.synthInstance x) <&&> succeeded x <&&>
    containsString "AddCommMonoid L" x)
  >=> elideBelow (fun x => (ofClass `Meta.isDefEq x) <&&> succeeded x <&&>
    containsString "h.toAddCommMonoid" x)
  >=> dropSubtrees (fun x => ofClass `Meta.isDefEq.onFailure x)
in
set_option trace.Meta.isDefEq true in
set_option trace.Meta.isDefEq.printTransparency true in
set_option trace.Meta.isDefEq.assign.checkTypes true in
set_option trace.Meta.synthInstance true in
set_option backward.isDefEq.respectTransparency false in
example [CommRing R] [Algebra R A] : LieAlgebra R (RestrictScalars R A L) where
  lie_smul t x y := (lie_smul (algebraMap R A t) (RestrictScalars.addEquiv R A L x)
    (RestrictScalars.addEquiv R A L y) :)

end RestrictScalars

end LieAlgebra

section ExtendScalars

variable [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [CommRing A] [Algebra R A]

@[simp]
lemma LieModule.toEnd_baseChange (x : L) :
    toEnd A (A ⊗[R] L) (A ⊗[R] M) (1 ⊗ₜ x) = (toEnd R L M x).baseChange A := by
  ext; simp

namespace LieSubmodule

variable (N : LieSubmodule R L M)

open LieModule

set_option backward.isDefEq.respectTransparency false in
variable {R L M} in
/-- If `A` is an `R`-algebra, any Lie submodule of a Lie module `M` with coefficients in `R` may be
pushed forward to a Lie submodule of `A ⊗ M` with coefficients in `A`.

This "base change" operation is also known as "extension of scalars". -/
def baseChange : LieSubmodule A (A ⊗[R] L) (A ⊗[R] M) :=
  { (N : Submodule R M).baseChange A with
    lie_mem := by
      intro x m hm
      rw [Submodule.mem_carrier, SetLike.mem_coe] at hm ⊢
      rw [Submodule.baseChange_eq_span] at hm
      obtain ⟨c, rfl⟩ := (Finsupp.mem_span_iff_linearCombination _ _ _).mp hm
      refine x.induction_on (by simp) (fun a y ↦ ?_) (fun y z hy hz ↦ ?_)
      · change toEnd A (A ⊗[R] L) (A ⊗[R] M) _ _ ∈ _
        simp_rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, toEnd_apply_apply]
        refine Submodule.sum_mem _ fun ⟨_, n, hn, h⟩ _ ↦ Submodule.smul_mem _ _ ?_
        rw [Subtype.coe_mk, ← h]
        exact Submodule.tmul_mem_baseChange_of_mem _ (N.lie_mem hn)
      · rw [add_lie]
        exact ((N : Submodule R M).baseChange A).add_mem hy hz }

@[simp]
lemma coe_baseChange :
    (N.baseChange A : Submodule A (A ⊗[R] M)) = (N : Submodule R M).baseChange A :=
  rfl

variable {N}

variable {R A L M} in
lemma tmul_mem_baseChange_of_mem (a : A) {m : M} (hm : m ∈ N) :
    a ⊗ₜ[R] m ∈ N.baseChange A :=
  (N : Submodule R M).tmul_mem_baseChange_of_mem a hm

lemma mem_baseChange_iff {m : A ⊗[R] M} :
    m ∈ N.baseChange A ↔
    m ∈ Submodule.span A ((N : Submodule R M).map (TensorProduct.mk R A M 1)) := by
  rw [← Submodule.baseChange_eq_span]; rfl

@[simp]
lemma baseChange_bot : (⊥ : LieSubmodule R L M).baseChange A = ⊥ := by
  simp only [baseChange, bot_toSubmodule, Submodule.baseChange_bot]
  rfl

@[simp]
lemma baseChange_top : (⊤ : LieSubmodule R L M).baseChange A = ⊤ := by
  simp only [baseChange, top_toSubmodule, Submodule.baseChange_top]
  rfl

lemma lie_baseChange {I : LieIdeal R L} {N : LieSubmodule R L M} :
    ⁅I, N⁆.baseChange A = ⁅I.baseChange A, N.baseChange A⁆ := by
  set s : Set (A ⊗[R] M) := { m | ∃ x ∈ I, ∃ n ∈ N, 1 ⊗ₜ ⁅x, n⁆ = m}
  have : (TensorProduct.mk R A M 1) '' {m | ∃ x ∈ I, ∃ n ∈ N, ⁅x, n⁆ = m} = s := by ext; simp [s]
  rw [← toSubmodule_inj, coe_baseChange, lieIdeal_oper_eq_linear_span',
    Submodule.baseChange_span, this, lieIdeal_oper_eq_linear_span']
  refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.mpr ?_)
  · rintro - ⟨x, hx, m, hm, rfl⟩
    exact ⟨1 ⊗ₜ x, tmul_mem_baseChange_of_mem 1 hx,
           1 ⊗ₜ m, tmul_mem_baseChange_of_mem 1 hm, by simp⟩
  · rintro - ⟨x, hx, m, hm, rfl⟩
    rw [mem_baseChange_iff] at hx hm
    refine Submodule.span_induction₂ (p := fun x m _ _ ↦ ⁅x, m⁆ ∈ Submodule.span A s)
      ?_ (by simp) (by simp) ?_ ?_ ?_ ?_ hx hm
    · rintro - - ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩; exact Submodule.subset_span ⟨x, hx, y, hy, by simp⟩
    all_goals { intros; simp [add_mem, Submodule.smul_mem, *] }

end LieSubmodule

end ExtendScalars
