/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Fabian Glöckle, Kyle Miller
-/
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Span.Defs

/-!
# Dual vector spaces

The dual space of an $R$-module $M$ is the $R$-module of $R$-linear maps $M \to R$.

## Main definitions

* Duals and transposes:
  * `Module.Dual R M` defines the dual space of the `R`-module `M`, as `M →ₗ[R] R`.
  * `Module.dualPairing R M` is the canonical pairing between `Dual R M` and `M`.
  * `Module.Dual.eval R M : M →ₗ[R] Dual R (Dual R)` is the canonical map to the double dual.
  * `Module.Dual.transpose` is the linear map from `M →ₗ[R] M'` to `Dual R M' →ₗ[R] Dual R M`.
  * `LinearMap.dualMap` is `Module.Dual.transpose` of a given linear map, for dot notation.
  * `LinearEquiv.dualMap` is for the dual of an equivalence.
* Submodules:
  * `Submodule.dualRestrict W` is the transpose `Dual R M →ₗ[R] Dual R W` of the inclusion map.
  * `Submodule.dualAnnihilator W` is the kernel of `W.dualRestrict`. That is, it is the submodule
    of `dual R M` whose elements all annihilate `W`.
  * `Submodule.dualPairing W` is the canonical pairing between `Dual R M ⧸ W.dualAnnihilator`
    and `W`. It is nondegenerate for vector spaces (`Subspace.dualPairing_nondegenerate`).

## Main results

* Annihilators:
  * `Module.dualAnnihilator_gc R M` is the antitone Galois correspondence between
    `Submodule.dualAnnihilator` and `Submodule.dualCoannihilator`.
* Finite-dimensional vector spaces:
  * `Module.evalEquiv` is the equivalence `V ≃ₗ[K] Dual K (Dual K V)`
  * `Module.mapEvalEquiv` is the order isomorphism between subspaces of `V` and
    subspaces of `Dual K (Dual K V)`.
-/

open Module Submodule

noncomputable section

namespace Module

variable (R A M : Type*)
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The dual space of an R-module M is the R-module of linear maps `M → R`. -/
abbrev Dual :=
  M →ₗ[R] R

/-- The canonical pairing of a vector space and its algebraic dual. -/
def dualPairing (R M) [CommSemiring R] [AddCommMonoid M] [Module R M] :
    Module.Dual R M →ₗ[R] M →ₗ[R] R :=
  LinearMap.id

@[simp]
theorem dualPairing_apply (v x) : dualPairing R M v x = v x :=
  rfl

namespace Dual

instance : Inhabited (Dual R M) := ⟨0⟩

/-- Maps a module M to the dual of the dual of M. See `Module.erange_coe` and
`Module.evalEquiv`. -/
def eval : M →ₗ[R] Dual R (Dual R M) :=
  LinearMap.flip LinearMap.id

@[simp]
theorem eval_apply (v : M) (a : Dual R M) : eval R M v a = a v :=
  rfl

variable {R M} {M' : Type*}
variable [AddCommMonoid M'] [Module R M']

/-- The transposition of linear maps, as a linear map from `M →ₗ[R] M'` to
`Dual R M' →ₗ[R] Dual R M`. -/
def transpose : (M →ₗ[R] M') →ₗ[R] Dual R M' →ₗ[R] Dual R M :=
  (LinearMap.llcomp R M M' R).flip

theorem transpose_apply (u : M →ₗ[R] M') (l : Dual R M') : transpose u l = l.comp u :=
  rfl

variable {M'' : Type*} [AddCommMonoid M''] [Module R M'']

theorem transpose_comp (u : M' →ₗ[R] M'') (v : M →ₗ[R] M') :
    transpose (u.comp v) = (transpose v).comp (transpose u) :=
  rfl

end Dual

end Module

section DualMap

open Module

variable {R M₁ M₂ : Type*} [CommSemiring R]
variable [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]

/-- Given a linear map `f : M₁ →ₗ[R] M₂`, `f.dualMap` is the linear map between the dual of
`M₂` and `M₁` such that it maps the functional `φ` to `φ ∘ f`. -/
def LinearMap.dualMap (f : M₁ →ₗ[R] M₂) : Dual R M₂ →ₗ[R] Dual R M₁ :=
  Module.Dual.transpose f

lemma LinearMap.dualMap_eq_lcomp (f : M₁ →ₗ[R] M₂) : f.dualMap = f.lcomp R R := rfl

theorem LinearMap.dualMap_def (f : M₁ →ₗ[R] M₂) : f.dualMap = Module.Dual.transpose f :=
  rfl

theorem LinearMap.dualMap_apply' (f : M₁ →ₗ[R] M₂) (g : Dual R M₂) : f.dualMap g = g.comp f :=
  rfl

@[simp]
theorem LinearMap.dualMap_apply (f : M₁ →ₗ[R] M₂) (g : Dual R M₂) (x : M₁) :
    f.dualMap g x = g (f x) :=
  rfl

@[simp]
theorem LinearMap.dualMap_id : (LinearMap.id : M₁ →ₗ[R] M₁).dualMap = LinearMap.id := by
  ext
  rfl

theorem LinearMap.dualMap_comp_dualMap {M₃ : Type*} [AddCommMonoid M₃] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) : f.dualMap.comp g.dualMap = (g.comp f).dualMap :=
  rfl

/-- If a linear map is surjective, then its dual is injective. -/
theorem LinearMap.dualMap_injective_of_surjective {f : M₁ →ₗ[R] M₂} (hf : Function.Surjective f) :
    Function.Injective f.dualMap := by
  intro φ ψ h
  ext x
  obtain ⟨y, rfl⟩ := hf x
  exact congr_arg (fun g : Module.Dual R M₁ => g y) h

/-- The `Linear_equiv` version of `LinearMap.dualMap`. -/
def LinearEquiv.dualMap (f : M₁ ≃ₗ[R] M₂) : Dual R M₂ ≃ₗ[R] Dual R M₁ where
  __ := f.toLinearMap.dualMap
  invFun := f.symm.toLinearMap.dualMap
  left_inv φ := LinearMap.ext fun x ↦ congr_arg φ (f.right_inv x)
  right_inv φ := LinearMap.ext fun x ↦ congr_arg φ (f.left_inv x)

@[simp]
theorem LinearEquiv.dualMap_apply (f : M₁ ≃ₗ[R] M₂) (g : Dual R M₂) (x : M₁) :
    f.dualMap g x = g (f x) :=
  rfl

@[simp]
theorem LinearEquiv.dualMap_refl :
    (LinearEquiv.refl R M₁).dualMap = LinearEquiv.refl R (Dual R M₁) := by
  ext
  rfl

@[simp]
theorem LinearEquiv.dualMap_symm {f : M₁ ≃ₗ[R] M₂} :
    (LinearEquiv.dualMap f).symm = LinearEquiv.dualMap f.symm :=
  rfl

theorem LinearEquiv.dualMap_trans {M₃ : Type*} [AddCommMonoid M₃] [Module R M₃] (f : M₁ ≃ₗ[R] M₂)
    (g : M₂ ≃ₗ[R] M₃) : g.dualMap.trans f.dualMap = (f.trans g).dualMap :=
  rfl

theorem Module.Dual.eval_naturality (f : M₁ →ₗ[R] M₂) :
    f.dualMap.dualMap ∘ₗ eval R M₁ = eval R M₂ ∘ₗ f := by
  rfl

@[simp]
lemma Dual.apply_one_mul_eq (f : Dual R R) (r : R) :
    f 1 * r = f r := by
  conv_rhs => rw [← mul_one r, ← smul_eq_mul]
  rw [map_smul, smul_eq_mul, mul_comm]

@[simp]
lemma LinearMap.range_dualMap_dual_eq_span_singleton (f : Dual R M₁) :
    range f.dualMap = R ∙ f := by
  ext m
  rw [Submodule.mem_span_singleton]
  refine ⟨fun ⟨r, hr⟩ ↦ ⟨r 1, ?_⟩, fun ⟨r, hr⟩ ↦ ⟨r • LinearMap.id, ?_⟩⟩
  · ext; simp [dualMap_apply', ← hr]
  · ext; simp [dualMap_apply', ← hr]

end DualMap

namespace Module

variable {K V : Type*}
variable [CommSemiring K] [AddCommMonoid V] [Module K V]

open Module Module.Dual Submodule LinearMap Module

section IsReflexive

open Function

variable (R M N : Type*)
variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

/-- A reflexive module is one for which the natural map to its double dual is a bijection.

Any finitely-generated projective module (and thus any finite-dimensional vector space)
is reflexive. See `Module.instIsReflexiveOfFiniteOfProjective`. -/
class IsReflexive : Prop where
  /-- A reflexive module is one for which the natural map to its double dual is a bijection. -/
  bijective_dual_eval' : Bijective (Dual.eval R M)

lemma bijective_dual_eval [IsReflexive R M] : Bijective (Dual.eval R M) :=
  IsReflexive.bijective_dual_eval'

variable [IsReflexive R M]

theorem erange_coe : LinearMap.range (eval R M) = ⊤ :=
  range_eq_top.mpr (bijective_dual_eval _ _).2

/-- The bijection between a reflexive module and its double dual, bundled as a `LinearEquiv`. -/
def evalEquiv : M ≃ₗ[R] Dual R (Dual R M) :=
  LinearEquiv.ofBijective _ (bijective_dual_eval R M)

@[simp] lemma evalEquiv_toLinearMap : evalEquiv R M = Dual.eval R M := rfl

@[simp] lemma evalEquiv_apply (m : M) : evalEquiv R M m = Dual.eval R M m := rfl

@[simp] lemma apply_evalEquiv_symm_apply (f : Dual R M) (g : Dual R (Dual R M)) :
    f ((evalEquiv R M).symm g) = g f := by
  set m := (evalEquiv R M).symm g
  rw [← (evalEquiv R M).apply_symm_apply g, evalEquiv_apply, Dual.eval_apply]

@[simp] lemma symm_dualMap_evalEquiv :
    (evalEquiv R M).symm.dualMap = Dual.eval R (Dual R M) := by
  ext; simp

@[simp] lemma Dual.eval_comp_comp_evalEquiv_eq
    {M' : Type*} [AddCommMonoid M'] [Module R M'] {f : M →ₗ[R] M'} :
    Dual.eval R M' ∘ₗ f ∘ₗ (evalEquiv R M).symm = f.dualMap.dualMap := by
  rw [← LinearMap.comp_assoc, LinearEquiv.comp_toLinearMap_symm_eq,
    evalEquiv_toLinearMap, eval_naturality]

lemma dualMap_dualMap_eq_iff_of_injective
    {M' : Type*} [AddCommMonoid M'] [Module R M'] {f g : M →ₗ[R] M'}
    (h : Injective (Dual.eval R M')) :
    f.dualMap.dualMap = g.dualMap.dualMap ↔ f = g := by
  simp only [← Dual.eval_comp_comp_evalEquiv_eq]
  refine ⟨fun hfg => ?_, fun a ↦ congrArg (Dual.eval R M').comp
    (congrFun (congrArg LinearMap.comp a) (evalEquiv R M).symm.toLinearMap)⟩
  rw [propext (cancel_left h), LinearEquiv.eq_comp_toLinearMap_iff] at hfg
  exact hfg

@[simp] lemma dualMap_dualMap_eq_iff
    {M' : Type*} [AddCommMonoid M'] [Module R M'] [IsReflexive R M'] {f g : M →ₗ[R] M'} :
    f.dualMap.dualMap = g.dualMap.dualMap ↔ f = g :=
  dualMap_dualMap_eq_iff_of_injective _ _ (bijective_dual_eval R M').injective

/-- The dual of a reflexive module is reflexive. -/
instance Dual.instIsReflecive : IsReflexive R (Dual R M) :=
  ⟨by simpa only [← symm_dualMap_evalEquiv] using (evalEquiv R M).dualMap.symm.bijective⟩

variable {R M N} in
/-- A direct summand of a reflexive module is reflexive. -/
lemma IsReflexive.of_split (i : N →ₗ[R] M) (s : M →ₗ[R] N) (H : s ∘ₗ i = .id) :
    IsReflexive R N where
  bijective_dual_eval' :=
    ⟨.of_comp (f := i.dualMap.dualMap) <|
      (bijective_dual_eval R M).1.comp (injective_of_comp_eq_id i _ H),
    .of_comp (g := s) <| (surjective_of_comp_eq_id i.dualMap.dualMap s.dualMap.dualMap <|
      congr_arg (dualMap ∘ dualMap) H).comp (bijective_dual_eval R M).2⟩

/-- The isomorphism `Module.evalEquiv` induces an order isomorphism on subspaces. -/
def mapEvalEquiv : Submodule R M ≃o Submodule R (Dual R (Dual R M)) :=
  Submodule.orderIsoMapComap (evalEquiv R M)

@[simp]
theorem mapEvalEquiv_apply (W : Submodule R M) :
    mapEvalEquiv R M W = W.map (Dual.eval R M) :=
  rfl

@[simp]
theorem mapEvalEquiv_symm_apply (W'' : Submodule R (Dual R (Dual R M))) :
    (mapEvalEquiv R M).symm W'' = W''.comap (Dual.eval R M) :=
  rfl

variable {R M N} in
lemma equiv (e : M ≃ₗ[R] N) : IsReflexive R N where
  bijective_dual_eval' := by
    let ed : Dual R (Dual R N) ≃ₗ[R] Dual R (Dual R M) := e.symm.dualMap.dualMap
    have : Dual.eval R N = ed.symm.comp ((Dual.eval R M).comp e.symm.toLinearMap) := by
      ext m f
      exact DFunLike.congr_arg f (e.apply_symm_apply m).symm
    simp only [this,
      coe_comp, LinearEquiv.coe_coe, EquivLike.comp_bijective]
    exact Bijective.comp (bijective_dual_eval R M) (LinearEquiv.bijective _)

instance _root_.MulOpposite.instModuleIsReflexive : IsReflexive R (MulOpposite M) :=
  equiv <| MulOpposite.opLinearEquiv _

-- see Note [lower instance priority]
instance (priority := 100) [IsDomain R] : NoZeroSMulDivisors R M := by
  refine (noZeroSMulDivisors_iff R M).mpr ?_
  intro r m hrm
  rw [or_iff_not_imp_left]
  intro hr
  suffices Dual.eval R M m = Dual.eval R M 0 from (bijective_dual_eval R M).injective this
  ext n
  simp only [Dual.eval_apply, map_zero, LinearMap.zero_apply]
  suffices r • n m = 0 from eq_zero_of_ne_zero_of_mul_left_eq_zero hr this
  rw [← LinearMap.map_smul_of_tower, hrm, LinearMap.map_zero]

end IsReflexive

end Module

namespace Submodule

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {W : Submodule R M}

/-- The `dualRestrict` of a submodule `W` of `M` is the linear map from the
  dual of `M` to the dual of `W` such that the domain of each linear map is
  restricted to `W`. -/
def dualRestrict (W : Submodule R M) : Module.Dual R M →ₗ[R] Module.Dual R W :=
  LinearMap.domRestrict' W

theorem dualRestrict_def (W : Submodule R M) : W.dualRestrict = W.subtype.dualMap :=
  rfl

@[simp]
theorem dualRestrict_apply (W : Submodule R M) (φ : Module.Dual R M) (x : W) :
    W.dualRestrict φ x = φ (x : M) :=
  rfl

/-- The `dualAnnihilator` of a submodule `W` is the set of linear maps `φ` such
  that `φ w = 0` for all `w ∈ W`. -/
def dualAnnihilator {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (W : Submodule R M) : Submodule R <| Module.Dual R M :=
  LinearMap.ker W.dualRestrict

@[simp]
theorem mem_dualAnnihilator (φ : Module.Dual R M) : φ ∈ W.dualAnnihilator ↔ ∀ w ∈ W, φ w = 0 := by
  refine LinearMap.mem_ker.trans ?_
  simp_rw [LinearMap.ext_iff, dualRestrict_apply]
  exact ⟨fun h w hw => h ⟨w, hw⟩, fun h w => h w.1 w.2⟩

/-- That $\operatorname{ker}(\iota^* : V^* \to W^*) = \operatorname{ann}(W)$.
This is the definition of the dual annihilator of the submodule $W$. -/
theorem dualRestrict_ker_eq_dualAnnihilator (W : Submodule R M) :
    LinearMap.ker W.dualRestrict = W.dualAnnihilator :=
  rfl

/-- The `dualAnnihilator` of a submodule of the dual space pulled back along the evaluation map
`Module.Dual.eval`. -/
def dualCoannihilator (Φ : Submodule R (Module.Dual R M)) : Submodule R M :=
  Φ.dualAnnihilator.comap (Module.Dual.eval R M)

@[simp]
theorem mem_dualCoannihilator {Φ : Submodule R (Module.Dual R M)} (x : M) :
    x ∈ Φ.dualCoannihilator ↔ ∀ φ ∈ Φ, (φ x : R) = 0 := by
  simp_rw [dualCoannihilator, mem_comap, mem_dualAnnihilator, Module.Dual.eval_apply]

lemma dualAnnihilator_map_dualMap_le {N : Type*} [AddCommMonoid N] [Module R N]
    (W : Submodule R M) (f : N →ₗ[R] M) :
    W.dualAnnihilator.map f.dualMap ≤ (W.comap f).dualAnnihilator := by
  intro; aesop

theorem comap_dualAnnihilator (Φ : Submodule R (Module.Dual R M)) :
    Φ.dualAnnihilator.comap (Module.Dual.eval R M) = Φ.dualCoannihilator := rfl

theorem map_dualCoannihilator_le (Φ : Submodule R (Module.Dual R M)) :
    Φ.dualCoannihilator.map (Module.Dual.eval R M) ≤ Φ.dualAnnihilator :=
  map_le_iff_le_comap.mpr (comap_dualAnnihilator Φ).le

variable (R M) in
theorem dualAnnihilator_gc :
    GaloisConnection
      (OrderDual.toDual ∘ (dualAnnihilator : Submodule R M → Submodule R (Module.Dual R M)))
      (dualCoannihilator ∘ OrderDual.ofDual) := by
  intro a b
  induction b using OrderDual.rec
  simp only [Function.comp_apply, OrderDual.toDual_le_toDual, OrderDual.ofDual_toDual]
  constructor <;>
    · intro h x hx
      simp only [mem_dualAnnihilator, mem_dualCoannihilator]
      intro y hy
      have := h hy
      simp only [mem_dualAnnihilator, mem_dualCoannihilator] at this
      exact this x hx

theorem le_dualAnnihilator_iff_le_dualCoannihilator {U : Submodule R (Module.Dual R M)}
    {V : Submodule R M} : U ≤ V.dualAnnihilator ↔ V ≤ U.dualCoannihilator :=
  (dualAnnihilator_gc R M).le_iff_le

@[simp]
theorem dualAnnihilator_bot : (⊥ : Submodule R M).dualAnnihilator = ⊤ :=
  (dualAnnihilator_gc R M).l_bot

@[simp]
theorem dualAnnihilator_top : (⊤ : Submodule R M).dualAnnihilator = ⊥ := by
  rw [eq_bot_iff]
  intro v
  simp_rw [mem_dualAnnihilator, mem_bot, mem_top, forall_true_left]
  exact fun h => LinearMap.ext h

@[simp]
theorem dualCoannihilator_bot : (⊥ : Submodule R (Module.Dual R M)).dualCoannihilator = ⊤ :=
  (dualAnnihilator_gc R M).u_top

@[mono]
theorem dualAnnihilator_anti {U V : Submodule R M} (hUV : U ≤ V) :
    V.dualAnnihilator ≤ U.dualAnnihilator :=
  (dualAnnihilator_gc R M).monotone_l hUV

@[mono]
theorem dualCoannihilator_anti {U V : Submodule R (Module.Dual R M)} (hUV : U ≤ V) :
    V.dualCoannihilator ≤ U.dualCoannihilator :=
  (dualAnnihilator_gc R M).monotone_u hUV

theorem le_dualAnnihilator_dualCoannihilator (U : Submodule R M) :
    U ≤ U.dualAnnihilator.dualCoannihilator :=
  (dualAnnihilator_gc R M).le_u_l U

theorem le_dualCoannihilator_dualAnnihilator (U : Submodule R (Module.Dual R M)) :
    U ≤ U.dualCoannihilator.dualAnnihilator :=
  (dualAnnihilator_gc R M).l_u_le U

theorem dualAnnihilator_dualCoannihilator_dualAnnihilator (U : Submodule R M) :
    U.dualAnnihilator.dualCoannihilator.dualAnnihilator = U.dualAnnihilator :=
  (dualAnnihilator_gc R M).l_u_l_eq_l U

theorem dualCoannihilator_dualAnnihilator_dualCoannihilator (U : Submodule R (Module.Dual R M)) :
    U.dualCoannihilator.dualAnnihilator.dualCoannihilator = U.dualCoannihilator :=
  (dualAnnihilator_gc R M).u_l_u_eq_u U

theorem dualAnnihilator_sup_eq (U V : Submodule R M) :
    (U ⊔ V).dualAnnihilator = U.dualAnnihilator ⊓ V.dualAnnihilator :=
  (dualAnnihilator_gc R M).l_sup

theorem dualCoannihilator_sup_eq (U V : Submodule R (Module.Dual R M)) :
    (U ⊔ V).dualCoannihilator = U.dualCoannihilator ⊓ V.dualCoannihilator :=
  (dualAnnihilator_gc R M).u_inf

theorem dualAnnihilator_iSup_eq {ι : Sort*} (U : ι → Submodule R M) :
    (⨆ i : ι, U i).dualAnnihilator = ⨅ i : ι, (U i).dualAnnihilator :=
  (dualAnnihilator_gc R M).l_iSup

theorem dualCoannihilator_iSup_eq {ι : Sort*} (U : ι → Submodule R (Module.Dual R M)) :
    (⨆ i : ι, U i).dualCoannihilator = ⨅ i : ι, (U i).dualCoannihilator :=
  (dualAnnihilator_gc R M).u_iInf

/-- See also `Subspace.dualAnnihilator_inf_eq` for vector subspaces. -/
theorem sup_dualAnnihilator_le_inf (U V : Submodule R M) :
    U.dualAnnihilator ⊔ V.dualAnnihilator ≤ (U ⊓ V).dualAnnihilator := by
  rw [le_dualAnnihilator_iff_le_dualCoannihilator, dualCoannihilator_sup_eq]
  apply inf_le_inf <;> exact le_dualAnnihilator_dualCoannihilator _

/-- See also `Subspace.dualAnnihilator_iInf_eq` for vector subspaces when `ι` is finite. -/
theorem iSup_dualAnnihilator_le_iInf {ι : Sort*} (U : ι → Submodule R M) :
    ⨆ i : ι, (U i).dualAnnihilator ≤ (⨅ i : ι, U i).dualAnnihilator := by
  rw [le_dualAnnihilator_iff_le_dualCoannihilator, dualCoannihilator_iSup_eq]
  apply iInf_mono
  exact fun i : ι => le_dualAnnihilator_dualCoannihilator (U i)

@[simp]
lemma coe_dualAnnihilator_span (s : Set M) :
    ((span R s).dualAnnihilator : Set (Module.Dual R M)) = {f | s ⊆ LinearMap.ker f} := by
  ext f
  simp only [SetLike.mem_coe, mem_dualAnnihilator, Set.mem_setOf_eq, ← LinearMap.mem_ker]
  exact span_le

@[simp]
lemma coe_dualCoannihilator_span (s : Set (Module.Dual R M)) :
    ((span R s).dualCoannihilator : Set M) = {x | ∀ f ∈ s, f x = 0} := by
  ext x
  have (φ : _) : x ∈ LinearMap.ker φ ↔ φ ∈ LinearMap.ker (Module.Dual.eval R M x) := by simp
  simp only [SetLike.mem_coe, mem_dualCoannihilator, Set.mem_setOf_eq, ← LinearMap.mem_ker, this]
  exact span_le

end Submodule

open Module

namespace LinearMap

variable {R M₁ M₂ : Type*} [CommSemiring R]
variable [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]
variable (f : M₁ →ₗ[R] M₂)

theorem ker_dualMap_eq_dualAnnihilator_range :
    LinearMap.ker f.dualMap = (range f).dualAnnihilator := by
  ext
  simp_rw [mem_ker, LinearMap.ext_iff, Submodule.mem_dualAnnihilator,
    ← SetLike.mem_coe, coe_range, Set.forall_mem_range]
  rfl

theorem range_dualMap_le_dualAnnihilator_ker :
    LinearMap.range f.dualMap ≤ (ker f).dualAnnihilator := by
  rintro _ ⟨ψ, rfl⟩
  simp_rw [Submodule.mem_dualAnnihilator, mem_ker]
  rintro x hx
  rw [dualMap_apply, hx, map_zero]

end LinearMap

section CommSemiring

variable {R M M' : Type*}
variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

namespace LinearMap

open Submodule

theorem ker_dualMap_eq_dualCoannihilator_range (f : M →ₗ[R] M') :
    LinearMap.ker f.dualMap = (range (Dual.eval R M' ∘ₗ f)).dualCoannihilator := by
  ext x; simp [LinearMap.ext_iff (f := dualMap f x)]

@[simp]
lemma dualCoannihilator_range_eq_ker_flip (B : M →ₗ[R] M' →ₗ[R] R) :
    (range B).dualCoannihilator = LinearMap.ker B.flip := by
  ext x; simp [LinearMap.ext_iff (f := B.flip x)]

end LinearMap

end CommSemiring
