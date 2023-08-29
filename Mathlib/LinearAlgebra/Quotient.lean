/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov
-/
import Mathlib.GroupTheory.QuotientGroup
import Mathlib.LinearAlgebra.Span

#align_import linear_algebra.quotient from "leanprover-community/mathlib"@"48085f140e684306f9e7da907cd5932056d1aded"

/-!
# Quotients by submodules

* If `p` is a submodule of `M`, `M ⧸ p` is the quotient of `M` with respect to `p`:
  that is, elements of `M` are identified if their difference is in `p`. This is itself a module.

-/

-- For most of this file we work over a noncommutative ring
section Ring

namespace Submodule

variable {R M : Type*} {r : R} {x y : M} [Ring R] [AddCommGroup M] [Module R M]

variable (p p' : Submodule R M)

open LinearMap QuotientAddGroup

/-- The equivalence relation associated to a submodule `p`, defined by `x ≈ y` iff `-x + y ∈ p`.

Note this is equivalent to `y - x ∈ p`, but defined this way to be defeq to the `AddSubgroup`
version, where commutativity can't be assumed. -/
def quotientRel : Setoid M :=
  QuotientAddGroup.leftRel p.toAddSubgroup
#align submodule.quotient_rel Submodule.quotientRel

theorem quotientRel_r_def {x y : M} : @Setoid.r _ p.quotientRel x y ↔ x - y ∈ p :=
  Iff.trans
    (by
      rw [leftRel_apply, sub_eq_add_neg, neg_add, neg_neg]
      -- ⊢ -x + y ∈ toAddSubgroup p ↔ -x + y ∈ p
      rfl)
      -- 🎉 no goals
    neg_mem_iff
#align submodule.quotient_rel_r_def Submodule.quotientRel_r_def

/-- The quotient of a module `M` by a submodule `p ⊆ M`. -/
instance hasQuotient : HasQuotient M (Submodule R M) :=
  ⟨fun p => Quotient (quotientRel p)⟩
#align submodule.has_quotient Submodule.hasQuotient

namespace Quotient

/-- Map associating to an element of `M` the corresponding element of `M/p`,
when `p` is a submodule of `M`. -/
def mk {p : Submodule R M} : M → M ⧸ p :=
  Quotient.mk''
#align submodule.quotient.mk Submodule.Quotient.mk

/- porting note: here and throughout elaboration is sped up *tremendously* (in some cases even
avoiding timeouts) by providing type ascriptions to `mk` (or `mk x`) and its variants. Lean 3
didn't need this help. -/
@[simp]
theorem mk'_eq_mk' {p : Submodule R M} (x : M) :
    @Quotient.mk' _ (quotientRel p) x = (mk : M → M ⧸ p) x :=
  rfl
#align submodule.quotient.mk_eq_mk Submodule.Quotient.mk'_eq_mk'

@[simp]
theorem mk''_eq_mk {p : Submodule R M} (x : M) : (Quotient.mk'' x : M ⧸ p) = (mk : M → M ⧸ p) x :=
  rfl
#align submodule.quotient.mk'_eq_mk Submodule.Quotient.mk''_eq_mk

@[simp]
theorem quot_mk_eq_mk {p : Submodule R M} (x : M) : (Quot.mk _ x : M ⧸ p) = (mk : M → M ⧸ p) x :=
  rfl
#align submodule.quotient.quot_mk_eq_mk Submodule.Quotient.quot_mk_eq_mk

protected theorem eq' {x y : M} : (mk x : M ⧸ p) = (mk : M → M ⧸ p) y ↔ -x + y ∈ p :=
  QuotientAddGroup.eq
#align submodule.quotient.eq' Submodule.Quotient.eq'

protected theorem eq {x y : M} : (mk x : M ⧸ p) = (mk y : M ⧸ p) ↔ x - y ∈ p :=
  (Submodule.Quotient.eq' p).trans (leftRel_apply.symm.trans p.quotientRel_r_def)
#align submodule.quotient.eq Submodule.Quotient.eq

instance : Zero (M ⧸ p) where
  -- Use Quotient.mk'' instead of mk here because mk is not reducible.
  -- This would lead to non-defeq diamonds.
  -- See also the same comment at the One instance for Con.
  zero := Quotient.mk'' 0

instance : Inhabited (M ⧸ p) :=
  ⟨0⟩

@[simp]
theorem mk_zero : mk 0 = (0 : M ⧸ p) :=
  rfl
#align submodule.quotient.mk_zero Submodule.Quotient.mk_zero

@[simp]
theorem mk_eq_zero : (mk x : M ⧸ p) = 0 ↔ x ∈ p := by simpa using (Quotient.eq' p : mk x = 0 ↔ _)
                                                      -- 🎉 no goals
#align submodule.quotient.mk_eq_zero Submodule.Quotient.mk_eq_zero

instance addCommGroup : AddCommGroup (M ⧸ p) :=
  QuotientAddGroup.Quotient.addCommGroup p.toAddSubgroup
#align submodule.quotient.add_comm_group Submodule.Quotient.addCommGroup

@[simp]
theorem mk_add : (mk (x + y) : M ⧸ p) = (mk x : M ⧸ p) + (mk y : M ⧸ p) :=
  rfl
#align submodule.quotient.mk_add Submodule.Quotient.mk_add

@[simp]
theorem mk_neg : (mk (-x) : M ⧸ p) = -(mk x : M ⧸ p) :=
  rfl
#align submodule.quotient.mk_neg Submodule.Quotient.mk_neg

@[simp]
theorem mk_sub : (mk (x - y) : M ⧸ p) = (mk x : M ⧸ p) - (mk y : M ⧸ p) :=
  rfl
#align submodule.quotient.mk_sub Submodule.Quotient.mk_sub

section SMul

variable {S : Type*} [SMul S R] [SMul S M] [IsScalarTower S R M] (P : Submodule R M)

instance instSMul' : SMul S (M ⧸ P) :=
  ⟨fun a =>
    Quotient.map' ((· • ·) a) fun x y h =>
      leftRel_apply.mpr <| by simpa using Submodule.smul_mem P (a • (1 : R)) (leftRel_apply.mp h)⟩
                              -- 🎉 no goals
#align submodule.quotient.has_smul' Submodule.Quotient.instSMul'

-- porting note: should this be marked as a `@[default_instance]`?
/-- Shortcut to help the elaborator in the common case. -/
instance instSMul : SMul R (M ⧸ P) :=
  Quotient.instSMul' P
#align submodule.quotient.has_smul Submodule.Quotient.instSMul

@[simp]
theorem mk_smul (r : S) (x : M) : (mk (r • x) : M ⧸ p) = r • mk x :=
  rfl
#align submodule.quotient.mk_smul Submodule.Quotient.mk_smul

instance smulCommClass (T : Type*) [SMul T R] [SMul T M] [IsScalarTower T R M]
    [SMulCommClass S T M] : SMulCommClass S T (M ⧸ P)
    where smul_comm _x _y := Quotient.ind' fun _z => congr_arg mk (smul_comm _ _ _)
#align submodule.quotient.smul_comm_class Submodule.Quotient.smulCommClass

instance isScalarTower (T : Type*) [SMul T R] [SMul T M] [IsScalarTower T R M] [SMul S T]
    [IsScalarTower S T M] : IsScalarTower S T (M ⧸ P)
    where smul_assoc _x _y := Quotient.ind' fun _z => congr_arg mk (smul_assoc _ _ _)
#align submodule.quotient.is_scalar_tower Submodule.Quotient.isScalarTower

instance isCentralScalar [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ M] [IsScalarTower Sᵐᵒᵖ R M]
    [IsCentralScalar S M] : IsCentralScalar S (M ⧸ P)
    where op_smul_eq_smul _x := Quotient.ind' fun _z => congr_arg mk <| op_smul_eq_smul _ _
#align submodule.quotient.is_central_scalar Submodule.Quotient.isCentralScalar

end SMul

section Module

variable {S : Type*}

instance mulAction' [Monoid S] [SMul S R] [MulAction S M] [IsScalarTower S R M]
    (P : Submodule R M) : MulAction S (M ⧸ P) :=
  Function.Surjective.mulAction mk (surjective_quot_mk _) <| Submodule.Quotient.mk_smul P
#align submodule.quotient.mul_action' Submodule.Quotient.mulAction'

-- porting note: should this be marked as a `@[default_instance]`?
instance mulAction (P : Submodule R M) : MulAction R (M ⧸ P) :=
  Quotient.mulAction' P
#align submodule.quotient.mul_action Submodule.Quotient.mulAction

instance smulZeroClass' [SMul S R] [SMulZeroClass S M] [IsScalarTower S R M] (P : Submodule R M) :
    SMulZeroClass S (M ⧸ P) :=
  ZeroHom.smulZeroClass ⟨mk, mk_zero _⟩ <| Submodule.Quotient.mk_smul P
#align submodule.quotient.smul_zero_class' Submodule.Quotient.smulZeroClass'

-- porting note: should this be marked as a `@[default_instance]`?
instance smulZeroClass (P : Submodule R M) : SMulZeroClass R (M ⧸ P) :=
  Quotient.smulZeroClass' P
#align submodule.quotient.smul_zero_class Submodule.Quotient.smulZeroClass

instance distribSMul' [SMul S R] [DistribSMul S M] [IsScalarTower S R M] (P : Submodule R M) :
    DistribSMul S (M ⧸ P) :=
  Function.Surjective.distribSMul {toFun := mk, map_zero' := rfl, map_add' := fun _ _ => rfl}
    (surjective_quot_mk _) (Submodule.Quotient.mk_smul P)
#align submodule.quotient.distrib_smul' Submodule.Quotient.distribSMul'

-- porting note: should this be marked as a `@[default_instance]`?
instance distribSMul (P : Submodule R M) : DistribSMul R (M ⧸ P) :=
  Quotient.distribSMul' P
#align submodule.quotient.distrib_smul Submodule.Quotient.distribSMul

instance distribMulAction' [Monoid S] [SMul S R] [DistribMulAction S M] [IsScalarTower S R M]
    (P : Submodule R M) : DistribMulAction S (M ⧸ P) :=
  Function.Surjective.distribMulAction {toFun := mk, map_zero' := rfl, map_add' := fun _ _ => rfl}
    (surjective_quot_mk _) (Submodule.Quotient.mk_smul P)
#align submodule.quotient.distrib_mul_action' Submodule.Quotient.distribMulAction'

-- porting note: should this be marked as a `@[default_instance]`?
instance distribMulAction (P : Submodule R M) : DistribMulAction R (M ⧸ P) :=
  Quotient.distribMulAction' P
#align submodule.quotient.distrib_mul_action Submodule.Quotient.distribMulAction

instance module' [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M] (P : Submodule R M) :
    Module S (M ⧸ P) :=
  Function.Surjective.module _ {toFun := mk, map_zero' := rfl, map_add' := fun _ _ => rfl}
    (surjective_quot_mk _) (Submodule.Quotient.mk_smul P)
#align submodule.quotient.module' Submodule.Quotient.module'

-- porting note: should this be marked as a `@[default_instance]`?
instance module (P : Submodule R M) : Module R (M ⧸ P) :=
  Quotient.module' P
#align submodule.quotient.module Submodule.Quotient.module

variable (S)

/-- The quotient of `P` as an `S`-submodule is the same as the quotient of `P` as an `R`-submodule,
where `P : Submodule R M`.
-/
def restrictScalarsEquiv [Ring S] [SMul S R] [Module S M] [IsScalarTower S R M]
    (P : Submodule R M) : (M ⧸ P.restrictScalars S) ≃ₗ[S] M ⧸ P :=
  { Quotient.congrRight fun _ _ => Iff.rfl with
    map_add' := fun x y => Quotient.inductionOn₂' x y fun _x' _y' => rfl
    map_smul' := fun _c x => Quotient.inductionOn' x fun _x' => rfl }
#align submodule.quotient.restrict_scalars_equiv Submodule.Quotient.restrictScalarsEquiv

@[simp]
theorem restrictScalarsEquiv_mk [Ring S] [SMul S R] [Module S M] [IsScalarTower S R M]
    (P : Submodule R M) (x : M) :
    restrictScalarsEquiv S P (mk x : M ⧸ P) = (mk x : M ⧸ P) :=
  rfl
#align submodule.quotient.restrict_scalars_equiv_mk Submodule.Quotient.restrictScalarsEquiv_mk

@[simp]
theorem restrictScalarsEquiv_symm_mk [Ring S] [SMul S R] [Module S M] [IsScalarTower S R M]
    (P : Submodule R M) (x : M) :
    (restrictScalarsEquiv S P).symm ((mk : M → M ⧸ P) x) = (mk : M → M ⧸ P) x :=
  rfl
#align submodule.quotient.restrict_scalars_equiv_symm_mk Submodule.Quotient.restrictScalarsEquiv_symm_mk

end Module

theorem mk_surjective : Function.Surjective (@mk _ _ _ _ _ p) := by
  rintro ⟨x⟩
  -- ⊢ ∃ a, mk a = Quot.mk Setoid.r x
  exact ⟨x, rfl⟩
  -- 🎉 no goals
#align submodule.quotient.mk_surjective Submodule.Quotient.mk_surjective

theorem nontrivial_of_lt_top (h : p < ⊤) : Nontrivial (M ⧸ p) := by
  obtain ⟨x, _, not_mem_s⟩ := SetLike.exists_of_lt h
  -- ⊢ Nontrivial (M ⧸ p)
  refine' ⟨⟨mk x, 0, _⟩⟩
  -- ⊢ mk x ≠ 0
  simpa using not_mem_s
  -- 🎉 no goals
#align submodule.quotient.nontrivial_of_lt_top Submodule.Quotient.nontrivial_of_lt_top

end Quotient

instance QuotientBot.infinite [Infinite M] : Infinite (M ⧸ (⊥ : Submodule R M)) :=
  Infinite.of_injective Submodule.Quotient.mk fun _x _y h =>
    sub_eq_zero.mp <| (Submodule.Quotient.eq ⊥).mp h
#align submodule.quotient_bot.infinite Submodule.QuotientBot.infinite

instance QuotientTop.unique : Unique (M ⧸ (⊤ : Submodule R M)) where
  default := 0
  uniq x := Quotient.inductionOn' x fun _x => (Submodule.Quotient.eq ⊤).mpr Submodule.mem_top
#align submodule.quotient_top.unique Submodule.QuotientTop.unique

instance QuotientTop.fintype : Fintype (M ⧸ (⊤ : Submodule R M)) :=
  Fintype.ofSubsingleton 0
#align submodule.quotient_top.fintype Submodule.QuotientTop.fintype

variable {p}

theorem subsingleton_quotient_iff_eq_top : Subsingleton (M ⧸ p) ↔ p = ⊤ := by
  constructor
  -- ⊢ Subsingleton (M ⧸ p) → p = ⊤
  · rintro h
    -- ⊢ p = ⊤
    refine' eq_top_iff.mpr fun x _ => _
    -- ⊢ x ∈ p
    have : x - 0 ∈ p := (Submodule.Quotient.eq p).mp (Subsingleton.elim _ _)
    -- ⊢ x ∈ p
    rwa [sub_zero] at this
    -- 🎉 no goals
  · rintro rfl
    -- ⊢ Subsingleton (M ⧸ ⊤)
    infer_instance
    -- 🎉 no goals
#align submodule.subsingleton_quotient_iff_eq_top Submodule.subsingleton_quotient_iff_eq_top

theorem unique_quotient_iff_eq_top : Nonempty (Unique (M ⧸ p)) ↔ p = ⊤ :=
  ⟨fun ⟨h⟩ => subsingleton_quotient_iff_eq_top.mp (@Unique.instSubsingleton _ h),
    by rintro rfl; exact ⟨QuotientTop.unique⟩⟩
       -- ⊢ Nonempty (Unique (M ⧸ ⊤))
                   -- 🎉 no goals
#align submodule.unique_quotient_iff_eq_top Submodule.unique_quotient_iff_eq_top

variable (p)

noncomputable instance Quotient.fintype [Fintype M] (S : Submodule R M) : Fintype (M ⧸ S) :=
  @_root_.Quotient.fintype _ _ _ fun _ _ => Classical.dec _
#align submodule.quotient.fintype Submodule.Quotient.fintype

theorem card_eq_card_quotient_mul_card [Fintype M] (S : Submodule R M) [DecidablePred (· ∈ S)] :
    Fintype.card M = Fintype.card S * Fintype.card (M ⧸ S) := by
  rw [mul_comm, ← Fintype.card_prod]
  -- ⊢ Fintype.card M = Fintype.card ((M ⧸ S) × { x // x ∈ S })
  exact Fintype.card_congr AddSubgroup.addGroupEquivQuotientProdAddSubgroup
  -- 🎉 no goals
#align submodule.card_eq_card_quotient_mul_card Submodule.card_eq_card_quotient_mul_card

section

variable {M₂ : Type*} [AddCommGroup M₂] [Module R M₂]

theorem quot_hom_ext (f g : (M ⧸ p) →ₗ[R] M₂) (h : ∀ x : M, f (Quotient.mk x) = g (Quotient.mk x)) :
    f = g :=
  LinearMap.ext fun x => Quotient.inductionOn' x h
#align submodule.quot_hom_ext Submodule.quot_hom_ext

/-- The map from a module `M` to the quotient of `M` by a submodule `p` as a linear map. -/
def mkQ : M →ₗ[R] M ⧸ p where
  toFun := Quotient.mk
  map_add' := by simp
                 -- 🎉 no goals
  map_smul' := by simp
                  -- 🎉 no goals
#align submodule.mkq Submodule.mkQ

@[simp]
theorem mkQ_apply (x : M) : p.mkQ x = (Quotient.mk x : M ⧸ p) :=
  rfl
#align submodule.mkq_apply Submodule.mkQ_apply

theorem mkQ_surjective (A : Submodule R M) : Function.Surjective A.mkQ := by
  rintro ⟨x⟩; exact ⟨x, rfl⟩
  -- ⊢ ∃ a, ↑(mkQ A) a = Quot.mk Setoid.r x
              -- 🎉 no goals
#align submodule.mkq_surjective Submodule.mkQ_surjective

end

variable {R₂ M₂ : Type*} [Ring R₂] [AddCommGroup M₂] [Module R₂ M₂] {τ₁₂ : R →+* R₂}

/-- Two `LinearMap`s from a quotient module are equal if their compositions with
`submodule.mkQ` are equal.

See note [partially-applied ext lemmas]. -/
@[ext 1100] -- porting note: increase priority so this applies before `LinearMap.ext`
theorem linearMap_qext ⦃f g : M ⧸ p →ₛₗ[τ₁₂] M₂⦄ (h : f.comp p.mkQ = g.comp p.mkQ) : f = g :=
  LinearMap.ext fun x => Quotient.inductionOn' x <| (LinearMap.congr_fun h : _)
#align submodule.linear_map_qext Submodule.linearMap_qext

/-- The map from the quotient of `M` by a submodule `p` to `M₂` induced by a linear map `f : M → M₂`
vanishing on `p`, as a linear map. -/
def liftQ (f : M →ₛₗ[τ₁₂] M₂) (h : p ≤ ker f) : M ⧸ p →ₛₗ[τ₁₂] M₂ :=
  { QuotientAddGroup.lift p.toAddSubgroup f.toAddMonoidHom h with
    map_smul' := by rintro a ⟨x⟩; exact f.map_smulₛₗ a x }
                    -- ⊢ AddHom.toFun { toFun := src✝.toFun, map_add' := (_ : ∀ (x y : M ⧸ toAddSubgr …
                                  -- 🎉 no goals
#align submodule.liftq Submodule.liftQ

@[simp]
theorem liftQ_apply (f : M →ₛₗ[τ₁₂] M₂) {h} (x : M) : p.liftQ f h (Quotient.mk x) = f x :=
  rfl
#align submodule.liftq_apply Submodule.liftQ_apply

@[simp]
theorem liftQ_mkQ (f : M →ₛₗ[τ₁₂] M₂) (h) : (p.liftQ f h).comp p.mkQ = f := by ext; rfl
                                                                               -- ⊢ ↑(comp (liftQ p f h) (mkQ p)) x✝ = ↑f x✝
                                                                                    -- 🎉 no goals
#align submodule.liftq_mkq Submodule.liftQ_mkQ

/-- Special case of `submodule.liftQ` when `p` is the span of `x`. In this case, the condition on
`f` simply becomes vanishing at `x`.-/
def liftQSpanSingleton (x : M) (f : M →ₛₗ[τ₁₂] M₂) (h : f x = 0) : (M ⧸ R ∙ x) →ₛₗ[τ₁₂] M₂ :=
  (R ∙ x).liftQ f <| by rw [span_singleton_le_iff_mem, LinearMap.mem_ker, h]
                        -- 🎉 no goals
#align submodule.liftq_span_singleton Submodule.liftQSpanSingleton

@[simp]
theorem liftQSpanSingleton_apply (x : M) (f : M →ₛₗ[τ₁₂] M₂) (h : f x = 0) (y : M) :
    liftQSpanSingleton x f h (Quotient.mk y) = f y :=
  rfl
#align submodule.liftq_span_singleton_apply Submodule.liftQSpanSingleton_apply

@[simp]
theorem range_mkQ : range p.mkQ = ⊤ :=
  eq_top_iff'.2 <| by rintro ⟨x⟩; exact ⟨x, rfl⟩
                      -- ⊢ Quot.mk Setoid.r x ∈ range (mkQ p)
                                  -- 🎉 no goals
#align submodule.range_mkq Submodule.range_mkQ

@[simp]
theorem ker_mkQ : ker p.mkQ = p := by ext; simp
                                      -- ⊢ x✝ ∈ ker (mkQ p) ↔ x✝ ∈ p
                                           -- 🎉 no goals
#align submodule.ker_mkq Submodule.ker_mkQ

theorem le_comap_mkQ (p' : Submodule R (M ⧸ p)) : p ≤ comap p.mkQ p' := by
  simpa using (comap_mono bot_le : ker p.mkQ ≤ comap p.mkQ p')
  -- 🎉 no goals
#align submodule.le_comap_mkq Submodule.le_comap_mkQ

@[simp]
theorem mkQ_map_self : map p.mkQ p = ⊥ := by
  rw [eq_bot_iff, map_le_iff_le_comap, comap_bot, ker_mkQ]
  -- 🎉 no goals
#align submodule.mkq_map_self Submodule.mkQ_map_self

@[simp]
theorem comap_map_mkQ : comap p.mkQ (map p.mkQ p') = p ⊔ p' := by simp [comap_map_eq, sup_comm]
                                                                  -- 🎉 no goals
#align submodule.comap_map_mkq Submodule.comap_map_mkQ

@[simp]
theorem map_mkQ_eq_top : map p.mkQ p' = ⊤ ↔ p ⊔ p' = ⊤ := by
  -- porting note: ambiguity of `map_eq_top_iff` is no longer automatically resolved by preferring
  -- the current namespace
  simp only [LinearMap.map_eq_top_iff p.range_mkQ, sup_comm, ker_mkQ]
  -- 🎉 no goals
#align submodule.map_mkq_eq_top Submodule.map_mkQ_eq_top

variable (q : Submodule R₂ M₂)

/-- The map from the quotient of `M` by submodule `p` to the quotient of `M₂` by submodule `q` along
`f : M → M₂` is linear. -/
def mapQ (f : M →ₛₗ[τ₁₂] M₂) (h : p ≤ comap f q) : M ⧸ p →ₛₗ[τ₁₂] M₂ ⧸ q :=
  p.liftQ (q.mkQ.comp f) <| by simpa [ker_comp] using h
                               -- 🎉 no goals
#align submodule.mapq Submodule.mapQ

@[simp]
theorem mapQ_apply (f : M →ₛₗ[τ₁₂] M₂) {h} (x : M) :
    mapQ p q f h (Quotient.mk x : M ⧸ p) = (Quotient.mk (f x) : M₂ ⧸ q) :=
  rfl
#align submodule.mapq_apply Submodule.mapQ_apply

theorem mapQ_mkQ (f : M →ₛₗ[τ₁₂] M₂) {h} : (mapQ p q f h).comp p.mkQ = q.mkQ.comp f := by
  ext x; rfl
  -- ⊢ ↑(comp (mapQ p q f h) (mkQ p)) x = ↑(comp (mkQ q) f) x
         -- 🎉 no goals
#align submodule.mapq_mkq Submodule.mapQ_mkQ

@[simp]
theorem mapQ_zero (h : p ≤ q.comap (0 : M →ₛₗ[τ₁₂] M₂) := (by simp)) :
                                                              -- 🎉 no goals
    p.mapQ q (0 : M →ₛₗ[τ₁₂] M₂) h = 0 := by
  ext
  -- ⊢ ↑(comp (mapQ p q 0 h) (mkQ p)) x✝ = ↑(comp 0 (mkQ p)) x✝
  simp
  -- 🎉 no goals
#align submodule.mapq_zero Submodule.mapQ_zero

/-- Given submodules `p ⊆ M`, `p₂ ⊆ M₂`, `p₃ ⊆ M₃` and maps `f : M → M₂`, `g : M₂ → M₃` inducing
`mapQ f : M ⧸ p → M₂ ⧸ p₂` and `mapQ g : M₂ ⧸ p₂ → M₃ ⧸ p₃` then
`mapQ (g ∘ f) = (mapQ g) ∘ (mapQ f)`. -/
theorem mapQ_comp {R₃ M₃ : Type*} [Ring R₃] [AddCommGroup M₃] [Module R₃ M₃] (p₂ : Submodule R₂ M₂)
    (p₃ : Submodule R₃ M₃) {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃} [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]
    (f : M →ₛₗ[τ₁₂] M₂) (g : M₂ →ₛₗ[τ₂₃] M₃) (hf : p ≤ p₂.comap f) (hg : p₂ ≤ p₃.comap g)
    (h := hf.trans (comap_mono hg)) :
    p.mapQ p₃ (g.comp f) h = (p₂.mapQ p₃ g hg).comp (p.mapQ p₂ f hf) := by
  ext
  -- ⊢ ↑(comp (mapQ p p₃ (comp g f) h) (mkQ p)) x✝ = ↑(comp (comp (mapQ p₂ p₃ g hg) …
  simp
  -- 🎉 no goals
#align submodule.mapq_comp Submodule.mapQ_comp

@[simp]
theorem mapQ_id (h : p ≤ p.comap LinearMap.id := (by rw [comap_id])) :
                                                     -- 🎉 no goals
    p.mapQ p LinearMap.id h = LinearMap.id := by
  ext
  -- ⊢ ↑(comp (mapQ p p LinearMap.id h) (mkQ p)) x✝ = ↑(comp LinearMap.id (mkQ p)) x✝
  simp
  -- 🎉 no goals
#align submodule.mapq_id Submodule.mapQ_id

theorem mapQ_pow {f : M →ₗ[R] M} (h : p ≤ p.comap f) (k : ℕ)
    (h' : p ≤ p.comap (f ^ k) := p.le_comap_pow_of_le_comap h k) :
    p.mapQ p (f ^ k) h' = p.mapQ p f h ^ k := by
  induction' k with k ih
  -- ⊢ mapQ p p (f ^ Nat.zero) h' = mapQ p p f h ^ Nat.zero
  · simp [LinearMap.one_eq_id]
    -- 🎉 no goals
  · simp only [LinearMap.iterate_succ]
    -- ⊢ mapQ p p (comp (f ^ k) f) (_ : p ≤ comap (comp (f ^ k) f) p) = comp (mapQ p  …
    -- porting note: why does any of these `optParams` need to be applied? Why didn't `simp` handle
    -- all of this for us?
    convert mapQ_comp p p p f (f ^ k) h (p.le_comap_pow_of_le_comap h k)
      (h.trans (comap_mono <| p.le_comap_pow_of_le_comap h k))
    exact (ih _).symm
    -- 🎉 no goals
#align submodule.mapq_pow Submodule.mapQ_pow

theorem comap_liftQ (f : M →ₛₗ[τ₁₂] M₂) (h) : q.comap (p.liftQ f h) = (q.comap f).map (mkQ p) :=
  le_antisymm (by rintro ⟨x⟩ hx; exact ⟨_, hx, rfl⟩)
                  -- ⊢ Quot.mk Setoid.r x ∈ map (mkQ p) (comap f q)
                                 -- 🎉 no goals
    (by rw [map_le_iff_le_comap, ← comap_comp, liftQ_mkQ])
        -- 🎉 no goals
#align submodule.comap_liftq Submodule.comap_liftQ

theorem map_liftQ [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) (h) (q : Submodule R (M ⧸ p)) :
    q.map (p.liftQ f h) = (q.comap p.mkQ).map f :=
  le_antisymm (by rintro _ ⟨⟨x⟩, hxq, rfl⟩; exact ⟨x, hxq, rfl⟩)
                  -- ⊢ ↑(liftQ p f h) (Quot.mk Setoid.r x) ∈ map f (comap (mkQ p) q)
                                            -- 🎉 no goals
    (by rintro _ ⟨x, hxq, rfl⟩; exact ⟨Quotient.mk x, hxq, rfl⟩)
        -- ⊢ ↑f x ∈ map (liftQ p f h) q
                                -- 🎉 no goals
#align submodule.map_liftq Submodule.map_liftQ

theorem ker_liftQ (f : M →ₛₗ[τ₁₂] M₂) (h) : ker (p.liftQ f h) = (ker f).map (mkQ p) :=
  comap_liftQ _ _ _ _
#align submodule.ker_liftq Submodule.ker_liftQ

theorem range_liftQ [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) (h) :
    range (p.liftQ f h) = range f := by simpa only [range_eq_map] using map_liftQ _ _ _ _
                                        -- 🎉 no goals
#align submodule.range_liftq Submodule.range_liftQ

theorem ker_liftQ_eq_bot (f : M →ₛₗ[τ₁₂] M₂) (h) (h' : ker f ≤ p) : ker (p.liftQ f h) = ⊥ := by
  rw [ker_liftQ, le_antisymm h h', mkQ_map_self]
  -- 🎉 no goals
#align submodule.ker_liftq_eq_bot Submodule.ker_liftQ_eq_bot

/-- The correspondence theorem for modules: there is an order isomorphism between submodules of the
quotient of `M` by `p`, and submodules of `M` larger than `p`. -/
def comapMkQRelIso : Submodule R (M ⧸ p) ≃o { p' : Submodule R M // p ≤ p' } where
  toFun p' := ⟨comap p.mkQ p', le_comap_mkQ p _⟩
  invFun q := map p.mkQ q
  left_inv p' := map_comap_eq_self <| by simp
                                         -- 🎉 no goals
  right_inv := fun ⟨q, hq⟩ => Subtype.ext_val <| by simpa [comap_map_mkQ p]
                                                    -- 🎉 no goals
  map_rel_iff' := comap_le_comap_iff <| range_mkQ _
#align submodule.comap_mkq.rel_iso Submodule.comapMkQRelIso

/-- The ordering on submodules of the quotient of `M` by `p` embeds into the ordering on submodules
of `M`. -/
def comapMkQOrderEmbedding : Submodule R (M ⧸ p) ↪o Submodule R M :=
  (RelIso.toRelEmbedding <| comapMkQRelIso p).trans (Subtype.relEmbedding (· ≤ ·) _)
#align submodule.comap_mkq.order_embedding Submodule.comapMkQOrderEmbedding

@[simp]
theorem comapMkQOrderEmbedding_eq (p' : Submodule R (M ⧸ p)) :
    comapMkQOrderEmbedding p p' = comap p.mkQ p' :=
  rfl
#align submodule.comap_mkq_embedding_eq Submodule.comapMkQOrderEmbedding_eq

theorem span_preimage_eq [RingHomSurjective τ₁₂] {f : M →ₛₗ[τ₁₂] M₂} {s : Set M₂} (h₀ : s.Nonempty)
    (h₁ : s ⊆ range f) : span R (f ⁻¹' s) = (span R₂ s).comap f := by
  suffices (span R₂ s).comap f ≤ span R (f ⁻¹' s) by exact le_antisymm (span_preimage_le f s) this
  -- ⊢ comap f (span R₂ s) ≤ span R (↑f ⁻¹' s)
  have hk : ker f ≤ span R (f ⁻¹' s) := by
    let y := Classical.choose h₀
    have hy : y ∈ s := Classical.choose_spec h₀
    rw [ker_le_iff]
    use y, h₁ hy
    rw [← Set.singleton_subset_iff] at hy
    exact Set.Subset.trans subset_span (span_mono (Set.preimage_mono hy))
  rw [← left_eq_sup] at hk
  -- ⊢ comap f (span R₂ s) ≤ span R (↑f ⁻¹' s)
  rw [range_coe f] at h₁
  -- ⊢ comap f (span R₂ s) ≤ span R (↑f ⁻¹' s)
  rw [hk, ← LinearMap.map_le_map_iff, map_span, map_comap_eq, Set.image_preimage_eq_of_subset h₁]
  -- ⊢ range f ⊓ span R₂ s ≤ span R₂ s
  exact inf_le_right
  -- 🎉 no goals
#align submodule.span_preimage_eq Submodule.span_preimage_eq

/-- If `P` is a submodule of `M` and `Q` a submodule of `N`,
and `f : M ≃ₗ N` maps `P` to `Q`, then `M ⧸ P` is equivalent to `N ⧸ Q`. -/
@[simps]
def Quotient.equiv {N : Type*} [AddCommGroup N] [Module R N] (P : Submodule R M)
    (Q : Submodule R N) (f : M ≃ₗ[R] N) (hf : P.map f = Q) : (M ⧸ P) ≃ₗ[R] N ⧸ Q :=
  { P.mapQ Q (f : M →ₗ[R] N) fun x hx => hf ▸ Submodule.mem_map_of_mem hx with
    toFun := P.mapQ Q (f : M →ₗ[R] N) fun x hx => hf ▸ Submodule.mem_map_of_mem hx
    invFun :=
      Q.mapQ P (f.symm : N →ₗ[R] M) fun x hx => by
        rw [← hf, Submodule.mem_map] at hx
        -- ⊢ x ∈ comap (↑(LinearEquiv.symm f)) P
        obtain ⟨y, hy, rfl⟩ := hx
        -- ⊢ ↑f y ∈ comap (↑(LinearEquiv.symm f)) P
        simpa
        -- 🎉 no goals
    left_inv := fun x => Quotient.inductionOn' x (by simp)
                                                     -- 🎉 no goals
    right_inv := fun x => Quotient.inductionOn' x (by simp) }
                                                      -- 🎉 no goals
#align submodule.quotient.equiv Submodule.Quotient.equiv
#align submodule.quotient.equiv_apply Submodule.Quotient.equiv_apply

@[simp]
theorem Quotient.equiv_symm {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (P : Submodule R M) (Q : Submodule R N) (f : M ≃ₗ[R] N)
    (hf : P.map f = Q) :
    (Quotient.equiv P Q f hf).symm =
      Quotient.equiv Q P f.symm ((Submodule.map_symm_eq_iff f).mpr hf) :=
  rfl
#align submodule.quotient.equiv_symm Submodule.Quotient.equiv_symm

@[simp]
theorem Quotient.equiv_trans {N O : Type*} [AddCommGroup N] [Module R N] [AddCommGroup O]
    [Module R O] (P : Submodule R M) (Q : Submodule R N) (S : Submodule R O) (e : M ≃ₗ[R] N)
    (f : N ≃ₗ[R] O) (he : P.map e = Q) (hf : Q.map f = S) (hef : P.map (e.trans f) = S) :
    Quotient.equiv P S (e.trans f) hef =
      (Quotient.equiv P Q e he).trans (Quotient.equiv Q S f hf) := by
  ext
  -- ⊢ ↑(equiv P S (LinearEquiv.trans e f) hef) x✝ = ↑(LinearEquiv.trans (equiv P Q …
  -- `simp` can deal with `hef` depending on `e` and `f`
  simp only [Quotient.equiv_apply, LinearEquiv.trans_apply, LinearEquiv.coe_trans]
  -- ⊢ ↑(mapQ P S (comp ↑f ↑e) (_ : P ≤ comap (comp ↑f ↑e) S)) x✝ = ↑(mapQ Q S ↑f ( …
  -- `rw` can deal with `mapQ_comp` needing extra hypotheses coming from the RHS
  rw [mapQ_comp, LinearMap.comp_apply]
  -- 🎉 no goals
#align submodule.quotient.equiv_trans Submodule.Quotient.equiv_trans

end Submodule

open Submodule

namespace LinearMap

section Ring

variable {R M R₂ M₂ R₃ M₃ : Type*}

variable [Ring R] [Ring R₂] [Ring R₃]

variable [AddCommMonoid M] [AddCommGroup M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

variable {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}

variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃] [RingHomSurjective τ₁₂]

theorem range_mkQ_comp (f : M →ₛₗ[τ₁₂] M₂) : f.range.mkQ.comp f = 0 :=
  LinearMap.ext fun x => by simp
                            -- 🎉 no goals
#align linear_map.range_mkq_comp LinearMap.range_mkQ_comp

theorem ker_le_range_iff {f : M →ₛₗ[τ₁₂] M₂} {g : M₂ →ₛₗ[τ₂₃] M₃} :
    ker g ≤ range f ↔ f.range.mkQ.comp g.ker.subtype = 0 := by
  rw [← range_le_ker_iff, Submodule.ker_mkQ, Submodule.range_subtype]
  -- 🎉 no goals
#align linear_map.ker_le_range_iff LinearMap.ker_le_range_iff

/-- An epimorphism is surjective. -/
theorem range_eq_top_of_cancel {f : M →ₛₗ[τ₁₂] M₂}
    (h : ∀ u v : M₂ →ₗ[R₂] M₂ ⧸ (range f), u.comp f = v.comp f → u = v) : range f = ⊤ := by
  have h₁ : (0 : M₂ →ₗ[R₂] M₂ ⧸ (range f)).comp f = 0 := zero_comp _
  -- ⊢ range f = ⊤
  rw [← Submodule.ker_mkQ (range f), ← h 0 f.range.mkQ (Eq.trans h₁ (range_mkQ_comp _).symm)]
  -- ⊢ ker 0 = ⊤
  exact ker_zero
  -- 🎉 no goals
#align linear_map.range_eq_top_of_cancel LinearMap.range_eq_top_of_cancel

end Ring

end LinearMap

open LinearMap

namespace Submodule

variable {R M : Type*} {r : R} {x y : M} [Ring R] [AddCommGroup M] [Module R M]

variable (p p' : Submodule R M)

/-- If `p = ⊥`, then `M / p ≃ₗ[R] M`. -/
def quotEquivOfEqBot (hp : p = ⊥) : (M ⧸ p) ≃ₗ[R] M :=
  LinearEquiv.ofLinear (p.liftQ id <| hp.symm ▸ bot_le) p.mkQ (liftQ_mkQ _ _ _) <|
    p.quot_hom_ext _ LinearMap.id fun _ => rfl
#align submodule.quot_equiv_of_eq_bot Submodule.quotEquivOfEqBot

@[simp]
theorem quotEquivOfEqBot_apply_mk (hp : p = ⊥) (x : M) :
    p.quotEquivOfEqBot hp (Quotient.mk x : M ⧸ p) = x :=
  rfl
#align submodule.quot_equiv_of_eq_bot_apply_mk Submodule.quotEquivOfEqBot_apply_mk

@[simp]
theorem quotEquivOfEqBot_symm_apply (hp : p = ⊥) (x : M) :
    (p.quotEquivOfEqBot hp).symm x = (Quotient.mk x : M ⧸ p) :=
  rfl
#align submodule.quot_equiv_of_eq_bot_symm_apply Submodule.quotEquivOfEqBot_symm_apply

@[simp]
theorem coe_quotEquivOfEqBot_symm (hp : p = ⊥) :
    ((p.quotEquivOfEqBot hp).symm : M →ₗ[R] M ⧸ p) = p.mkQ :=
  rfl
#align submodule.coe_quot_equiv_of_eq_bot_symm Submodule.coe_quotEquivOfEqBot_symm

/-- Quotienting by equal submodules gives linearly equivalent quotients. -/
def quotEquivOfEq (h : p = p') : (M ⧸ p) ≃ₗ[R] M ⧸ p' :=
  { @Quotient.congr _ _ (quotientRel p) (quotientRel p') (Equiv.refl _) fun a b => by
      subst h
      -- ⊢ Setoid.r a b ↔ Setoid.r (↑(Equiv.refl M) a) (↑(Equiv.refl M) b)
      rfl with
      -- 🎉 no goals
    map_add' := by
      rintro ⟨x⟩ ⟨y⟩
      -- ⊢ Equiv.toFun src✝ (Quot.mk Setoid.r x + Quot.mk Setoid.r y) = Equiv.toFun src …
      rfl
      -- 🎉 no goals
    map_smul' := by
      rintro x ⟨y⟩
      -- ⊢ AddHom.toFun { toFun := src✝.toFun, map_add' := (_ : ∀ (x y : M ⧸ p), Equiv. …
      rfl }
      -- 🎉 no goals
#align submodule.quot_equiv_of_eq Submodule.quotEquivOfEq

@[simp]
theorem quotEquivOfEq_mk (h : p = p') (x : M) :
    Submodule.quotEquivOfEq p p' h (Submodule.Quotient.mk x : M ⧸ p) =
      (Submodule.Quotient.mk x : M ⧸ p') :=
  rfl
#align submodule.quot_equiv_of_eq_mk Submodule.quotEquivOfEq_mk

@[simp]
theorem Quotient.equiv_refl (P : Submodule R M) (Q : Submodule R M)
    (hf : P.map (LinearEquiv.refl R M : M →ₗ[R] M) = Q) :
    Quotient.equiv P Q (LinearEquiv.refl R M) hf = quotEquivOfEq _ _ (by simpa using hf) :=
                                                                         -- 🎉 no goals
  rfl
#align submodule.quotient.equiv_refl Submodule.Quotient.equiv_refl

end Submodule

end Ring

section CommRing

variable {R M M₂ : Type*} {r : R} {x y : M} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup M₂] [Module R M₂] (p : Submodule R M) (q : Submodule R M₂)

namespace Submodule

/-- Given modules `M`, `M₂` over a commutative ring, together with submodules `p ⊆ M`, `q ⊆ M₂`,
the natural map $\{f ∈ Hom(M, M₂) | f(p) ⊆ q \} \to Hom(M/p, M₂/q)$ is linear. -/
def mapQLinear : compatibleMaps p q →ₗ[R] M ⧸ p →ₗ[R] M₂ ⧸ q
    where
  toFun f := mapQ _ _ f.val f.property
  map_add' x y := by
    ext
    -- ⊢ ↑(LinearMap.comp ((fun f => mapQ p q ↑f (_ : ↑f ∈ compatibleMaps p q)) (x +  …
    rfl
    -- 🎉 no goals
  map_smul' c f := by
    ext
    -- ⊢ ↑(LinearMap.comp (AddHom.toFun { toFun := fun f => mapQ p q ↑f (_ : ↑f ∈ com …
    rfl
    -- 🎉 no goals
#align submodule.mapq_linear Submodule.mapQLinear

end Submodule

end CommRing
