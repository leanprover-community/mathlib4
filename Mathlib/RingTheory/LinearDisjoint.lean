/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.LinearAlgebra.LinearDisjoint
import Mathlib.LinearAlgebra.TensorProduct.Subalgebra
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!

# Linearly disjoint of subalgebras

This file contains basics about the linearly disjoint of subalgebras.

## Main definitions

- ...

## Main results

- ...

## Tags

linearly disjoint, linearly independent, tensor product

## TODO

- ...

-/

open scoped Classical TensorProduct

open FiniteDimensional

noncomputable section

universe u v w

namespace Subalgebra

variable {R : Type u} {S : Type v}

section Semiring

variable [CommSemiring R] [Semiring S] [Algebra R S]

variable (A B : Subalgebra R S)

/-- If `A` and `B` are subalgebras of `S / R`,
then `A` and `B` are linearly disjoint, if they are linearly disjoint as submodules of `S`. -/
@[mk_iff]
protected structure LinearDisjoint : Prop where
  submodule : (toSubmodule A).LinearDisjoint (toSubmodule B)

variable {A B}

@[nontriviality]
theorem LinearDisjoint.of_subsingleton [Subsingleton R] : A.LinearDisjoint B :=
  ⟨.of_subsingleton⟩

/-- Linearly disjoint is symmetric if elements in the module commute. -/
theorem LinearDisjoint.symm_of_commute (H : A.LinearDisjoint B)
    (hc : ∀ (a : A) (b : B), Commute a.1 b.1) : B.LinearDisjoint A :=
  ⟨H.1.symm_of_commute hc⟩

/-- Linearly disjoint is symmetric if elements in the module commute. -/
theorem linearDisjoint_symm_of_commute
    (hc : ∀ (a : A) (b : B), Commute a.1 b.1) : A.LinearDisjoint B ↔ B.LinearDisjoint A :=
  ⟨fun H ↦ H.symm_of_commute hc, fun H ↦ H.symm_of_commute fun _ _ ↦ (hc _ _).symm⟩

namespace LinearDisjoint

variable (A B)

theorem of_bot_left : (⊥ : Subalgebra R S).LinearDisjoint B := ⟨.of_one_left _⟩

theorem of_bot_right : A.LinearDisjoint ⊥ := ⟨.of_one_right _⟩

end LinearDisjoint

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring S] [Algebra R S]

variable {A B : Subalgebra R S}

/-- Linearly disjoint is symmetric in a commutative ring. -/
theorem LinearDisjoint.symm (H : A.LinearDisjoint B) : B.LinearDisjoint A :=
  H.symm_of_commute fun _ _ ↦ mul_comm _ _

/-- Linearly disjoint is symmetric in a commutative ring. -/
theorem linearDisjoint_symm : A.LinearDisjoint B ↔ B.LinearDisjoint A :=
  ⟨LinearDisjoint.symm, LinearDisjoint.symm⟩

namespace LinearDisjoint

variable (H : A.LinearDisjoint B)

/-- If `A` and `B` are subalgebras in a commutative algebra `S` over `R`, and if they are
linearly disjoint, then there is the natural isomorphism
`A ⊗[R] B ≃ₐ[R] A ⊔ B` induced by multiplication in `S`. -/
protected def mulMap :=
  (AlgEquiv.ofInjective (A.mulMap B) H.1.1).trans (equivOfEq _ _ (mulMap_range A B))

@[simp]
theorem val_mulMap_tmul (a : A) (b : B) : (H.mulMap (a ⊗ₜ[R] b) : S) = a.1 * b.1 := rfl

theorem sup_free_of_free [Module.Free R A] [Module.Free R B] : Module.Free R ↥(A ⊔ B) :=
  Module.Free.of_equiv H.mulMap.toLinearEquiv

end LinearDisjoint

end CommSemiring

section Ring

namespace LinearDisjoint

variable [CommRing R] [Ring S] [Algebra R S]

variable (A B : Subalgebra R S)

section TODO

variable {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [Algebra R A]

-- TODO: remove once #12846 is merged
/-- The ordered set of subalgebras of the opposite algebra is isomorphic to the
ordered set of subalgebras. -/
def _root_.Subalgebra.equivOpposite : Subalgebra R Aᵐᵒᵖ ≃o Subalgebra R A where
  toFun S := { MulOpposite.unop (Submodule.equivOpposite (toSubmodule S)) with
    mul_mem' := fun ha hb ↦ S.mul_mem hb ha
    algebraMap_mem' := S.algebraMap_mem }
  invFun S := { Submodule.equivOpposite.symm (MulOpposite.op (toSubmodule S)) with
    mul_mem' := fun ha hb ↦ S.mul_mem hb ha
    algebraMap_mem' := S.algebraMap_mem }
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' {_} {_} :=
    Submodule.comap_le_comap_iff_of_surjective (MulOpposite.opLinearEquiv R).surjective _ _

-- TODO: remove once #12846 is merged
/-- There is a natural linear isomorphism from a subalgebra `S` to
its `Subalgebra.equivOpposite`. -/
def _root_.Subalgebra.opLinearEquiv (S : Subalgebra R A) : S ≃ₗ[R] equivOpposite.symm S :=
  ((MulOpposite.opLinearEquiv R).symm.ofSubmodule' (toSubmodule S)).symm

-- TODO: remove once #12846 is merged
/-- There is a natural algebra isomorphism from a subalgebra `S` to
the opposite of its `Subalgebra.equivOpposite`. -/
def _root_.Subalgebra.opAlgEquiv (S : Subalgebra R A) : S ≃ₐ[R] (equivOpposite.symm S)ᵐᵒᵖ where
  __ := opLinearEquiv S ≪≫ₗ MulOpposite.opLinearEquiv _
  map_mul' _ _ := rfl
  commutes' _ := rfl

-- TODO: remove once #12846 is merged
/-- There is a natural algebra isomorphism from the opposite of a subalgebra `S` to
the its `Subalgebra.equivOpposite`. -/
def _root_.Subalgebra.opAlgEquiv' (S : Subalgebra R A) : Sᵐᵒᵖ ≃ₐ[R] equivOpposite.symm S where
  __ := (MulOpposite.opLinearEquiv _).symm ≪≫ₗ opLinearEquiv S
  map_mul' _ _ := rfl
  commutes' _ := rfl

end TODO

lemma mulLeftMap_ker_eq_bot_iff_linearIndependent_op {ι : Type*} (a : ι → A) :
    LinearMap.ker (Submodule.mulLeftMap (M := toSubmodule A) (toSubmodule B) a) = ⊥ ↔
    LinearIndependent (equivOpposite.symm B) (MulOpposite.op ∘ A.val ∘ a) := by
  -- need this instance otherwise `LinearMap.ker_eq_bot` does not work
  letI : AddCommGroup (ι →₀ toSubmodule B) := Finsupp.instAddCommGroup
  letI : AddCommGroup (ι →₀ equivOpposite.symm B) := Finsupp.instAddCommGroup
  simp_rw [LinearIndependent, LinearMap.ker_eq_bot]
  let i : (ι →₀ B) →ₗ[R] S := Submodule.mulLeftMap (M := toSubmodule A) (toSubmodule B) a
  let j : (ι →₀ B) →ₗ[R] S := (MulOpposite.opLinearEquiv _).symm.toLinearMap ∘ₗ
    (Finsupp.total ι Sᵐᵒᵖ (equivOpposite.symm B) (MulOpposite.op ∘ A.val ∘ a)).restrictScalars R ∘ₗ
    (Finsupp.mapRange.linearEquiv (opLinearEquiv B)).toLinearMap
  suffices i = j by
    change Function.Injective i ↔ _
    simp_rw [this, j, LinearMap.coe_comp,
      LinearEquiv.coe_coe, EquivLike.comp_injective, EquivLike.injective_comp]
    rfl
  ext
  simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, coe_val,
    Finsupp.mapRange.linearEquiv_toLinearMap, LinearEquiv.coe_coe,
    MulOpposite.coe_opLinearEquiv_symm, LinearMap.coe_restrictScalars,
    Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Finsupp.total_single,
    MulOpposite.unop_smul, MulOpposite.unop_op, i, j]
  exact Submodule.mulLeftMap_apply_single _ _ _

variable {A B} in
theorem map_linearIndependent_left_op_of_flat (H : A.LinearDisjoint B) [Module.Flat R B]
    {ι : Type*} {a : ι → A} (ha : LinearIndependent R a) :
    LinearIndependent (equivOpposite.symm B) (MulOpposite.op ∘ A.val ∘ a) := by
  haveI : Module.Flat R (toSubmodule B) := ‹_›
  have h := H.1.map_linearIndependent_left_of_flat ha
  rwa [mulLeftMap_ker_eq_bot_iff_linearIndependent_op] at h

theorem of_map_linearIndependent_left_op {ι : Type*} (a : Basis ι R A)
    (H : LinearIndependent (equivOpposite.symm B) (MulOpposite.op ∘ A.val ∘ a)) :
    A.LinearDisjoint B := by
  rw [← mulLeftMap_ker_eq_bot_iff_linearIndependent_op] at H
  exact ⟨.of_map_linearIndependent_left _ _ a H⟩

lemma mulRightMap_ker_eq_bot_iff_linearIndependent {ι : Type*} (b : ι → B) :
    LinearMap.ker (Submodule.mulRightMap (toSubmodule A) (N := toSubmodule B) b) = ⊥ ↔
    LinearIndependent A (B.val ∘ b) := by
  -- need this instance otherwise `LinearMap.ker_eq_bot` does not work
  letI : AddCommGroup (ι →₀ toSubmodule A) := Finsupp.instAddCommGroup
  simp_rw [LinearIndependent, LinearMap.ker_eq_bot]
  let i : (ι →₀ A) →ₗ[R] S := Submodule.mulRightMap (toSubmodule A) (N := toSubmodule B) b
  let j : (ι →₀ A) →ₗ[R] S := (Finsupp.total ι S A (B.val ∘ b)).restrictScalars R
  suffices i = j by change Function.Injective i ↔ Function.Injective j; rw [this]
  ext
  simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, coe_val,
    LinearMap.coe_restrictScalars, Finsupp.total_single, i, j]
  exact Submodule.mulRightMap_apply_single _ _ _

variable {A B} in
theorem map_linearIndependent_right_of_flat (H : A.LinearDisjoint B) [Module.Flat R A]
    {ι : Type*} {b : ι → B} (hb : LinearIndependent R b) :
    LinearIndependent A (B.val ∘ b) := by
  haveI : Module.Flat R (toSubmodule A) := ‹_›
  have h := H.1.map_linearIndependent_right_of_flat hb
  rwa [mulRightMap_ker_eq_bot_iff_linearIndependent] at h

theorem of_map_linearIndependent_right {ι : Type*} (b : Basis ι R B)
    (H : LinearIndependent A (B.val ∘ b)) : A.LinearDisjoint B := by
  rw [← mulRightMap_ker_eq_bot_iff_linearIndependent] at H
  exact ⟨.of_map_linearIndependent_right _ _ b H⟩

variable {A B} in
theorem map_linearIndependent_left_of_flat_of_commute (H : A.LinearDisjoint B) [Module.Flat R B]
    {ι : Type*} {a : ι → A} (ha : LinearIndependent R a)
    (hc : ∀ (a : A) (b : B), Commute a.1 b.1) : LinearIndependent B (A.val ∘ a) :=
  (H.symm_of_commute hc).map_linearIndependent_right_of_flat ha

theorem of_map_linearIndependent_left_of_commute {ι : Type*} (a : Basis ι R A)
    (H : LinearIndependent B (A.val ∘ a)) (hc : ∀ (a : A) (b : B), Commute a.1 b.1) :
    A.LinearDisjoint B :=
  (of_map_linearIndependent_right B A a H).symm_of_commute fun _ _ ↦ (hc _ _).symm

variable {A B} in
theorem map_linearIndependent_mul_of_flat_left (H : A.LinearDisjoint B) [Module.Flat R A]
    {κ ι : Type*} {a : κ → A} {b : ι → B} (ha : LinearIndependent R a)
    (hb : LinearIndependent R b) : LinearIndependent R fun (i : κ × ι) ↦ (a i.1).1 * (b i.2).1 := by
  haveI : Module.Flat R (toSubmodule A) := ‹_›
  exact H.1.map_linearIndependent_mul_of_flat_left ha hb

variable {A B} in
theorem map_linearIndependent_mul_of_flat_right (H : A.LinearDisjoint B) [Module.Flat R B]
    {κ ι : Type*} {a : κ → A} {b : ι → B} (ha : LinearIndependent R a)
    (hb : LinearIndependent R b) : LinearIndependent R fun (i : κ × ι) ↦ (a i.1).1 * (b i.2).1 := by
  haveI : Module.Flat R (toSubmodule B) := ‹_›
  exact H.1.map_linearIndependent_mul_of_flat_right ha hb

variable {A B} in
theorem map_linearIndependent_mul_of_flat (H : A.LinearDisjoint B)
    (hf : Module.Flat R A ∨ Module.Flat R B)
    {κ ι : Type*} {a : κ → A} {b : ι → B} (ha : LinearIndependent R a)
    (hb : LinearIndependent R b) : LinearIndependent R fun (i : κ × ι) ↦ (a i.1).1 * (b i.2).1 :=
  H.1.map_linearIndependent_mul_of_flat hf ha hb

theorem of_map_linearIndependent_mul {κ ι : Type*} (a : Basis κ R A) (b : Basis ι R B)
    (H : LinearIndependent R fun (i : κ × ι) ↦ (a i.1).1 * (b i.2).1) : A.LinearDisjoint B :=
  ⟨.of_map_linearIndependent_mul _ _ a b H⟩

variable {A B}

variable (H : A.LinearDisjoint B)

theorem of_le_left_of_flat {A' : Subalgebra R S}
    (h : A' ≤ A) [Module.Flat R B] : A'.LinearDisjoint B := by
  haveI : Module.Flat R (toSubmodule B) := ‹_›
  exact ⟨H.1.of_le_left_of_flat h⟩

theorem of_le_right_of_flat {B' : Subalgebra R S}
    (h : B' ≤ B) [Module.Flat R A] : A.LinearDisjoint B' := by
  haveI : Module.Flat R (toSubmodule A) := ‹_›
  exact ⟨H.1.of_le_right_of_flat h⟩

theorem of_le_of_flat_right {A' B' : Subalgebra R S}
    (ha : A' ≤ A) (hb : B' ≤ B) [Module.Flat R B] [Module.Flat R A'] :
    A'.LinearDisjoint B' := (H.of_le_left_of_flat ha).of_le_right_of_flat hb

theorem of_le_of_flat_left {A' B' : Subalgebra R S}
    (ha : A' ≤ A) (hb : B' ≤ B) [Module.Flat R A] [Module.Flat R B'] :
    A'.LinearDisjoint B' := (H.of_le_right_of_flat hb).of_le_left_of_flat ha

theorem rank_inf_eq_one_of_commute_of_flat_of_inj (hf : Module.Flat R A ∨ Module.Flat R B)
    (hc : ∀ (a b : ↥(A ⊓ B)), Commute a.1 b.1)
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R ↥(A ⊓ B) = 1 := by
  nontriviality R
  refine le_antisymm (H.1.rank_inf_le_one_of_commute_of_flat hf hc) ?_
  have : 1 ≤ Module.rank R (⊥ : Subalgebra R S) := by
    let s : Set (⊥ : Subalgebra R S) := {1}
    have : LinearIndependent R fun x : s ↦ x.1 := by
      rw [LinearIndependent, LinearMap.ker_eq_bot]
      have : (Finsupp.total s (⊥ : Subalgebra R S) R fun x ↦ x.1) =
          Algebra.linearMap R (⊥ : Subalgebra R S) ∘ₗ
          (Finsupp.LinearEquiv.finsuppUnique R R s).toLinearMap := by
        ext x
        simp [show x = ⟨1, Set.mem_singleton 1⟩ from Subsingleton.elim _ _]
      simp_rw [this, LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.injective_comp]
      intro x y hxy
      exact hinj congr(val _ $(hxy))
    simpa only [Cardinal.mk_fintype, Fintype.card_ofSubsingleton,
      Nat.cast_one, s] using this.cardinal_le_rank'
  exact this.trans <| rank_le_of_submodule (toSubmodule (⊥ : Subalgebra R S)) (toSubmodule (A ⊓ B))
    (bot_le : (⊥ : Subalgebra R S) ≤ A ⊓ B)

theorem rank_inf_eq_one_of_commute_of_flat_left_of_inj [Module.Flat R A]
    (hc : ∀ (a b : ↥(A ⊓ B)), Commute a.1 b.1)
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R ↥(A ⊓ B) = 1 :=
  H.rank_inf_eq_one_of_commute_of_flat_of_inj (Or.inl ‹_›) hc hinj

theorem rank_inf_eq_one_of_commute_of_flat_right_of_inj [Module.Flat R B]
    (hc : ∀ (a b : ↥(A ⊓ B)), Commute a.1 b.1)
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R ↥(A ⊓ B) = 1 :=
  H.rank_inf_eq_one_of_commute_of_flat_of_inj (Or.inr ‹_›) hc hinj

theorem rank_eq_one_of_commute_of_flat_of_self_of_inj (H : A.LinearDisjoint A) [Module.Flat R A]
    (hc : ∀ (a b : A), Commute a.1 b.1)
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R A = 1 := by
  rw [← inf_of_le_left (le_refl A)] at hc ⊢
  exact H.rank_inf_eq_one_of_commute_of_flat_left_of_inj hc hinj

end LinearDisjoint

end Ring

section CommRing

namespace LinearDisjoint

variable [CommRing R] [CommRing S] [Algebra R S]

variable (A B : Subalgebra R S)

variable {A B} in
theorem map_linearIndependent_left_of_flat (H : A.LinearDisjoint B) [Module.Flat R B]
    {ι : Type*} {a : ι → A} (ha : LinearIndependent R a) : LinearIndependent B (A.val ∘ a) :=
  H.map_linearIndependent_left_of_flat_of_commute ha fun _ _ ↦ mul_comm _ _

theorem of_map_linearIndependent_left {ι : Type*} (a : Basis ι R A)
    (H : LinearIndependent B (A.val ∘ a)) : A.LinearDisjoint B :=
  of_map_linearIndependent_left_of_commute A B a H fun _ _ ↦ mul_comm _ _

variable {A B}

variable (H : A.LinearDisjoint B)

theorem rank_inf_eq_one_of_flat_of_inj (hf : Module.Flat R A ∨ Module.Flat R B)
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R ↥(A ⊓ B) = 1 :=
  H.rank_inf_eq_one_of_commute_of_flat_of_inj hf (fun _ _ ↦ mul_comm _ _) hinj

theorem rank_inf_eq_one_of_flat_left_of_inj [Module.Flat R A]
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R ↥(A ⊓ B) = 1 :=
  H.rank_inf_eq_one_of_commute_of_flat_left_of_inj (fun _ _ ↦ mul_comm _ _) hinj

theorem rank_inf_eq_one_of_flat_right_of_inj [Module.Flat R B]
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R ↥(A ⊓ B) = 1 :=
  H.rank_inf_eq_one_of_commute_of_flat_right_of_inj (fun _ _ ↦ mul_comm _ _) hinj

theorem rank_eq_one_of_flat_of_self_of_inj (H : A.LinearDisjoint A) [Module.Flat R A]
    (hinj : Function.Injective (algebraMap R S)) : Module.rank R A = 1 :=
  H.rank_eq_one_of_commute_of_flat_of_self_of_inj (fun _ _ ↦ mul_comm _ _) hinj

theorem rank_sup_of_free [Module.Free R A] [Module.Free R B] :
    Module.rank R ↥(A ⊔ B) = Module.rank R A * Module.rank R B := by
  nontriviality R
  rw [← rank_tensorProduct', H.mulMap.toLinearEquiv.rank_eq]

theorem finrank_sup_of_free [Module.Free R A] [Module.Free R B] :
    finrank R ↥(A ⊔ B) = finrank R A * finrank R B := by
  simpa only [map_mul] using congr(Cardinal.toNat $(H.rank_sup_of_free))

/-- TODO: remove once #12076 is merged -/
axiom _root_.Module.Finite.injective_of_surjective_of_injective
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] (i f : N →ₗ[R] M)
    (hi : Function.Injective i) (hf : Function.Surjective f) : Function.Injective f

theorem of_finrank_sup_of_free [Module.Free R A] [Module.Free R B]
    [Module.Finite R A] [Module.Finite R B]
    (H : finrank R ↥(A ⊔ B) = finrank R A * finrank R B) : A.LinearDisjoint B := by
  nontriviality R
  rw [← finrank_tensorProduct] at H
  obtain ⟨j, hj⟩ := exists_linearIndependent_of_le_finrank H.ge
  rw [LinearIndependent, LinearMap.ker_eq_bot] at hj
  let j' := Finsupp.total _ ↥(A ⊔ B) R j ∘ₗ
    (LinearEquiv.ofFinrankEq (A ⊗[R] B) _ (by simp)).toLinearMap
  replace hj : Function.Injective j' := by simpa [j']
  have hf : Function.Surjective (mulMap' A B).toLinearMap := mulMap'_surjective A B
  haveI := Subalgebra.finite_sup A B
  rw [linearDisjoint_iff, Submodule.linearDisjoint_iff]
  exact Subtype.val_injective.comp (Module.Finite.injective_of_surjective_of_injective j' _ hj hf)

/-- If `A` and `B` are linearly disjoint, if `A` is free and `B` is flat,
then `[B[A] : B] = [A : R]`. See also `Subalgebra.adjoin_rank_le`. -/
theorem adjoin_rank_eq_rank_left [Module.Free R A] [Module.Flat R B]
    [Nontrivial R] [Nontrivial S] :
    Module.rank B (Algebra.adjoin B (A : Set S)) = Module.rank R A := by
  rw [← rank_toSubmodule, Module.Free.rank_eq_card_chooseBasisIndex R A,
    A.adjoin_eq_span_basis B (Module.Free.chooseBasis R A)]
  change Module.rank B (Submodule.span B (Set.range (A.val ∘ Module.Free.chooseBasis R A))) = _
  have := H.map_linearIndependent_left_of_flat (Module.Free.chooseBasis R A).linearIndependent
  rw [rank_span this, Cardinal.mk_range_eq _ this.injective]

/-- If `A` and `B` are linearly disjoint, if `B` is free and `A` is flat,
then `[A[B] : A] = [B : R]`. See also `Subalgebra.adjoin_rank_le`. -/
theorem adjoin_rank_eq_rank_right [Module.Free R B] [Module.Flat R A]
    [Nontrivial R] [Nontrivial S] :
    Module.rank A (Algebra.adjoin A (B : Set S)) = Module.rank R B :=
  H.symm.adjoin_rank_eq_rank_left

-- TODO: move to suitable place
variable (A B) in
theorem _root_.Subalgebra.rank_sup_eq_rank_left_mul_rank_of_free
    [Module.Free R A] [Module.Free A (Algebra.adjoin A (B : Set S))] :
    Module.rank R ↥(A ⊔ B) = Module.rank R A * Module.rank A (Algebra.adjoin A (B : Set S)) := by
  rcases subsingleton_or_nontrivial R with _ | _
  · haveI := Module.subsingleton R S; simp
  nontriviality S using rank_subsingleton'
  letI : Algebra A (Algebra.adjoin A (B : Set S)) := Subalgebra.algebra _
  letI : SMul A (Algebra.adjoin A (B : Set S)) := Algebra.toSMul
  haveI : IsScalarTower R A (Algebra.adjoin A (B : Set S)) :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  rw [rank_mul_rank R A (Algebra.adjoin A (B : Set S))]
  change _ = Module.rank R ((Algebra.adjoin A (B : Set S)).restrictScalars R)
  rw [Algebra.restrictScalars_adjoin]; rfl

-- TODO: move to suitable place
variable (A B) in
theorem _root_.Subalgebra.rank_sup_eq_rank_right_mul_rank_of_free
    [Module.Free R B] [Module.Free B (Algebra.adjoin B (A : Set S))] :
    Module.rank R ↥(A ⊔ B) = Module.rank R B * Module.rank B (Algebra.adjoin B (A : Set S)) := by
  rw [sup_comm, rank_sup_eq_rank_left_mul_rank_of_free]

-- TODO: move to suitable place
variable (A B) in
theorem _root_.Subalgebra.finrank_sup_eq_finrank_left_mul_finrank_of_free
    [Module.Free R A] [Module.Free A (Algebra.adjoin A (B : Set S))] :
    finrank R ↥(A ⊔ B) = finrank R A * finrank A (Algebra.adjoin A (B : Set S)) := by
  simpa only [map_mul] using congr(Cardinal.toNat $(rank_sup_eq_rank_left_mul_rank_of_free A B))

-- TODO: move to suitable place
variable (A B) in
theorem _root_.Subalgebra.finrank_sup_eq_finrank_right_mul_finrank_of_free
    [Module.Free R B] [Module.Free B (Algebra.adjoin B (A : Set S))] :
    finrank R ↥(A ⊔ B) = finrank R B * finrank B (Algebra.adjoin B (A : Set S)) := by
  rw [sup_comm, finrank_sup_eq_finrank_left_mul_finrank_of_free]

-- TODO: move to suitable place
variable (A B) in
theorem _root_.Subalgebra.finrank_left_dvd_finrank_sup_of_free
    [Module.Free R A] [Module.Free A (Algebra.adjoin A (B : Set S))] :
    finrank R A ∣ finrank R ↥(A ⊔ B) := ⟨_, finrank_sup_eq_finrank_left_mul_finrank_of_free A B⟩

-- TODO: move to suitable place
variable (A B) in
theorem _root_.Subalgebra.finrank_right_dvd_finrank_sup_of_free
    [Module.Free R B] [Module.Free B (Algebra.adjoin B (A : Set S))] :
    finrank R B ∣ finrank R ↥(A ⊔ B) := ⟨_, finrank_sup_eq_finrank_right_mul_finrank_of_free A B⟩

-- TODO: move to suitable place
theorem _root_.bijective_algebraMap_of_linearEquiv
    {F E : Type*} [CommRing F] [Ring E] [Algebra F E]
    (b : F ≃ₗ[F] E) : Function.Bijective (algebraMap F E) := by
  have h : b.symm (b 1 * b (b.symm 1)) = b.symm 1 * b.symm (b 1 * b 1) := by
    let j := b.symm.toLinearMap ∘ₗ .mulLeft F (b 1) ∘ₗ b.toLinearMap
    change j (b.symm 1) = (b.symm 1) • j 1
    rw [← map_smul, smul_eq_mul, mul_one]
  replace h : b 1 = (algebraMap F E) (b.symm (b 1 * b 1)) := by
    apply_fun b at h
    rwa [b.apply_symm_apply, b.apply_symm_apply, mul_one, mul_comm (b.symm 1),
      ← smul_eq_mul, map_smul, b.apply_symm_apply, Algebra.smul_def, mul_one] at h
  refine Function.bijective_iff_has_inverse.2 ⟨fun y ↦ b.symm y * b.symm (b 1 * b 1),
    fun x ↦ b.injective ?_, fun y ↦ ?_⟩
  · dsimp only; rw [mul_comm, ← smul_eq_mul, map_smul, Algebra.smul_def, ← h, b.apply_symm_apply,
      ← Algebra.commutes x (b 1), ← Algebra.smul_def, ← map_smul, smul_eq_mul, mul_one]
  · dsimp only; rw [map_mul, ← h, ← Algebra.smul_def, ← map_smul, smul_eq_mul, mul_one,
      b.apply_symm_apply]

-- TODO: move to suitable place
theorem _root_.Subalgebra.eq_bot_of_finrank_one_of_free
    {F E : Type*} [CommRing F] [StrongRankCondition F] [Ring E] [Algebra F E]
    {S : Subalgebra F E} (h : finrank F S = 1) [Module.Free F S] : S = ⊥ := by
  refine bot_unique fun x hx ↦ Algebra.mem_bot.2 ?_
  obtain ⟨y, hy⟩ := (bijective_algebraMap_of_linearEquiv ((basisUnique Unit h).repr ≪≫ₗ
    Finsupp.LinearEquiv.finsuppUnique _ _ _).symm).surjective ⟨x, hx⟩
  exact ⟨y, congr(Subtype.val $(hy))⟩

theorem of_finrank_coprime_of_free [Module.Free R A] [Module.Free R B]
    [Module.Free A (Algebra.adjoin A (B : Set S))] [Module.Free B (Algebra.adjoin B (A : Set S))]
    (H : (finrank R A).Coprime (finrank R B)) : A.LinearDisjoint B := by
  nontriviality R
  by_cases h1 : finrank R A = 0
  · rw [h1, Nat.coprime_zero_left] at H
    rw [eq_bot_of_finrank_one_of_free H]
    exact of_bot_right _
  by_cases h2 : finrank R B = 0
  · rw [h2, Nat.coprime_zero_right] at H
    rw [eq_bot_of_finrank_one_of_free H]
    exact of_bot_left _
  haveI := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h1)
  haveI := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h2)
  haveI := finite_sup A B
  have : finrank R A ≤ finrank R ↥(A ⊔ B) := LinearMap.finrank_le_finrank_of_injective <|
    Submodule.inclusion_injective (show toSubmodule A ≤ toSubmodule (A ⊔ B) by simp)
  exact of_finrank_sup_of_free <| (finrank_sup_le_of_free A B).antisymm <|
    Nat.le_of_dvd (lt_of_lt_of_le (Nat.pos_of_ne_zero h1) this) <| H.mul_dvd_of_dvd_of_dvd
      (finrank_left_dvd_finrank_sup_of_free A B) (finrank_right_dvd_finrank_sup_of_free A B)

variable (A B)

theorem of_linearDisjoint_finite_left (hi : Algebra.IsIntegral R A)
    (H : ∀ A' : Subalgebra R S, A' ≤ A → [Module.Finite R A'] → A'.LinearDisjoint B) :
    A.LinearDisjoint B := by
  rw [linearDisjoint_iff, Submodule.linearDisjoint_iff]
  intro x y hxy
  obtain ⟨M', hM, hf, h⟩ :=
    TensorProduct.exists_finite_submodule_left_of_finite' {x, y} (Set.toFinite _)
  obtain ⟨s, hs⟩ := Module.Finite.iff_fg.1 hf
  have hs' : (s : Set S) ⊆ A := by rwa [← hs, Submodule.span_le] at hM
  let A' := Algebra.adjoin R (s : Set S)
  have hf' : Submodule.FG (toSubmodule A') := fg_adjoin_of_finite s.finite_toSet fun x hx ↦
    (isIntegral_algHom_iff A.val Subtype.val_injective).2 (hi ⟨x, hs' hx⟩)
  replace hf' : Module.Finite R A' := Module.Finite.iff_fg.2 hf'
  have hA : toSubmodule A' ≤ toSubmodule A := Algebra.adjoin_le_iff.2 hs'
  replace h : {x, y} ⊆ (LinearMap.range (LinearMap.rTensor (toSubmodule B)
      (Submodule.inclusion hA)) : Set _) := fun _ hx ↦ by
    have : Submodule.inclusion hM = Submodule.inclusion hA ∘ₗ Submodule.inclusion
      (show M' ≤ toSubmodule A' by
        rw [← hs, Submodule.span_le]; exact Algebra.adjoin_le_iff.1 (le_refl _)) := rfl
    rw [this, LinearMap.rTensor_comp] at h
    exact LinearMap.range_comp_le_range _ _ (h hx)
  obtain ⟨x', hx'⟩ := h (show x ∈ {x, y} by simp)
  obtain ⟨y', hy'⟩ := h (show y ∈ {x, y} by simp)
  rw [← hx', ← hy']; congr
  exact (H A' hA).1.1 (by simp [← Submodule.mulMap_comp_rTensor _ _ _ hA, hx', hy', hxy])

theorem of_linearDisjoint_finite_right (hi : Algebra.IsIntegral R B)
    (H : ∀ B' : Subalgebra R S, B' ≤ B → [Module.Finite R B'] → A.LinearDisjoint B') :
    A.LinearDisjoint B :=
  (of_linearDisjoint_finite_left B A hi fun B' hB' _ ↦ (H B' hB').symm).symm

variable {A B}

theorem of_linearDisjoint_finite
    (hA : Algebra.IsIntegral R A) (hB : Algebra.IsIntegral R B)
    (H : ∀ (A' B' : Subalgebra R S), A' ≤ A → B' ≤ B →
      [Module.Finite R A'] → [Module.Finite R B'] → A'.LinearDisjoint B') :
    A.LinearDisjoint B :=
  of_linearDisjoint_finite_left A B hA fun _ hA' _ ↦
    of_linearDisjoint_finite_right _ B hB fun _ hB' _ ↦ H _ _ hA' hB'

end LinearDisjoint

end CommRing

section FieldAndRing

namespace LinearDisjoint

variable [Field R] [Ring S] [Algebra R S]

variable {A B : Subalgebra R S} (H : A.LinearDisjoint B)

theorem inf_eq_bot_of_commute (hc : ∀ (a b : ↥(A ⊓ B)), Commute a.1 b.1) : A ⊓ B = ⊥ :=
  eq_bot_of_rank_le_one (H.1.rank_inf_le_one_of_commute_of_flat_left hc)

theorem eq_bot_of_commute_of_self (H : A.LinearDisjoint A)
    (hc : ∀ (a b : A), Commute a.1 b.1) : A = ⊥ := by
  rw [← inf_of_le_left (le_refl A)] at hc ⊢
  exact H.inf_eq_bot_of_commute hc

end LinearDisjoint

end FieldAndRing

section FieldAndCommRing

namespace LinearDisjoint

variable [Field R] [CommRing S] [Nontrivial S] [Algebra R S]

variable {A B : Subalgebra R S} (H : A.LinearDisjoint B)

theorem inf_eq_bot : A ⊓ B = ⊥ := H.inf_eq_bot_of_commute fun _ _ ↦ mul_comm _ _

theorem eq_bot_of_self (H : A.LinearDisjoint A) : A = ⊥ :=
  H.eq_bot_of_commute_of_self fun _ _ ↦ mul_comm _ _

end LinearDisjoint

end FieldAndCommRing

end Subalgebra
