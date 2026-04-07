/-
Copyright (c) 2026 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module
public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Augmentation ideals

* `Ideal.IsAugmentation` :  An ideal `I` of an `A`-algebra `S` is an augmentation ideal
  if it is submodule a complement of `⊥ : Subalgebra A S`.

* `Ideal.isAugmentation_subalgebra_iff` : If `S` is a subalgebra of an `R`-algebra `A`,
  then an ideal `I`of `A` is an augmentation ideal for the `R`-algebra structure if and only if
  it is an augmentation ideal for the `S`-algebra structure.

-/


/-
section DistribLattice

variable {α : Type*} [DistribLattice α] [BoundedOrder α] {a b c : α}

theorem DistribLattice.isCompl_assoc_of_disjoint (hab : Disjoint a b) (h : IsCompl (a ⊔ b) c) :
    IsCompl a (b ⊔ c) := by
  rcases h with ⟨hd, hc⟩
  apply IsCompl.mk
  · intro x hx hx'
    refine hd (le_trans hx le_sup_left) ?_
    rw [← left_eq_inf, inf_sup_left] at hx'
    rw [hx']
    simp only [sup_le_iff, inf_le_right, and_true]
    convert bot_le
    rw [eq_bot_iff]
    apply hab (inf_le_of_left_le hx) inf_le_right
  · simp only [Codisjoint, sup_le_iff, and_imp]
    intro x hxa hxb hxc
    exact hc (by simp only [sup_le_iff, hxa, hxb, and_self]) hxc

-- The lattice of submodules is modular but is not distributive in general. However :

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem Submodule.isCompl_assoc_of_disjoint {a b c : Submodule R M}
    (hab : Disjoint a b) (h : IsCompl (a ⊔ b) c) : IsCompl a (b ⊔ c) := by
  rcases h with ⟨hd, hc⟩
  apply IsCompl.mk
  · rw [disjoint_def]
    intro x hxa hxbc
    obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.mp hxbc
    suffices z = 0 by
      apply disjoint_def.mp hab _ hxa
      rw [this, add_zero]
      exact hy
    apply disjoint_def.mp hd _ _ hz
    rw [mem_sup]
    exact ⟨y + z, hxa, -y , neg_mem hy, by simp only [add_neg_cancel_comm]⟩
  · simp only [Codisjoint, sup_le_iff, and_imp]
    intro x hxa hxb hxc
    exact hc (by simp only [sup_le_iff, hxa, hxb, and_self]) hxc

end DistribLattice
-/

/-
section

open AlgHom RingHom Submodule Ideal.Quotient

open TensorProduct LinearMap

variable (R : Type*) [CommRing R] {A : Type*} [CommRing A] [Algebra R A] (J : Ideal A)
  {M : Type*} [AddCommGroup M] [Module A M] {M₁ M₂ : Submodule A M}

namespace LinearMap

variable (hM : IsCompl M₁ M₂)(Q : Type*) [AddCommGroup Q] [Module A Q]

theorem ker_lTensor_of_linearProjOfIsCompl :
    ker (lTensor Q (Submodule.linearProjOfIsCompl _ _ hM)) = range (lTensor Q M₂.subtype) := by
  rw [← exact_iff]
  apply lTensor_exact
  simp only [exact_iff, range_subtype, linearProjOfIsCompl_ker]
  simp only [← range_eq_top, linearProjOfIsCompl_range]

theorem ker_rTensor_of_linearProjOfIsCompl :
    ker (rTensor Q (Submodule.linearProjOfIsCompl _ _ hM)) = range (rTensor Q M₂.subtype) := by
  rw [← exact_iff]
  apply rTensor_exact
  simp only [exact_iff, range_subtype, linearProjOfIsCompl_ker]
  simp [← range_eq_top, linearProjOfIsCompl_range]

theorem ker_baseChange_of_linearProjOfIsCompl (R : Type*) [CommRing R] [Algebra A R] :
    ker (baseChange R (Submodule.linearProjOfIsCompl _ _ hM)) =
      range (baseChange R M₂.subtype) := by
  simpa [← exact_iff] using ker_lTensor_of_linearProjOfIsCompl hM R

theorem isCompl_lTensor (hM : IsCompl M₁ M₂) :
    IsCompl (range (lTensor Q M₁.subtype)) (range (lTensor Q M₂.subtype)) := by
  have hq :
    M₁.subtype.comp (Submodule.linearProjOfIsCompl _ _ hM)
      + M₂.subtype.comp (Submodule.linearProjOfIsCompl _ _ hM.symm) = id := by
    ext x
    simp only [add_apply, coe_comp, coe_subtype, Function.comp_apply, id_coe, id_eq]
    erw [Submodule.IsCompl.projection_add_projection_eq_self]
  apply IsCompl.mk
  · rw [disjoint_def]
    intro x h h'
    rw [← id_apply x (R := A), ← lTensor_id, ← hq]
    simp only [lTensor_add, lTensor_comp,
      LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply]
    rw [← ker_lTensor_of_linearProjOfIsCompl hM Q] at h'
    rw [← ker_lTensor_of_linearProjOfIsCompl hM.symm Q] at h
    rw [mem_ker] at h h'
    simp only [h', _root_.map_zero, h, add_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    rw [← lTensor_id_apply Q _ x, ← hq]
    simp only [lTensor_add, lTensor_comp, add_apply, coe_comp, Function.comp_apply]
    exact Submodule.add_mem _ (mem_sup_left (LinearMap.mem_range_self _ _))
      (mem_sup_right (LinearMap.mem_range_self _ _))

end LinearMap

/-
theorem Submodule.disjoint_map (hM : Disjoint M₁ M₂) {N : Type*} [AddCommGroup N] [Module A N]
    {f : M →ₗ[A] N} (hf : Function.Injective f) : Disjoint (M₁.map f) (M₂.map f) := by
  rw [Submodule.disjoint_def] at hM ⊢
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hy'⟩
  rw [hf hy'] at hy
  rw [hM x hx hy, LinearMap.map_zero]

theorem Submodule.codisjoint_map (hM : Codisjoint M₁ M₂) {N : Type*} [AddCommGroup N] [Module A N]
    {f : M →ₗ[A] N} (hf : Function.Surjective f) : Codisjoint (M₁.map f) (M₂.map f) := by
  rw [codisjoint_iff, eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := hf y
  obtain ⟨y, z, hy, hz, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hM x
  rw [LinearMap.map_add]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (mem_map_of_mem hy))
    (Submodule.mem_sup_right (mem_map_of_mem hz))
-/

theorem Submodule.isCompl_map (hM : IsCompl M₁ M₂) {N : Type*} [AddCommGroup N] [Module A N]
    (f : M ≃ₗ[A] N) : IsCompl (M₁.map f.toLinearMap) (M₂.map f.toLinearMap) :=
  IsCompl.mk (Submodule.disjoint_map f.injective hM.disjoint)
    (Submodule.codisjoint_map f.surjective hM.codisjoint)

theorem LinearMap.isCompl_rTensor (Q : Type*) [AddCommGroup Q] [Module A Q] (hM : IsCompl M₁ M₂) :
    IsCompl (range (rTensor Q M₁.subtype)) (range (rTensor Q M₂.subtype)) := by
  simp only [← comm_comp_lTensor_comp_comm_eq]
  simp only [LinearMap.range_comp]
  apply Submodule.isCompl_map
  simp only [LinearEquiv.range, Submodule.map_top]
  exact LinearMap.isCompl_lTensor Q hM

theorem LinearMap.isCompl_baseChange (hM : IsCompl M₁ M₂)
    (R : Type*) [CommRing R] [Algebra A R] :
    IsCompl (range (baseChange R M₁.subtype)) (range (baseChange R M₂.subtype)) := by
  rw [← isCompl_restrictScalars_iff A]
  exact isCompl_lTensor R hM

theorem Algebra.baseChange_bot {R S : Type*} [CommRing R] [Algebra A R] [CommRing S] [Algebra A S] :
    Subalgebra.toSubmodule ⊥ = LinearMap.range
      (LinearMap.baseChange R (Subalgebra.toSubmodule (⊥ : Subalgebra A S)).subtype) := by
  ext x
  simp only [Subalgebra.mem_toSubmodule, Algebra.mem_bot, Set.mem_range, LinearMap.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y ⊗ₜ[A] ⟨1, (Subalgebra.mem_toSubmodule ⊥).mpr (one_mem ⊥)⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    induction y using TensorProduct.induction_on with
    | zero =>
      use 0
      simp [LinearMap.map_zero]
    | tmul r s =>
      rcases s with ⟨s, hs⟩
      simp only [Subalgebra.mem_toSubmodule] at hs
      obtain ⟨a, rfl⟩ := hs
      use a • r
      simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        toRingHom_eq_coe, RingHom.coe_coe, baseChange_tmul, coe_subtype, smul_tmul]
      rw [Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one]
    | add x y hx hy =>
      obtain ⟨x', hx⟩ := hx
      obtain ⟨y', hy⟩ := hy
      use x' + y'
      simp [hx, hy, map_add]

theorem Algebra.TensorProduct.map_includeRight_eq_range_baseChange
    {S : Type*} [CommRing S] [Algebra A S] {I : Ideal S}
    (R : Type*) [CommRing R] [Algebra A R]  :
    (I.map Algebra.TensorProduct.includeRight).restrictScalars R
      = LinearMap.range ((Submodule.restrictScalars A I).subtype.baseChange R) := by
  ext x
  simp only [restrictScalars_mem, LinearMap.mem_range]
  constructor
  · intro hx
    induction hx using Submodule.closure_induction with
    | zero => use 0; simp
    | add _ _ _ _ hx hy =>
      obtain ⟨x, rfl⟩ := hx
      obtain ⟨y, rfl⟩ := hy
      use x + y; simp
    | smul_mem a x hx =>
      revert hx
      induction a using TensorProduct.induction_on with
      | add u' v' hu hv =>
        intro hx
        obtain ⟨u, hu⟩ := hu hx
        obtain ⟨v, hv⟩ := hv hx
        use u + v; simp [hu, hv, right_distrib]
      | zero =>
        intro hx
        use 0; simp
      | tmul r s =>
        rintro ⟨i, hi, rfl⟩
        use r ⊗ₜ[A] (⟨s • i, smul_mem I s hi⟩)
        simp
  · rintro ⟨y, rfl⟩
    induction y using TensorProduct.induction_on with
    | zero => simp only [_root_.map_zero, Submodule.zero_mem]
    | tmul r s =>
      rcases s with ⟨s, hs⟩
      simp only [restrictScalars_mem] at hs
      simp only [baseChange_tmul, coe_subtype]
      rw [← mul_one r, ← smul_eq_mul, ← TensorProduct.smul_tmul']
      rw [← IsScalarTower.algebraMap_smul (R ⊗[A] S) r, smul_eq_mul]
      apply Ideal.mul_mem_left
      exact Ideal.mem_map_of_mem Algebra.TensorProduct.includeRight hs
    | add x y hx hy =>
      simp only [map_add]
      exact Ideal.add_mem _ hx hy

end
-/

/-
namespace Submodule

/- This section proves the complementary property for tensor products that is necessary to prove
  that the tensor product of algebras with augmentation ideals has an augmentation ideal -/
open TensorProduct LinearMap

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M] {M' M'' : Submodule A M}
  {N : Type*} [AddCommGroup N] [Module A N] {N' N'' : Submodule A N}

variable (M' N') in
/-- The submodule of M ⊗[A] N image of M' ⊗[A] N' -/
noncomputable def TensorProduct : Submodule A (M ⊗[A] N) :=
  range (TensorProduct.mapIncl M' N')
namespace TensorProduct

variable (A M N) in
theorem top_top : TensorProduct (⊤ : Submodule A M) (⊤ : Submodule A N) = ⊤ := by
  simp [ -mapIncl, TensorProduct, range_mapIncl, map₂_mk_top_top_eq_top, ← span_tmul_eq_top]

variable (N') in
lemma mono_left (h : M' ≤ M'') : TensorProduct M' N' ≤ TensorProduct M'' N' :=
  TensorProduct.range_mapIncl_mono  h le_rfl

variable (M') in
lemma mono_right (h : N' ≤ N'') : TensorProduct M' N' ≤ TensorProduct M' N'' :=
  TensorProduct.range_mapIncl_mono le_rfl h

variable (N') in
lemma sup_left : TensorProduct (M' ⊔ M'') N' = TensorProduct M' N' ⊔ TensorProduct M'' N' := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simp only [_root_.map_zero, Submodule.zero_mem]
    | tmul m n =>
      rcases m with ⟨_, hm⟩
      rcases mem_sup.mp hm with ⟨m', hm', m'', hm'', rfl⟩
      simp only [mapIncl, map_tmul, coe_subtype, add_tmul]
      refine add_mem (mem_sup_left ?_) (mem_sup_right ?_)
      · exact ⟨⟨m', hm'⟩ ⊗ₜ[A] n, rfl⟩
      · exact ⟨⟨m'', hm''⟩ ⊗ₜ[A] n, rfl⟩
    | add x y hx hy => simp only [map_add, add_mem hx hy]
  · simp only [sup_le_iff]
    refine ⟨range_mapIncl_mono le_sup_left le_rfl,
      range_mapIncl_mono le_sup_right le_rfl⟩

variable (M') in
lemma sup_right : TensorProduct M' (N' ⊔ N'') = TensorProduct M' N' ⊔ TensorProduct M' N'' := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simp only [_root_.map_zero, Submodule.zero_mem]
    | tmul m n =>
      rcases n with ⟨_, hn⟩
      rcases mem_sup.mp hn with ⟨n', hn', n'', hn'', rfl⟩
      simp only [mapIncl, map_tmul, coe_subtype, tmul_add]
      refine add_mem (mem_sup_left ?_) (mem_sup_right ?_)
      · exact ⟨m ⊗ₜ[A] ⟨n', hn'⟩, rfl⟩
      · exact ⟨m ⊗ₜ[A] ⟨n'', hn''⟩, rfl⟩
    | add x y hx hy => simp only [map_add, add_mem hx hy]
  · simp only [sup_le_iff]
    refine ⟨range_mapIncl_mono le_rfl le_sup_left,
      range_mapIncl_mono le_rfl le_sup_right⟩

variable (N') in
lemma disjoint_left (hM : IsCompl M' M'') :
    Disjoint (TensorProduct M' N') (TensorProduct M'' N') := by
  have hq : M'.subtype.comp (linearProjOfIsCompl _ _ hM) +
      M''.subtype.comp (linearProjOfIsCompl _ _ hM.symm) = LinearMap.id := by
    ext x
    simp only [add_apply, LinearMap.coe_comp, coe_subtype, Function.comp_apply, id_coe, id_eq]
    erw [Submodule.IsCompl.projection_add_projection_eq_self]
  rw [disjoint_def]
  intro x h h'
  rw [← id_apply x (R := A), ← rTensor_id, ← hq]
  simp only [rTensor_add, rTensor_comp,
    add_apply, coe_comp, Function.comp_apply]
  change x ∈ range (TensorProduct.map _ N'.subtype) at h h'
  rw [← rTensor_comp_lTensor] at h h'
  replace h : x ∈ range (rTensor N M'.subtype) := range_comp_le_range _ _ h
  replace h' : x ∈ range (rTensor N M''.subtype) := range_comp_le_range _ _ h'
  rw [← ker_rTensor_of_linearProjOfIsCompl hM.symm N, mem_ker] at h
  rw [← ker_rTensor_of_linearProjOfIsCompl hM N, mem_ker] at h'
  simp only [h, h', _root_.map_zero, add_zero]

variable (M') in
lemma disjoint_right {N' N'' : Submodule A N} (hN : IsCompl N' N'') :
    Disjoint (TensorProduct M' N') (TensorProduct M' N'') := by
  have hq : N'.subtype.comp (linearProjOfIsCompl _ _ hN) +
      N''.subtype.comp (linearProjOfIsCompl _ _ hN.symm) = LinearMap.id := by
    ext x
    simp only [add_apply, LinearMap.coe_comp, coe_subtype, Function.comp_apply,
      id_coe, id_eq]
    erw [Submodule.IsCompl.projection_add_projection_eq_self]
  rw [disjoint_def]
  intro x h h'
  rw [← id_apply x (R := A), ← lTensor_id, ← hq]
  simp only [lTensor_add, lTensor_comp, add_apply, coe_comp, Function.comp_apply]
  change x ∈ range (TensorProduct.map M'.subtype _) at h h'
  rw [← lTensor_comp_rTensor] at h h'
  replace h : x ∈ range (lTensor M N'.subtype) := range_comp_le_range _ _ h
  replace h' : x ∈ range (lTensor M N''.subtype) := range_comp_le_range _ _ h'
  rw [← ker_lTensor_of_linearProjOfIsCompl hN.symm M, mem_ker] at h
  rw [← ker_lTensor_of_linearProjOfIsCompl hN M, mem_ker] at h'
  simp only [h, h', _root_.map_zero, add_zero]

variable (N) in
theorem isCompl_left_top (hM : IsCompl M' M'') :
    IsCompl (TensorProduct M' (⊤ : Submodule A N)) (TensorProduct M'' ⊤) := by
  apply IsCompl.mk
  · exact disjoint_left ⊤ hM
  · rw [codisjoint_iff, ← sup_left, codisjoint_iff.mp hM.codisjoint]
    exact top_top A M N

variable (M) in
theorem isCompl_right_top {N' N'' : Submodule A N} (hN : IsCompl N' N'') :
    IsCompl (TensorProduct (⊤ : Submodule A M) N') (TensorProduct ⊤ N'') := by
  apply IsCompl.mk
  · exact disjoint_right ⊤ hN
  · rw [codisjoint_iff, ← sup_right, codisjoint_iff.mp hN.codisjoint]
    exact top_top A M N

theorem isCompl_left_left (hM : IsCompl M' M'') (hN : IsCompl N' N'') :
    IsCompl (TensorProduct M' N') (TensorProduct ⊤ N'' ⊔ TensorProduct M'' ⊤) := by
  suffices TensorProduct M' N'' ⊔ TensorProduct M'' ⊤
    = TensorProduct ⊤ N'' ⊔ M''.TensorProduct ⊤ by
    rw [← this]
    apply isCompl_assoc_of_disjoint
    · exact disjoint_right M' hN
    · rw [← sup_right, codisjoint_iff.mp hN.codisjoint]
      exact isCompl_left_top N hM
  rw [← codisjoint_iff.mp hM.codisjoint, sup_left,
    ← codisjoint_iff.mp hN.codisjoint, sup_right]
  simp only [sup_assoc]
  apply congr_arg₂ _ rfl
  nth_rewrite 3 [sup_comm]
  rw [← sup_assoc, sup_idem, sup_comm]

end Submodule.TensorProduct
-/

section bot

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] (S : Subalgebra R A) (r : R)

/-
theorem Subalgebra.mem_bot_iff : r ∈ (⊥ : Subalgebra S R) ↔ r ∈ S := by
  simp only [Algebra.mem_bot, Set.mem_range, Subtype.exists]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact hr
  · intro hr
    exact ⟨r, hr, rfl⟩

#find_home! Subalgebra.mem_bot_iff
-/

@[simp]
theorem Subalgebra.restrictScalars_toSubmodule_bot :
    Submodule.restrictScalars R (Subalgebra.toSubmodule (⊥ : Subalgebra S A))
      = Subalgebra.toSubmodule S := by
  rw [← Subalgebra.restrictScalars_toSubmodule]
  congr
  ext x
  simp [Subalgebra.mem_restrictScalars, Algebra.mem_bot]
#find_home! Subalgebra.restrictScalars_toSubmodule_bot

@[simp]
lemma Submodule.restrictScalars_restrictScalars
    {R S T M : Type*} [Semiring R] [Semiring S] [Semiring T] [SMul R S] [SMul R T] [SMul S T]
    [AddCommMonoid M] [Module R M] [Module S M] [Module T M]
    [IsScalarTower R S M] [IsScalarTower S T M] [IsScalarTower R T M]
    (N : Submodule T M) :
    (N.restrictScalars S).restrictScalars R = N.restrictScalars R :=
  rfl
#find_home! Submodule.restrictScalars_restrictScalars

theorem Subalgebra.codisjoint_bot_iff (I : Ideal A) :
    Codisjoint (Subalgebra.toSubmodule (⊥ : Subalgebra S A)) (I.restrictScalars S) ↔
    Codisjoint (Subalgebra.toSubmodule S) (I.restrictScalars R) := by
  simp [← Submodule.codisjoint_restrictScalars_iff R]

theorem Subalgebra.disjoint_bot_iff (I : Ideal R) :
    Disjoint (Subalgebra.toSubmodule (⊥ : Subalgebra S R)) (I.restrictScalars S) ↔
    Disjoint (Subalgebra.toSubmodule S) (I.restrictScalars A) := by
  rw [← Submodule.disjoint_restrictScalars_iff A,
    Subalgebra.restrictScalars_toSubmodule_bot]
  exact Iff.rfl

end bot

namespace Ideal

variable (R : Type*) [CommRing R] {A : Type*} [CommRing A] [Algebra R A] (J : Ideal A)

open TensorProduct Ideal LinearMap Submodule

/-- An ideal `J` of a commutative `R`-algebra `A` is an augmentation ideal
if it is a submodule complement to `⊥ : Subalgebra R A`. -/
def IsAugmentation (R : Type*) [CommSemiring R]
    {A : Type*} [CommSemiring A] [Algebra R A] (J : Ideal A) : Prop :=
  IsCompl (Subalgebra.toSubmodule (⊥ : Subalgebra R A)) (J.restrictScalars R)

/-- If `S` is a subalgebra of an `R`-algebra `A`, then an ideal `I`of `A` is an augmentation ideal
for the `R`-algebra structure
if and only if it is an augmentation ideal for the `S`-algebra structure. -/
theorem isAugmentation_subalgebra_iff {R : Type*} [CommSemiring R] {A : Type*} [CommSemiring A]
    [Algebra R A] {S : Subalgebra R A} {I : Ideal A} :
    I.IsAugmentation S ↔ IsCompl (Subalgebra.toSubmodule S) (I.restrictScalars R) := by
  unfold Ideal.IsAugmentation
  rw [← Submodule.isCompl_restrictScalars_iff R, Subalgebra.restrictScalars_toSubmodule_bot]
  exact Iff.rfl

end Ideal

end Ideal
