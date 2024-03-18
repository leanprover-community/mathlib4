/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
import Mathlib.Topology.Algebra.Module.Alternating.Basic
import Mathlib.Analysis.NormedSpace.Multilinear.Basic
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.Analysis.NormedSpace.HahnBanach.SeparatingDual

/-!
# Injective seminorm on the tensor of a finite family of normed spaces.

Let `𝕜` be a nontrivially normed field and `E i` be a family of normed `𝕜`-vector spaces,
indexed by a finite type `ι`. We define a seminorm on `⨂[𝕜] i, E i`, which we call the
"injective seminorm". It is chosen to satisfy the following property: for every
normed `𝕜`-vector space `F`, the linear equivalence
`MultilinearMap 𝕜 E F ≃ₗ[𝕜] (⨂[𝕜] i, E i) →ₗ[𝕜] F`
expressing the universal property of the tensor product induces an isometric linear equivalence
`ContinuusMultilinearMap 𝕜 E F ≃ₗᵢ[𝕜] (⨂[𝕜] i, E i) →L[𝕜] F`.

-/

variable {ι : Type*} [Fintype ι]

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

open scoped TensorProduct

open BigOperators

namespace PiTensorProduct

section seminorm

lemma toDualMultilinearMap_bound (x : ⨂[𝕜] i, E i) :
    ∃ (C : ℝ), 0 ≤ C ∧ ∀ (G : Type*) [SeminormedAddCommGroup G]
    [NormedSpace 𝕜 G] (f : ContinuousMultilinearMap 𝕜 E G),
    ‖lift f.toMultilinearMap x‖ ≤ C * ‖f‖ := by
  induction' x using PiTensorProduct.induction_on with r m x y hx hy
  · existsi ‖r‖ * ∏ i : ι, ‖m i‖
    constructor
    · exact mul_nonneg (norm_nonneg r) (Finset.prod_nonneg (fun i _ ↦ norm_nonneg (m i)))
    · intro G _ _ f
      simp only [map_smul, lift.tprod, ContinuousMultilinearMap.coe_coe]
      rw [mul_assoc, mul_comm _ ‖f‖, norm_smul]
      exact le_trans (mul_le_mul_of_nonneg_left (ContinuousMultilinearMap.le_opNorm f m)
        (norm_nonneg r)) (le_refl _)
  · obtain ⟨Cx, hCx⟩ := hx; obtain ⟨Cy, hCy⟩ := hy
    existsi Cx + Cy
    constructor
    · exact add_nonneg hCx.1 hCy.1
    · intro G _ _ f
      rw [map_add, add_mul]
      refine le_trans (norm_add_le _ _) (add_le_add (hCx.2 _ f) (hCy.2 _ f))

@[simps!]
noncomputable def toDualContinuousMultilinearMap : (⨂[𝕜] i, E i) →ₗ[𝕜]
    ContinuousMultilinearMap 𝕜 E F →L[𝕜] F where
  toFun x := LinearMap.mkContinuousOfExistsBound
    ((LinearMap.flip (lift (R := 𝕜) (s := E) (E := F)).toLinearMap x) ∘ₗ
    ContinuousMultilinearMap.toMultilinearMapLinear) (by
      obtain ⟨C, hC⟩ := toDualMultilinearMap_bound x
      existsi C
      intro f
      simp only [LinearMap.coe_comp, Function.comp_apply,
        ContinuousMultilinearMap.toMultilinearMapLinear_apply, LinearMap.flip_apply,
        LinearEquiv.coe_coe]
      exact hC.2 F f)
  map_add' x y := by
    ext _
    simp only [map_add, LinearMap.mkContinuousOfExistsBound_apply, LinearMap.coe_comp,
      Function.comp_apply, ContinuousMultilinearMap.toMultilinearMapLinear_apply,
      LinearMap.add_apply, LinearMap.flip_apply, LinearEquiv.coe_coe, ContinuousLinearMap.add_apply]
  map_smul' a x := by
    ext _
    simp only [map_smul, LinearMap.mkContinuousOfExistsBound_apply, LinearMap.coe_comp,
      Function.comp_apply, ContinuousMultilinearMap.toMultilinearMapLinear_apply,
      LinearMap.smul_apply, LinearMap.flip_apply, LinearEquiv.coe_coe, RingHom.id_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply]

@[simp]
lemma toDualContinuousMultilinearMap_tprod_apply (m : (i : ι) → E i)
    (f : ContinuousMultilinearMap 𝕜 E F) :
    toDualContinuousMultilinearMap (⨂ₜ[𝕜] i, m i) f = f m := by
  simp only [toDualContinuousMultilinearMap_apply_toFun, lift.tprod,
    ContinuousMultilinearMap.coe_coe]

noncomputable def injectiveSeminorm : Seminorm 𝕜 (⨂[𝕜] i, E i) :=
  sSup {p | ∃ (G : Type (max (max u_1 u_2) u_3)) (_ : SeminormedAddCommGroup G)
  (_ : NormedSpace 𝕜 G), p = Seminorm.comp (normSeminorm 𝕜 (ContinuousMultilinearMap 𝕜 E G →L[𝕜] G))
  (toDualContinuousMultilinearMap (F := G) (𝕜 := 𝕜) (E := E))}

lemma dualSeminorms_bounded : BddAbove {p | ∃ (G : Type (max (max u_1 u_2) u_3))
    (_ : SeminormedAddCommGroup G) (_ : NormedSpace 𝕜 G),
    p = Seminorm.comp (normSeminorm 𝕜 (ContinuousMultilinearMap 𝕜 E G →L[𝕜] G))
    (toDualContinuousMultilinearMap (F := G) (𝕜 := 𝕜) (E := E))} := by
  rw [Seminorm.bddAbove_iff]
  set bound : (⨂[𝕜] i, E i) → ℝ :=
    fun x ↦ Classical.choose (toDualMultilinearMap_bound x)
  existsi bound
  rw [mem_upperBounds]
  intro p hp
  simp only [Set.mem_image] at hp
  let ⟨q, hq⟩ := hp
  simp only [Set.mem_setOf_eq] at hq
  intro x
  rw [← hq.2]
  obtain ⟨⟨G, G₁, ⟨G₂, h⟩⟩⟩ := hq
  letI := G₁
  letI := G₂
  rw [h]
  simp only [Seminorm.comp_apply, ge_iff_le]
  let hbound := Classical.choose_spec (toDualMultilinearMap_bound x)
  exact ContinuousLinearMap.opNorm_le_bound _ hbound.1 (fun f ↦ by
    simp only [toDualContinuousMultilinearMap_apply_toFun]
    exact hbound.2 G f)

@[simp]
theorem injectiveSeminorm_apply (x : ⨂[𝕜] i, E i) :
    injectiveSeminorm x = ⨆ p : {p | ∃ (G : Type (max (max u_1 u_2) u_3))
    (_ : SeminormedAddCommGroup G) (_ : NormedSpace 𝕜 G), p = Seminorm.comp (normSeminorm 𝕜
    (ContinuousMultilinearMap 𝕜 E G →L[𝕜] G))
    (toDualContinuousMultilinearMap (F := G) (𝕜 := 𝕜) (E := E))}, p.1 x := by
  refine Seminorm.sSup_apply dualSeminorms_bounded

theorem injectiveSeminorm_bound (f : ContinuousMultilinearMap 𝕜 E F) (x : ⨂[𝕜] i, E i) :
    ‖lift f.toMultilinearMap x‖ ≤ ‖f‖ * injectiveSeminorm x := by
  set G := (⨂[𝕜] i, E i) ⧸ LinearMap.ker (lift f.toMultilinearMap)
  set G' := LinearMap.range (lift f.toMultilinearMap)
  set e := LinearMap.quotKerEquivRange (lift f.toMultilinearMap)
  letI := SeminormedAddCommGroup.induced G G' e
  letI := NormedSpace.induced 𝕜 G G' e
  set f'₀ := lift.symm (e.symm.toLinearMap ∘ₗ LinearMap.rangeRestrict (lift f.toMultilinearMap))
  have hf'₀ : ∀ (x : Π (i : ι), E i), ‖f'₀ x‖ ≤ ‖f‖ * ∏ i, ‖x i‖ := fun x ↦ by
    change ‖e (f'₀ x)‖ ≤ _
    simp only [lift_symm, LinearMap.compMultilinearMap_apply, LinearMap.coe_comp,
        LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.apply_symm_apply, Submodule.coe_norm,
        LinearMap.codRestrict_apply, lift.tprod, ContinuousMultilinearMap.coe_coe, e, f'₀]
    exact f.le_opNorm x
  set f' := MultilinearMap.mkContinuous f'₀ ‖f‖ hf'₀
  have hnorm : ‖f'‖ ≤ ‖f‖ := (f'.opNorm_le_iff (norm_nonneg f)).mpr hf'₀
  have heq : e (lift f'.toMultilinearMap x) = lift f.toMultilinearMap x := by
    induction' x using PiTensorProduct.induction_on with a m _ _ hx hy
    · simp only [lift_symm, map_smul, lift.tprod, ContinuousMultilinearMap.coe_coe,
      MultilinearMap.coe_mkContinuous, LinearMap.compMultilinearMap_apply, LinearMap.coe_comp,
      LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.apply_symm_apply, SetLike.val_smul,
      LinearMap.codRestrict_apply, f', f'₀]
    · simp only [map_add, AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid, hx, hy]
  suffices h : ‖lift f'.toMultilinearMap x‖ ≤ ‖f'‖ * injectiveSeminorm x by
    change ‖(e (lift f'.toMultilinearMap x)).1‖ ≤ _ at h
    rw [heq] at h
    refine le_trans h (mul_le_mul_of_nonneg_right hnorm (apply_nonneg _ _))
  have hle : Seminorm.comp (normSeminorm 𝕜 (ContinuousMultilinearMap 𝕜 E G →L[𝕜] G))
      (toDualContinuousMultilinearMap (F := G) (𝕜 := 𝕜) (E := E)) ≤ injectiveSeminorm := by
    simp only [injectiveSeminorm]
    refine le_csSup dualSeminorms_bounded ?_
    rw [Set.mem_setOf]
    existsi G, inferInstance, inferInstance
    rfl
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (hle x) (norm_nonneg f'))
  simp only [Seminorm.comp_apply, coe_normSeminorm, ← toDualContinuousMultilinearMap_apply_apply]
  rw [mul_comm]
  exact ContinuousLinearMap.le_opNorm _ _

theorem injectiveSeminorm_tprod_le (m : Π (i : ι), E i) :
    injectiveSeminorm (⨂ₜ[𝕜] i, m i) ≤ ∏ i, ‖m i‖ := by
  rw [injectiveSeminorm_apply]
  apply csSup_le
  · rw [Set.range_nonempty_iff_nonempty]
    simp only [Set.coe_setOf, nonempty_subtype]
    existsi 0, PUnit, inferInstance, inferInstance
    ext x
    simp only [Seminorm.zero_apply, Seminorm.comp_apply, coe_normSeminorm]
    have heq : toDualContinuousMultilinearMap (F := PUnit) x = 0 := by ext _
    rw [heq, norm_zero]
  · intro a ha
    simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.mem_range, Subtype.exists, exists_prop] at ha
    let ⟨p, ⟨⟨G, _, _, hp⟩, hpa⟩⟩ := ha
    rw [← hpa, hp]
    simp only [Seminorm.comp_apply, coe_normSeminorm, ge_iff_le]
    rw [ContinuousLinearMap.opNorm_le_iff (Finset.prod_nonneg (fun _ _ ↦ norm_nonneg _))]
    intro f
    simp only [toDualContinuousMultilinearMap_apply_toFun, lift.tprod,
        ContinuousMultilinearMap.coe_coe]
    rw [mul_comm]
    exact ContinuousMultilinearMap.le_opNorm f m

noncomputable instance : SeminormedAddCommGroup (⨂[𝕜] i, E i) :=
  AddGroupSeminorm.toSeminormedAddCommGroup injectiveSeminorm.toAddGroupSeminorm

noncomputable instance : NormedSpace 𝕜 (⨂[𝕜] i, E i) where
  norm_smul_le a x := by
    change injectiveSeminorm.toFun (a • x) ≤ _
    rw [injectiveSeminorm.smul']
    rfl

@[simps]
noncomputable def liftEquiv : ContinuousMultilinearMap 𝕜 E F ≃ₗ[𝕜] (⨂[𝕜] i, E i) →L[𝕜] F where
  toFun f := LinearMap.mkContinuous (lift f.toMultilinearMap) ‖f‖
    (fun x ↦ injectiveSeminorm_bound f x)
  map_add' f g := by ext _; simp only [ContinuousMultilinearMap.toMultilinearMap_add, map_add,
    LinearMap.mkContinuous_apply, LinearMap.add_apply, ContinuousLinearMap.add_apply]
  map_smul' a f := by ext _; simp only [ContinuousMultilinearMap.toMultilinearMap_smul, map_smul,
    LinearMap.mkContinuous_apply, LinearMap.smul_apply, RingHom.id_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply]
  invFun l := MultilinearMap.mkContinuous (lift.symm l.toLinearMap) ‖l‖ (fun x ↦ by
    simp only [lift_symm, LinearMap.compMultilinearMap_apply, ContinuousLinearMap.coe_coe]
    refine le_trans (ContinuousLinearMap.le_opNorm _ _) (mul_le_mul_of_nonneg_left ?_
      (norm_nonneg l))
    exact injectiveSeminorm_tprod_le x)
  left_inv f := by ext x; simp only [LinearMap.mkContinuous_coe, LinearEquiv.symm_apply_apply,
      MultilinearMap.coe_mkContinuous, ContinuousMultilinearMap.coe_coe]
  right_inv l := by
    rw [← ContinuousLinearMap.coe_inj]
    apply PiTensorProduct.ext; ext m
    simp only [lift_symm, LinearMap.mkContinuous_coe, LinearMap.compMultilinearMap_apply,
      lift.tprod, ContinuousMultilinearMap.coe_coe, MultilinearMap.coe_mkContinuous,
      ContinuousLinearMap.coe_coe]

@[simps!]
noncomputable def liftIsometry  : ContinuousMultilinearMap 𝕜 E F ≃ₗᵢ[𝕜] (⨂[𝕜] i, E i) →L[𝕜] F :=
  {liftEquiv with
   norm_map' := by
     intro f
     refine le_antisymm ?_ ?_
     · simp only [liftEquiv_apply]
       exact LinearMap.mkContinuous_norm_le _ (norm_nonneg f) _
     · conv_lhs => rw [← liftEquiv.left_inv f]
       simp only [LinearEquiv.invFun_eq_symm, liftEquiv_symm_apply]
       exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg _) _}

variable (𝕜)

@[simps!]
noncomputable def tprodL : ContinuousMultilinearMap 𝕜 E (⨂[𝕜] i, E i) :=
  liftIsometry.invFun (ContinuousLinearMap.id 𝕜 _)

variable {𝕜}

@[simp]
theorem tprodL_coe : (tprodL 𝕜).toMultilinearMap = tprod 𝕜 (s := E) := by
  ext m
  simp only [ContinuousMultilinearMap.coe_coe, tprodL_toFun]

@[simp]
theorem liftIsometry.tprod {f : ContinuousMultilinearMap 𝕜 E F} (m : Π (i : ι), E i) :
    liftIsometry.toFun f (tprod 𝕜 m) = f m := by
  simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv, liftIsometry_toFun_toFun]
  exact lift.tprod m

@[simp]
theorem liftIsometry.tprodL {f : ContinuousMultilinearMap 𝕜 E F} (m : Π (i : ι), E i) :
    liftIsometry.toFun f (tprodL 𝕜 m) = f m := by
  simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv, tprodL_toFun, liftIsometry_toFun_toFun]
  exact lift.tprod m

@[simp]
theorem liftIsometry_symm (l : (⨂[𝕜] i, E i) →L[𝕜] F) :
    liftIsometry.symm.toFun l = l.compContinuousMultilinearMap (tprodL 𝕜) := by
  ext m
  simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv, liftIsometry_symm_apply_toFun,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply, tprodL_toFun]

@[simp]
theorem liftIsometry_tprodL :
    liftIsometry.toFun (tprodL 𝕜) = ContinuousLinearMap.id 𝕜 (⨂[𝕜] i, E i) := by
  ext x
  simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv, liftIsometry_toFun_toFun, tprodL_coe,
    ContinuousLinearMap.coe_id', id_eq]
  change lift (tprod 𝕜) x = _
  rw [lift_tprod, LinearMap.id_apply]

end seminorm

section map

variable {E' E'' : ι → Type*}
variable [∀ i, SeminormedAddCommGroup (E' i)] [∀ i, NormedSpace 𝕜 (E' i)]
variable [∀ i, SeminormedAddCommGroup (E'' i)] [∀ i, NormedSpace 𝕜 (E'' i)]
variable (g : Π i, E' i →L[𝕜] E'' i) (f : Π i, E i →L[𝕜] E' i)

/--
Let `Eᵢ` and `Fᵢ` be two families of normed `𝕜`-vector spaces.
Let `f` be a family of continuous `𝕜`-linear maps between `Eᵢ` and `Fᵢ`, i.e.
`f : Πᵢ Eᵢ →L[𝕜] Fᵢ`, then there is an induced continuous linear map
`⨂ᵢ Eᵢ → ⨂ᵢ Fᵢ` by `⨂ aᵢ ↦ ⨂ fᵢ aᵢ`.
-/
noncomputable def mapL : (⨂[𝕜] i, E i) →L[𝕜] ⨂[𝕜] i, E' i :=
  liftIsometry.toFun <| (tprodL 𝕜).compContinuousLinearMap f

@[simp] lemma mapL_tprod (x : Π i, E i) :
    mapL f (tprod 𝕜 x) = tprod 𝕜 fun i ↦ f i (x i) :=
  liftIsometry.tprodL _

@[simp]
theorem mapL_coe : (mapL f).toLinearMap = map (fun i ↦ (f i).toLinearMap) := by
  ext
  simp only [LinearMap.compMultilinearMap_apply, ContinuousLinearMap.coe_coe, mapL_tprod, map_tprod]

@[simp]
theorem mapL_apply (x : ⨂[𝕜] i, E i) : mapL f x = map (fun i ↦ (f i).toLinearMap) x := by
  induction' x using PiTensorProduct.induction_on with _ _ _ _ hx hy
  · simp only [map_smul, mapL_tprod, map_tprod, ContinuousLinearMap.coe_coe]
  · simp only [map_add, hx, hy]

/-- Given submodules `p i ⊆ E i`, this is the natural map: `⨂[𝕜] i, p i → ⨂[𝕜] i, E i`.
This is the continuous version of `PiTensorProduct.mapIncl`.
-/
@[simp]
noncomputable def mapLIncl (p : Π i, Submodule 𝕜 (E i)) : (⨂[𝕜] i, p i) →L[𝕜] ⨂[𝕜] i, E i :=
  mapL fun (i : ι) ↦ (p i).subtypeL

theorem mapL_comp : mapL (fun (i : ι) ↦ g i ∘L f i) = mapL g ∘L mapL f := by
  apply ContinuousLinearMap.coe_injective
  ext
  simp only [mapL_coe, ContinuousLinearMap.coe_comp, LinearMap.compMultilinearMap_apply, map_tprod,
    LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply]

theorem liftIsometry_comp_mapL (h : ContinuousMultilinearMap 𝕜 E' F) :
    liftIsometry.toFun h ∘L mapL f = liftIsometry.toFun (h.compContinuousLinearMap f) := by
  apply ContinuousLinearMap.coe_injective
  ext
  simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv, ContinuousLinearMap.coe_comp,
    LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, ContinuousLinearMap.coe_coe,
    Function.comp_apply, mapL_tprod, liftIsometry_toFun_toFun]
  erw [lift.tprod]

attribute [local ext high] ext

@[simp]
theorem mapL_id : mapL (fun i ↦ ContinuousLinearMap.id 𝕜 (E i)) = ContinuousLinearMap.id _ _ := by
  apply ContinuousLinearMap.coe_injective
  ext
  simp only [LinearMap.compMultilinearMap_apply, ContinuousLinearMap.coe_coe, mapL_tprod,
    ContinuousLinearMap.coe_id', id_eq, ContinuousLinearMap.coe_id, LinearMap.id_coe]

@[simp]
theorem mapL_one : mapL (fun (i : ι) ↦ (1 : E i →L[𝕜] E i)) = 1 :=
  mapL_id

theorem mapL_mul (f₁ f₂ : Π i, E i →L[𝕜] E i) :
    mapL (fun i ↦ f₁ i * f₂ i) = mapL f₁ * mapL f₂ :=
  mapL_comp f₁ f₂

/-- Upgrading `PiTensorProduct.mapL` to a `MonoidHom` when `E = F`.-/
@[simps]
noncomputable def mapLMonoidHom : (Π i, E i →L[𝕜] E i) →* ((⨂[𝕜] i, E i) →L[𝕜] ⨂[𝕜] i, E i) where
  toFun := mapL
  map_one' := mapL_one
  map_mul' := mapL_mul

@[simp]
protected theorem mapL_pow (f : Π i, E i →L[𝕜] E i) (n : ℕ) :
    mapL (f ^ n) = mapL f ^ n := MonoidHom.map_pow mapLMonoidHom _ _

open Function in
private theorem mapL_add_smul_aux [DecidableEq ι] (i : ι) (u : E i →L[𝕜] E' i) :
    (fun j ↦ (update f i u j).toLinearMap) =
    update (fun j ↦ (f j).toLinearMap) i u.toLinearMap := by
  symm
  rw [update_eq_iff]
  constructor
  · simp only [update_same]
  · exact fun _ h ↦ by simp only [ne_eq, h, not_false_eq_true, update_noteq]

open Function in
protected theorem mapL_add [DecidableEq ι] (i : ι) (u v : E i →L[𝕜] E' i) :
    mapL (update f i (u + v)) = mapL (update f i u) + mapL (update f i v) := by
  ext x
  simp only [mapL_apply, mapL_add_smul_aux, ContinuousLinearMap.coe_add, PiTensorProduct.map_add,
    LinearMap.add_apply, ContinuousLinearMap.add_apply]

open Function in
protected theorem mapL_smul [DecidableEq ι] (i : ι) (c : 𝕜) (u : E i →L[𝕜] E' i) :
    mapL (update f i (c • u)) = c • mapL (update f i u) := by
  ext x
  simp only [mapL_apply, mapL_add_smul_aux, ContinuousLinearMap.coe_smul, PiTensorProduct.map_smul,
    LinearMap.smul_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply]

theorem mapL_opNorm : ‖mapL f‖ ≤ ∏ i, ‖f i‖ := by
  rw [ContinuousLinearMap.opNorm_le_iff (Finset.prod_nonneg (fun _ _ ↦ norm_nonneg _))]
  intro x
  rw [mapL, liftIsometry]
  simp only
  rw [liftEquiv]
  simp only [LinearMap.mkContinuous_apply]
  refine le_trans (injectiveSeminorm_bound _ _) (mul_le_mul_of_nonneg_right ?_ (norm_nonneg x))
  rw [ContinuousMultilinearMap.opNorm_le_iff _ (Finset.prod_nonneg (fun _ _ ↦ norm_nonneg _))]
  intro m
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  refine le_trans (injectiveSeminorm_tprod_le (fun i ↦ (f i) (m i))) ?_
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) (fun _ _ ↦ ContinuousLinearMap.le_opNorm _ _ )

variable (𝕜 E E')

/-- The tensor of a family of linear maps from `sᵢ` to `tᵢ`, as a multilinear map of
the family.
-/
@[simps!]
noncomputable def mapLMultilinear : ContinuousMultilinearMap 𝕜 (fun (i : ι) ↦ E i →L[𝕜] E' i)
    ((⨂[𝕜] i, E i) →L[𝕜] ⨂[𝕜] i, E' i) :=
  MultilinearMap.mkContinuous
  { toFun := mapL
    map_smul':= fun _ _ _ _ ↦ PiTensorProduct.mapL_smul _ _ _ _
    map_add' := fun _ _ _ _ ↦ PiTensorProduct.mapL_add _ _ _ _}
  1 (fun f ↦ by rw [one_mul]; exact mapL_opNorm f)

variable {𝕜 E E'}

theorem mapLMultilinear_opNorm : ‖mapLMultilinear 𝕜 E E'‖ ≤ 1 := by
  simp only [mapLMultilinear]
  apply MultilinearMap.mkContinuous_norm_le _ zero_le_one

end map

end PiTensorProduct
