/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Homology.Embedding.IsSupported
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Homology of the extension of an homological complex

Given an embedding `e : c.Embedding c'` and `K : HomologicalComplex C c`, we shall
compute the homology of `K.extend e`. In degrees that are not in the image of `e.f`,
the homology is obviously zero. When `e.f j = j`, we construct an isomorphism
`(K.extend e).homology j' ≅ K.homology j`.

-/

open CategoryTheory Limits Category

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category C] [HasZeroMorphisms C]
  [HasZeroObject C]

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

namespace extend

section HomologyData

variable {i j k : ι} {i' j' k' : ι'} (hj' : e.f j = j')
  (hi : c.prev j = i) (hi' : c'.prev j' = i') (hk : c.next j = k) (hk' : c'.next j' = k')

include hk hk' in
lemma comp_d_eq_zero_iff ⦃W : C⦄ (φ : W ⟶ K.X j) :
    φ ≫ K.d j k = 0 ↔ φ ≫ (K.extendXIso e hj').inv ≫ (K.extend e).d j' k' = 0 := by
  by_cases hjk : c.Rel j k
  · have hk' : e.f k = k' := by rw [← hk', ← hj', c'.next_eq' (e.rel hjk)]
    rw [K.extend_d_eq e hj' hk', Iso.inv_hom_id_assoc,
      ← cancel_mono (K.extendXIso e hk').inv, zero_comp, assoc]
  · simp only [K.shape _ _ hjk, comp_zero, true_iff]
    rw [K.extend_d_from_eq_zero e j' k' j hj', comp_zero, comp_zero]
    rw [hk]
    exact hjk

include hi hi' in
lemma d_comp_eq_zero_iff ⦃W : C⦄ (φ : K.X j ⟶ W) :
    K.d i j ≫ φ = 0 ↔ (K.extend e).d i' j' ≫ (K.extendXIso e hj').hom ≫ φ = 0 := by
  by_cases hij : c.Rel i j
  · have hi' : e.f i = i' := by rw [← hi', ← hj', c'.prev_eq' (e.rel hij)]
    rw [K.extend_d_eq e hi' hj', assoc, assoc, Iso.inv_hom_id_assoc,
      ← cancel_epi (K.extendXIso e hi').hom, comp_zero]
  · simp only [K.shape _ _ hij, zero_comp, true_iff]
    rw [K.extend_d_to_eq_zero e i' j' j hj', zero_comp]
    rw [hi]
    exact hij

namespace leftHomologyData

variable (cone : KernelFork (K.d j k)) (hcone : IsLimit cone)

/-- The kernel fork of `(K.extend e).d j' k'` that is deduced from a kernel
fork of `K.d j k `. -/
@[simp]
noncomputable def kernelFork : KernelFork ((K.extend e).d j' k') :=
  KernelFork.ofι (cone.ι ≫ (extendXIso K e hj').inv)
    (by rw [assoc, ← comp_d_eq_zero_iff K e hj' hk hk' cone.ι, cone.condition])

/-- The limit kernel fork of `(K.extend e).d j' k'` that is deduced from a limit
kernel fork of `K.d j k `. -/
noncomputable def isLimitKernelFork : IsLimit (kernelFork K e hj' hk hk' cone) :=
  KernelFork.isLimitOfIsLimitOfIff hcone ((K.extend e).d j' k')
    (extendXIso K e hj').symm (comp_d_eq_zero_iff K e hj' hk hk')

variable (cocone : CokernelCofork (hcone.lift (KernelFork.ofι (K.d i j) (K.d_comp_d i j k))))
  (hcocone : IsColimit cocone)

include hi hi' hcone in
/-- Auxiliary lemma for `lift_d_comp_eq_zero_iff`. -/
lemma lift_d_comp_eq_zero_iff' ⦃W : C⦄ (f' : K.X i ⟶ cone.pt)
    (hf' : f' ≫ cone.ι = K.d i j)
    (f'' : (K.extend e).X i' ⟶ cone.pt)
    (hf'' : f'' ≫ cone.ι ≫ (extendXIso K e hj').inv = (K.extend e).d i' j')
    (φ : cone.pt ⟶ W) :
    f' ≫ φ = 0 ↔ f'' ≫ φ = 0 := by
  by_cases hij : c.Rel i j
  · have hi'' : e.f i = i' := by rw [← hi', ← hj', c'.prev_eq' (e.rel hij)]
    have : (K.extendXIso e hi'').hom ≫ f' = f'' := by
      apply Fork.IsLimit.hom_ext hcone
      rw [assoc, hf', ← cancel_mono (extendXIso K e hj').inv, assoc, assoc, hf'',
        K.extend_d_eq e hi'' hj']
    rw [← cancel_epi (K.extendXIso e hi'').hom, comp_zero, ← this, assoc]
  · have h₁ : f' = 0 := by
      apply Fork.IsLimit.hom_ext hcone
      simp only [zero_comp, hf', K.shape _ _ hij]
    have h₂ : f'' = 0 := by
      apply Fork.IsLimit.hom_ext hcone
      dsimp
      rw [← cancel_mono (extendXIso K e hj').inv, assoc, hf'', zero_comp, zero_comp,
        K.extend_d_to_eq_zero e i' j' j hj']
      rw [hi]
      exact hij
    simp [h₁, h₂]

include hi hi' in
lemma lift_d_comp_eq_zero_iff ⦃W : C⦄ (φ : cone.pt ⟶ W) :
    hcone.lift (KernelFork.ofι (K.d i j) (K.d_comp_d i j k)) ≫ φ = 0 ↔
      ((isLimitKernelFork K e hj' hk hk' cone hcone).lift
      (KernelFork.ofι ((K.extend e).d i' j') (d_comp_d _ _ _ _))) ≫ φ = 0 :=
  lift_d_comp_eq_zero_iff' K e hj' hi hi' cone hcone _ (hcone.fac _ _) _
    (IsLimit.fac _ _ WalkingParallelPair.zero) _

/-- Auxiliary definition for `extend.leftHomologyData`. -/
noncomputable def cokernelCofork :
    CokernelCofork ((isLimitKernelFork K e hj' hk hk' cone hcone).lift
      (KernelFork.ofι ((K.extend e).d i' j') (d_comp_d _ _ _ _))) :=
  CokernelCofork.ofπ cocone.π (by
    rw [← lift_d_comp_eq_zero_iff K e hj' hi hi' hk hk' cone hcone]
    exact cocone.condition)

/-- Auxiliary definition for `extend.leftHomologyData`. -/
noncomputable def isColimitCokernelCofork :
    IsColimit (cokernelCofork K e hj' hi hi' hk hk' cone hcone cocone) :=
  CokernelCofork.isColimitOfIsColimitOfIff' hcocone _
    (lift_d_comp_eq_zero_iff K e hj' hi hi' hk hk' cone hcone)

end leftHomologyData

open leftHomologyData in
/-- The left homology data of `(K.extend e).sc' i' j' k'` that is deduced
from a left homology data of `K.sc' i j k`. -/
@[simps]
noncomputable def leftHomologyData (h : (K.sc' i j k).LeftHomologyData) :
    ((K.extend e).sc' i' j' k').LeftHomologyData where
  K := h.K
  H := h.H
  i := h.i ≫ (extendXIso K e hj').inv
  π := h.π
  wi := by
    dsimp
    rw [assoc, ← comp_d_eq_zero_iff K e hj' hk hk']
    exact h.wi
  hi := isLimitKernelFork K e hj' hk hk' _ h.hi
  wπ := by
    dsimp
    rw [← lift_d_comp_eq_zero_iff K e hj' hi hi' hk hk' _ h.hi]
    exact h.wπ
  hπ := isColimitCokernelCofork K e hj' hi hi' hk hk' _ h.hi _ h.hπ

namespace rightHomologyData

variable (cocone : CokernelCofork (K.d i j)) (hcocone : IsColimit cocone)

/-- The cokernel cofork of `(K.extend e).d i' j'` that is deduced from a cokernel
cofork of `K.d i j`. -/
@[simp]
noncomputable def cokernelCofork : CokernelCofork ((K.extend e).d i' j') :=
  CokernelCofork.ofπ ((extendXIso K e hj').hom ≫ cocone.π) (by
    rw [← d_comp_eq_zero_iff K e hj' hi hi' cocone.π, cocone.condition])

/-- The colimit cokernel cofork of `(K.extend e).d i' j'` that is deduced from a
colimit cokernel cofork of `K.d i j`. -/
noncomputable def isColimitCokernelCofork : IsColimit (cokernelCofork K e hj' hi hi' cocone) :=
  CokernelCofork.isColimitOfIsColimitOfIff hcocone ((K.extend e).d i' j')
    (extendXIso K e hj') (d_comp_eq_zero_iff K e hj' hi hi')

variable (cone : KernelFork (hcocone.desc (CokernelCofork.ofπ (K.d j k) (K.d_comp_d i j k))))
  (hcone : IsLimit cone)

include hk hk' hcocone in
lemma d_comp_desc_eq_zero_iff' ⦃W : C⦄ (f' : cocone.pt ⟶ K.X k)
    (hf' : cocone.π ≫ f' = K.d j k)
    (f'' : cocone.pt ⟶ (K.extend e).X k')
    (hf'' : (extendXIso K e hj').hom ≫ cocone.π ≫ f'' = (K.extend e).d j' k')
    (φ : W ⟶ cocone.pt) :
    φ ≫ f' = 0 ↔ φ ≫ f'' = 0 := by
  by_cases hjk : c.Rel j k
  · have hk'' : e.f k = k' := by rw [← hk', ← hj', c'.next_eq' (e.rel hjk)]
    have : f' ≫ (K.extendXIso e hk'').inv = f'' := by
      apply Cofork.IsColimit.hom_ext hcocone
      rw [reassoc_of% hf', ← cancel_epi (extendXIso K e hj').hom, hf'',
        K.extend_d_eq e hj' hk'']
    rw [← cancel_mono (K.extendXIso e hk'').inv, zero_comp, assoc, this]
  · have h₁ : f' = 0 := by
      apply Cofork.IsColimit.hom_ext hcocone
      simp only [hf', comp_zero, K.shape _ _ hjk]
    have h₂ : f'' = 0 := by
      apply Cofork.IsColimit.hom_ext hcocone
      rw [← cancel_epi (extendXIso K e hj').hom, hf'', comp_zero, comp_zero,
        K.extend_d_from_eq_zero e j' k' j hj']
      rw [hk]
      exact hjk
    simp [h₁, h₂]

include hk hk' in
lemma d_comp_desc_eq_zero_iff ⦃W : C⦄ (φ : W ⟶ cocone.pt) :
    φ ≫ hcocone.desc (CokernelCofork.ofπ (K.d j k) (K.d_comp_d i j k)) = 0 ↔
      φ ≫ ((isColimitCokernelCofork K e hj' hi hi' cocone hcocone).desc
      (CokernelCofork.ofπ ((K.extend e).d j' k') (d_comp_d _ _ _ _))) = 0 :=
  d_comp_desc_eq_zero_iff' K e hj' hk hk' cocone hcocone _ (hcocone.fac _ _) _ (by
    simpa using (isColimitCokernelCofork K e hj' hi hi' cocone hcocone).fac _
      WalkingParallelPair.one) _

/-- Auxiliary definition for `extend.rightHomologyData`. -/
noncomputable def kernelFork :
    KernelFork ((isColimitCokernelCofork K e hj' hi hi' cocone hcocone).desc
      (CokernelCofork.ofπ ((K.extend e).d j' k') (d_comp_d _ _ _ _))) :=
  KernelFork.ofι cone.ι (by
    rw [← d_comp_desc_eq_zero_iff K e hj' hi hi' hk hk' cocone hcocone]
    exact cone.condition)

/-- Auxiliary definition for `extend.rightHomologyData`. -/
noncomputable def isLimitKernelFork :
    IsLimit (kernelFork K e hj' hi hi' hk hk' cocone hcocone cone) :=
  KernelFork.isLimitOfIsLimitOfIff' hcone _
    (d_comp_desc_eq_zero_iff K e hj' hi hi' hk hk' cocone hcocone)

end rightHomologyData

open rightHomologyData in
/-- The right homology data of `(K.extend e).sc' i' j' k'` that is deduced
from a right homology data of `K.sc' i j k`. -/
@[simps]
noncomputable def rightHomologyData (h : (K.sc' i j k).RightHomologyData) :
    ((K.extend e).sc' i' j' k').RightHomologyData where
  Q := h.Q
  H := h.H
  p := (extendXIso K e hj').hom ≫ h.p
  ι := h.ι
  wp := by
    dsimp
    rw [← d_comp_eq_zero_iff K e hj' hi hi']
    exact h.wp
  hp := isColimitCokernelCofork K e hj' hi hi' _ h.hp
  wι := by
    dsimp
    rw [← d_comp_desc_eq_zero_iff K e hj' hi hi' hk hk' _ h.hp]
    exact h.wι
  hι := isLimitKernelFork K e hj' hi hi' hk hk' _ h.hp _ h.hι

/-- Computation of the `g'` field of `extend.rightHomologyData`. -/
lemma rightHomologyData_g' (h : (K.sc' i j k).RightHomologyData) (hk'' : e.f k = k') :
    (rightHomologyData K e hj' hi hi' hk hk' h).g' = h.g' ≫ (K.extendXIso e hk'').inv := by
  rw [← cancel_epi h.p, ← cancel_epi (extendXIso K e hj').hom]
  have := (rightHomologyData K e hj' hi hi' hk hk' h).p_g'
  dsimp at this
  rw [assoc] at this
  rw [this, K.extend_d_eq e hj' hk'', h.p_g'_assoc, shortComplexFunctor'_obj_g]

/-- The homology data of `(K.extend e).sc' i' j' k'` that is deduced
from a homology data of `K.sc' i j k`. -/
@[simps]
noncomputable def homologyData (h : (K.sc' i j k).HomologyData) :
    ((K.extend e).sc' i' j' k').HomologyData where
  left := leftHomologyData K e hj' hi hi' hk hk' h.left
  right := rightHomologyData K e hj' hi hi' hk hk' h.right
  iso := h.iso

/-- The homology data of `(K.extend e).sc j'` that is deduced
from a homology data of `K.sc' i j k`. -/
@[simps!]
noncomputable def homologyData' (h : (K.sc' i j k).HomologyData) :
    ((K.extend e).sc j').HomologyData :=
  homologyData K e hj' hi rfl hk rfl h

end HomologyData

lemma hasHomology {j : ι} {j' : ι'} (hj' : e.f j = j') [K.HasHomology j] :
    (K.extend e).HasHomology j' :=
  ShortComplex.HasHomology.mk'
    (homologyData' K e hj' rfl rfl ((K.sc j).homologyData))

instance (j : ι) [K.HasHomology j] : (K.extend e).HasHomology (e.f j) :=
  hasHomology K e rfl

instance [∀ j, K.HasHomology j] (j' : ι') : (K.extend e).HasHomology j' := by
  by_cases h : ∃ j, e.f j = j'
  · obtain ⟨j, rfl⟩ := h
    infer_instance
  · have hj := isZero_extend_X K e j' (by tauto)
    exact ShortComplex.HasHomology.mk'
      (ShortComplex.HomologyData.ofZeros _ (hj.eq_of_tgt _ _) (hj.eq_of_src _ _))

end extend

lemma extend_exactAt (j' : ι') (hj' : ∀ j, e.f j ≠ j') :
    (K.extend e).ExactAt j' :=
  exactAt_of_isSupported _ e j' hj'

section

variable {j : ι} {j' : ι'} (hj' : e.f j = j') [K.HasHomology j] [L.HasHomology j]
  [(K.extend e).HasHomology j'] [(L.extend e).HasHomology j']

/-- The isomorphism `(K.extend e).cycles j' ≅ K.cycles j` when `e.f j = j'`. -/
noncomputable def extendCyclesIso :
    (K.extend e).cycles j' ≅ K.cycles j :=
  (extend.homologyData' K e hj' rfl rfl (K.sc j).homologyData).left.cyclesIso ≪≫
    (K.sc j).homologyData.left.cyclesIso.symm

/-- The isomorphism `(K.extend e).opcycles j' ≅ K.opcycles j` when `e.f j = j'`. -/
noncomputable def extendOpcyclesIso :
    (K.extend e).opcycles j' ≅ K.opcycles j :=
  (extend.homologyData' K e hj' rfl rfl (K.sc j).homologyData).right.opcyclesIso ≪≫
    (K.sc j).homologyData.right.opcyclesIso.symm

/-- The isomorphism `(K.extend e).homology j' ≅ K.homology j` when `e.f j = j'`. -/
noncomputable def extendHomologyIso :
    (K.extend e).homology j' ≅ K.homology j :=
  (extend.homologyData' K e hj' rfl rfl (K.sc j).homologyData).left.homologyIso ≪≫
    (K.sc j).homologyData.left.homologyIso.symm

include hj' in
lemma extend_exactAt_iff :
    (K.extend e).ExactAt j' ↔ K.ExactAt j := by
  simp only [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (K.extendHomologyIso e hj').isZero_iff

@[reassoc (attr := simp)]
lemma extendCyclesIso_hom_iCycles :
    (K.extendCyclesIso e hj').hom ≫ K.iCycles j =
      (K.extend e).iCycles j' ≫ (K.extendXIso e hj').hom := by
  rw [← cancel_epi (K.extendCyclesIso e hj').inv, Iso.inv_hom_id_assoc]
  dsimp [extendCyclesIso, iCycles]
  rw [assoc, ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles_assoc]
  dsimp
  rw [assoc, Iso.inv_hom_id, comp_id,
    ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i]

@[reassoc (attr := simp)]
lemma extendCyclesIso_inv_iCycles :
    (K.extendCyclesIso e hj').inv ≫ (K.extend e).iCycles j' =
      K.iCycles j ≫ (K.extendXIso e hj').inv := by
  simp only [← cancel_epi (K.extendCyclesIso e hj').hom, Iso.hom_inv_id_assoc,
    extendCyclesIso_hom_iCycles_assoc, Iso.hom_inv_id, comp_id]

@[reassoc (attr := simp)]
lemma homologyπ_extendHomologyIso_hom :
    (K.extend e).homologyπ j' ≫ (K.extendHomologyIso e hj').hom =
      (K.extendCyclesIso e hj').hom ≫ K.homologyπ j := by
  dsimp [extendHomologyIso, homologyπ]
  rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc,
    ← cancel_mono (K.sc j).homologyData.left.homologyIso.hom,
    assoc, assoc, assoc, Iso.inv_hom_id, comp_id,
    ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
  dsimp [extendCyclesIso]
  simp only [assoc, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
lemma homologyπ_extendHomologyIso_inv :
    K.homologyπ j ≫ (K.extendHomologyIso e hj').inv =
      (K.extendCyclesIso e hj').inv ≫ (K.extend e).homologyπ j' := by
  simp only [← cancel_mono (K.extendHomologyIso e hj').hom,
    assoc, Iso.inv_hom_id, comp_id, homologyπ_extendHomologyIso_hom, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
lemma pOpcycles_extendOpcyclesIso_inv :
    K.pOpcycles j ≫ (K.extendOpcyclesIso e hj').inv =
      (K.extendXIso e hj').inv ≫ (K.extend e).pOpcycles j' := by
  rw [← cancel_mono (K.extendOpcyclesIso e hj').hom, assoc, assoc, Iso.inv_hom_id, comp_id]
  dsimp [extendOpcyclesIso, pOpcycles]
  rw [ShortComplex.RightHomologyData.pOpcycles_comp_opcyclesIso_hom_assoc]
  dsimp
  rw [assoc, Iso.inv_hom_id_assoc, ShortComplex.RightHomologyData.p_comp_opcyclesIso_inv]
  rfl

@[reassoc (attr := simp)]
lemma pOpcycles_extendOpcyclesIso_hom :
    (K.extend e).pOpcycles j' ≫ (K.extendOpcyclesIso e hj').hom =
      (K.extendXIso e hj').hom ≫ K.pOpcycles j := by
  simp only [← cancel_mono (K.extendOpcyclesIso e hj').inv,
    assoc, Iso.hom_inv_id, comp_id, pOpcycles_extendOpcyclesIso_inv, Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]
lemma extendHomologyIso_hom_homologyι :
    (K.extendHomologyIso e hj').hom ≫ K.homologyι j =
      (K.extend e).homologyι j' ≫ (K.extendOpcyclesIso e hj').hom := by
  simp only [← cancel_epi ((K.extend e).homologyπ j'),
    homologyπ_extendHomologyIso_hom_assoc, homology_π_ι, extendCyclesIso_hom_iCycles_assoc,
    homology_π_ι_assoc, pOpcycles_extendOpcyclesIso_hom]

@[reassoc (attr := simp)]
lemma extendHomologyIso_inv_homologyι :
    (K.extendHomologyIso e hj').inv ≫ (K.extend e).homologyι j' =
      K.homologyι j ≫ (K.extendOpcyclesIso e hj').inv := by
  simp only [← cancel_epi (K.extendHomologyIso e hj').hom,
    Iso.hom_inv_id_assoc, extendHomologyIso_hom_homologyι_assoc, Iso.hom_inv_id, comp_id]

variable {K L}

@[reassoc (attr := simp)]
lemma extendCyclesIso_hom_naturality :
    cyclesMap (extendMap φ e) j' ≫ (L.extendCyclesIso e hj').hom =
      (K.extendCyclesIso e hj').hom ≫ cyclesMap φ j := by
  simp [← cancel_mono (L.iCycles j), extendMap_f φ e hj']

@[reassoc (attr := simp)]
lemma extendHomologyIso_hom_naturality :
    homologyMap (extendMap φ e) j' ≫ (L.extendHomologyIso e hj').hom =
      (K.extendHomologyIso e hj').hom ≫ homologyMap φ j := by
  simp [← cancel_epi ((K.extend e).homologyπ _)]

include hj' in
lemma quasiIsoAt_extendMap_iff :
    QuasiIsoAt (extendMap φ e) j' ↔ QuasiIsoAt φ j := by
  simp only [quasiIsoAt_iff_isIso_homologyMap]
  exact (MorphismProperty.isomorphisms C).arrow_mk_iso_iff
    (Arrow.isoMk (K.extendHomologyIso e hj') (L.extendHomologyIso e hj'))

end

lemma quasiIso_extendMap_iff [∀ j, K.HasHomology j] [∀ j, L.HasHomology j] :
    QuasiIso (extendMap φ e) ↔ QuasiIso φ := by
  simp only [quasiIso_iff, ← fun j ↦ quasiIsoAt_extendMap_iff φ e (j := j) (hj' := rfl)]
  constructor
  · tauto
  · intro h j'
    by_cases hj' : ∃ j, e.f j = j'
    · obtain ⟨j, rfl⟩ := hj'
      exact h j
    · rw [quasiIsoAt_iff_exactAt]
      all_goals
        exact extend_exactAt _ _ _ (by simpa using hj')

end HomologicalComplex
