import Mathlib.Algebra.Homology.Embedding
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

open CategoryTheory Limits Category

variable {C : Type*} [Category C] [HasZeroMorphisms C]

namespace CategoryTheory

namespace Limits

namespace KernelFork

variable {X Y : C} {g : X ⟶ Y} (c : KernelFork g) (hc : IsLimit c)

def isLimitOfIsLimitOfIff {Y' : C} (g' : X ⟶ Y')
    (iff : ∀ ⦃W : C⦄ (φ : W ⟶ X), φ ≫ g = 0 ↔ φ ≫ g' = 0) :
    IsLimit (KernelFork.ofι (f := g') c.ι (by rw [← iff, c.condition])) :=
  KernelFork.IsLimit.ofι _ _
    (fun s hs => hc.lift (KernelFork.ofι s (by rw [iff, hs])))
    (fun s hs => hc.fac _ _)
    (fun s hs m hm => Fork.IsLimit.hom_ext hc (by simp [hm]))

def isLimitOfIsLimitOfIff' {X' Y' : C} (g' : X' ⟶ Y') (e : X ≅ X')
    (iff : ∀ ⦃W : C⦄ (φ : W ⟶ X), φ ≫ g = 0 ↔ φ ≫ e.hom ≫ g' = 0) :
    IsLimit (KernelFork.ofι (f := g') (c.ι ≫ e.hom) (by simp [← iff])) := by
  let e' : parallelPair g' 0 ≅ parallelPair (e.hom ≫ g') 0 :=
    parallelPair.ext e.symm (Iso.refl _) (by simp) (by simp)
  refine (IsLimit.postcomposeHomEquiv e' _).1
    (IsLimit.ofIsoLimit (isLimitOfIsLimitOfIff c hc (e.hom ≫ g') iff)
      (Fork.ext (Iso.refl _) ?_))
  change 𝟙 _ ≫ (c.ι ≫ e.hom) ≫ e.inv = c.ι
  simp

end KernelFork

namespace CokernelCofork

variable {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f) (hc : IsColimit c)

def isColimitOfIsColimitOfIff {X' : C} (f' : X' ⟶ Y)
    (iff : ∀ ⦃W : C⦄ (φ : Y ⟶ W), f ≫ φ = 0 ↔ f' ≫ φ = 0) :
    IsColimit (CokernelCofork.ofπ (f := f') c.π (by rw [← iff, c.condition])) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun s hs => hc.desc (CokernelCofork.ofπ s (by rw [iff, hs])))
    (fun s hs => hc.fac _ _)
    (fun s hs m hm => Cofork.IsColimit.hom_ext hc (by simp [hm]))

def isColimitOfIsColimitOfIff' {X' Y' : C} (f' : X' ⟶ Y') (e : Y' ≅ Y)
    (iff : ∀ ⦃W : C⦄ (φ : Y ⟶ W), f ≫ φ = 0 ↔ f' ≫ e.hom ≫ φ = 0) :
    IsColimit (CokernelCofork.ofπ (f := f') (e.hom ≫ c.π) (by simp [← iff])) := by
  let e' : parallelPair (f' ≫ e.hom) 0 ≅ parallelPair f' 0 :=
    parallelPair.ext (Iso.refl _) e.symm (by simp) (by simp)
  refine (IsColimit.precomposeHomEquiv e' _).1
    (IsColimit.ofIsoColimit (isColimitOfIsColimitOfIff c hc (f' ≫ e.hom)
      (by simpa only [assoc] using iff)) (Cofork.ext (Iso.refl _) ?_))
  change c.π ≫ 𝟙 _ = e.inv ≫ e.hom ≫ c.π
  simp

end CokernelCofork

end Limits

end CategoryTheory

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category C] [HasZeroMorphisms C]
  [HasZeroObject C]

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

namespace extend

section HomologyData

variable {i j k : ι} {i' j' k' : ι'} (hj' : e.f j = j')
  (hi : c.prev j = i) (hi' : c'.prev j' = i') (hk : c.next j = k) (hk' : c'.next j' = k')

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

namespace LeftHomologyData

variable (cone : KernelFork (K.d j k)) (hcone : IsLimit cone)

@[simp]
noncomputable def kernelFork : KernelFork ((K.extend e).d j' k') :=
  KernelFork.ofι (cone.ι ≫ (extendXIso K e hj').inv)
    (by rw [assoc, ← comp_d_eq_zero_iff K e hj' hk hk' cone.ι, cone.condition])

noncomputable def isLimitKernelFork : IsLimit (kernelFork K e hj' hk hk' cone) :=
  KernelFork.isLimitOfIsLimitOfIff' cone hcone ((K.extend e).d j' k')
    (extendXIso K e hj').symm (comp_d_eq_zero_iff K e hj' hk hk')

variable (cocone : CokernelCofork (hcone.lift (KernelFork.ofι (K.d i j) (K.d_comp_d i j k))))
  (hcocone : IsColimit cocone)

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

lemma lift_d_comp_eq_zero_iff ⦃W : C⦄ (φ : cone.pt ⟶ W) :
    hcone.lift (KernelFork.ofι (K.d i j) (K.d_comp_d i j k)) ≫ φ = 0 ↔
      ((isLimitKernelFork K e hj' hk hk' cone hcone).lift
      (KernelFork.ofι ((K.extend e).d i' j') (d_comp_d _ _ _ _))) ≫ φ = 0 :=
  lift_d_comp_eq_zero_iff' K e hj' hi hi' cone hcone _ (hcone.fac _ _) _
    (IsLimit.fac _ _ WalkingParallelPair.zero) _

noncomputable def cokernelCofork :
    CokernelCofork ((isLimitKernelFork K e hj' hk hk' cone hcone).lift
      (KernelFork.ofι ((K.extend e).d i' j') (d_comp_d _ _ _ _))) :=
  CokernelCofork.ofπ cocone.π (by
    rw [← lift_d_comp_eq_zero_iff K e hj' hi hi' hk hk' cone hcone]
    exact cocone.condition)

noncomputable def isColimitCokernelCofork :
    IsColimit (cokernelCofork K e hj' hi hi' hk hk' cone hcone cocone) :=
  CokernelCofork.isColimitOfIsColimitOfIff cocone hcocone _
    (lift_d_comp_eq_zero_iff K e hj' hi hi' hk hk' cone hcone)

end LeftHomologyData

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
  hi := LeftHomologyData.isLimitKernelFork K e hj' hk hk' _ h.hi
  wπ := by
    erw [← LeftHomologyData.lift_d_comp_eq_zero_iff K e hj' hi hi' hk hk' _ h.hi]
    exact h.wπ
  hπ := LeftHomologyData.isColimitCokernelCofork K e hj' hi hi' hk hk' _ h.hi _ h.hπ

lemma d_comp_eq_zero_iff ⦃W : C⦄ (φ : K.X j ⟶ W) :
    K.d i j ≫ φ = 0 ↔ (K.extend e).d i' j' ≫ (K.extendXIso e hj').hom ≫ φ = 0 := by
  by_cases hij : c.Rel i j
  · have hi' : e.f i = i' := by rw [← hi', ← hj', c'.prev_eq' (e.rel hij)]
    rw [K.extend_d_eq e hi' hj', assoc, assoc, Iso.inv_hom_id_assoc,
      ← cancel_epi (K.extendXIso e hi').inv, comp_zero, Iso.inv_hom_id_assoc]
  · simp only [K.shape _ _ hij, zero_comp, comp_zero, true_iff]
    rw [K.extend_d_to_eq_zero e i' j' j hj', zero_comp]
    rw [hi]
    exact hij

namespace RightHomologyData

variable (cocone : CokernelCofork (K.d i j)) (hcocone : IsColimit cocone)

@[simp]
noncomputable def cokernelCofork : CokernelCofork ((K.extend e).d i' j') :=
  CokernelCofork.ofπ ((extendXIso K e hj').hom ≫ cocone.π)
    (by rw [← d_comp_eq_zero_iff K e hj' hi hi' cocone.π, cocone.condition])

noncomputable def isColimitCokernelCofork : IsColimit (cokernelCofork K e hj' hi hi' cocone) :=
  CokernelCofork.isColimitOfIsColimitOfIff' cocone hcocone ((K.extend e).d i' j')
    (extendXIso K e hj') (d_comp_eq_zero_iff K e hj' hi hi')

variable (cone : KernelFork (hcocone.desc (CokernelCofork.ofπ (K.d j k) (K.d_comp_d i j k))))
  (hcone : IsLimit cone)

lemma lift_d_comp_eq_zero_iff' (g' : cocone.pt ⟶ K.X k)
    (hg' : cocone.π ≫ g' = K.d j k)
    (g'' : cocone.pt ⟶ (K.extend e).X k')
    (hg'' : (extendXIso K e hj').hom ≫ cocone.π ≫ g'' = (K.extend e).d j' k')
    ⦃W : C⦄ (φ : W ⟶ cocone.pt) :
    φ ≫ g' = 0 ↔ φ ≫ g'' = 0 := by
  by_cases hjk : c.Rel j k
  · have hk'' : e.f k = k' := by rw [← hk', ← hj', c'.next_eq' (e.rel hjk)]
    have : g' ≫ (K.extendXIso e hk'').inv = g'' := by
      apply Cofork.IsColimit.hom_ext hcocone
      rw [reassoc_of% hg', ← cancel_epi (extendXIso K e hj').hom, hg'',
        K.extend_d_eq e hj' hk'']
    rw [← cancel_mono (K.extendXIso e hk'').hom, assoc, zero_comp, ← this, assoc,
      Iso.inv_hom_id, comp_id]
  · have h₁ : g' = 0 := by
      apply Cofork.IsColimit.hom_ext hcocone
      simp only [comp_zero, hg', K.shape _ _ hjk]
    have h₂ : g'' = 0 := by
      apply Cofork.IsColimit.hom_ext hcocone
      dsimp
      rw [← cancel_epi (extendXIso K e hj').hom, hg'', comp_zero, comp_zero,
        K.extend_d_from_eq_zero e j' k' j hj']
      rw [hk]
      exact hjk
    simp [h₁, h₂]

lemma comp_desc_d_eq_zero_iff ⦃W : C⦄ (φ : W ⟶ cocone.pt) :
    φ ≫ hcocone.desc (CokernelCofork.ofπ (K.d j k) (by simp)) = 0 ↔
      φ ≫ (isColimitCokernelCofork K e hj' hi hi' cocone hcocone).desc
    (CokernelCofork.ofπ ((K.extend e).d j' k') (by simp)) = 0 :=
  lift_d_comp_eq_zero_iff' K e hj' hk hk' cocone hcocone _ (by apply hcocone.fac) _
    (by
      rw [← assoc]
      exact (isColimitCokernelCofork K e hj' hi hi' cocone hcocone).fac _
        WalkingParallelPair.one) _

noncomputable def kernelFork :
    KernelFork ((isColimitCokernelCofork K e hj' hi hi' cocone hcocone).desc
      (CokernelCofork.ofπ ((K.extend e).d j' k') (d_comp_d _ _ _ _))) :=
  KernelFork.ofι cone.ι (by
    rw [← comp_desc_d_eq_zero_iff K e hj' hi hi' hk hk' cocone hcocone]
    exact cone.condition)

noncomputable def isLimitLernelFork :
    IsLimit (kernelFork K e hj' hi hi' hk hk' cocone hcocone cone) :=
  KernelFork.isLimitOfIsLimitOfIff cone hcone _
    (comp_desc_d_eq_zero_iff K e hj' hi hi' hk hk' cocone hcocone)

end RightHomologyData

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
  hp := RightHomologyData.isColimitCokernelCofork K e hj' hi hi' _ h.hp
  wι := by
    erw [← RightHomologyData.comp_desc_d_eq_zero_iff K e hj' hi hi' hk hk' _ h.hp]
    exact h.wι
  hι := RightHomologyData.isLimitLernelFork K e hj' hi hi' hk hk' _ h.hp _ h.hι

@[simps]
noncomputable def homologyData (h : (K.sc' i j k).HomologyData) :
    ((K.extend e).sc' i' j' k').HomologyData where
  left := leftHomologyData K e hj' hi hi' hk hk' h.left
  right := rightHomologyData K e hj' hi hi' hk hk' h.right
  iso := h.iso

@[simps!]
noncomputable def homologyData' (h : (K.sc' i j k).HomologyData) :
    ((K.extend e).sc j').HomologyData :=
  homologyData K e hj' hi rfl hk rfl h

end HomologyData

variable {j : ι} {j' : ι'} (hj' : e.f j = j')

lemma hasHomology [K.HasHomology j] : (K.extend e).HasHomology j' :=
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

section

variable {j : ι} {j' : ι'} (hj' : e.f j = j') [K.HasHomology j] [L.HasHomology j]
  [(K.extend e).HasHomology j'] [(L.extend e).HasHomology j']

noncomputable def extendCyclesIso :
    (K.extend e).cycles j' ≅ K.cycles j :=
  (extend.homologyData' K e hj' rfl rfl (K.sc j).homologyData).left.cyclesIso ≪≫
    (K.sc j).homologyData.left.cyclesIso.symm

noncomputable def extendOpcyclesIso :
    (K.extend e).opcycles j' ≅ K.opcycles j :=
  (extend.homologyData' K e hj' rfl rfl (K.sc j).homologyData).right.opcyclesIso ≪≫
    (K.sc j).homologyData.right.opcyclesIso.symm

noncomputable def extendHomologyIso :
    (K.extend e).homology j' ≅ K.homology j :=
  (extend.homologyData' K e hj' rfl rfl (K.sc j).homologyData).left.homologyIso ≪≫
    (K.sc j).homologyData.left.homologyIso.symm

@[reassoc (attr := simp)]
lemma extendCyclesIso_hom_iCycles :
    (K.extendCyclesIso e hj').hom ≫ K.iCycles j =
      (K.extend e).iCycles j' ≫ (K.extendXIso e hj').hom := by
  rw [← cancel_epi (K.extendCyclesIso e hj').inv, Iso.inv_hom_id_assoc]
  dsimp [extendCyclesIso]
  rw [assoc]
  erw [ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles_assoc]
  dsimp
  rw [assoc, Iso.inv_hom_id, comp_id]
  erw [ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i]
  rfl

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
  dsimp [extendHomologyIso]
  erw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc]
  rw [← cancel_mono (K.sc j).homologyData.left.homologyIso.hom,
    assoc, assoc, assoc, Iso.inv_hom_id, comp_id]
  erw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
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
  dsimp [extendOpcyclesIso]
  erw [ShortComplex.RightHomologyData.pOpcycles_comp_opcyclesIso_hom_assoc]
  dsimp
  rw [assoc, Iso.inv_hom_id_assoc]
  erw [ShortComplex.RightHomologyData.p_comp_opcyclesIso_inv]
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

end

end HomologicalComplex
