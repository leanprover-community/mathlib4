import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

-- mostly from LTE

open CategoryTheory Limits ZeroObject Category

namespace CategoryTheory

variable {C : Type*} [Category C] [HasZeroMorphisms C]

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

variable {ι ι' : Type*} (c : ComplexShape ι) (c' : ComplexShape ι')

lemma Option.eq_none_or_eq_some (x : Option ι) :
    x = none ∨ ∃ y, x = some y := by
  cases x
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

namespace ComplexShape

structure Embed where
  f : ι → ι'
  injective_f : Function.Injective f
  rel {i₁ i₂ : ι} (h : c.Rel i₁ i₂) : c'.Rel (f i₁) (f i₂)

namespace Embed

variable {c c'}
variable (e : Embed c c')

open Classical in
noncomputable def r (i' : ι') : Option ι :=
  if h : ∃ (i : ι), e.f i = i'
  then some h.choose
  else none

lemma r_eq_some {i : ι} {i' : ι'} (hi : e.f i = i') :
    e.r i' = some i := by
  have h : ∃ (i : ι), e.f i = i' := ⟨i, hi⟩
  have : h.choose = i := e.injective_f (h.choose_spec.trans (hi.symm))
  dsimp [r]
  rw [dif_pos ⟨i, hi⟩, this]

lemma f_eq_of_r_eq_some {i : ι} {i' : ι'} (hi : e.r i' = some i) :
    e.f i = i' := by
  by_cases h : ∃ (k : ι), e.f k = i'
  · obtain ⟨k, hk⟩ := h
    have : some i = some k := by
      rw [← e.r_eq_some hk, hi]
    rw [← hk]
    congr 1
    simpa using this
  · simp [r, dif_neg h] at hi

end Embed

end ComplexShape

namespace HomologicalComplex

variable {c c'} {C : Type*} [Category C] [HasZeroMorphisms C]
  [HasZeroObject C]

variable (K : HomologicalComplex C c) (e : c.Embed c')

namespace extend

noncomputable def X : Option ι → C
  | some x => K.X x
  | none => 0

noncomputable def XIso {i : Option ι} {j : ι} (hj : i = some j) :
    X K i ≅ K.X j := eqToIso (by subst hj; rfl)

lemma isZero_X {i : Option ι} (hi : i = none) :
    IsZero (X K i) := by
  subst hi
  exact Limits.isZero_zero _

noncomputable def d : ∀ (i j : Option ι), extend.X K i ⟶ extend.X K j
  | none, _ => 0
  | some i, some j => K.d i j
  | some _, none => 0

lemma d_none_eq_zero (i j : Option ι) (hi : i = none) :
    d K i j = 0 := by subst hi; rfl

lemma d_none_eq_zero' (i j : Option ι) (hj : j = none) :
    d K i j = 0 := by subst hj; cases i <;> rfl

lemma d_eq {i j : Option ι} {a b : ι}
    (hi : i = some a) (hj : j = some b) :
    d K i j = (XIso K hi).hom ≫ K.d a b ≫ (XIso K hj).inv := by
  subst hi hj
  dsimp [XIso, d]
  erw [id_comp, comp_id]

end extend

noncomputable def extend : HomologicalComplex C c' where
  X i' := extend.X K (e.r i')
  d i' j' := extend.d K (e.r i') (e.r j')
  shape i' j' h := by
    dsimp
    obtain hi'|⟨i, hi⟩ := (e.r i').eq_none_or_eq_some
    · rw [extend.d_none_eq_zero K _ _ hi']
    · obtain hj'|⟨j, hj⟩ := (e.r j').eq_none_or_eq_some
      · rw [extend.d_none_eq_zero' K _ _ hj']
      · rw [extend.d_eq K hi hj,K.shape, zero_comp, comp_zero]
        obtain rfl := e.f_eq_of_r_eq_some hi
        obtain rfl := e.f_eq_of_r_eq_some hj
        intro hij
        exact h (e.rel hij)
  d_comp_d' i' j' k' _ _ := by
    dsimp
    obtain hi'|⟨i, hi⟩ := (e.r i').eq_none_or_eq_some
    · rw [extend.d_none_eq_zero K _ _ hi', zero_comp]
    · obtain hj'|⟨j, hj⟩ := (e.r j').eq_none_or_eq_some
      · rw [extend.d_none_eq_zero K _ _ hj', comp_zero]
      · obtain hk'|⟨k, hk⟩ := (e.r k').eq_none_or_eq_some
        · rw [extend.d_none_eq_zero' K _ _ hk', comp_zero]
        · rw [extend.d_eq K hi hj,
            extend.d_eq K hj hk, assoc, assoc,
            Iso.inv_hom_id_assoc, K.d_comp_d_assoc, zero_comp, comp_zero]

noncomputable def extendXIso {i' : ι'} {i : ι} (h : e.f i = i') :
    (K.extend e).X i' ≅ K.X i :=
  extend.XIso K (e.r_eq_some h)

lemma isZero_extend_X (i' : ι') (hi' : e.r i' = none) :
    IsZero ((K.extend e).X i') :=
  extend.isZero_X K hi'

lemma extend_d_eq {i' j' : ι'} {i j : ι} (hi : e.f i = i') (hj : e.f j = j') :
    (K.extend e).d i' j' = (K.extendXIso e hi).hom ≫ K.d i j ≫
      (K.extendXIso e hj).inv := by
  apply extend.d_eq

lemma extend_d_from_eq_zero (i' j' : ι') (i : ι) (hi : e.f i = i') (hi' : ¬ c.Rel i (c.next i)) :
    (K.extend e).d i' j' = 0 := by
  obtain hj'|⟨j, hj⟩ := (e.r j').eq_none_or_eq_some
  · exact extend.d_none_eq_zero' _ _ _ hj'
  · rw [extend_d_eq K e hi (e.f_eq_of_r_eq_some hj), K.shape, zero_comp, comp_zero]
    intro hij
    obtain rfl := c.next_eq' hij
    exact hi' hij

lemma extend_d_to_eq_zero (i' j' : ι') (j : ι) (hj : e.f j = j') (hj' : ¬ c.Rel (c.prev j) j) :
    (K.extend e).d i' j' = 0 := by
  obtain hi'|⟨i, hi⟩ := (e.r i').eq_none_or_eq_some
  · exact extend.d_none_eq_zero _ _ _ hi'
  · rw [extend_d_eq K e (e.f_eq_of_r_eq_some hi) hj, K.shape, zero_comp, comp_zero]
    intro hij
    obtain rfl := c.prev_eq' hij
    exact hj' hij

namespace extend

section LeftHomologyData

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

lemma kernelFork_condition :
    (Fork.ι cone ≫ (extendXIso K e hj').inv) ≫ (extend K e).d j' k' = 0 := by
  rw [assoc, ← comp_d_eq_zero_iff K e hj' hk hk' cone.ι, cone.condition]

@[simp]
noncomputable def kernelFork : KernelFork ((K.extend e).d j' k') :=
  KernelFork.ofι (Fork.ι cone ≫ (extendXIso K e hj').inv)
    (by rw [assoc, ← comp_d_eq_zero_iff K e hj' hk hk' cone.ι, cone.condition])

noncomputable def isLimitKernelFork : IsLimit (kernelFork K e hj' hk hk' cone) :=
  KernelFork.isLimitOfIsLimitOfIff' cone hcone ((K.extend e).d j' k')
    (extendXIso K e hj').symm (comp_d_eq_zero_iff K e hj' hk hk')

variable (cocone : CokernelCofork (hcone.lift (KernelFork.ofι (K.d i j) (K.d_comp_d i j k))))
  (hcocone : IsColimit cocone)

lemma lift_d_comp_eq_zero_iff ⦃W : C⦄ (φ : cone.pt ⟶ W) :
    hcone.lift (KernelFork.ofι (K.d i j) (K.d_comp_d i j k)) ≫ φ = 0 ↔
      ((isLimitKernelFork K e hj' hk hk' cone hcone).lift
      (KernelFork.ofι ((K.extend e).d i' j') (d_comp_d _ _ _ _))) ≫ φ = 0 := by
  have ⟨f', h₁⟩ : ∃ f', f' = hcone.lift (KernelFork.ofι (K.d i j) (K.d_comp_d i j k)) := ⟨_, rfl⟩
  have ⟨f'', h₂⟩ : ∃ f'', f'' = ((isLimitKernelFork K e hj' hk hk' cone hcone).lift
      (KernelFork.ofι ((K.extend e).d i' j') (d_comp_d _ _ _ _))) := ⟨_, rfl⟩
  suffices f' ≫ φ = 0 ↔ f'' ≫ φ = 0 by simpa only [h₁, h₂] using this
  have hf' : f' ≫ cone.ι = K.d i j := by rw [h₁]; apply hcone.fac _
  have hf'' : f'' ≫ cone.ι = (K.extend e).d i' j' ≫ (extendXIso K e hj').hom := by
    rw [h₂, ← cancel_mono (extendXIso K e hj').inv, assoc, assoc, Iso.hom_inv_id, comp_id]
    exact ((isLimitKernelFork K e hj' hk hk' cone hcone).fac _) WalkingParallelPair.zero
  by_cases hij : c.Rel i j
  · have hi'' : e.f i = i' := by rw [← hi', ← hj', c'.prev_eq' (e.rel hij)]
    have : (K.extendXIso e hi'').hom ≫ f' = f'' := by
      apply Fork.IsLimit.hom_ext hcone
      rw [assoc, hf', hf'', K.extend_d_eq e hi'' hj', assoc, assoc, Iso.inv_hom_id, comp_id]
    rw [← cancel_epi (K.extendXIso e hi'').hom, comp_zero, ← this, assoc]
  · have h₃ : f' = 0 := by
      apply Fork.IsLimit.hom_ext hcone
      simp only [zero_comp, hf', K.shape _ _ hij]
    have h₄ : f'' = 0 := by
      apply Fork.IsLimit.hom_ext hcone
      dsimp
      rw [hf'', zero_comp, K.extend_d_to_eq_zero e i' j' j hj', zero_comp]
      rw [hi]
      exact hij
    simp [h₃, h₄]

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

variable (h : (K.sc' i j k).LeftHomologyData)

noncomputable def leftHomologyData  :
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

end LeftHomologyData

end extend

end HomologicalComplex
