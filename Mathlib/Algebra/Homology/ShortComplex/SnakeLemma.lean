import Mathlib.Algebra.Homology.ShortComplex.Refinements
import Mathlib.CategoryTheory.Abelian.Opposite
import Mathlib.CategoryTheory.Adjunction.Limits

namespace CategoryTheory

open Category Limits Preadditive

variable (C : Type _) [Category C] [Abelian C]

namespace ShortComplex

structure SnakeInput where
  L₀ : ShortComplex C
  L₁ : ShortComplex C
  L₂ : ShortComplex C
  L₃ : ShortComplex C
  v₀₁ : L₀ ⟶ L₁
  v₁₂ : L₁ ⟶ L₂
  v₂₃ : L₂ ⟶ L₃
  w₀₂ : v₀₁ ≫ v₁₂ = 0 := by aesop_cat
  w₁₃ : v₁₂ ≫ v₂₃ = 0 := by aesop_cat
  h₀ : IsLimit (KernelFork.ofι _ w₀₂)
  h₃ : IsColimit (CokernelCofork.ofπ _ w₁₃)
  epi_L₁_g : Epi L₁.g
  L₁_exact  : L₁.Exact
  mono_L₂_f : Mono L₂.f
  L₂_exact : L₂.Exact

initialize_simps_projections SnakeInput (-h₀, -h₃)

namespace SnakeInput

attribute [reassoc (attr := simp)] w₀₂ w₁₃

variable {C}
variable (S : SnakeInput C)

attribute [instance] epi_L₁_g
attribute [instance] mono_L₂_f

@[simps]
noncomputable def op : SnakeInput Cᵒᵖ where
  L₀ := S.L₃.op
  L₁ := S.L₂.op
  L₂ := S.L₁.op
  L₃ := S.L₀.op
  epi_L₁_g := by dsimp ; infer_instance
  mono_L₂_f := by dsimp ; infer_instance
  v₀₁ := opMap S.v₂₃
  v₁₂ := opMap S.v₁₂
  v₂₃ := opMap S.v₀₁
  w₀₂ := congr_arg opMap S.w₁₃
  w₁₃ := congr_arg opMap S.w₀₂
  h₀ := isLimitForkMapOfIsLimit'
    (ShortComplex.opEquiv C).functor _ (CokernelCofork.IsColimit.ofπOp _ _ S.h₃)
  h₃ := isColimitCoforkMapOfIsColimit'
    (ShortComplex.opEquiv C).functor _ (KernelFork.IsLimit.ofιOp _ _ S.h₀)
  L₁_exact := S.L₂_exact.op
  L₂_exact := S.L₁_exact.op

@[reassoc (attr := simp)] lemma w₀₂_τ₁ : S.v₀₁.τ₁ ≫ S.v₁₂.τ₁ = 0 := by
  rw [← comp_τ₁, S.w₀₂, zero_τ₁]
@[reassoc (attr := simp)] lemma w₀₂_τ₂ : S.v₀₁.τ₂ ≫ S.v₁₂.τ₂ = 0 := by
  rw [← comp_τ₂, S.w₀₂, zero_τ₂]
@[reassoc (attr := simp)] lemma w₀₂_τ₃ : S.v₀₁.τ₃ ≫ S.v₁₂.τ₃ = 0 := by
  rw [← comp_τ₃, S.w₀₂, zero_τ₃]
@[reassoc (attr := simp)] lemma w₁₃_τ₁ : S.v₁₂.τ₁ ≫ S.v₂₃.τ₁ = 0 := by
  rw [← comp_τ₁, S.w₁₃, zero_τ₁]
@[reassoc (attr := simp)] lemma w₁₃_τ₂ : S.v₁₂.τ₂ ≫ S.v₂₃.τ₂ = 0 := by
  rw [← comp_τ₂, S.w₁₃, zero_τ₂]
@[reassoc (attr := simp)] lemma w₁₃_τ₃ : S.v₁₂.τ₃ ≫ S.v₂₃.τ₃ = 0 := by
  rw [← comp_τ₃, S.w₁₃, zero_τ₃]

noncomputable def h₀τ₁ : IsLimit (KernelFork.ofι S.v₀₁.τ₁ S.w₀₂_τ₁) :=
isLimitForkMapOfIsLimit' π₁ S.w₀₂ S.h₀
noncomputable def h₀τ₂ : IsLimit (KernelFork.ofι S.v₀₁.τ₂ S.w₀₂_τ₂) :=
isLimitForkMapOfIsLimit' π₂ S.w₀₂ S.h₀
noncomputable def h₀τ₃ : IsLimit (KernelFork.ofι S.v₀₁.τ₃ S.w₀₂_τ₃) :=
isLimitForkMapOfIsLimit' π₃ S.w₀₂ S.h₀

instance mono_v₀₁_τ₁ : Mono S.v₀₁.τ₁ := mono_of_isLimit_fork S.h₀τ₁
instance mono_v₀₁_τ₂ : Mono S.v₀₁.τ₂ := mono_of_isLimit_fork S.h₀τ₂
instance mono_v₀₁_τ₃ : Mono S.v₀₁.τ₃ := mono_of_isLimit_fork S.h₀τ₃

lemma exact_C₁_up : (ShortComplex.mk S.v₀₁.τ₁ S.v₁₂.τ₁
    (by rw [← comp_τ₁, S.w₀₂, zero_τ₁])).Exact :=
  exact_of_f_is_kernel _ S.h₀τ₁
lemma exact_C₂_up : (ShortComplex.mk S.v₀₁.τ₂ S.v₁₂.τ₂
    (by rw [← comp_τ₂, S.w₀₂, zero_τ₂])).Exact :=
  exact_of_f_is_kernel _ S.h₀τ₂
lemma exact_C₃_up : (ShortComplex.mk S.v₀₁.τ₃ S.v₁₂.τ₃
    (by rw [← comp_τ₃, S.w₀₂, zero_τ₃])).Exact :=
  exact_of_f_is_kernel _ S.h₀τ₃

instance mono_L₀_f [Mono S.L₁.f] : Mono S.L₀.f := by
  have : Mono (S.L₀.f ≫ S.v₀₁.τ₂) := by
    rw [← S.v₀₁.comm₁₂]
    apply mono_comp
  exact mono_of_mono _ S.v₀₁.τ₂

noncomputable def h₃_τ₁ : IsColimit (CokernelCofork.ofπ S.v₂₃.τ₁ S.w₁₃_τ₁) :=
  isColimitCoforkMapOfIsColimit' π₁ S.w₁₃ S.h₃
noncomputable def h₃_τ₂ : IsColimit (CokernelCofork.ofπ S.v₂₃.τ₂ S.w₁₃_τ₂) :=
  isColimitCoforkMapOfIsColimit' π₂ S.w₁₃ S.h₃
noncomputable def h₃_τ₃ : IsColimit (CokernelCofork.ofπ S.v₂₃.τ₃ S.w₁₃_τ₃) :=
  isColimitCoforkMapOfIsColimit' π₃ S.w₁₃ S.h₃

instance epi_v₂₃_τ₁ : Epi S.v₂₃.τ₁ := epi_of_isColimit_cofork S.h₃_τ₁
instance epi_v₂₃_τ₂ : Epi S.v₂₃.τ₂ := epi_of_isColimit_cofork S.h₃_τ₂
instance epi_v₂₃_τ₃ : Epi S.v₂₃.τ₃ := epi_of_isColimit_cofork S.h₃_τ₃

lemma exact_C₁_down: (ShortComplex.mk S.v₁₂.τ₁ S.v₂₃.τ₁
    (by rw [← comp_τ₁, S.w₁₃, zero_τ₁])).Exact :=
  exact_of_g_is_cokernel _ S.h₃_τ₁
lemma exact_C₂_down : (ShortComplex.mk S.v₁₂.τ₂ S.v₂₃.τ₂
    (by rw [← comp_τ₂, S.w₁₃, zero_τ₂])).Exact :=
  exact_of_g_is_cokernel _ S.h₃_τ₂
lemma exact_C₃_down : (ShortComplex.mk S.v₁₂.τ₃ S.v₂₃.τ₃
    (by rw [← comp_τ₃, S.w₁₃, zero_τ₃])).Exact :=
  exact_of_g_is_cokernel _ S.h₃_τ₃

instance epi_L₃_g [Epi S.L₂.g] : Epi S.L₃.g := by
  have : Epi (S.v₂₃.τ₂ ≫ S.L₃.g) := by
    rw [S.v₂₃.comm₂₃]
    apply epi_comp
  exact epi_of_epi S.v₂₃.τ₂ _

lemma ex₀ : S.L₀.Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  obtain ⟨A₁, π₁, hπ₁, y₁, hy₁⟩ := S.L₁_exact.exact_up_to_refinements (x₂ ≫ S.v₀₁.τ₂) (by
    rw [assoc, S.v₀₁.comm₂₃, reassoc_of% hx₂, zero_comp])
  have hy₁' : y₁ ≫ S.v₁₂.τ₁ = 0 := by
    simp only [← cancel_mono S.L₂.f, assoc, zero_comp, S.v₁₂.comm₁₂,
      ← reassoc_of% hy₁, w₀₂_τ₂, comp_zero]
  obtain ⟨x₁, hx₁⟩ : ∃ x₁, x₁ ≫ S.v₀₁.τ₁ = y₁:= ⟨_, S.exact_C₁_up.lift_f y₁ hy₁'⟩
  refine' ⟨A₁, π₁, hπ₁, x₁, _⟩
  simp only [← cancel_mono S.v₀₁.τ₂, assoc, ← S.v₀₁.comm₁₂,
    reassoc_of% hx₁, hy₁]

lemma ex₃ : S.L₃.Exact := S.op.ex₀.unop

noncomputable def P := pullback S.L₁.g S.v₀₁.τ₃

noncomputable def P' := pushout S.L₂.f S.v₂₃.τ₁

@[simp] noncomputable def φ₂ : S.P ⟶ S.L₂.X₂ := pullback.fst ≫ S.v₁₂.τ₂

noncomputable def φ₁ : S.P ⟶ S.L₂.X₁ :=
  S.L₂_exact.lift S.φ₂
    (by simp only [φ₂, assoc, S.v₁₂.comm₂₃, pullback.condition_assoc, w₀₂_τ₃, comp_zero])

@[reassoc (attr := simp)] lemma φ₁_L₂_f : S.φ₁ ≫ S.L₂.f = S.φ₂ := S.L₂_exact.lift_f _ _

noncomputable def L₀' : ShortComplex C where
  X₁ := S.L₁.X₁
  X₂ := S.P
  X₃ := S.L₀.X₃
  f := pullback.lift S.L₁.f 0 (by simp)
  g := pullback.snd
  zero := by simp

@[reassoc (attr := simp)] lemma L₁_f_φ₁ : S.L₀'.f ≫ S.φ₁ = S.v₁₂.τ₁ := by
  dsimp only [L₀']
  simp only [← cancel_mono S.L₂.f, assoc, φ₁_L₂_f, φ₂, pullback.lift_fst_assoc,
    S.v₁₂.comm₁₂]

instance : Epi S.L₀'.g := by dsimp only [L₀'] ; infer_instance
instance [Mono S.L₁.f] : Mono S.L₀'.f := ⟨fun h₁ h₂ eq => by
  replace eq := eq =≫ pullback.fst
  dsimp [L₀'] at eq
  simpa only [assoc, pullback.lift_fst, cancel_mono] using eq⟩

@[simps]
noncomputable def v₀₁' : S.L₀' ⟶ S.L₁ where
  τ₁ := 𝟙 _
  τ₂ := pullback.fst
  τ₃ := S.v₀₁.τ₃
  comm₁₂ := by simp only [L₀', id_comp, pullback.lift_fst]
  comm₂₃ := pullback.condition

instance : Epi S.L₁.toCycles := by
  rw [← S.L₁.exact_iff_epi_toCycles]
  exact S.L₁_exact

instance : IsIso (cyclesMap S.v₀₁') := by
  refine' ⟨⟨S.L₀'.liftCycles (pullback.lift (S.L₁.iCycles) 0 (by simp)) (by simp [L₀']), _, _⟩⟩
  · simp only [← cancel_mono S.L₀'.iCycles, assoc, id_comp, liftCycles_i]
    apply pullback.hom_ext
    · rw [assoc, pullback.lift_fst, cyclesMap_i, v₀₁'_τ₂]
    · rw [assoc, pullback.lift_snd, comp_zero]
      exact S.L₀'.iCycles_g.symm
  · simp only [← cancel_mono S.L₁.iCycles, liftCycles_comp_cyclesMap, v₀₁'_τ₂, limit.lift_π,
      PullbackCone.mk_π_app, liftCycles_i, id_comp]

lemma L₀'_exact : S.L₀'.Exact := by
  rw [S.L₀'.exact_iff_epi_toCycles, ← comp_id S.L₀'.toCycles,
    ← IsIso.hom_inv_id (cyclesMap S.v₀₁'), ← assoc]
  have : Epi (S.L₀'.toCycles ≫ cyclesMap S.v₀₁') := by
    simp only [toCycles_naturality S.v₀₁', v₀₁'_τ₁, id_comp]
    infer_instance
  apply epi_comp

noncomputable def δ : S.L₀.X₃ ⟶ S.L₃.X₁ :=
S.L₀'_exact.desc (S.φ₁ ≫ S.v₂₃.τ₁) (by simp only [L₁_f_φ₁_assoc, w₁₃_τ₁])

@[reassoc (attr := simp)]
lemma snd_δ : (pullback.snd : S.P ⟶ _) ≫ S.δ = S.φ₁ ≫ S.v₂₃.τ₁ :=
S.L₀'_exact.g_desc _ _

lemma snd_δ_inr : (pullback.snd : S.P ⟶ _) ≫ S.δ ≫ (pushout.inr : _ ⟶ S.P') =
  pullback.fst ≫ S.v₁₂.τ₂ ≫ pushout.inl :=
by simp only [snd_δ_assoc, ← pushout.condition, φ₂, φ₁_L₂_f_assoc, assoc]

@[simp]
noncomputable def L₀X₂ToP : S.L₀.X₂ ⟶ S.P := pullback.lift S.v₀₁.τ₂ S.L₀.g S.v₀₁.comm₂₃

@[reassoc]
lemma L₀X₂ToP_comp_pullback_snd : S.L₀X₂ToP ≫ pullback.snd = S.L₀.g := by simp

@[reassoc]
lemma L₀X₂ToP_comp_φ₁ : S.L₀X₂ToP ≫ S.φ₁ = 0 :=
by simp only [← cancel_mono S.L₂.f, L₀X₂ToP, assoc, φ₂, φ₁_L₂_f,
  pullback.lift_fst_assoc, w₀₂_τ₂, zero_comp]

lemma L₀_g_δ : S.L₀.g ≫ S.δ = 0 :=
by erw [← L₀X₂ToP_comp_pullback_snd, assoc, S.L₀'_exact.g_desc,
  L₀X₂ToP_comp_φ₁_assoc, zero_comp]

lemma δ_L₃_f : S.δ ≫ S.L₃.f = 0 :=
by erw [← cancel_epi S.L₀'.g, S.L₀'_exact.g_desc_assoc, assoc, S.v₂₃.comm₁₂, S.φ₁_L₂_f_assoc,
  φ₂, assoc, w₁₃_τ₂, comp_zero, comp_zero]

@[simps]
noncomputable def L₁' : ShortComplex C := ShortComplex.mk _ _ S.L₀_g_δ

@[simps]
noncomputable def L₂' : ShortComplex C := ShortComplex.mk _ _ S.δ_L₃_f

lemma exact_L₁' : S.L₁'.Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A₀ k₃ hk₃
  dsimp at k₃ hk₃
  obtain ⟨A₁, π₁, hπ₁, p, hp⟩ := surjective_up_to_refinements_of_epi S.L₀'.g k₃
  dsimp [L₀'] at p hp
  have hp' : (p ≫ S.φ₁) ≫ S.v₂₃.τ₁ = 0 := by
    rw [assoc, ← S.snd_δ, ← reassoc_of% hp, hk₃, comp_zero]
  obtain ⟨A₂, π₂, hπ₂, x₁, hx₁⟩ := S.exact_C₁_down.exact_up_to_refinements (p ≫ S.φ₁) hp'
  dsimp at x₁ hx₁
  let x₂' := x₁ ≫ S.L₁.f
  let x₂ := π₂ ≫ p ≫ pullback.fst
  have hx₂' : (x₂ - x₂') ≫ S.v₁₂.τ₂ = 0 := by
    simp only [sub_comp, assoc, ← S.v₁₂.comm₁₂, ← reassoc_of% hx₁, φ₂, φ₁_L₂_f, sub_self]
  let k₂ : A₂ ⟶ S.L₀.X₂ := S.exact_C₂_up.lift _ hx₂'
  have hk₂ : k₂ ≫ S.v₀₁.τ₂ = x₂ - x₂' := S.exact_C₂_up.lift_f _ _
  have hk₂' : k₂ ≫ S.L₀.g = π₂ ≫ p ≫ pullback.snd := by
    simp only [← cancel_mono S.v₀₁.τ₃, assoc, ← S.v₀₁.comm₂₃, reassoc_of% hk₂, sub_comp, S.L₁.zero,
      comp_zero, sub_zero, pullback.condition]
  refine' ⟨A₂, π₂ ≫ π₁, epi_comp _ _, k₂, _⟩
  simp only [assoc, L₁'_f, ← hk₂', hp]

@[simp]
noncomputable def PIsoUnopOpP' : S.P ≅ Opposite.unop S.op.P' :=
pullbackIsoUnopPushout _ _

@[simp]
noncomputable def P'IsoUnopOpP : S.P' ≅ Opposite.unop S.op.P :=
pushoutIsoUnopPullback _ _

lemma op_δ : S.op.δ = S.δ.op := Quiver.Hom.unop_inj (by
  rw [Quiver.Hom.unop_op, ← cancel_mono (pushout.inr : _ ⟶ S.P'),
    ← cancel_epi (pullback.snd : S.P ⟶ _), S.snd_δ_inr,
    ← cancel_mono S.P'IsoUnopOpP.hom, ← cancel_epi S.PIsoUnopOpP'.inv,
    P'IsoUnopOpP, PIsoUnopOpP', assoc, assoc, assoc, assoc,
    pushoutIsoUnopPullback_inr_hom, pullbackIsoUnopPushout_inv_snd_assoc,
    pushoutIsoUnopPullback_inl_hom, pullbackIsoUnopPushout_inv_fst_assoc]
  apply Quiver.Hom.op_inj
  simpa only [op_comp, Quiver.Hom.op_unop, assoc] using S.op.snd_δ_inr)

noncomputable def L₂'OpIso : S.L₂'.op ≅ S.op.L₁' :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by aesop_cat)
    (by dsimp ; simp only [id_comp, comp_id, S.op_δ])

lemma exact_L₂' : S.L₂'.Exact := by
  rw [← exact_op_iff, exact_iff_of_iso S.L₂'OpIso]
  exact S.op.exact_L₁'

variable (S₁ S₂ S₃ : SnakeInput C)

@[ext]
structure Hom :=
  f₀ : S₁.L₀ ⟶ S₂.L₀
  f₁ : S₁.L₁ ⟶ S₂.L₁
  f₂ : S₁.L₂ ⟶ S₂.L₂
  f₃ : S₁.L₃ ⟶ S₂.L₃
  comm₀₁ : f₀ ≫ S₂.v₀₁ = S₁.v₀₁ ≫ f₁ := by aesop_cat
  comm₁₂ : f₁ ≫ S₂.v₁₂ = S₁.v₁₂ ≫ f₂ := by aesop_cat
  comm₂₃ : f₂ ≫ S₂.v₂₃ = S₁.v₂₃ ≫ f₃ := by aesop_cat

namespace Hom

attribute [reassoc] comm₀₁ comm₁₂ comm₂₃

@[simps]
def id : Hom S S where
  f₀ := 𝟙 _
  f₁ := 𝟙 _
  f₂ := 𝟙 _
  f₃ := 𝟙 _

variable {S₁ S₂ S₃}

@[simps]
def comp (f : Hom S₁ S₂) (g : Hom S₂ S₃) : Hom S₁ S₃ where
  f₀ := f.f₀ ≫ g.f₀
  f₁ := f.f₁ ≫ g.f₁
  f₂ := f.f₂ ≫ g.f₂
  f₃ := f.f₃ ≫ g.f₃
  comm₀₁ := by simp only [assoc, comm₀₁, comm₀₁_assoc]
  comm₁₂ := by simp only [assoc, comm₁₂, comm₁₂_assoc]
  comm₂₃ := by simp only [assoc, comm₂₃, comm₂₃_assoc]

end Hom

instance : Category (SnakeInput C) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

variable {S₁ S₂ S₃}

@[simp] lemma id_f₀ : Hom.f₀ (𝟙 S) = 𝟙 _ := rfl
@[simp] lemma id_f₁ : Hom.f₁ (𝟙 S) = 𝟙 _ := rfl
@[simp] lemma id_f₂ : Hom.f₂ (𝟙 S) = 𝟙 _ := rfl
@[simp] lemma id_f₃ : Hom.f₃ (𝟙 S) = 𝟙 _ := rfl

section

variable (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃)

@[simp] lemma comp_f₀ : (f ≫ g).f₀ = f.f₀ ≫ g.f₀ := rfl
@[simp] lemma comp_f₁ : (f ≫ g).f₁ = f.f₁ ≫ g.f₁ := rfl
@[simp] lemma comp_f₂ : (f ≫ g).f₂ = f.f₂ ≫ g.f₂ := rfl
@[simp] lemma comp_f₃ : (f ≫ g).f₃ = f.f₃ ≫ g.f₃ := rfl

end

@[simps]
def functorL₉ : SnakeInput C ⥤ ShortComplex C where
  obj S := S.L₀
  map f := f.f₀

@[simps]
def functorL₁ : SnakeInput C ⥤ ShortComplex C where
  obj S := S.L₁
  map f := f.f₁

@[simps]
def functorL₂ : SnakeInput C ⥤ ShortComplex C where
  obj S := S.L₂
  map f := f.f₂

@[simps]
def functorL₃ : SnakeInput C ⥤ ShortComplex C where
  obj S := S.L₃
  map f := f.f₃

@[simps]
noncomputable def functorP : SnakeInput C ⥤ C where
  obj S := S.P
  map f := pullback.map _ _ _ _ f.f₁.τ₂ f.f₀.τ₃ f.f₁.τ₃ f.f₁.comm₂₃.symm
      (congr_arg ShortComplex.Hom.τ₃ f.comm₀₁.symm)
  map_id _ := by dsimp [P] ; aesop_cat
  map_comp _ _ := by dsimp [P] ; aesop_cat

noncomputable def functorL₀' : SnakeInput C ⥤ ShortComplex C where
  obj S := S.L₀'
  map f :=
  { τ₁ := f.f₁.τ₁,
    τ₂ := functorP.map f,
    τ₃ := f.f₀.τ₃,
    comm₁₂ := by
      dsimp [L₀']
      apply pullback.hom_ext
      · simp only [assoc, limit.lift_π, PullbackCone.mk_π_app, limit.lift_π_assoc, f.f₁.comm₁₂]
      · simp only [assoc, limit.lift_π, PullbackCone.mk_π_app, comp_zero,
          limit.lift_π_assoc, zero_comp]
    comm₂₃ := pullback.lift_snd _ _ _ }
  map_id _ := by
    ext
    · aesop_cat
    · apply pullback.hom_ext <;> simp
    · aesop_cat
  map_comp _ _ := by
    ext
    · aesop_cat
    · apply pullback.hom_ext <;> simp
    · aesop_cat

@[reassoc]
lemma naturality_φ₂ (f : S₁ ⟶ S₂) : S₁.φ₂ ≫ f.f₂.τ₂ = functorP.map f ≫ S₂.φ₂ := by
  dsimp
  simp only [assoc, pullback.lift_fst_assoc, ← comp_τ₂, f.comm₁₂]

@[reassoc]
lemma naturality_φ₁ (f : S₁ ⟶ S₂) : S₁.φ₁ ≫ f.f₂.τ₁ = functorP.map f ≫ S₂.φ₁ := by
  simp only [← cancel_mono S₂.L₂.f, assoc, φ₁_L₂_f, ← naturality_φ₂, f.f₂.comm₁₂, φ₁_L₂_f_assoc]

@[reassoc]
lemma naturality_δ (f : S₁ ⟶ S₂) : f.f₀.τ₃ ≫ S₂.δ = S₁.δ ≫ f.f₃.τ₁ := by
  rw [← cancel_epi (pullback.snd : S₁.P ⟶ _), S₁.snd_δ_assoc, ← comp_τ₁, ← f.comm₂₃,
    comp_τ₁, naturality_φ₁_assoc, ← S₂.snd_δ, functorP_map, pullback.lift_snd_assoc, assoc]

lemma comp_δ_eq {A : C} (x₀₃ : A ⟶ S.L₀.X₃) (x₁₂ : A ⟶ S.L₁.X₂) (x₂₁ : A ⟶ S.L₂.X₁)
    (h₁₂ : x₁₂ ≫ S.L₁.g = x₀₃ ≫ S.v₀₁.τ₃) (h₂₁ : x₁₂ ≫ S.v₁₂.τ₂ = x₂₁ ≫ S.L₂.f) :
    x₀₃ ≫ S.δ = x₂₁ ≫ S.v₂₃.τ₁ := by
  have eq := (pullback.lift x₁₂ x₀₃ h₁₂) ≫= S.snd_δ
  rw [pullback.lift_snd_assoc] at eq
  rw [eq, ← assoc]
  congr 1
  simp only [← cancel_mono S.L₂.f, ← h₂₁, assoc, φ₁_L₂_f, φ₂, limit.lift_π_assoc,
    PullbackCone.mk_π_app]

variable (C)

@[simps]
noncomputable def functorL₁' : SnakeInput C ⥤ ShortComplex C where
  obj S := S.L₁'
  map f :=
    { τ₁ := f.f₀.τ₂
      τ₂ := f.f₀.τ₃
      τ₃ := f.f₃.τ₁
      comm₁₂ := f.f₀.comm₂₃
      comm₂₃ := naturality_δ f }

@[simps]
noncomputable def functorL₂' : SnakeInput C ⥤ ShortComplex C where
  obj S := S.L₂'
  map f :=
    { τ₁ := f.f₀.τ₃,
      τ₂ := f.f₃.τ₁,
      τ₃ := f.f₃.τ₂,
      comm₁₂ := naturality_δ f
      comm₂₃ := f.f₃.comm₁₂ }

end SnakeInput

end ShortComplex

end CategoryTheory
