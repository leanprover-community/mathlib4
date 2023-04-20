import Mathlib.Algebra.Homology.ShortComplex.LeftHomology

open ZeroObject

namespace CategoryTheory

open Category Limits

namespace ShortComplex

variable {C D : Type _} [Category C] [Category D]
  [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

structure RightHomologyData :=
(Q H : C)
(p : S.X₂ ⟶ Q)
(ι : H ⟶ Q)
(wp : S.f ≫ p = 0)
(hp : IsColimit (CokernelCofork.ofπ p wp))
(wι : ι ≫ hp.desc (CokernelCofork.ofπ _ S.zero) = 0)
(hι : IsLimit (KernelFork.ofι ι wι))

initialize_simps_projections RightHomologyData (-hp, -hι)

namespace RightHomologyData

@[simps]
noncomputable def of_ker_of_coker [HasCokernel S.f] [HasKernel (cokernel.desc S.f S.g S.zero)] :
  S.RightHomologyData :=
{ Q := cokernel S.f,
  H := kernel (cokernel.desc S.f S.g S.zero),
  p := cokernel.π _,
  ι := kernel.ι _,
  wp := cokernel.condition _,
  hp := cokernelIsCokernel _,
  wι := kernel.condition _,
  hι := kernelIsKernel _, }

attribute [reassoc (attr := simp)] wp wι

variable {S}
variable (h : S.RightHomologyData) {A : C}

instance : Epi h.p :=
  ⟨fun _ _ => Cofork.IsColimit.hom_ext h.hp⟩

instance : Mono h.ι :=
  ⟨fun _ _ => Fork.IsLimit.hom_ext h.hι⟩

def desc_Q (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) : h.Q ⟶ A :=
h.hp.desc (CokernelCofork.ofπ k hk)

@[reassoc (attr := simp)]
lemma p_desc_Q (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) :
  h.p ≫ h.desc_Q k hk = k :=
h.hp.fac _ WalkingParallelPair.one

@[simp]
def desc_H (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) : h.H ⟶ A :=
  h.ι ≫ h.desc_Q k hk

/-- The morphism `h.Q ⟶ S.X₃` induced by `S.g : S.X₂ ⟶ S.X₃` and the fact that
`h.Q` is a cokernel of `S.f : S.X₁ ⟶ S.X₂`. -/
def g' : h.Q ⟶ S.X₃ := h.desc_Q S.g S.zero

@[reassoc (attr := simp)]
lemma p_g' : h.p ≫ h.g' = S.g :=
p_desc_Q _ _ _

@[reassoc (attr := simp)]
lemma ι_g' : h.ι ≫ h.g' = 0 := h.wι

@[reassoc]
lemma ι_desc_Q_eq_zero_of_boundary (k : S.X₂ ⟶ A) (x : S.X₃ ⟶ A) (hx : k = S.g ≫ x) :
  h.ι ≫ h.desc_Q k (by rw [hx, S.zero_assoc, zero_comp]) = 0 := by
  rw [show 0 = h.ι ≫ h.g' ≫ x by simp]
  congr 1
  simp only [← cancel_epi h.p, hx, p_desc_Q, p_g'_assoc]

/-- For `h : S.RightHomologyData`, this is a restatement of `h.hι `, saying that
`ι : h.H ⟶ h.Q` is a kernel of `h.g' : h.Q ⟶ S.X₃`. -/
def hι' : IsLimit (KernelFork.ofι h.ι h.ι_g') := h.hι

def lift_H (k : A ⟶ h.Q) (hk : k ≫ h.g' = 0) :
  A ⟶ h.H :=
h.hι.lift (KernelFork.ofι k hk)

@[reassoc (attr := simp)]
lemma lift_H_ι (k : A ⟶ h.Q) (hk : k ≫ h.g' = 0) :
  h.lift_H k hk ≫ h.ι = k :=
h.hι.fac (KernelFork.ofι k hk) WalkingParallelPair.zero

variable (S)

@[simps]
def of_isLimit_kernelFork (hf : S.f = 0) (c : KernelFork S.g) (hc : IsLimit c) :
  S.RightHomologyData where
  Q := S.X₂
  H := c.pt
  p := 𝟙 _
  ι := c.ι
  wp := by rw [comp_id, hf]
  hp := CokernelCofork.IsColimit.of_id _ hf
  wι := KernelFork.condition _
  hι := IsLimit.ofIsoLimit hc (Fork.ext (Iso.refl _) (by aesop_cat))

@[simp] lemma of_isLimit_kernelFork_g' (hf : S.f = 0) (c : KernelFork S.g)
    (hc : IsLimit c) : (of_isLimit_kernelFork S hf c hc).g' = S.g := by
  rw [← cancel_epi (of_isLimit_kernelFork S hf c hc).p, p_g',
    of_isLimit_kernelFork_p, id_comp]

@[simps!]
noncomputable def of_hasKernel [HasKernel S.g] (hf : S.f = 0) : S.RightHomologyData :=
of_isLimit_kernelFork S hf _ (kernelIsKernel _)

@[simps]
def of_isColimit_cokernelCofork (hg : S.g = 0) (c : CokernelCofork S.f) (hc : IsColimit c) :
  S.RightHomologyData where
  Q := c.pt
  H := c.pt
  p := c.π
  ι := 𝟙 _
  wp := CokernelCofork.condition _
  hp := IsColimit.ofIsoColimit hc (Cofork.ext (Iso.refl _) (by aesop_cat))
  wι := Cofork.IsColimit.hom_ext hc (by simp [hg])
  hι := KernelFork.IsLimit.of_id _ (Cofork.IsColimit.hom_ext hc (by simp [hg]))

@[simp] lemma of_isColimit_cokernelCofork_g' (hg : S.g = 0) (c : CokernelCofork S.f)
  (hc : IsColimit c) : (of_isColimit_cokernelCofork S hg c hc).g' = 0 :=
by rw [← cancel_epi (of_isColimit_cokernelCofork S hg c hc).p, p_g', hg, comp_zero]

@[simp]
noncomputable def of_hasCokernel [HasCokernel S.f] (hg : S.g = 0) : S.RightHomologyData :=
of_isColimit_cokernelCofork S hg _ (cokernelIsCokernel _)

@[simps]
def of_zeros (hf : S.f = 0) (hg : S.g = 0) : S.RightHomologyData where
  Q := S.X₂
  H := S.X₂
  p := 𝟙 _
  ι := 𝟙 _
  wp := by rw [comp_id, hf]
  hp := CokernelCofork.IsColimit.of_id _ hf
  wι := by
    change 𝟙 _ ≫ S.g = 0
    simp only [hg, comp_zero]
  hι := KernelFork.IsLimit.of_id _ hg

@[simp]
lemma of_zeros_g' (hf : S.f = 0) (hg : S.g = 0) :
    (of_zeros S hf hg).g' = 0 := by
  rw [← cancel_epi ((of_zeros S hf hg).p), comp_zero, p_g', hg]

@[simps]
noncomputable def cokernel_sequence' {X Y : C} (f : X ⟶ Y) (c : CokernelCofork f)
    (hc : IsColimit c) [HasZeroObject C] :
    RightHomologyData (ShortComplex.mk f c.π c.condition) where
  Q := c.pt
  H := 0
  p := c.π
  ι := 0
  wp := c.condition
  hp := IsColimit.ofIsoColimit hc (Cofork.ext (Iso.refl _) (by simp))
  wι := Subsingleton.elim _ _
  hι := by
    refine' KernelFork.IsLimit.of_isZero_of_mono _ _ _
    . dsimp
      convert (inferInstance : Mono (𝟙 c.pt))
      haveI := epi_of_isColimit_cofork hc
      rw [← cancel_epi c.π]
      simp only [parallelPair_obj_one, Functor.const_obj_obj, id_comp,
        Cofork.IsColimit.π_desc, Cofork.π_ofπ, comp_id]
    . apply isZero_zero

@[simps!]
noncomputable def cokernel_sequence {X Y : C} (f : X ⟶ Y) [HasCokernel f] [HasZeroObject C] :
    RightHomologyData (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)) := by
  let h := cokernel_sequence' f _ (cokernelIsCokernel f)
  exact h

end RightHomologyData

class HasRightHomology : Prop :=
(condition : Nonempty S.RightHomologyData)

noncomputable def rightHomologyData [HasRightHomology S] :
  S.RightHomologyData := HasRightHomology.condition.some

variable {S}

namespace HasRightHomology

lemma mk' (h : S.RightHomologyData) : HasRightHomology S :=
⟨Nonempty.intro h⟩

instance of_ker_of_coker
    [HasCokernel S.f] [HasKernel (cokernel.desc S.f S.g S.zero)] :
  S.HasRightHomology := HasRightHomology.mk' (RightHomologyData.of_ker_of_coker S)

instance of_hasKernel {Y Z : C} (g : Y ⟶ Z) (X : C) [HasKernel g] :
    (ShortComplex.mk (0 : X ⟶ Y) g zero_comp).HasRightHomology :=
  HasRightHomology.mk' (RightHomologyData.of_hasKernel _ rfl)

instance of_hasCokernel {X Y : C} (f : X ⟶ Y) (Z : C) [HasCokernel f] :
    (ShortComplex.mk f (0 : Y ⟶ Z) comp_zero).HasRightHomology :=
  HasRightHomology.mk' (RightHomologyData.of_hasCokernel _ rfl)

instance of_zeros (X Y Z : C) :
    (ShortComplex.mk (0 : X ⟶ Y) (0 : Y ⟶ Z) zero_comp).HasRightHomology :=
  HasRightHomology.mk' (RightHomologyData.of_zeros _ rfl rfl)

end HasRightHomology

namespace RightHomologyData

@[simps]
def op (h : S.RightHomologyData) : S.op.LeftHomologyData where
  K := Opposite.op h.Q
  H := Opposite.op h.H
  i := h.p.op
  π := h.ι.op
  wi := Quiver.Hom.unop_inj h.wp
  hi := CokernelCofork.IsColimit.ofπ_op _ _ h.hp
  wπ := Quiver.Hom.unop_inj h.wι
  hπ := KernelFork.IsLimit.ofι_op _ _ h.hι

@[simp] lemma op_f' (h : S.RightHomologyData) :
    h.op.f' = h.g'.op := rfl

@[simps]
def unop {S : ShortComplex Cᵒᵖ} (h : S.RightHomologyData) : S.unop.LeftHomologyData where
  K := Opposite.unop h.Q
  H := Opposite.unop h.H
  i := h.p.unop
  π := h.ι.unop
  wi := Quiver.Hom.op_inj h.wp
  hi := CokernelCofork.IsColimit.ofπ_unop _ _ h.hp
  wπ := Quiver.Hom.op_inj h.wι
  hπ := KernelFork.IsLimit.ofι_unop _ _ h.hι

@[simp] lemma unop_f' {S : ShortComplex Cᵒᵖ} (h : S.RightHomologyData) :
    h.unop.f' = h.g'.unop := rfl

end RightHomologyData

namespace LeftHomologyData

@[simps]
def op (h : S.LeftHomologyData) : S.op.RightHomologyData where
  Q := Opposite.op h.K
  H := Opposite.op h.H
  p := h.i.op
  ι := h.π.op
  wp := Quiver.Hom.unop_inj h.wi
  hp := KernelFork.IsLimit.ofι_op _ _ h.hi
  wι := Quiver.Hom.unop_inj h.wπ
  hι := CokernelCofork.IsColimit.ofπ_op _ _ h.hπ

@[simp] lemma op_g' (h : S.LeftHomologyData) :
    h.op.g' = h.f'.op := rfl

@[simps]
def unop {S : ShortComplex Cᵒᵖ} (h : S.LeftHomologyData) : S.unop.RightHomologyData where
  Q := Opposite.unop h.K
  H := Opposite.unop h.H
  p := h.i.unop
  ι := h.π.unop
  wp := Quiver.Hom.op_inj h.wi
  hp := KernelFork.IsLimit.ofι_unop _ _ h.hi
  wι := Quiver.Hom.op_inj h.wπ
  hι := CokernelCofork.IsColimit.ofπ_unop _ _ h.hπ

@[simp] lemma unop_g' {S : ShortComplex Cᵒᵖ} (h : S.LeftHomologyData) :
    h.unop.g' = h.f'.unop := rfl

end LeftHomologyData

instance [S.HasLeftHomology] : HasRightHomology S.op :=
  HasRightHomology.mk' S.leftHomologyData.op

instance [S.HasRightHomology] : HasLeftHomology S.op :=
  HasLeftHomology.mk' S.rightHomologyData.op

lemma hasLeftHomology_iff_op (S : ShortComplex C) :
    S.HasLeftHomology ↔ S.op.HasRightHomology :=
  ⟨fun _ => inferInstance, fun _ => HasLeftHomology.mk' S.op.rightHomologyData.unop⟩

lemma hasRightHomology_iff_op (S : ShortComplex C) :
    S.HasRightHomology ↔ S.op.HasLeftHomology :=
  ⟨fun _ => inferInstance, fun _ => HasRightHomology.mk' S.op.leftHomologyData.unop⟩

lemma hasLeftHomology_iff_unop (S : ShortComplex Cᵒᵖ) :
    S.HasLeftHomology ↔ S.unop.HasRightHomology :=
  S.unop.hasRightHomology_iff_op.symm

lemma hasRightHomology_iff_unop (S : ShortComplex Cᵒᵖ) :
    S.HasRightHomology ↔ S.unop.HasLeftHomology :=
  S.unop.hasLeftHomology_iff_op.symm

section

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData)

structure RightHomologyMapData where
  φQ : h₁.Q ⟶ h₂.Q
  φH : h₁.H ⟶ h₂.H
  commp : h₁.p ≫ φQ = φ.τ₂ ≫ h₂.p := by aesop_cat
  commg' : φQ ≫ h₂.g' = h₁.g' ≫ φ.τ₃ := by aesop_cat
  commι : φH ≫ h₂.ι = h₁.ι ≫ φQ := by aesop_cat

namespace RightHomologyMapData

attribute [reassoc (attr := simp)] commp commg' commι

@[simps]
def zero (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
  RightHomologyMapData 0 h₁ h₂ where
  φQ := 0
  φH := 0

@[simps]
def id (h : S.RightHomologyData) : RightHomologyMapData (𝟙 S) h h where
  φQ := 𝟙 _
  φH := 𝟙 _

@[simps]
def comp {φ : S₁ ⟶ S₂} {φ' : S₂ ⟶ S₃} {h₁ : S₁.RightHomologyData}
  {h₂ : S₂.RightHomologyData} {h₃ : S₃.RightHomologyData}
  (ψ : RightHomologyMapData φ h₁ h₂) (ψ' : RightHomologyMapData φ' h₂ h₃) :
  RightHomologyMapData (φ ≫ φ') h₁ h₃ where
  φQ := ψ.φQ ≫ ψ'.φQ
  φH := ψ.φH ≫ ψ'.φH

instance : Subsingleton (RightHomologyMapData φ h₁ h₂) :=
  ⟨fun ψ₁ ψ₂ => by
    have hQ : ψ₁.φQ = ψ₂.φQ := by rw [← cancel_epi h₁.p, commp, commp]
    have hH : ψ₁.φH = ψ₂.φH := by rw [← cancel_mono h₂.ι, commι, commι, hQ]
    cases ψ₁
    cases ψ₂
    congr⟩

instance : Inhabited (RightHomologyMapData φ h₁ h₂) := ⟨by
  let φQ : h₁.Q ⟶ h₂.Q := h₁.desc_Q (φ.τ₂ ≫ h₂.p) (by rw [← φ.comm₁₂_assoc, h₂.wp, comp_zero])
  have commg' : φQ ≫ h₂.g' = h₁.g' ≫ φ.τ₃ :=
    by rw [← cancel_epi h₁.p, RightHomologyData.p_desc_Q_assoc, assoc,
      RightHomologyData.p_g', φ.comm₂₃, RightHomologyData.p_g'_assoc]
  let φH : h₁.H ⟶ h₂.H := h₂.lift_H (h₁.ι ≫ φQ)
    (by rw [assoc, commg', RightHomologyData.ι_g'_assoc, zero_comp])
  exact ⟨φQ, φH, by simp, commg', by simp⟩⟩

instance : Unique (RightHomologyMapData φ h₁ h₂) := Unique.mk' _

def _root_.CategoryTheory.ShortComplex.rightHomologyMapData :
  RightHomologyMapData φ h₁ h₂ := default

variable {φ h₁ h₂}

lemma congr_φH {γ₁ γ₂ : RightHomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂) : γ₁.φH = γ₂.φH := by rw [eq]
lemma congr_φQ {γ₁ γ₂ : RightHomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂) : γ₁.φQ = γ₂.φQ := by rw [eq]

@[simps]
def of_zeros (φ : S₁ ⟶ S₂) (hf₁ : S₁.f = 0) (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) (hg₂ : S₂.g = 0) :
  RightHomologyMapData φ (RightHomologyData.of_zeros S₁ hf₁ hg₁)
    (RightHomologyData.of_zeros S₂ hf₂ hg₂) where
  φQ := φ.τ₂
  φH := φ.τ₂

@[simps]
def of_isLimit_kernelFork (φ : S₁ ⟶ S₂)
    (hf₁ : S₁.f = 0) (c₁ : KernelFork S₁.g) (hc₁ : IsLimit c₁)
    (hf₂ : S₂.f = 0) (c₂ : KernelFork S₂.g) (hc₂ : IsLimit c₂) (f : c₁.pt ⟶ c₂.pt)
    (comm : c₁.ι ≫ φ.τ₂ = f ≫ c₂.ι) :
    RightHomologyMapData φ (RightHomologyData.of_isLimit_kernelFork S₁ hf₁ c₁ hc₁)
      (RightHomologyData.of_isLimit_kernelFork S₂ hf₂ c₂ hc₂) where
  φQ := φ.τ₂
  φH := f
  commg' := by simp only [RightHomologyData.of_isLimit_kernelFork_Q,
    RightHomologyData.of_isLimit_kernelFork_g', φ.comm₂₃]
  commι := comm.symm

@[simps]
def of_isColimit_cokernelCofork (φ : S₁ ⟶ S₂)
  (hg₁ : S₁.g = 0) (c₁ : CokernelCofork S₁.f) (hc₁ : IsColimit c₁)
  (hg₂ : S₂.g = 0) (c₂ : CokernelCofork S₂.f) (hc₂ : IsColimit c₂) (f : c₁.pt ⟶ c₂.pt)
  (comm : φ.τ₂ ≫ c₂.π = c₁.π ≫ f) :
  RightHomologyMapData φ (RightHomologyData.of_isColimit_cokernelCofork S₁ hg₁ c₁ hc₁)
    (RightHomologyData.of_isColimit_cokernelCofork S₂ hg₂ c₂ hc₂) where
  φQ := f
  φH := f
  commp := comm.symm

variable (S)

@[simps]
def compatibility_of_zeros_of_isLimit_kernelFork (hf : S.f = 0) (hg : S.g = 0)
    (c : KernelFork S.g) (hc : IsLimit c) :
    RightHomologyMapData (𝟙 S)
      (RightHomologyData.of_isLimit_kernelFork S hf c hc)
      (RightHomologyData.of_zeros S hf hg) where
  φQ := 𝟙 _
  φH := c.ι

@[simps]
def compatibility_of_zeros_of_isColimit_cokernelCofork (hf : S.f = 0) (hg : S.g = 0)
  (c : CokernelCofork S.f) (hc : IsColimit c) :
  RightHomologyMapData (𝟙 S)
    (RightHomologyData.of_zeros S hf hg)
    (RightHomologyData.of_isColimit_cokernelCofork S hg c hc) where
  φQ := c.π
  φH := c.π

end RightHomologyMapData

end

variable (S)

noncomputable def rightHomology [HasRightHomology S] : C := S.rightHomologyData.H
noncomputable def cyclesCo [HasRightHomology S] : C := S.rightHomologyData.Q
noncomputable def rightHomology_ι [HasRightHomology S] : S.rightHomology ⟶ S.cyclesCo :=
  S.rightHomologyData.ι
noncomputable def p_cyclesCo [HasRightHomology S] : S.X₂ ⟶ S.cyclesCo := S.rightHomologyData.p
noncomputable def fromCyclesCo [HasRightHomology S] : S.cyclesCo ⟶ S.X₃ := S.rightHomologyData.g'

@[reassoc (attr := simp)]
lemma f_p_cyclesCo [HasRightHomology S] : S.f ≫ S.p_cyclesCo = 0 :=
  S.rightHomologyData.wp

@[reassoc (attr := simp)]
lemma p_fromCyclesCo [HasRightHomology S] : S.p_cyclesCo ≫ S.fromCyclesCo = S.g :=
  S.rightHomologyData.p_g'

instance [HasRightHomology S] : Epi S.p_cyclesCo := by
  dsimp only [p_cyclesCo]
  infer_instance

instance [HasRightHomology S] : Mono S.rightHomology_ι := by
  dsimp only [rightHomology_ι]
  infer_instance

variable {S}

def rightHomology_map' (φ : S₁ ⟶ S₂) (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
  h₁.H ⟶ h₂.H := (rightHomologyMapData φ _ _).φH

def cyclesCo_map' (φ : S₁ ⟶ S₂) (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
  h₁.Q ⟶ h₂.Q := (rightHomologyMapData φ _ _).φQ

@[reassoc (attr := simp)]
lemma p_cyclesCo_map' (φ : S₁ ⟶ S₂) (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    h₁.p ≫ cyclesCo_map' φ h₁ h₂ = φ.τ₂ ≫ h₂.p :=
  RightHomologyMapData.commp _

@[reassoc (attr := simp)]
lemma rightHomology_ι_naturality' (φ : S₁ ⟶ S₂)
    (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    rightHomology_map' φ h₁ h₂ ≫ h₂.ι = h₁.ι ≫ cyclesCo_map' φ h₁ h₂ :=
  RightHomologyMapData.commι _

noncomputable def rightHomology_map [HasRightHomology S₁] [HasRightHomology S₂]
    (φ : S₁ ⟶ S₂) : S₁.rightHomology ⟶ S₂.rightHomology :=
  rightHomology_map' φ _ _

noncomputable def cyclesCo_map [HasRightHomology S₁] [HasRightHomology S₂]
    (φ : S₁ ⟶ S₂) : S₁.cyclesCo ⟶ S₂.cyclesCo :=
  cyclesCo_map' φ _ _

@[reassoc (attr := simp)]
lemma p_cyclesCo_map (φ : S₁ ⟶ S₂) [S₁.HasRightHomology] [S₂.HasRightHomology] :
    S₁.p_cyclesCo ≫ cyclesCo_map φ = φ.τ₂ ≫ S₂.p_cyclesCo :=
  p_cyclesCo_map' _ _ _

@[reassoc (attr := simp)]
lemma fromCyclesCo_naturality (φ : S₁ ⟶ S₂) [S₁.HasRightHomology] [S₂.HasRightHomology] :
    cyclesCo_map φ ≫ S₂.fromCyclesCo = S₁.fromCyclesCo ≫ φ.τ₃ := by
  simp only [← cancel_epi S₁.p_cyclesCo, p_cyclesCo_map_assoc, p_fromCyclesCo,
    p_fromCyclesCo_assoc, φ.comm₂₃]

@[reassoc (attr := simp)]
lemma rightHomology_ι_naturality [HasRightHomology S₁] [HasRightHomology S₂]
    (φ : S₁ ⟶ S₂) :
    rightHomology_map φ ≫ S₂.rightHomology_ι = S₁.rightHomology_ι ≫ cyclesCo_map φ :=
  rightHomology_ι_naturality' _ _ _

namespace RightHomologyMapData

variable {φ : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}
  (γ : RightHomologyMapData φ h₁ h₂)

lemma rightHomology_map'_eq : rightHomology_map' φ h₁ h₂ = γ.φH :=
  RightHomologyMapData.congr_φH (Subsingleton.elim _ _)

lemma cyclesCo_map'_eq : cyclesCo_map' φ h₁ h₂ = γ.φQ :=
  RightHomologyMapData.congr_φQ (Subsingleton.elim _ _)

end RightHomologyMapData

@[simp]
lemma rightHomology_map'_id (h : S.RightHomologyData) :
    rightHomology_map' (𝟙 S) h h = 𝟙 _ :=
  (RightHomologyMapData.id h).rightHomology_map'_eq

@[simp]
lemma cyclesCo_map'_id (h : S.RightHomologyData) :
    cyclesCo_map' (𝟙 S) h h = 𝟙 _ :=
  (RightHomologyMapData.id h).cyclesCo_map'_eq

variable (S)

@[simp]
lemma rightHomology_map_id [HasRightHomology S] :
    rightHomology_map (𝟙 S) = 𝟙 _ :=
  rightHomology_map'_id _

@[simp]
lemma cyclesCo_map_id [HasRightHomology S] :
    cyclesCo_map (𝟙 S) = 𝟙 _ :=
  cyclesCo_map'_id _

@[simp]
lemma rightHomology_map'_zero (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    rightHomology_map' 0 h₁ h₂ = 0 :=
  (RightHomologyMapData.zero h₁ h₂).rightHomology_map'_eq

@[simp]
lemma cyclesCo_map'_zero (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    cyclesCo_map' 0 h₁ h₂ = 0 :=
  (RightHomologyMapData.zero h₁ h₂).cyclesCo_map'_eq

variable (S₁ S₂)

@[simp]
lemma right_homology_map_zero [HasRightHomology S₁] [HasRightHomology S₂] :
    rightHomology_map (0 : S₁ ⟶ S₂) = 0 :=
  rightHomology_map'_zero _ _

@[simp]
lemma cyclesCo_map_zero [HasRightHomology S₁] [HasRightHomology S₂] :
  cyclesCo_map (0 : S₁ ⟶ S₂) = 0 :=
cyclesCo_map'_zero _ _

variable {S₁ S₂}

lemma rightHomology_map'_comp (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
    (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) (h₃ : S₃.RightHomologyData) :
    rightHomology_map' (φ₁ ≫ φ₂) h₁ h₃ = rightHomology_map' φ₁ h₁ h₂ ≫
      rightHomology_map' φ₂ h₂ h₃ := by
  let γ₁ := rightHomologyMapData φ₁ h₁ h₂
  let γ₂ := rightHomologyMapData φ₂ h₂ h₃
  rw [γ₁.rightHomology_map'_eq, γ₂.rightHomology_map'_eq, (γ₁.comp γ₂).rightHomology_map'_eq,
    RightHomologyMapData.comp_φH]

lemma cyclesCo_map'_comp (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
    (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) (h₃ : S₃.RightHomologyData) :
    cyclesCo_map' (φ₁ ≫ φ₂) h₁ h₃ = cyclesCo_map' φ₁ h₁ h₂ ≫ cyclesCo_map' φ₂ h₂ h₃ := by
  let γ₁ := rightHomologyMapData φ₁ h₁ h₂
  let γ₂ := rightHomologyMapData φ₂ h₂ h₃
  rw [γ₁.cyclesCo_map'_eq, γ₂.cyclesCo_map'_eq, (γ₁.comp γ₂).cyclesCo_map'_eq,
    RightHomologyMapData.comp_φQ]

@[simp]
lemma rightHomology_map_comp [HasRightHomology S₁] [HasRightHomology S₂] [HasRightHomology S₃]
    (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) :
    rightHomology_map (φ₁ ≫ φ₂) = rightHomology_map φ₁ ≫ rightHomology_map φ₂ :=
rightHomology_map'_comp _ _ _ _ _

@[simp]
lemma cyclesCo_map_comp [HasRightHomology S₁] [HasRightHomology S₂] [HasRightHomology S₃]
    (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) :
    cyclesCo_map (φ₁ ≫ φ₂) = cyclesCo_map φ₁ ≫ cyclesCo_map φ₂ :=
  cyclesCo_map'_comp _ _ _ _ _

@[simps]
def rightHomology_map_iso' (e : S₁ ≅ S₂) (h₁ : S₁.RightHomologyData)
    (h₂ : S₂.RightHomologyData) : h₁.H ≅ h₂.H where
  hom := rightHomology_map' e.hom h₁ h₂
  inv := rightHomology_map' e.inv h₂ h₁
  hom_inv_id := by rw [← rightHomology_map'_comp, e.hom_inv_id, rightHomology_map'_id]
  inv_hom_id := by rw [← rightHomology_map'_comp, e.inv_hom_id, rightHomology_map'_id]

instance isIso_rightHomology_map'_of_isIso (φ : S₁ ⟶ S₂) [IsIso φ]
    (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    IsIso (rightHomology_map' φ h₁ h₂) :=
  (inferInstance : IsIso (rightHomology_map_iso' (asIso φ) h₁ h₂).hom)

@[simps]
def cyclesCo_map_iso' (e : S₁ ≅ S₂) (h₁ : S₁.RightHomologyData)
  (h₂ : S₂.RightHomologyData) : h₁.Q ≅ h₂.Q where
  hom := cyclesCo_map' e.hom h₁ h₂
  inv := cyclesCo_map' e.inv h₂ h₁
  hom_inv_id := by rw [← cyclesCo_map'_comp, e.hom_inv_id, cyclesCo_map'_id]
  inv_hom_id := by rw [← cyclesCo_map'_comp, e.inv_hom_id, cyclesCo_map'_id]

instance isIso_cyclesCo_map'_of_isIso (φ : S₁ ⟶ S₂) [IsIso φ]
    (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    IsIso (cyclesCo_map' φ h₁ h₂) :=
  (inferInstance : IsIso (cyclesCo_map_iso' (asIso φ) h₁ h₂).hom)

@[simps]
noncomputable def rightHomology_map_iso (e : S₁ ≅ S₂) [S₁.HasRightHomology]
  [S₂.HasRightHomology] : S₁.rightHomology ≅ S₂.rightHomology where
  hom := rightHomology_map e.hom
  inv := rightHomology_map e.inv
  hom_inv_id := by rw [← rightHomology_map_comp, e.hom_inv_id, rightHomology_map_id]
  inv_hom_id := by rw [← rightHomology_map_comp, e.inv_hom_id, rightHomology_map_id]

instance isIso_rightHomology_map_of_iso (φ : S₁ ⟶ S₂) [IsIso φ] [S₁.HasRightHomology]
    [S₂.HasRightHomology] :
    IsIso (rightHomology_map φ) :=
  (inferInstance : IsIso (rightHomology_map_iso (asIso φ)).hom)

@[simps]
noncomputable def cyclesCo_map_iso (e : S₁ ≅ S₂) [S₁.HasRightHomology]
    [S₂.HasRightHomology] : S₁.cyclesCo ≅ S₂.cyclesCo where
  hom := cyclesCo_map e.hom
  inv := cyclesCo_map e.inv
  hom_inv_id := by rw [← cyclesCo_map_comp, e.hom_inv_id, cyclesCo_map_id]
  inv_hom_id := by rw [← cyclesCo_map_comp, e.inv_hom_id, cyclesCo_map_id]

instance is_iso_cycles_map_of_iso (φ : S₁ ⟶ S₂) [IsIso φ] [S₁.HasRightHomology]
    [S₂.HasRightHomology] : IsIso (cyclesCo_map φ) :=
  (inferInstance : IsIso (cyclesCo_map_iso (asIso φ)).hom)

variable {S}

noncomputable def RightHomologyData.rightHomology_iso (h : S.RightHomologyData) [S.HasRightHomology] :
  S.rightHomology ≅ h.H := rightHomology_map_iso' (Iso.refl _) _ _

noncomputable def RightHomologyData.cyclesCo_iso (h : S.RightHomologyData) [S.HasRightHomology] :
  S.cyclesCo ≅ h.Q := cyclesCo_map_iso' (Iso.refl _) _ _

@[reassoc (attr := simp)]
lemma RightHomologyData.p_comp_cyclesCo_iso_inv (h : S.RightHomologyData) [S.HasRightHomology] :
    h.p ≫ h.cyclesCo_iso.inv = S.p_cyclesCo := by
  dsimp [p_cyclesCo, RightHomologyData.cyclesCo_iso]
  simp only [p_cyclesCo_map', id_τ₂, id_comp]

@[reassoc (attr := simp)]
lemma RightHomologyData.p_cyclesCo_comp_cyclesCo_iso_hom (h : S.RightHomologyData)
    [S.HasRightHomology] : S.p_cyclesCo ≫ h.cyclesCo_iso.hom = h.p := by
  simp only [← h.p_comp_cyclesCo_iso_inv, assoc, Iso.inv_hom_id, comp_id]

namespace RightHomologyMapData

variable {φ : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}
  (γ : RightHomologyMapData φ h₁ h₂)

lemma rightHomology_map_eq [S₁.HasRightHomology] [S₂.HasRightHomology] :
    rightHomology_map φ = h₁.rightHomology_iso.hom ≫ γ.φH ≫ h₂.rightHomology_iso.inv := by
  dsimp [RightHomologyData.rightHomology_iso, rightHomology_map_iso']
  rw [← γ.rightHomology_map'_eq, ← rightHomology_map'_comp,
    ← rightHomology_map'_comp, id_comp, comp_id]
  rfl

lemma cyclesCo_map_eq [S₁.HasRightHomology] [S₂.HasRightHomology] :
    cyclesCo_map φ = h₁.cyclesCo_iso.hom ≫ γ.φQ ≫ h₂.cyclesCo_iso.inv := by
  dsimp [RightHomologyData.cyclesCo_iso, cycles_map_iso']
  rw [← γ.cyclesCo_map'_eq, ← cyclesCo_map'_comp, ← cyclesCo_map'_comp, id_comp, comp_id]
  rfl

lemma rightHomology_map_comm [S₁.HasRightHomology] [S₂.HasRightHomology] :
    rightHomology_map φ ≫ h₂.rightHomology_iso.hom = h₁.rightHomology_iso.hom ≫ γ.φH := by
  simp only [γ.rightHomology_map_eq, assoc, Iso.inv_hom_id, comp_id]

lemma cyclesCo_map_comm [S₁.HasRightHomology] [S₂.HasRightHomology] :
    cyclesCo_map φ ≫ h₂.cyclesCo_iso.hom = h₁.cyclesCo_iso.hom ≫ γ.φQ := by
  simp only [γ.cyclesCo_map_eq, assoc, Iso.inv_hom_id, comp_id]

end RightHomologyMapData

variable (C)

/-- We shall say that a category with right homology is a category for which
all short complexes have right homology. -/
abbrev _root_.CategoryTheory.CategoryWithRightHomology : Prop :=
  ∀ (S : ShortComplex C), S.HasRightHomology

@[simps]
noncomputable def rightHomology_functor [CategoryWithRightHomology C] :
    ShortComplex C ⥤ C where
  obj S := S.rightHomology
  map := rightHomology_map

@[simps]
noncomputable def cyclesCo_functor [CategoryWithRightHomology C] :
    ShortComplex C ⥤ C where
  obj S := S.cyclesCo
  map := cyclesCo_map

@[simps]
noncomputable def rightHomology_ι_natTrans [CategoryWithRightHomology C] :
    rightHomology_functor C ⟶ cyclesCo_functor C where
  app S := rightHomology_ι S
  naturality := fun _ _ φ => rightHomology_ι_naturality φ

@[simps]
noncomputable def p_cyclesCo_natTrans [CategoryWithRightHomology C] :
    ShortComplex.π₂ ⟶ cyclesCo_functor C where
  app S := S.p_cyclesCo

@[simps]
noncomputable def fromCyclesCo_natTrans [CategoryWithRightHomology C] :
    cyclesCo_functor C ⟶ π₃ where
  app S := S.fromCyclesCo
  naturality := fun _ _  φ => fromCyclesCo_naturality φ

@[simps]
def LeftHomologyMapData.op {S₁ S₂ : ShortComplex C} {φ : S₁ ⟶ S₂}
    {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}
    (ψ : LeftHomologyMapData φ h₁ h₂) : RightHomologyMapData (op_map φ) h₂.op h₁.op where
  φQ := ψ.φK.op
  φH := ψ.φH.op
  commp := Quiver.Hom.unop_inj (by simp)
  commg' := Quiver.Hom.unop_inj (by simp)
  commι := Quiver.Hom.unop_inj (by simp)

@[simps]
def LeftHomologyMapData.unop {S₁ S₂ : ShortComplex Cᵒᵖ} {φ : S₁ ⟶ S₂}
    {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}
    (ψ : LeftHomologyMapData φ h₁ h₂) : RightHomologyMapData (unop_map φ) h₂.unop h₁.unop where
  φQ := ψ.φK.unop
  φH := ψ.φH.unop
  commp := Quiver.Hom.op_inj (by simp)
  commg' := Quiver.Hom.op_inj (by simp)
  commι := Quiver.Hom.op_inj (by simp)

@[simps]
def RightHomologyMapData.op {S₁ S₂ : ShortComplex C} {φ : S₁ ⟶ S₂}
    {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}
    (ψ : RightHomologyMapData φ h₁ h₂) : LeftHomologyMapData (op_map φ) h₂.op h₁.op where
  φK := ψ.φQ.op
  φH := ψ.φH.op
  commi := Quiver.Hom.unop_inj (by simp)
  commf' := Quiver.Hom.unop_inj (by simp)
  commπ := Quiver.Hom.unop_inj (by simp)

@[simps]
def RightHomologyMapData.unop {S₁ S₂ : ShortComplex Cᵒᵖ} {φ : S₁ ⟶ S₂}
    {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}
    (ψ : RightHomologyMapData φ h₁ h₂) : LeftHomologyMapData (unop_map φ) h₂.unop h₁.unop where
  φK := ψ.φQ.unop
  φH := ψ.φH.unop
  commi := Quiver.Hom.op_inj (by simp)
  commf' := Quiver.Hom.op_inj (by simp)
  commπ := Quiver.Hom.op_inj (by simp)

variable (S)

noncomputable def rightHomology_op_iso [S.HasLeftHomology] :
    S.op.rightHomology ≅ Opposite.op S.leftHomology :=
  S.leftHomologyData.op.rightHomology_iso

noncomputable def leftHomology_op_iso [S.HasRightHomology] :
    S.op.leftHomology ≅ Opposite.op S.rightHomology :=
  S.rightHomologyData.op.leftHomology_iso

noncomputable def cyclesCo_op_iso [S.HasLeftHomology] :
    S.op.cyclesCo ≅ Opposite.op S.cycles :=
  S.leftHomologyData.op.cyclesCo_iso

noncomputable def cycles_op_iso [S.HasRightHomology] :
    S.op.cycles ≅ Opposite.op S.cyclesCo :=
  S.rightHomologyData.op.cycles_iso

@[simp]
lemma leftHomology_map'_op
    (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    (leftHomology_map' φ h₁ h₂).op = rightHomology_map' (op_map φ) h₂.op h₁.op := by
  let γ : LeftHomologyMapData φ h₁ h₂ := default
  simp only [γ.leftHomology_map'_eq, (γ.op).rightHomology_map'_eq,
    LeftHomologyMapData.op_φH]

@[simp]
lemma leftHomology_map_op (φ : S₁ ⟶ S₂) [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    (leftHomology_map φ).op = (S₂.rightHomology_op_iso).inv ≫ rightHomology_map
      (op_map φ) ≫ (S₁.rightHomology_op_iso).hom := by
  dsimp [rightHomology_op_iso, RightHomologyData.rightHomology_iso, rightHomology_map,
    leftHomology_map]
  simp only [← rightHomology_map'_comp, comp_id, id_comp, leftHomology_map'_op]

@[simp]
lemma rightHomology_map'_op
    (φ : S₁ ⟶ S₂) (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    (rightHomology_map' φ h₁ h₂).op = leftHomology_map' (op_map φ) h₂.op h₁.op := by
  let γ : RightHomologyMapData φ h₁ h₂ := default
  simp only [γ.rightHomology_map'_eq, (γ.op).leftHomology_map'_eq,
    RightHomologyMapData.op_φH]

@[simp]
lemma rightHomology_map_op (φ : S₁ ⟶ S₂) [S₁.HasRightHomology] [S₂.HasRightHomology] :
    (rightHomology_map φ).op = (S₂.leftHomology_op_iso).inv ≫ leftHomology_map
      (op_map φ) ≫ (S₁.leftHomology_op_iso).hom := by
  dsimp [leftHomology_op_iso, LeftHomologyData.leftHomology_iso, leftHomology_map,
    rightHomology_map]
  simp only [← leftHomology_map'_comp, comp_id, id_comp, rightHomology_map'_op]

instance _root_.CategoryTheory.CategoryWithRightHomology.op
    [CategoryWithRightHomology C] : CategoryWithLeftHomology Cᵒᵖ :=
  fun S => ShortComplex.HasLeftHomology_of_iso S.unop_op

-- we need of_epi_of_isIso_of_mono
instance _root_.CategoryTheory.CategoryWithLeftHomology.op
    [CategoryWithLeftHomology C] : CategoryWithRightHomology Cᵒᵖ :=
  fun S => ShortComplex.HasRightHomology_of_iso S.unop_op

#exit
end ShortComplex

end CategoryTheory

attribute [-simp] CategoryTheory.ShortComplex.RightHomologyMapData.mk.injEq

#lint

#exit
-----

end

variables {S₁ S₂ S₃ : short_complex C}

namespace right_homology_data

@[simp]
def of_epi_of_is_iso_of_mono (φ : S₁ ⟶ S₂) (h : right_homology_data S₁)
  [epi φ.τ₁] [is_iso φ.τ₂] [mono φ.τ₃] : right_homology_data S₂ :=
begin
  haveI : epi (op_map φ).τ₁ := by { dsimp, apply_instance, },
  haveI : is_iso (op_map φ).τ₂ := by { dsimp, apply_instance, },
  haveI : mono (op_map φ).τ₃ := by { dsimp, apply_instance, },
  exact (left_homology_data.of_epi_of_is_iso_of_mono' (op_map φ) h.op).unop,
end

@[simp]
lemma of_epi_of_is_iso_of_mono_p (φ : S₁ ⟶ S₂) (h : right_homology_data S₁)
  [epi φ.τ₁] [is_iso φ.τ₂] [mono φ.τ₃] :
    (right_homology_data.of_epi_of_is_iso_of_mono φ h).p = inv φ.τ₂ ≫ h.p :=
begin
  change (h.p.op ≫ inv φ.τ₂.op).unop = _,
  simp only [quiver.hom.unop_op, unop_comp, unop_inv],
end

@[simp]
lemma of_epi_of_is_iso_of_mono_g' (φ : S₁ ⟶ S₂) (h : right_homology_data S₁)
  [epi φ.τ₁] [is_iso φ.τ₂] [mono φ.τ₃] :
    (of_epi_of_is_iso_of_mono φ h).g' = h.g' ≫ φ.τ₃ :=
begin
  rw [← cancel_epi (of_epi_of_is_iso_of_mono φ h).p, p_g'],
  simp only [of_epi_of_is_iso_of_mono_p, assoc, p_g'_assoc, is_iso.eq_inv_comp, φ.comm₂₃],
end

@[simp]
lemma of_epi_of_is_iso_of_mono_ι (φ : S₁ ⟶ S₂) (h : right_homology_data S₁)
  [epi φ.τ₁] [is_iso φ.τ₂] [mono φ.τ₃] :
    (of_epi_of_is_iso_of_mono φ h).ι = h.ι := rfl

@[simp]
def of_epi_of_is_iso_of_mono' (φ : S₁ ⟶ S₂) (h : right_homology_data S₂)
  [epi φ.τ₁] [is_iso φ.τ₂] [mono φ.τ₃] : right_homology_data S₁ :=
begin
  haveI : epi (op_map φ).τ₁ := by { dsimp, apply_instance, },
  haveI : is_iso (op_map φ).τ₂ := by { dsimp, apply_instance, },
  haveI : mono (op_map φ).τ₃ := by { dsimp, apply_instance, },
  exact (left_homology_data.of_epi_of_is_iso_of_mono (op_map φ) h.op).unop,
end

@[simp]
lemma of_epi_of_is_iso_of_mono'_p (φ : S₁ ⟶ S₂) (h : right_homology_data S₂)
  [epi φ.τ₁] [is_iso φ.τ₂] [mono φ.τ₃] :
    (of_epi_of_is_iso_of_mono' φ h).p = φ.τ₂ ≫ h.p := rfl

@[simp]
lemma of_epi_of_is_iso_of_mono'_g'_τ₃ (φ : S₁ ⟶ S₂) (h : right_homology_data S₂)
  [epi φ.τ₁] [is_iso φ.τ₂] [mono φ.τ₃] :
  (of_epi_of_is_iso_of_mono' φ h).g' ≫ φ.τ₃ = h.g' :=
by rw [← cancel_epi (of_epi_of_is_iso_of_mono' φ h).p, p_g'_assoc,
    of_epi_of_is_iso_of_mono'_p, assoc, p_g', φ.comm₂₃]

@[simp]
lemma of_epi_of_is_iso_of_mono'_ι (φ : S₁ ⟶ S₂) (h : right_homology_data S₂)
  [epi φ.τ₁] [is_iso φ.τ₂] [mono φ.τ₃] :
    (of_epi_of_is_iso_of_mono' φ h).ι = h.ι := rfl

def of_iso (e : S₁ ≅ S₂) (h₁ : right_homology_data S₁) : right_homology_data S₂ :=
h₁.of_epi_of_is_iso_of_mono e.hom

end right_homology_data

lemma has_right_homology_of_epi_of_is_iso_of_mono (φ : S₁ ⟶ S₂) [has_right_homology S₁]
  [epi φ.τ₁] [is_iso φ.τ₂] [mono φ.τ₃] : has_right_homology S₂ :=
has_right_homology.mk' (right_homology_data.of_epi_of_is_iso_of_mono φ S₁.some_right_homology_data)

lemma has_right_homology_of_epi_of_is_iso_of_mono' (φ : S₁ ⟶ S₂) [has_right_homology S₂]
  [epi φ.τ₁] [is_iso φ.τ₂] [mono φ.τ₃] : has_right_homology S₁ :=
has_right_homology.mk' (right_homology_data.of_epi_of_is_iso_of_mono' φ S₂.some_right_homology_data)

lemma has_right_homology_of_iso {S₁ S₂ : short_complex C}
  (e : S₁ ≅ S₂) [has_right_homology S₁] : has_right_homology S₂ :=
has_right_homology_of_epi_of_is_iso_of_mono e.hom

variables (φ : S₁ ⟶ S₂)
  (h₁ : S₁.right_homology_data) (h₂ : S₂.right_homology_data)

---


@[simps]
def right_homology_functor_op_nat_iso [category_with_right_homology C] :
  (right_homology_functor C).op ≅ op_functor C ⋙ left_homology_functor Cᵒᵖ :=
nat_iso.of_components (λ S, (op_left_homology_iso S.unop).symm) (by simp)

@[simps]
def left_homology_functor_op_nat_iso [category_with_left_homology C] :
  (left_homology_functor C).op ≅ op_functor C ⋙ right_homology_functor Cᵒᵖ :=
nat_iso.of_components (λ S, (op_right_homology_iso S.unop).symm) (by simp)

namespace right_homology_map_data

@[simps]
def of_epi_of_is_iso_of_mono (φ : S₁ ⟶ S₂) (h : right_homology_data S₁)
  [epi φ.τ₁] [is_iso φ.τ₂] [mono φ.τ₃] :
    right_homology_map_data φ h (right_homology_data.of_epi_of_is_iso_of_mono φ h) :=
{ φQ := 𝟙 _,
  φH := 𝟙 _,
  commp' := by simp only [comp_id, right_homology_data.of_epi_of_is_iso_of_mono_p, is_iso.hom_inv_id_assoc],
  commg'' := by simp only [right_homology_data.of_epi_of_is_iso_of_mono_g', id_comp],
  commι' := by simp only [comp_id, right_homology_data.of_epi_of_is_iso_of_mono_ι, id_comp], }

@[simps]
def of_epi_of_is_iso_of_mono' (φ : S₁ ⟶ S₂) (h : right_homology_data S₂)
  [epi φ.τ₁] [is_iso φ.τ₂] [mono φ.τ₃] :
    right_homology_map_data φ (right_homology_data.of_epi_of_is_iso_of_mono' φ h) h :=
{ φQ := 𝟙 _,
  φH := 𝟙 _,
  commp' := by { dsimp, simp only [comp_id], },
  commg'' := by { simp only [right_homology_data.of_epi_of_is_iso_of_mono'_g'_τ₃, id_comp], },
  commι' := by { dsimp, simp only [comp_id, id_comp], }, }

end right_homology_map_data

instance (φ : S₁ ⟶ S₂) (h₁ : S₁.right_homology_data) (h₂ : S₂.right_homology_data)
  [epi φ.τ₁] [is_iso φ.τ₂] [mono φ.τ₃] :
  is_iso (right_homology_map' φ h₁ h₂) :=
begin
  let h₂' := right_homology_data.of_epi_of_is_iso_of_mono φ h₁,
  haveI : is_iso (right_homology_map' φ h₁ h₂'),
  { let γ := right_homology_map_data.of_epi_of_is_iso_of_mono φ h₁,
    rw γ.right_homology_map'_eq,
    dsimp,
    apply_instance, },
  have eq := right_homology_map'_comp φ (𝟙 S₂) h₁ h₂' h₂,
  rw comp_id at eq,
  rw eq,
  apply_instance,
end

instance (φ : S₁ ⟶ S₂) [S₁.has_right_homology] [S₂.has_right_homology]
  [epi φ.τ₁] [is_iso φ.τ₂] [mono φ.τ₃] :
  is_iso (right_homology_map φ) :=
by { dsimp only [right_homology_map], apply_instance, }

section

variables (S) (h : S.right_homology_data) {A : C} (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0)
  [has_right_homology S]

def desc_cycles_co : S.cycles_co ⟶ A :=
S.some_right_homology_data.desc_Q k hk

@[simp, reassoc]
lemma p_desc_cycles_co : S.p_cycles_co ≫ S.desc_cycles_co k hk = k :=
right_homology_data.p_desc_Q _ k hk

def cycles_co_is_cokernel : is_colimit (cokernel_cofork.of_π S.p_cycles_co S.f_cycles_co_p) :=
S.some_right_homology_data.hp

lemma is_iso_p_cycles_co_of (hf : S.f = 0) : is_iso (S.p_cycles_co) :=
cokernel_cofork.is_colimit.is_iso_π_of_zero _ S.cycles_co_is_cokernel hf

@[simps]
def cycles_co_iso_cokernel [has_cokernel S.f] : S.cycles_co ≅ cokernel S.f :=
{ hom := S.desc_cycles_co (cokernel.π S.f) (by simp),
  inv := cokernel.desc S.f S.p_cycles_co (by simp),
  hom_inv_id' := by simp only [← cancel_epi S.p_cycles_co, p_desc_cycles_co_assoc,
    cokernel.π_desc, comp_id],
  inv_hom_id' := by simp only [← cancel_epi (cokernel.π S.f), cokernel.π_desc_assoc,
    p_desc_cycles_co, comp_id], }

@[simp]
def desc_right_homology : S.right_homology ⟶ A :=
S.right_homology_ι ≫ S.desc_cycles_co k hk

lemma ι_desc_cycles_co_eq_zero_of_boundary (x : S.X₃ ⟶ A) (hx : k = S.g ≫ x) :
S.right_homology_ι ≫ S.desc_cycles_co k (by rw [hx, S.zero_assoc, zero_comp]) = 0 :=
right_homology_data.ι_desc_Q_eq_zero_of_boundary _ k x hx

@[simp, reassoc]
lemma right_homology_ι_comp_from_cycles_co :
  S.right_homology_ι ≫ S.from_cycles_co = 0 :=
S.ι_desc_cycles_co_eq_zero_of_boundary S.g (𝟙 _) (by rw comp_id)

def right_homology_is_kernel :
  is_limit (kernel_fork.of_ι S.right_homology_ι S.right_homology_ι_comp_from_cycles_co) :=
S.some_right_homology_data.hι

variable {S}

@[simp, reassoc]
lemma right_homology_data.right_homology_iso_inv_comp_right_homology_ι :
  h.right_homology_iso.inv ≫ S.right_homology_ι = h.ι ≫ h.cycles_co_iso.inv :=
begin
  dsimp only [right_homology_ι, right_homology_data.right_homology_iso,
    right_homology_map_iso', iso.refl, right_homology_data.cycles_co_iso, cycles_co_map_iso'],
  rw ← right_homology_ι_naturality',
end

@[simp, reassoc]
lemma right_homology_data.right_homology_ι_comp_cycles_co_iso_hom :
   S.right_homology_ι ≫ h.cycles_co_iso.hom = h.right_homology_iso.hom ≫ h.ι :=
by simp only [← cancel_mono h.cycles_co_iso.inv, ← cancel_epi h.right_homology_iso.inv,
  assoc, iso.hom_inv_id, comp_id, iso.inv_hom_id_assoc,
  h.right_homology_iso_inv_comp_right_homology_ι]

@[simp, reassoc]
lemma right_homology_data.cycles_co_iso_inv_comp_desc_cycles_co :
  h.cycles_co_iso.inv ≫ S.desc_cycles_co k hk = h.desc_Q k hk :=
by simp only [← cancel_epi h.p, h.p_comp_cycles_co_iso_inv_assoc, p_desc_cycles_co,
  h.p_desc_Q]

@[simp, reassoc]
lemma right_homology_data.cycles_co_iso_inv_comp_desc_cycles_co' :
  h.cycles_co_iso.hom ≫ h.desc_Q k hk =  S.desc_cycles_co k hk :=
by rw [← cancel_epi h.cycles_co_iso.inv, iso.inv_hom_id_assoc,
  h.cycles_co_iso_inv_comp_desc_cycles_co]

lemma right_homology_data.ext_iff' (f₁ f₂ : A ⟶ S.right_homology) :
  f₁ = f₂ ↔ f₁ ≫ h.right_homology_iso.hom ≫ h.ι = f₂ ≫ h.right_homology_iso.hom ≫ h.ι :=
by simp only [← cancel_mono h.right_homology_iso.hom, ← cancel_mono h.ι, assoc]

end

namespace has_right_homology

variable (S)

@[protected]
lemma has_cokernel [S.has_right_homology] : has_cokernel S.f :=
⟨⟨⟨_, S.some_right_homology_data.hp⟩⟩⟩

lemma has_kernel [S.has_right_homology] [has_cokernel S.f] :
  has_kernel (cokernel.desc S.f S.g S.zero) :=
begin
  let h := S.some_right_homology_data,
  haveI : has_limit (parallel_pair h.g' 0) := ⟨⟨⟨_, h.hι'⟩⟩⟩,
  let e : parallel_pair h.g' 0 ≅ parallel_pair (cokernel.desc S.f S.g S.zero) 0 :=
    parallel_pair.ext (is_colimit.cocone_point_unique_up_to_iso h.hp (cokernel_is_cokernel S.f))
      (iso.refl _) (by tidy) (by tidy),
  exact has_limit_of_iso e,
end

end has_right_homology

variable (S)

def right_homology_iso_kernel_desc [S.has_right_homology] [has_cokernel S.f]
  [has_kernel (cokernel.desc S.f S.g S.zero)] :
  S.right_homology ≅ kernel (cokernel.desc S.f S.g S.zero) :=
(right_homology_data.of_coker_of_ker S).right_homology_iso

namespace right_homology_data

variable {S}

lemma is_iso_p_of_zero_f (h : right_homology_data S) (hf : S.f = 0) : is_iso h.p :=
⟨⟨h.desc_Q (𝟙 S.X₂) (by rw [hf, zero_comp]), p_desc_Q _ _ _,
  by simp only [←cancel_epi h.p, p_desc_Q_assoc, id_comp, comp_id]⟩⟩

end right_homology_data

end short_complex

end category_theory
