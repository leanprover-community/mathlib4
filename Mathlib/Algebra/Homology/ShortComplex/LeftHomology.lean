import Mathlib.Algebra.Homology.ShortComplex.Basic

open ZeroObject

namespace CategoryTheory

open Category

namespace Limits

variable {C : Type _} [Category C] [HasZeroMorphisms C]

def KernelFork.IsLimit.of_id {X Y : C} (f : X ⟶ Y) (hf : f = 0) :
    IsLimit (KernelFork.ofι (𝟙 X) (show 𝟙 X ≫ f = 0 by rw [hf, comp_zero])) :=
  KernelFork.IsLimit.ofι _ _ (fun x _ => x) (fun _ _ => comp_id _)
    (fun _ _ _ hb => by simp only [← hb, comp_id])

def KernelFork.IsLimit.of_isZero_of_mono {X Y : C} {f : X ⟶ Y} (c : KernelFork f)
    (hf : Mono f) (h : IsZero c.pt) : IsLimit c :=
  isLimitAux _ (fun s => 0) (fun s => by rw [zero_comp, ← cancel_mono f, zero_comp, s.condition])
    (fun _ _ _ => h.eq_of_tgt _ _)

lemma KernelFork.IsLimit.isIso_ι_of_zero {X Y : C} {f : X ⟶ Y} (c : KernelFork f)
    (hc : IsLimit c) (hf : f = 0) : IsIso c.ι := by
  let e : c.pt ≅ X := IsLimit.conePointUniqueUpToIso hc
    (KernelFork.IsLimit.of_id (f : X ⟶ Y) hf)
  have eq : e.inv ≫ c.ι = 𝟙 X := Fork.IsLimit.lift_ι hc
  haveI : IsIso (e.inv ≫ c.ι) := by
    rw [eq]
    infer_instance
  exact IsIso.of_isIso_comp_left e.inv c.ι

def CokernelCofork.IsColimit.of_id {X Y : C} (f : X ⟶ Y) (hf : f = 0) :
    IsColimit (CokernelCofork.ofπ (𝟙 Y) (show f ≫ 𝟙 Y = 0 by rw [hf, zero_comp])) :=
  CokernelCofork.IsColimit.ofπ  _ _ (fun x _ => x) (fun _ _ => id_comp _)
    (fun _ _ _ hb => by simp only [← hb, id_comp])

def CokernelCofork.IsColimit.of_isZero_of_epi {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f)
    (hf : Epi f) (h : IsZero c.pt) : IsColimit c :=
  isColimitAux _ (fun s => 0) (fun s => by rw [comp_zero, ← cancel_epi f, comp_zero, s.condition])
    (fun _ _ _ => h.eq_of_src _ _)

lemma CokernelCofork.IsColimit.isIso_π_of_zero {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f)
    (hc : IsColimit c) (hf : f = 0) : IsIso c.π := by
  let e : c.pt ≅ Y := IsColimit.coconePointUniqueUpToIso hc
    (CokernelCofork.IsColimit.of_id (f : X ⟶ Y) hf)
  have eq : c.π ≫ e.hom = 𝟙 Y := Cofork.IsColimit.π_desc hc
  haveI : IsIso (c.π ≫ e.hom) := by
    rw [eq]
    dsimp
    infer_instance
  exact IsIso.of_isIso_comp_right c.π e.hom

def CokernelCofork.IsColimit.ofπ_op {X Y Q : C} (p : Y ⟶ Q) {f : X ⟶ Y}
    (w : f ≫ p = 0) (h : IsColimit (CokernelCofork.ofπ p w)) :
    IsLimit (KernelFork.ofι p.op (show p.op ≫ f.op = 0 by rw [← op_comp, w, op_zero])) :=
  KernelFork.IsLimit.ofι _ _
    (fun x hx => (h.desc (CokernelCofork.ofπ x.unop (Quiver.Hom.op_inj hx))).op)
    (fun x hx => Quiver.Hom.unop_inj (Cofork.IsColimit.π_desc h))
    (fun x hx b hb => Quiver.Hom.unop_inj (Cofork.IsColimit.hom_ext h
      (by simpa only [Quiver.Hom.unop_op, Cofork.IsColimit.π_desc] using Quiver.Hom.op_inj hb)))

def CokernelCofork.IsColimit.ofπ_unop {X Y Q : Cᵒᵖ} (p : Y ⟶ Q) {f : X ⟶ Y}
    (w : f ≫ p = 0) (h : IsColimit (CokernelCofork.ofπ p w)) :
    IsLimit (KernelFork.ofι p.unop (show p.unop ≫ f.unop = 0 by rw [← unop_comp, w, unop_zero])) :=
  KernelFork.IsLimit.ofι _ _
    (fun x hx => (h.desc (CokernelCofork.ofπ x.op (Quiver.Hom.op_inj hx))).unop)
    (fun x hx => Quiver.Hom.op_inj (Cofork.IsColimit.π_desc h))
    (fun x hx b hb => Quiver.Hom.op_inj (Cofork.IsColimit.hom_ext h
      (by simpa only [Quiver.Hom.op_unop, Cofork.IsColimit.π_desc] using Quiver.Hom.unop_inj hb)))

def KernelFork.IsLimit.ofι_op {K X Y : C} (i : K ⟶ X) {f : X ⟶ Y}
    (w : i ≫ f = 0) (h : IsLimit (KernelFork.ofι i w)) :
    IsColimit (CokernelCofork.ofπ i.op
      (show f.op ≫ i.op = 0 by rw [← op_comp, w, op_zero])) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun x hx => (h.lift (KernelFork.ofι x.unop (Quiver.Hom.op_inj hx))).op)
    (fun x hx => Quiver.Hom.unop_inj (Fork.IsLimit.lift_ι h))
    (fun x hx b hb => Quiver.Hom.unop_inj (Fork.IsLimit.hom_ext h (by
      simpa only [Quiver.Hom.unop_op, Fork.IsLimit.lift_ι] using Quiver.Hom.op_inj hb)))

def KernelFork.IsLimit.ofι_unop {K X Y : Cᵒᵖ} (i : K ⟶ X) {f : X ⟶ Y}
    (w : i ≫ f = 0) (h : IsLimit (KernelFork.ofι i w)) :
    IsColimit (CokernelCofork.ofπ i.unop
      (show f.unop ≫ i.unop = 0 by rw [← unop_comp, w, unop_zero])) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun x hx => (h.lift (KernelFork.ofι x.op (Quiver.Hom.unop_inj hx))).unop)
    (fun x hx => Quiver.Hom.op_inj (Fork.IsLimit.lift_ι h))
    (fun x hx b hb => Quiver.Hom.op_inj (Fork.IsLimit.hom_ext h (by
      simpa only [Quiver.Hom.op_unop, Fork.IsLimit.lift_ι] using Quiver.Hom.unop_inj hb)))

end Limits

end CategoryTheory

/-
open category_theory category_theory.category category_theory.limits
open_locale zero_object

namespace category_theory.limits

variables {C : Type*} [category C] [has_zero_morphisms C]


/-- fork.is_limit.lift_ι has to be fixed -/
@[simp, reassoc]
lemma fork.is_limit.lift_ι' {X Y : C} {f g : X ⟶ Y} {c : fork f g} (hc : is_limit c)
  (c' : fork f g ) : hc.lift c' ≫ c.ι = c'.ι :=
by apply fork.is_limit.lift_ι

namespace kernel_fork

def is_limit.of_ι_op {K X Y : C} (i : K ⟶ X) {f : X ⟶ Y}
  (w : i ≫ f = 0) (h : is_limit (kernel_fork.of_ι i w)) :
  is_colimit (cokernel_cofork.of_π i.op
    (show f.op ≫ i.op = 0, by simpa only [← op_comp, w])) :=
cokernel_cofork.is_colimit.of_π _ _
  (λ A x hx, (h.lift (kernel_fork.of_ι x.unop (quiver.hom.op_inj hx))).op)
  (λ A x hx, quiver.hom.unop_inj (fork.is_limit.lift_ι h))
  (λ A x hx b hb, quiver.hom.unop_inj (fork.is_limit.hom_ext h begin
    simp only [quiver.hom.unop_op, fork.is_limit.lift_ι],
    exact quiver.hom.op_inj hb,
  end))

def is_limit.of_ι_unop {K X Y : Cᵒᵖ} (i : K ⟶ X) {f : X ⟶ Y}
  (w : i ≫ f = 0) (h : is_limit (kernel_fork.of_ι i w)) :
  is_colimit (cokernel_cofork.of_π i.unop
    (show f.unop ≫ i.unop = 0, by simpa only [← unop_comp, w])) :=
cokernel_cofork.is_colimit.of_π _ _
  (λ A x hx, (h.lift (kernel_fork.of_ι x.op (quiver.hom.unop_inj hx))).unop)
  (λ A x hx, quiver.hom.op_inj (fork.is_limit.lift_ι h))
  (λ A x hx b hb, quiver.hom.op_inj (fork.is_limit.hom_ext h begin
    simp only [quiver.hom.op_unop, fork.is_limit.lift_ι],
    exact quiver.hom.unop_inj hb,
  end))

lemma is_limit.is_iso_ι_of_zero {X Y : C} {f : X ⟶ Y} (c : kernel_fork f)
  (hc : is_limit c) (hf : f = 0) : is_iso c.ι :=
begin
  subst hf,
  let e : c.X ≅ X := is_limit.cone_point_unique_up_to_iso hc (kernel_zero (0 : X ⟶ Y) rfl),
  have eq : e.inv ≫ fork.ι c  = 𝟙 X := fork.is_limit.lift_ι hc,
  haveI : is_iso (e.inv ≫ fork.ι c),
  { rw eq, dsimp, apply_instance, },
  exact is_iso.of_is_iso_comp_left e.inv (fork.ι c),
end

end kernel_fork

namespace cokernel_cofork

def is_colimit.of_π_op {X Y Q : C} (p : Y ⟶ Q) {f : X ⟶ Y}
  (w : f ≫ p = 0) (h : is_colimit (cokernel_cofork.of_π p w)) :
  is_limit (kernel_fork.of_ι p.op
    (show p.op ≫ f.op = 0, by simpa only [← op_comp, w])) :=
kernel_fork.is_limit.of_ι _ _
  (λ A x hx, (h.desc (cokernel_cofork.of_π x.unop (quiver.hom.op_inj hx))).op)
  (λ A x hx, quiver.hom.unop_inj (cofork.is_colimit.π_desc h))
  (λ A x hx b hb, quiver.hom.unop_inj (cofork.is_colimit.hom_ext h begin
    simp only [quiver.hom.unop_op, cofork.is_colimit.π_desc],
    exact quiver.hom.op_inj hb,
  end))

def is_colimit.of_π_unop {X Y Q : Cᵒᵖ} (p : Y ⟶ Q) {f : X ⟶ Y}
  (w : f ≫ p = 0) (h : is_colimit (cokernel_cofork.of_π p w)) :
  is_limit (kernel_fork.of_ι p.unop
    (show p.unop ≫ f.unop = 0, by simpa only [← unop_comp, w])) :=
kernel_fork.is_limit.of_ι _ _
  (λ A x hx, (h.desc (cokernel_cofork.of_π x.op (quiver.hom.unop_inj hx))).unop)
  (λ A x hx, quiver.hom.op_inj (cofork.is_colimit.π_desc h))
  (λ A x hx b hb, quiver.hom.op_inj (cofork.is_colimit.hom_ext h begin
    simp only [quiver.hom.op_unop, cofork.is_colimit.π_desc],
    exact quiver.hom.unop_inj hb,
  end))

lemma is_colimit.is_iso_π_of_zero {X Y : C} {f : X ⟶ Y} (c : cokernel_cofork f)
  (hc : is_colimit c) (hf : f = 0) : is_iso c.π :=
begin
  subst hf,
  let e : c.X ≅ Y := is_colimit.cocone_point_unique_up_to_iso hc (cokernel_zero (0 : X ⟶ Y) rfl),
  have eq : cofork.π c ≫ e.hom = 𝟙 Y := cofork.is_colimit.π_desc hc,
  haveI : is_iso (cofork.π c ≫ e.hom),
  { rw eq, dsimp, apply_instance, },
  exact is_iso.of_is_iso_comp_right (cofork.π c) e.hom,
end

end cokernel_cofork

end category_theory.limits

open category_theory.limits
-/

namespace CategoryTheory

open Category Limits

namespace ShortComplex

variable {C D : Type _} [Category C] [Category D]
  [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

structure LeftHomologyData :=
(K H : C)
(i : K ⟶ S.X₂)
(π : K ⟶ H)
(wi : i ≫ S.g = 0)
(hi : IsLimit (KernelFork.ofι i wi))
(wπ : hi.lift (KernelFork.ofι _ S.zero) ≫ π = 0)
(hπ : IsColimit (CokernelCofork.ofπ π wπ))

initialize_simps_projections LeftHomologyData (-hi, -hπ)

namespace LeftHomologyData

@[simps]
noncomputable def of_ker_of_coker [HasKernel S.g] [HasCokernel (kernel.lift S.g S.f S.zero)] :
  S.LeftHomologyData :=
{ K := kernel S.g,
  H := cokernel (kernel.lift S.g S.f S.zero),
  i := kernel.ι _,
  π := cokernel.π _,
  wi := kernel.condition _,
  hi := kernelIsKernel _,
  wπ := cokernel.condition _,
  hπ := cokernelIsCokernel _, }

attribute [reassoc (attr := simp)] wi wπ

variable {S}
variable (h : S.LeftHomologyData) {A : C}

instance : Mono h.i :=
  ⟨fun _ _ => Fork.IsLimit.hom_ext h.hi⟩

instance : Epi h.π :=
  ⟨fun _ _ => Cofork.IsColimit.hom_ext h.hπ⟩

def lift_K (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) : A ⟶ h.K :=
h.hi.lift (KernelFork.ofι k hk)

@[reassoc (attr := simp)]
lemma lift_K_i (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) :
  h.lift_K k hk ≫ h.i = k :=
h.hi.fac _ WalkingParallelPair.zero

@[simp]
def lift_H (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) : A ⟶ h.H :=
  h.lift_K k hk ≫ h.π

/-- The morphism `S.X₁ ⟶ h.K` induced by `S.f : S.X₁ ⟶ S.X₂` and the fact that
`h.K` is a kernel of `S.g : S.X₂ ⟶ S.X₃`. -/
def f' : S.X₁ ⟶ h.K := h.lift_K S.f S.zero

@[reassoc (attr := simp)]
lemma f'_i : h.f' ≫ h.i = S.f :=
lift_K_i _ _ _

@[reassoc (attr := simp)]
lemma f'_π : h.f' ≫ h.π = 0 := h.wπ

@[reassoc]
lemma lift_K_π_eq_zero_of_boundary (k : A ⟶ S.X₂) (x : A ⟶ S.X₁) (hx : k = x ≫ S.f) :
    h.lift_K k (by rw [hx, assoc, S.zero, comp_zero]) ≫ h.π = 0 := by
  rw [show 0 = (x ≫ h.f') ≫ h.π by simp]
  congr 1
  simp only [← cancel_mono h.i, hx, lift_K_i, assoc, f'_i]

/-- For `h : S.LeftHomologyData`, this is a restatement of `h.hπ`, saying that
`π : h.K ⟶ h.H` is a cokernel of `h.f' : S.X₁ ⟶ h.K`. -/
def hπ' : IsColimit (CokernelCofork.ofπ h.π h.f'_π) := h.hπ

def desc_H (k : h.K ⟶ A) (hk : h.f' ≫ k = 0) :
  h.H ⟶ A :=
h.hπ.desc (CokernelCofork.ofπ k hk)

@[reassoc (attr := simp)]
lemma π_desc_H (k : h.K ⟶ A) (hk : h.f' ≫ k = 0) :
  h.π ≫ h.desc_H k hk = k :=
h.hπ.fac (CokernelCofork.ofπ k hk) WalkingParallelPair.one

variable (S)

@[simps]
def of_isColimit_cokernelCofork (hg : S.g = 0) (c : CokernelCofork S.f) (hc : IsColimit c) :
  S.LeftHomologyData where
  K := S.X₂
  H := c.pt
  i := 𝟙 _
  π := c.π
  wi := by rw [id_comp, hg]
  hi := KernelFork.IsLimit.of_id _ hg
  wπ := CokernelCofork.condition _
  hπ := IsColimit.ofIsoColimit hc (Cofork.ext (Iso.refl _) (by aesop_cat))

@[simp] lemma of_isColimit_cokernelCofork_f' (hg : S.g = 0) (c : CokernelCofork S.f)
    (hc : IsColimit c) : (of_isColimit_cokernelCofork S hg c hc).f' = S.f := by
  rw [← cancel_mono (of_isColimit_cokernelCofork S hg c hc).i, f'_i,
    of_isColimit_cokernelCofork_i]
  dsimp
  rw [comp_id]

@[simps!]
noncomputable def of_hasCokernel [HasCokernel S.f] (hg : S.g = 0) : S.LeftHomologyData :=
of_isColimit_cokernelCofork S hg _ (cokernelIsCokernel _)

@[simps]
def of_isLimit_kernelFork (hf : S.f = 0) (c : KernelFork S.g) (hc : IsLimit c) :
  S.LeftHomologyData where
  K := c.pt
  H := c.pt
  i := c.ι
  π := 𝟙 _
  wi := KernelFork.condition _
  hi := IsLimit.ofIsoLimit hc (Fork.ext (Iso.refl _) (by aesop_cat))
  wπ := Fork.IsLimit.hom_ext hc (by
    dsimp
    simp only [comp_id, zero_comp, Fork.IsLimit.lift_ι, Fork.ι_ofι, hf])
  hπ := CokernelCofork.IsColimit.of_id _ (Fork.IsLimit.hom_ext hc (by
    dsimp
    simp only [comp_id, zero_comp, Fork.IsLimit.lift_ι, Fork.ι_ofι, hf]))

@[simp] lemma of_isLimit_kernelFork_f' (hf : S.f = 0) (c : KernelFork S.g)
  (hc : IsLimit c) : (of_isLimit_kernelFork S hf c hc).f' = 0 :=
by rw [← cancel_mono (of_isLimit_kernelFork S hf c hc).i, f'_i, hf, zero_comp]

@[simp]
noncomputable def of_hasKernel [HasKernel S.g] (hf : S.f = 0) : S.LeftHomologyData :=
of_isLimit_kernelFork S hf _ (kernelIsKernel _)

@[simps]
def of_zeros (hf : S.f = 0) (hg : S.g = 0) : S.LeftHomologyData where
  K := S.X₂
  H := S.X₂
  i := 𝟙 _
  π := 𝟙 _
  wi := by rw [id_comp, hg]
  hi := KernelFork.IsLimit.of_id _ hg
  wπ := by
    change S.f ≫ 𝟙 _ = 0
    simp only [hf, zero_comp]
  hπ := CokernelCofork.IsColimit.of_id _ hf

@[simp]
lemma of_zeros_f' (hf : S.f = 0) (hg : S.g = 0) :
    (of_zeros S hf hg).f' = 0 := by
  rw [← cancel_mono ((of_zeros S hf hg).i), zero_comp, f'_i, hf]

@[simps]
noncomputable def kernel_sequence' {X Y : C} (f : X ⟶ Y) (c : KernelFork f) (hc : IsLimit c)
  [HasZeroObject C] :
  LeftHomologyData (ShortComplex.mk c.ι f (KernelFork.condition c)) where
  K := c.pt
  H := 0
  i := c.ι
  π := 0
  wi := KernelFork.condition _
  hi := IsLimit.ofIsoLimit hc (Fork.ext (Iso.refl _) (by simp))
  wπ := Subsingleton.elim _ _
  hπ := by
    refine' CokernelCofork.IsColimit.of_isZero_of_epi _ _ _
    . dsimp
      convert (inferInstance : Epi (𝟙 c.pt))
      haveI := mono_of_isLimit_fork hc
      rw [← cancel_mono c.ι]
      simp only [Fork.ofι_pt, parallelPair_obj_zero, Functor.const_obj_obj,
        Fork.IsLimit.lift_ι, Fork.ι_ofι, id_comp, comp_id]
    . apply isZero_zero

@[simps!]
noncomputable def kernel_sequence {X Y : C} (f : X ⟶ Y) [HasKernel f] [HasZeroObject C] :
    LeftHomologyData (ShortComplex.mk (kernel.ι f) f (kernel.condition f)) := by
  let h := kernel_sequence' f _ (kernelIsKernel f)
  exact h

/-
section change

variables {S} {K H : C} {f' : S.X₁ ⟶ K} {i : K ⟶ S.X₂}
  (commf' : f' ≫ i = S.f) (e : K ≅ h.K) (commi : e.hom ≫ h.i = i)
  (π : K ⟶ H) (hπ₀ : f' ≫ π = 0) (hπ : is_colimit (cokernel_cofork.of_π π hπ₀))

include commf' commi hπ

@[simps]
def change :
  LeftHomologyData S :=
begin
  have wi : i ≫ S.g = 0 := by rw [← commi, assoc, h.wi, comp_zero],
  have hi : is_limit (kernel_fork.of_ι i wi) :=
    is_limit.of_iso_limit h.hi (fork.ext e.symm (by simp [← commi])),
  let f'' := hi.lift (kernel_fork.of_ι S.f S.zero),
  have eq : f'' = f',
  { rw [← cancel_mono e.hom, ← cancel_mono h.i, assoc, commi],
    dsimp,
    erw fork.is_limit.lift_ι,
    simp only [kernel_fork.ι_of_ι, assoc, commi, commf'], },
  have wπ' : f'' ≫ π = 0 := by rw [eq, hπ₀],
  have hπ' : is_colimit (cokernel_cofork.of_π π wπ'),
  { let e : parallel_pair f'' 0 ≅ parallel_pair f' 0 :=
      parallel_pair.ext (iso.refl _) (iso.refl _) (by simp [eq]) (by simp),
    equiv_rw (is_colimit.precompose_inv_equiv e _).symm,
    exact is_colimit.of_iso_colimit hπ (cofork.ext (iso.refl _) (by tidy)), },
  exact ⟨K, H, i, π, wi, hi, wπ', hπ'⟩,
end

@[simp] lemma change_f' : (h.change commf' e commi π hπ₀ hπ).f' = f' :=
by rw [← cancel_mono (h.change commf' e commi π hπ₀ hπ).i, f'_i, change_i, commf']

end change-/

end LeftHomologyData

class HasLeftHomology : Prop :=
(condition : Nonempty S.LeftHomologyData)

noncomputable def leftHomologyData [HasLeftHomology S] :
  S.LeftHomologyData := HasLeftHomology.condition.some

variable {S}

namespace HasLeftHomology

lemma mk' (h : S.LeftHomologyData) : HasLeftHomology S :=
⟨Nonempty.intro h⟩

instance of_ker_of_coker
    [HasKernel S.g] [HasCokernel (kernel.lift S.g S.f S.zero)] :
  S.HasLeftHomology := HasLeftHomology.mk' (LeftHomologyData.of_ker_of_coker S)

instance of_hasCokernel {X Y : C} (f : X ⟶ Y) (Z : C) [HasCokernel f] :
    (ShortComplex.mk f (0 : Y ⟶ Z) comp_zero).HasLeftHomology :=
  HasLeftHomology.mk' (LeftHomologyData.of_hasCokernel _ rfl)

instance of_hasKernel {Y Z : C} (g : Y ⟶ Z) (X : C) [HasKernel g] :
    (ShortComplex.mk (0 : X ⟶ Y) g zero_comp).HasLeftHomology :=
  HasLeftHomology.mk' (LeftHomologyData.of_hasKernel _ rfl)

instance of_zeros (X Y Z : C) :
    (ShortComplex.mk (0 : X ⟶ Y) (0 : Y ⟶ Z) zero_comp).HasLeftHomology :=
  HasLeftHomology.mk' (LeftHomologyData.of_zeros _ rfl rfl)

end HasLeftHomology

section

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData)

structure LeftHomologyMapData where
  φK : h₁.K ⟶ h₂.K
  φH : h₁.H ⟶ h₂.H
  commi : φK ≫ h₂.i = h₁.i ≫ φ.τ₂ := by aesop_cat
  commf' : h₁.f' ≫ φK = φ.τ₁ ≫ h₂.f' := by aesop_cat
  commπ : h₁.π ≫ φH = φK ≫ h₂.π := by aesop_cat

namespace LeftHomologyMapData

attribute [reassoc (attr := simp)] commi commf' commπ

@[simps]
def zero (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
  LeftHomologyMapData 0 h₁ h₂ where
  φK := 0
  φH := 0

@[simps]
def id (h : S.LeftHomologyData) : LeftHomologyMapData (𝟙 S) h h where
  φK := 𝟙 _
  φH := 𝟙 _

@[simps]
def comp {φ : S₁ ⟶ S₂} {φ' : S₂ ⟶ S₃} {h₁ : S₁.LeftHomologyData}
  {h₂ : S₂.LeftHomologyData} {h₃ : S₃.LeftHomologyData}
  (ψ : LeftHomologyMapData φ h₁ h₂) (ψ' : LeftHomologyMapData φ' h₂ h₃) :
  LeftHomologyMapData (φ ≫ φ') h₁ h₃ :=
{ φK := ψ.φK ≫ ψ'.φK,
  φH := ψ.φH ≫ ψ'.φH, }

instance : Subsingleton (LeftHomologyMapData φ h₁ h₂) :=
  ⟨fun ψ₁ ψ₂ => by
    have hK : ψ₁.φK = ψ₂.φK := by rw [← cancel_mono h₂.i, commi, commi]
    have hH : ψ₁.φH = ψ₂.φH := by rw [← cancel_epi h₁.π, commπ, commπ, hK]
    cases ψ₁
    cases ψ₂
    congr⟩

attribute [-simp] mk.injEq

instance : Inhabited (LeftHomologyMapData φ h₁ h₂) := ⟨by
  let φK : h₁.K ⟶ h₂.K := h₂.lift_K (h₁.i ≫ φ.τ₂)
    (by rw [assoc, φ.comm₂₃, h₁.wi_assoc, zero_comp])
  have commf' : h₁.f' ≫ φK = φ.τ₁ ≫ h₂.f' := by
    rw [← cancel_mono h₂.i, assoc, assoc, LeftHomologyData.lift_K_i,
      LeftHomologyData.f'_i_assoc, LeftHomologyData.f'_i, φ.comm₁₂]
  let φH : h₁.H ⟶ h₂.H := h₁.desc_H (φK ≫ h₂.π)
    (by rw [reassoc_of% commf', h₂.f'_π, comp_zero])
  exact ⟨φK, φH, by simp, commf', by simp⟩⟩

instance : Unique (LeftHomologyMapData φ h₁ h₂) := Unique.mk' _

def _root_.CategoryTheory.ShortComplex.leftHomologyMapData :
  LeftHomologyMapData φ h₁ h₂ := default

variable {φ h₁ h₂}

lemma congr_φH {γ₁ γ₂ : LeftHomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂) : γ₁.φH = γ₂.φH := by rw [eq]
lemma congr_φK {γ₁ γ₂ : LeftHomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂) : γ₁.φK = γ₂.φK := by rw [eq]

@[simps]
def of_zeros (φ : S₁ ⟶ S₂) (hf₁ : S₁.f = 0) (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) (hg₂ : S₂.g = 0) :
  LeftHomologyMapData φ (LeftHomologyData.of_zeros S₁ hf₁ hg₁)
    (LeftHomologyData.of_zeros S₂ hf₂ hg₂) where
  φK := φ.τ₂
  φH := φ.τ₂
  commf' := by simp only [LeftHomologyData.of_zeros_f', φ.comm₁₂, zero_comp, comp_zero]

@[simps]
def of_isColimit_cokernelCofork (φ : S₁ ⟶ S₂)
  (hg₁ : S₁.g = 0) (c₁ : CokernelCofork S₁.f) (hc₁ : IsColimit c₁)
  (hg₂ : S₂.g = 0) (c₂ : CokernelCofork S₂.f) (hc₂ : IsColimit c₂) (f : c₁.pt ⟶ c₂.pt)
  (comm : φ.τ₂ ≫ c₂.π = c₁.π ≫ f) :
  LeftHomologyMapData φ (LeftHomologyData.of_isColimit_cokernelCofork S₁ hg₁ c₁ hc₁)
    (LeftHomologyData.of_isColimit_cokernelCofork S₂ hg₂ c₂ hc₂) where
  φK := φ.τ₂
  φH := f
  commi := by simp
  commf' := by simp only [LeftHomologyData.of_isColimit_cokernelCofork_f', φ.comm₁₂]
  commπ := comm.symm

@[simps]
def of_isLimit_kernelFork (φ : S₁ ⟶ S₂)
  (hf₁ : S₁.f = 0) (c₁ : KernelFork S₁.g) (hc₁ : IsLimit c₁)
  (hf₂ : S₂.f = 0) (c₂ : KernelFork S₂.g) (hc₂ : IsLimit c₂) (f : c₁.pt ⟶ c₂.pt)
  (comm : c₁.ι ≫ φ.τ₂ = f ≫ c₂.ι) :
  LeftHomologyMapData φ (LeftHomologyData.of_isLimit_kernelFork S₁ hf₁ c₁ hc₁)
    (LeftHomologyData.of_isLimit_kernelFork S₂ hf₂ c₂ hc₂) where
  φK := f
  φH := f
  commi := comm.symm
  commf' := by simp only [LeftHomologyData.of_isLimit_kernelFork_f', zero_comp, comp_zero]

variable (S)

@[simps]
def compatibility_of_zeros_of_isColimit_cokernelCofork (hf : S.f = 0) (hg : S.g = 0)
  (c : CokernelCofork S.f) (hc : IsColimit c) :
  LeftHomologyMapData (𝟙 S) (LeftHomologyData.of_zeros S hf hg)
    (LeftHomologyData.of_isColimit_cokernelCofork S hg c hc) where
  φK := 𝟙 _
  φH := c.π

@[simps]
def compatibility_of_zeros_of_isLimit_kernelFork (hf : S.f = 0) (hg : S.g = 0)
  (c : KernelFork S.g) (hc : IsLimit c) :
  LeftHomologyMapData (𝟙 S)
    (LeftHomologyData.of_isLimit_kernelFork S hf c hc)
    (LeftHomologyData.of_zeros S hf hg) where
  φK := c.ι
  φH := c.ι

end LeftHomologyMapData

end

variable (S)

noncomputable def leftHomology [HasLeftHomology S] : C := S.leftHomologyData.H
noncomputable def cycles [HasLeftHomology S] : C := S.leftHomologyData.K
noncomputable def leftHomology_π [HasLeftHomology S] : S.cycles ⟶ S.leftHomology :=
  S.leftHomologyData.π
noncomputable def cycles_i [HasLeftHomology S] : S.cycles ⟶ S.X₂ := S.leftHomologyData.i
noncomputable def toCycles [HasLeftHomology S] : S.X₁ ⟶ S.cycles := S.leftHomologyData.f'

@[reassoc (attr := simp)]
lemma cycles_i_g [HasLeftHomology S] : S.cycles_i ≫ S.g = 0 :=
  S.leftHomologyData.wi

@[reassoc (attr := simp)]
lemma toCycles_i [HasLeftHomology S] : S.toCycles ≫ S.cycles_i = S.f :=
  S.leftHomologyData.f'_i

instance [HasLeftHomology S] : Mono S.cycles_i := by
  dsimp only [cycles_i]
  infer_instance

instance [HasLeftHomology S] : Epi S.leftHomology_π := by
  dsimp only [leftHomology_π]
  infer_instance

variable {S}

def leftHomology_map' (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
  h₁.H ⟶ h₂.H := (leftHomologyMapData φ _ _).φH

def cycles_map' (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
  h₁.K ⟶ h₂.K := (leftHomologyMapData φ _ _).φK

@[reassoc (attr := simp)]
lemma cycles_map'_i (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    cycles_map' φ h₁ h₂ ≫ h₂.i = h₁.i ≫ φ.τ₂ :=
  LeftHomologyMapData.commi _

@[reassoc (attr := simp)]
lemma leftHomology_π_naturality' (φ : S₁ ⟶ S₂)
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    h₁.π ≫ leftHomology_map' φ h₁ h₂ = cycles_map' φ h₁ h₂ ≫ h₂.π :=
  LeftHomologyMapData.commπ _

noncomputable def leftHomology_map [HasLeftHomology S₁] [HasLeftHomology S₂]
    (φ : S₁ ⟶ S₂) : S₁.leftHomology ⟶ S₂.leftHomology :=
  leftHomology_map' φ _ _

noncomputable def cycles_map [HasLeftHomology S₁] [HasLeftHomology S₂]
    (φ : S₁ ⟶ S₂) : S₁.cycles ⟶ S₂.cycles :=
  cycles_map' φ _ _

@[reassoc (attr := simp)]
lemma cycles_map_i (φ : S₁ ⟶ S₂) [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    cycles_map φ ≫ S₂.cycles_i = S₁.cycles_i ≫ φ.τ₂ :=
  cycles_map'_i _ _ _

@[reassoc (attr := simp)]
lemma toCycles_naturality (φ : S₁ ⟶ S₂) [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    S₁.toCycles ≫ cycles_map φ = φ.τ₁ ≫ S₂.toCycles := by
  simp only [← cancel_mono S₂.cycles_i, φ.comm₁₂, assoc, toCycles_i,
    cycles_map_i, toCycles_i_assoc]

@[reassoc (attr := simp)]
lemma leftHomology_π_naturality [HasLeftHomology S₁] [HasLeftHomology S₂]
    (φ : S₁ ⟶ S₂) :
    S₁.leftHomology_π ≫ leftHomology_map φ = cycles_map φ ≫ S₂.leftHomology_π :=
  leftHomology_π_naturality' _ _ _

namespace LeftHomologyMapData

variable {φ : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}
  (γ : LeftHomologyMapData φ h₁ h₂)

lemma leftHomology_map'_eq : leftHomology_map' φ h₁ h₂ = γ.φH :=
  LeftHomologyMapData.congr_φH (Subsingleton.elim _ _)

lemma cycles_map'_eq : cycles_map' φ h₁ h₂ = γ.φK :=
  LeftHomologyMapData.congr_φK (Subsingleton.elim _ _)

end LeftHomologyMapData

@[simp]
lemma leftHomology_map'_id (h : S.LeftHomologyData) :
    leftHomology_map' (𝟙 S) h h = 𝟙 _ :=
  (LeftHomologyMapData.id h).leftHomology_map'_eq

@[simp]
lemma cycles_map'_id (h : S.LeftHomologyData) :
    cycles_map' (𝟙 S) h h = 𝟙 _ :=
  (LeftHomologyMapData.id h).cycles_map'_eq

variable (S)

@[simp]
lemma leftHomology_map_id [HasLeftHomology S] :
    leftHomology_map (𝟙 S) = 𝟙 _ :=
  leftHomology_map'_id _

@[simp]
lemma cycles_map_id [HasLeftHomology S] :
    cycles_map (𝟙 S) = 𝟙 _ :=
  cycles_map'_id _

@[simp]
lemma leftHomology_map'_zero (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    leftHomology_map' 0 h₁ h₂ = 0 :=
  (LeftHomologyMapData.zero h₁ h₂).leftHomology_map'_eq

@[simp]
lemma cycles_map'_zero (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    cycles_map' 0 h₁ h₂ = 0 :=
  (LeftHomologyMapData.zero h₁ h₂).cycles_map'_eq

variable (S₁ S₂)

@[simp]
lemma left_homology_map_zero [HasLeftHomology S₁] [HasLeftHomology S₂] :
    leftHomology_map (0 : S₁ ⟶ S₂) = 0 :=
  leftHomology_map'_zero _ _

@[simp]
lemma cycles_map_zero [HasLeftHomology S₁] [HasLeftHomology S₂] :
  cycles_map (0 : S₁ ⟶ S₂) = 0 :=
cycles_map'_zero _ _

variable {S₁ S₂}

lemma leftHomology_map'_comp (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) (h₃ : S₃.LeftHomologyData) :
    leftHomology_map' (φ₁ ≫ φ₂) h₁ h₃ = leftHomology_map' φ₁ h₁ h₂ ≫
      leftHomology_map' φ₂ h₂ h₃ := by
  let γ₁ := leftHomologyMapData φ₁ h₁ h₂
  let γ₂ := leftHomologyMapData φ₂ h₂ h₃
  rw [γ₁.leftHomology_map'_eq, γ₂.leftHomology_map'_eq, (γ₁.comp γ₂).leftHomology_map'_eq,
    LeftHomologyMapData.comp_φH]

lemma cycles_map'_comp (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) (h₃ : S₃.LeftHomologyData) :
    cycles_map' (φ₁ ≫ φ₂) h₁ h₃ = cycles_map' φ₁ h₁ h₂ ≫ cycles_map' φ₂ h₂ h₃ := by
  let γ₁ := leftHomologyMapData φ₁ h₁ h₂
  let γ₂ := leftHomologyMapData φ₂ h₂ h₃
  rw [γ₁.cycles_map'_eq, γ₂.cycles_map'_eq, (γ₁.comp γ₂).cycles_map'_eq,
    LeftHomologyMapData.comp_φK]

@[simp]
lemma leftHomology_map_comp [HasLeftHomology S₁] [HasLeftHomology S₂] [HasLeftHomology S₃]
    (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) :
    leftHomology_map (φ₁ ≫ φ₂) = leftHomology_map φ₁ ≫ leftHomology_map φ₂ :=
leftHomology_map'_comp _ _ _ _ _

@[simp]
lemma cycles_map_comp [HasLeftHomology S₁] [HasLeftHomology S₂] [HasLeftHomology S₃]
    (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) :
    cycles_map (φ₁ ≫ φ₂) = cycles_map φ₁ ≫ cycles_map φ₂ :=
  cycles_map'_comp _ _ _ _ _

@[simps]
def leftHomology_map_iso' (e : S₁ ≅ S₂) (h₁ : S₁.LeftHomologyData)
    (h₂ : S₂.LeftHomologyData) : h₁.H ≅ h₂.H where
  hom := leftHomology_map' e.hom h₁ h₂
  inv := leftHomology_map' e.inv h₂ h₁
  hom_inv_id := by rw [← leftHomology_map'_comp, e.hom_inv_id, leftHomology_map'_id]
  inv_hom_id := by rw [← leftHomology_map'_comp, e.inv_hom_id, leftHomology_map'_id]

instance isIso_leftHomology_map'_of_isIso (φ : S₁ ⟶ S₂) [IsIso φ]
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    IsIso (leftHomology_map' φ h₁ h₂) :=
  (inferInstance : IsIso (leftHomology_map_iso' (asIso φ) h₁ h₂).hom)

@[simps]
def cycles_map_iso' (e : S₁ ≅ S₂) (h₁ : S₁.LeftHomologyData)
  (h₂ : S₂.LeftHomologyData) : h₁.K ≅ h₂.K where
  hom := cycles_map' e.hom h₁ h₂
  inv := cycles_map' e.inv h₂ h₁
  hom_inv_id := by rw [← cycles_map'_comp, e.hom_inv_id, cycles_map'_id]
  inv_hom_id := by rw [← cycles_map'_comp, e.inv_hom_id, cycles_map'_id]

instance isIso_cycles_map'_of_isIso (φ : S₁ ⟶ S₂) [IsIso φ]
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    IsIso (cycles_map' φ h₁ h₂) :=
  (inferInstance : IsIso (cycles_map_iso' (asIso φ) h₁ h₂).hom)

@[simps]
noncomputable def leftHomology_map_iso (e : S₁ ≅ S₂) [S₁.HasLeftHomology]
  [S₂.HasLeftHomology] : S₁.leftHomology ≅ S₂.leftHomology where
  hom := leftHomology_map e.hom
  inv := leftHomology_map e.inv
  hom_inv_id := by rw [← leftHomology_map_comp, e.hom_inv_id, leftHomology_map_id]
  inv_hom_id := by rw [← leftHomology_map_comp, e.inv_hom_id, leftHomology_map_id]

instance isIso_leftHomologyMap_of_iso (φ : S₁ ⟶ S₂) [IsIso φ] [S₁.HasLeftHomology]
    [S₂.HasLeftHomology] :
    IsIso (leftHomology_map φ) :=
  (inferInstance : IsIso (leftHomology_map_iso (asIso φ)).hom)

@[simps]
noncomputable def cycles_map_iso (e : S₁ ≅ S₂) [S₁.HasLeftHomology]
    [S₂.HasLeftHomology] : S₁.cycles ≅ S₂.cycles where
  hom := cycles_map e.hom
  inv := cycles_map e.inv
  hom_inv_id := by rw [← cycles_map_comp, e.hom_inv_id, cycles_map_id]
  inv_hom_id := by rw [← cycles_map_comp, e.inv_hom_id, cycles_map_id]

instance isIso_cycles_map_of_iso (φ : S₁ ⟶ S₂) [IsIso φ] [S₁.HasLeftHomology]
    [S₂.HasLeftHomology] : IsIso (cycles_map φ) :=
  (inferInstance : IsIso (cycles_map_iso (asIso φ)).hom)

variable {S}

noncomputable def LeftHomologyData.leftHomology_iso (h : S.LeftHomologyData) [S.HasLeftHomology] :
  S.leftHomology ≅ h.H := leftHomology_map_iso' (Iso.refl _) _ _

noncomputable def LeftHomologyData.cycles_iso (h : S.LeftHomologyData) [S.HasLeftHomology] :
  S.cycles ≅ h.K := cycles_map_iso' (Iso.refl _) _ _

@[reassoc (attr := simp)]
lemma LeftHomologyData.cycles_iso_hom_comp_i (h : S.LeftHomologyData) [S.HasLeftHomology] :
    h.cycles_iso.hom ≫ h.i = S.cycles_i := by
  dsimp [cycles_i, LeftHomologyData.cycles_iso]
  simp only [cycles_map'_i, id_τ₂, comp_id]

@[reassoc (attr := simp)]
lemma LeftHomologyData.cycles_iso_inv_comp_cycles_i (h : S.LeftHomologyData)
    [S.HasLeftHomology] : h.cycles_iso.inv ≫ S.cycles_i = h.i := by
  simp only [← h.cycles_iso_hom_comp_i, Iso.inv_hom_id_assoc]

namespace LeftHomologyMapData

variable {φ : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}
  (γ : LeftHomologyMapData φ h₁ h₂)

lemma leftHomology_map_eq [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    leftHomology_map φ = h₁.leftHomology_iso.hom ≫ γ.φH ≫ h₂.leftHomology_iso.inv := by
  dsimp [LeftHomologyData.leftHomology_iso, leftHomology_map_iso']
  rw [← γ.leftHomology_map'_eq, ← leftHomology_map'_comp,
    ← leftHomology_map'_comp, id_comp, comp_id]
  rfl

lemma cycles_map_eq [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    cycles_map φ = h₁.cycles_iso.hom ≫ γ.φK ≫ h₂.cycles_iso.inv := by
  dsimp [LeftHomologyData.cycles_iso, cycles_map_iso']
  rw [← γ.cycles_map'_eq, ← cycles_map'_comp, ← cycles_map'_comp, id_comp, comp_id]
  rfl

lemma leftHomology_map_comm [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    leftHomology_map φ ≫ h₂.leftHomology_iso.hom = h₁.leftHomology_iso.hom ≫ γ.φH := by
  simp only [γ.leftHomology_map_eq, assoc, Iso.inv_hom_id, comp_id]

lemma cycles_map_comm [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    cycles_map φ ≫ h₂.cycles_iso.hom = h₁.cycles_iso.hom ≫ γ.φK := by
  simp only [γ.cycles_map_eq, assoc, Iso.inv_hom_id, comp_id]

end LeftHomologyMapData

variable (C)

/-- We shall say that a category with left homology is a category for which
all short complexes have left homology. -/
abbrev _root_.CategoryTheory.CategoryWithLeftHomology : Prop :=
  ∀ (S : ShortComplex C), S.HasLeftHomology

@[simps]
noncomputable def leftHomology_functor [CategoryWithLeftHomology C] :
    ShortComplex C ⥤ C where
  obj S := S.leftHomology
  map := leftHomology_map

@[simps]
noncomputable def cycles_functor [CategoryWithLeftHomology C] :
    ShortComplex C ⥤ C where
  obj S := S.cycles
  map := cycles_map

@[simps]
noncomputable def leftHomology_π_natTrans [CategoryWithLeftHomology C] :
    cycles_functor C ⟶ leftHomology_functor C where
  app S := leftHomology_π S
  naturality := fun _ _ φ => (leftHomology_π_naturality φ).symm

@[simps]
noncomputable def cycles_i_natTrans [CategoryWithLeftHomology C] :
    cycles_functor C ⟶ ShortComplex.π₂ where
  app S := S.cycles_i

@[simps]
noncomputable def toCycles_natTrans [CategoryWithLeftHomology C] :
    π₁ ⟶ cycles_functor C where
  app S := S.toCycles
  naturality := fun _ _  φ => (toCycles_naturality φ).symm

namespace LeftHomologyData

variable {C}

@[simps]
noncomputable def of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₁)
  [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : LeftHomologyData S₂ := by
  let i : h.K ⟶ S₂.X₂ := h.i ≫ φ.τ₂
  have wi : i ≫ S₂.g = 0 := by simp only [assoc, φ.comm₂₃, h.wi_assoc, zero_comp]
  have hi : IsLimit (KernelFork.ofι i wi) := KernelFork.IsLimit.ofι _ _
    (fun x hx => h.lift_K (x ≫ inv φ.τ₂) (by rw [assoc, ← cancel_mono φ.τ₃, assoc,
      assoc, ← φ.comm₂₃, IsIso.inv_hom_id_assoc, hx, zero_comp]))
    (fun x hx => by simp) (fun x hx b hb => by
      dsimp
      rw [← cancel_mono h.i, ← cancel_mono φ.τ₂, assoc, assoc, lift_K_i_assoc,
        assoc, IsIso.inv_hom_id, comp_id, hb])
  let f' := hi.lift (KernelFork.ofι S₂.f S₂.zero)
  have hf' : φ.τ₁ ≫ f' = h.f' := by
    have eq := @Fork.IsLimit.lift_ι _ _ _ _ _ _ _ ((KernelFork.ofι S₂.f S₂.zero)) hi
    simp only [Fork.ι_ofι] at eq
    rw [← cancel_mono h.i, ← cancel_mono φ.τ₂, assoc, assoc, eq, f'_i, φ.comm₁₂]
  have wπ : f' ≫ h.π = 0 := by
    rw [← cancel_epi φ.τ₁, comp_zero, reassoc_of% hf', h.f'_π]
  have hπ : IsColimit (CokernelCofork.ofπ h.π wπ) := CokernelCofork.IsColimit.ofπ _ _
    (fun x hx => h.desc_H x (by rw [← hf', assoc, hx, comp_zero]))
    (fun x hx => by simp) (fun x hx b hb => by rw [← cancel_epi h.π, π_desc_H, hb])
  exact ⟨h.K, h.H, i, h.π, wi, hi, wπ, hπ⟩

@[simp]
lemma of_epi_of_isIso_of_mono_τ₁_f' (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₁)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : φ.τ₁ ≫ (of_epi_of_isIso_of_mono φ h).f' = h.f' := by
  rw [← cancel_mono (of_epi_of_isIso_of_mono φ h).i, assoc, f'_i,
    of_epi_of_isIso_of_mono_i, f'_i_assoc, φ.comm₁₂]

@[simps]
noncomputable def of_epi_of_isIso_of_mono' (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₂)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : LeftHomologyData S₁ := by
  let i : h.K ⟶ S₁.X₂ := h.i ≫ inv φ.τ₂
  have wi : i ≫ S₁.g = 0 := by
    rw [assoc, ← cancel_mono φ.τ₃, zero_comp, assoc, assoc, ← φ.comm₂₃,
      IsIso.inv_hom_id_assoc, h.wi]
  have hi : IsLimit (KernelFork.ofι i wi) := KernelFork.IsLimit.ofι _ _
    (fun x hx => h.lift_K (x ≫ φ.τ₂)
      (by rw [assoc, φ.comm₂₃, reassoc_of% hx, zero_comp]))
    (fun x hx => by simp )
    (fun x hx b hb => by rw [← cancel_mono h.i, ← cancel_mono (inv φ.τ₂), assoc, assoc,
      hb, lift_K_i_assoc, assoc, IsIso.hom_inv_id, comp_id])
  let f' := hi.lift (KernelFork.ofι S₁.f S₁.zero)
  have hf' : f' ≫ i = S₁.f := Fork.IsLimit.lift_ι _
  have hf'' : f' = φ.τ₁ ≫ h.f' := by
    rw [← cancel_mono h.i, ← cancel_mono (inv φ.τ₂), assoc, assoc, assoc, hf', f'_i_assoc,
      φ.comm₁₂_assoc, IsIso.hom_inv_id, comp_id]
  have wπ : f' ≫ h.π = 0 := by simp only [hf'', assoc, f'_π, comp_zero]
  have hπ : IsColimit (CokernelCofork.ofπ h.π wπ) := CokernelCofork.IsColimit.ofπ _ _
    (fun x hx => h.desc_H x (by rw [← cancel_epi φ.τ₁, ← reassoc_of% hf'', hx, comp_zero]))
    (fun x hx => π_desc_H _ _ _)
    (fun x hx b hx => by rw [← cancel_epi h.π, π_desc_H, hx])
  exact ⟨h.K, h.H, i, h.π, wi, hi, wπ, hπ⟩

@[simp]
lemma of_epi_of_is_iso_of_mono'_f' (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₂)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
  (of_epi_of_isIso_of_mono' φ h).f' = φ.τ₁ ≫ h.f' :=
by rw [← cancel_mono (of_epi_of_isIso_of_mono' φ h).i, f'_i, of_epi_of_isIso_of_mono'_i,
    assoc, f'_i_assoc, φ.comm₁₂_assoc, IsIso.hom_inv_id, comp_id]

noncomputable def of_iso (e : S₁ ≅ S₂) (h₁ : LeftHomologyData S₁) : LeftHomologyData S₂ :=
  h₁.of_epi_of_isIso_of_mono e.hom

end LeftHomologyData

variable {C}

lemma HasLeftHomology_of_epi_of_is_iso_of_mono (φ : S₁ ⟶ S₂) [HasLeftHomology S₁]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HasLeftHomology S₂ :=
  HasLeftHomology.mk' (LeftHomologyData.of_epi_of_isIso_of_mono φ S₁.leftHomologyData)

lemma HasLeftHomology_of_epi_of_is_iso_of_mono' (φ : S₁ ⟶ S₂) [HasLeftHomology S₂]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HasLeftHomology S₁ :=
HasLeftHomology.mk' (LeftHomologyData.of_epi_of_isIso_of_mono' φ S₂.leftHomologyData)

lemma HasLeftHomology_of_iso {S₁ S₂ : ShortComplex C}
    (e : S₁ ≅ S₂) [HasLeftHomology S₁] : HasLeftHomology S₂ :=
  HasLeftHomology_of_epi_of_is_iso_of_mono e.hom

namespace LeftHomologyMapData

@[simps]
def of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₁)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    LeftHomologyMapData φ h (LeftHomologyData.of_epi_of_isIso_of_mono φ h) where
  φK := 𝟙 _
  φH := 𝟙 _
  commf' := by simp only [LeftHomologyData.of_epi_of_isIso_of_mono_τ₁_f' φ h, comp_id]

@[simps]
noncomputable def of_epi_of_isIso_of_mono' (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₂)
  [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    LeftHomologyMapData φ (LeftHomologyData.of_epi_of_isIso_of_mono' φ h) h :=
{ φK := 𝟙 _,
  φH := 𝟙 _, }

end LeftHomologyMapData

instance (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    IsIso (leftHomology_map' φ h₁ h₂) := by
  let h₂' := LeftHomologyData.of_epi_of_isIso_of_mono φ h₁
  haveI : IsIso (leftHomology_map' φ h₁ h₂') := by
    rw [(LeftHomologyMapData.of_epi_of_isIso_of_mono φ h₁).leftHomology_map'_eq]
    dsimp
    infer_instance
  have eq := leftHomology_map'_comp φ (𝟙 S₂) h₁ h₂' h₂
  rw [comp_id] at eq
  rw [eq]
  infer_instance

instance (φ : S₁ ⟶ S₂) [S₁.HasLeftHomology] [S₂.HasLeftHomology]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    IsIso (leftHomology_map φ) := by
  dsimp only [leftHomology_map]
  infer_instance

section

variable (S) (h : LeftHomologyData S)
  {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) [HasLeftHomology S]

noncomputable def lift_cycles : A ⟶ S.cycles :=
  S.leftHomologyData.lift_K k hk

@[reassoc (attr := simp)]
lemma lift_cycles_i : S.lift_cycles k hk ≫ S.cycles_i = k :=
  LeftHomologyData.lift_K_i _ k hk

@[reassoc]
lemma comp_lift_cycles {A' : C} (α : A' ⟶ A) :
    α ≫ S.lift_cycles k hk = S.lift_cycles (α ≫ k) (by rw [assoc, hk, comp_zero]) := by
  simp only [← cancel_mono S.cycles_i, assoc, lift_cycles_i]

noncomputable def cycles_is_kernel : IsLimit (KernelFork.ofι S.cycles_i S.cycles_i_g) :=
  S.leftHomologyData.hi

lemma isIso_cycles_i_of (hg : S.g = 0) : IsIso (S.cycles_i) :=
  KernelFork.IsLimit.isIso_ι_of_zero _ S.cycles_is_kernel hg

@[simps]
noncomputable def cycles_iso_kernel [HasKernel S.g] : S.cycles ≅ kernel S.g where
  hom := kernel.lift S.g S.cycles_i (by simp)
  inv := S.lift_cycles (kernel.ι S.g) (by simp)
  hom_inv_id := by simp only [←  cancel_mono S.cycles_i, assoc, lift_cycles_i,
    kernel.lift_ι, id_comp]
  inv_hom_id := by simp only [← cancel_mono (kernel.ι S.g), assoc, kernel.lift_ι,
    lift_cycles_i, id_comp]

@[simp]
noncomputable def lift_leftHomology : A ⟶ S.leftHomology :=
  S.lift_cycles k hk ≫ S.leftHomology_π

lemma lift_cycles_π_eq_zero_of_boundary (x : A ⟶ S.X₁) (hx : k = x ≫ S.f) :
    S.lift_cycles k (by rw [hx, assoc, S.zero, comp_zero])≫ S.leftHomology_π = 0 :=
  LeftHomologyData.lift_K_π_eq_zero_of_boundary _ k x hx

@[reassoc (attr := simp)]
lemma toCycles_comp_leftHomology_π :
  S.toCycles ≫ S.leftHomology_π = 0 :=
S.lift_cycles_π_eq_zero_of_boundary S.f (𝟙 _) (by rw [id_comp])

noncomputable def leftHomology_is_cokernel :
    IsColimit (CokernelCofork.ofπ S.leftHomology_π S.toCycles_comp_leftHomology_π) :=
  S.leftHomologyData.hπ

@[reassoc (attr := simp)]
lemma lift_cycles_comp_cycles_map (φ : S ⟶ S₁) [S₁.HasLeftHomology] :
  S.lift_cycles k hk ≫ cycles_map φ =
    S₁.lift_cycles (k ≫ φ.τ₂) (by rw [assoc, φ.comm₂₃, reassoc_of% hk, zero_comp]) :=
by simp only [← cancel_mono (S₁.cycles_i), assoc, cycles_map_i, lift_cycles_i_assoc, lift_cycles_i]

variable {S}

@[reassoc (attr := simp)]
lemma LeftHomologyData.leftHomology_π_comp_leftHomology_iso_hom :
    S.leftHomology_π ≫ h.leftHomology_iso.hom = h.cycles_iso.hom ≫ h.π := by
  dsimp only [leftHomology_π, leftHomology_iso, cycles_iso, leftHomology_map_iso',
    cycles_map_iso', Iso.refl]
  rw [← leftHomology_π_naturality']

@[reassoc (attr := simp)]
lemma LeftHomologyData.π_comp_left_homology_iso_inv :
    h.π ≫ h.leftHomology_iso.inv = h.cycles_iso.inv ≫ S.leftHomology_π := by
  simp only [← cancel_epi h.cycles_iso.hom, ← cancel_mono h.leftHomology_iso.hom, assoc,
    Iso.inv_hom_id, comp_id, Iso.hom_inv_id_assoc,
    LeftHomologyData.leftHomology_π_comp_leftHomology_iso_hom]

@[reassoc (attr := simp)]
lemma LeftHomologyData.lift_cycles_comp_cycles_iso_hom :
  S.lift_cycles k hk ≫ h.cycles_iso.hom = h.lift_K k hk :=
by simp only [←cancel_mono h.i, assoc, LeftHomologyData.cycles_iso_hom_comp_i,
  lift_cycles_i, LeftHomologyData.lift_K_i]

@[simp]
lemma LeftHomologyData.lift_K_comp_cycles_iso_inv :
    h.lift_K k hk ≫ h.cycles_iso.inv = S.lift_cycles k hk := by
  rw [← h.lift_cycles_comp_cycles_iso_hom, assoc, Iso.hom_inv_id, comp_id]

lemma LeftHomologyData.ext_iff' (f₁ f₂ : S.leftHomology ⟶ A) :
    f₁ = f₂ ↔ h.π ≫ h.leftHomology_iso.inv ≫ f₁ = h.π ≫ h.leftHomology_iso.inv ≫ f₂ := by
  rw [← cancel_epi h.leftHomology_iso.inv, cancel_epi h.π]

end

namespace HasLeftHomology

variable (S)

lemma hasKernel [S.HasLeftHomology] : HasKernel S.g :=
⟨⟨⟨_, S.leftHomologyData.hi⟩⟩⟩

lemma hasCokernel [S.HasLeftHomology] [HasKernel S.g] :
    HasCokernel (kernel.lift S.g S.f S.zero) := by
  let h := S.leftHomologyData
  haveI : HasColimit (parallelPair h.f' 0) := ⟨⟨⟨_, h.hπ'⟩⟩⟩
  let e : parallelPair (kernel.lift S.g S.f S.zero) 0 ≅ parallelPair h.f' 0 :=
    parallelPair.ext (Iso.refl _)
      (IsLimit.conePointUniqueUpToIso (kernelIsKernel S.g) h.hi)
      (by aesop_cat) (by aesop_cat)
  exact hasColimitOfIso e

end HasLeftHomology

noncomputable def leftHomology_iso_cokernel_lift [S.HasLeftHomology] [HasKernel S.g]
    [HasCokernel (kernel.lift S.g S.f S.zero)] :
    S.leftHomology ≅ cokernel (kernel.lift S.g S.f S.zero) :=
  (LeftHomologyData.of_ker_of_coker S).leftHomology_iso

namespace LeftHomologyData

lemma isIso_i_of_zero_g (h : LeftHomologyData S) (hg : S.g = 0) : IsIso h.i :=
  ⟨⟨h.lift_K (𝟙 S.X₂) (by rw [hg, id_comp]),
    by simp only [← cancel_mono h.i, id_comp, assoc, lift_K_i, comp_id], lift_K_i _ _ _⟩⟩

end LeftHomologyData

end ShortComplex

end CategoryTheory
