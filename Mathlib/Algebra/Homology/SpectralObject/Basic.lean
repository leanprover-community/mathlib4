import Mathlib.Algebra.Homology.SpectralObject.Misc
import Mathlib.Algebra.Homology.ExactSequenceFour

namespace CategoryTheory

open Category Limits

namespace Abelian

section

variable (C ι : Type*) [Category C] [Category ι] [Abelian C]

open ComposableArrows

structure SpectralObject where
  H (n : ℤ) : ComposableArrows ι 1 ⥤ C
  δ' (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    functorArrows ι 1 2 2 ⋙ H n₀ ⟶ functorArrows ι 0 1 2 ⋙ H n₁
  exact₁' (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (D : ComposableArrows ι 2) :
    (mk₂ ((δ' n₀ n₁ h).app D) ((H n₁).map ((mapFunctorArrows ι 0 1 0 2 2).app D))).Exact
  exact₂' (n : ℤ) (D : ComposableArrows ι 2) :
    (mk₂ ((H n).map ((mapFunctorArrows ι 0 1 0 2 2).app D))
      ((H n).map ((mapFunctorArrows ι 0 2 1 2 2).app D))).Exact
  exact₃' (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (D : ComposableArrows ι 2) :
    (mk₂ ((H n₀).map ((mapFunctorArrows ι 0 2 1 2 2).app D)) ((δ' n₀ n₁ h).app D)).Exact

namespace SpectralObject

variable {C ι}
variable (X : SpectralObject C ι)

section

variable (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)

def δ : (X.H n₀).obj (mk₁ g) ⟶ (X.H n₁).obj (mk₁ f) :=
  (X.δ' n₀ n₁ hn₁).app (mk₂ f g)

lemma δ_naturality {i' j' k' : ι} (f' : i' ⟶ j') (g' : j' ⟶ k')
    (α : mk₁ f ⟶ mk₁ f') (β : mk₁ g ⟶ mk₁ g') (hαβ : α.app 1 = β.app 0):
    (X.H n₀).map β ≫ X.δ n₀ n₁ hn₁ f' g' = X.δ n₀ n₁ hn₁ f g ≫ (X.H n₁).map α := by
  let φ : mk₂ f g ⟶ mk₂ f' g' := homMk₂ (α.app 0) (α.app 1) (β.app 1) (naturality' α 0 1)
    (by simpa only [hαβ] using naturality' β 0 1)
  have h := (X.δ' n₀ n₁ hn₁).naturality φ
  dsimp at h
  convert h
  · ext
    · exact hαβ.symm
    · rfl
  · ext <;> rfl

section

variable (fg : i ⟶ k) (h : f ≫ g = fg)

@[simp]
noncomputable def iso₁ :
    mk₂ (X.δ n₀ n₁ hn₁ f g) ((X.H n₁).map (twoδ₂Toδ₁ f g fg h)) ≅
      mk₂ ((X.δ' n₀ n₁ hn₁).app (mk₂ f g)) (((X.H n₁).map
        ((mapFunctorArrows ι 0 1 0 2 2).app (mk₂ f g)))) :=
  isoMk₂ (Iso.refl _) (Iso.refl _) ((X.H n₁).mapIso
    (isoMk₁ (Iso.refl _) (Iso.refl _) (by simpa using h.symm)))
    (by aesop_cat) (by
      dsimp [twoδ₂Toδ₁]
      simp only [← Functor.map_comp, id_comp]
      congr 1
      ext <;> simp)

@[reassoc (attr := simp)]
lemma zero₁ :
    X.δ n₀ n₁ hn₁ f g ≫
      (X.H n₁).map (twoδ₂Toδ₁ f g fg h) = 0 :=
  (exact_of_iso (X.iso₁ n₀ n₁ hn₁ f g fg h).symm (X.exact₁' n₀ n₁ hn₁ (mk₂ f g))).zero 0

@[simps]
def sc₁ : ShortComplex C :=
  ShortComplex.mk _ _ (X.zero₁ n₀ n₁ hn₁ f g fg h)

lemma exact₁ : (X.sc₁ n₀ n₁ hn₁ f g fg h).Exact :=
  (exact_of_iso (X.iso₁ n₀ n₁ hn₁ f g fg h).symm (X.exact₁' n₀ n₁ hn₁ (mk₂ f g))).exact 0

@[simp]
noncomputable def iso₂ :
    mk₂ ((X.H n₀).map (twoδ₂Toδ₁ f g fg h)) ((X.H n₀).map (twoδ₁Toδ₀ f g fg h)) ≅
        (mk₂ ((X.H n₀).map ((mapFunctorArrows ι 0 1 0 2 2).app (mk₂ f g)))
      ((X.H n₀).map ((mapFunctorArrows ι 0 2 1 2 2).app (mk₂ f g)))) :=
  isoMk₂ (Iso.refl _) ((X.H n₀).mapIso
    (isoMk₁ (Iso.refl _) (Iso.refl _) (by simpa using h.symm))) (Iso.refl _) (by
      dsimp
      simp only [← Functor.map_comp, id_comp]
      congr 1
      ext <;> simp; rfl) (by
      dsimp
      simp only [← Functor.map_comp, comp_id]
      congr 1
      ext <;> simp; rfl)

@[reassoc (attr := simp)]
lemma zero₂ :
    (X.H n₀).map (twoδ₂Toδ₁ f g fg h) ≫
      (X.H n₀).map (twoδ₁Toδ₀ f g fg h) = 0 :=
  (exact_of_iso (X.iso₂ n₀ f g fg h).symm (X.exact₂' n₀ (mk₂ f g))).zero 0

@[simps]
def sc₂ : ShortComplex C :=
  ShortComplex.mk _ _ (X.zero₂ n₀ f g fg h)

lemma exact₂ : (X.sc₂ n₀ f g fg h).Exact :=
  (exact_of_iso (X.iso₂ n₀ f g fg h).symm (X.exact₂' n₀ (mk₂ f g))).exact 0

@[simp]
noncomputable def iso₃ :
    mk₂ ((X.H n₀).map (twoδ₁Toδ₀ f g fg h))
        (X.δ n₀ n₁ hn₁ f g) ≅
      mk₂ ((X.H n₀).map ((mapFunctorArrows ι 0 2 1 2 2).app (mk₂ f g)))
        ((X.δ' n₀ n₁ hn₁).app (mk₂ f g)) :=
  isoMk₂ ((X.H n₀).mapIso (isoMk₁ (Iso.refl _) (Iso.refl _) (by simpa using h.symm)))
    (Iso.refl _) (Iso.refl _) (by
      dsimp
      rw [comp_id, ← Functor.map_comp]
      congr 1
      aesop_cat) (by aesop_cat)

@[reassoc (attr := simp)]
lemma zero₃ :
    (X.H n₀).map (twoδ₁Toδ₀ f g fg h) ≫ X.δ n₀ n₁ hn₁ f g = 0 :=
  (exact_of_iso (X.iso₃ n₀ n₁ hn₁ f g fg h).symm (X.exact₃' n₀ n₁ hn₁ (mk₂ f g))).zero 0

@[simps]
def sc₃ : ShortComplex C :=
  ShortComplex.mk _ _ (X.zero₃ n₀ n₁ hn₁ f g fg h)

lemma exact₃ : (X.sc₃ n₀ n₁ hn₁ f g fg h).Exact :=
  (exact_of_iso (X.iso₃ n₀ n₁ hn₁ f g fg h).symm (X.exact₃' n₀ n₁ hn₁ (mk₂ f g))).exact 0

@[simp]
noncomputable def composableArrows₅ :
    ComposableArrows C 5 :=
  mk₅ ((X.H n₀).map (twoδ₂Toδ₁ f g fg h)) ((X.H n₀).map (twoδ₁Toδ₀ f g fg h))
    (X.δ n₀ n₁ hn₁ f g) ((X.H n₁).map (twoδ₂Toδ₁ f g fg h))
    ((X.H n₁).map (twoδ₁Toδ₀ f g fg h))

lemma composableArrows₅_exact :
    (X.composableArrows₅ n₀ n₁ hn₁ f g fg h).Exact := by
  subst h
  exact exact_of_δ₀ (X.exact₂ n₀ f g _ rfl).exact_toComposableArrows
     (exact_of_δ₀ (X.exact₃ n₀ n₁ hn₁ f g _ rfl).exact_toComposableArrows
        (exact_of_δ₀ (X.exact₁ n₀ n₁ hn₁ f g _ rfl).exact_toComposableArrows
          ((X.exact₂ n₁ f g _ rfl).exact_toComposableArrows)))

end

end

section

variable (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
    {i j k l : ι} (f : i ⟶ j) (g : j ⟶ k) (h : k ⟶ l)

@[reassoc (attr := simp)]
lemma δ_δ : X.δ n₀ n₁ hn₁ g h ≫ X.δ n₁ n₂ hn₂ f g = 0 := by
  have eq := X.δ_naturality n₁ n₂ hn₂ f g f (g ≫ h) (𝟙 _) (twoδ₂Toδ₁ g h _ rfl) rfl
  rw [Functor.map_id, comp_id] at eq
  rw [← eq, X.zero₁_assoc n₀ n₁ hn₁ g h _ rfl, zero_comp]

end

section

variable (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁)
  {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)

noncomputable def cycles : C := kernel (X.δ n₀ n₁ hn₁ f g)

noncomputable def opcycles : C := cokernel (X.δ n₀ n₁ hn₁ f g)

noncomputable def iCycles :
    X.cycles n₀ n₁ hn₁ f g ⟶ (X.H n₀).obj (mk₁ g) :=
  kernel.ι _

noncomputable def pOpcycles :
    (X.H n₁).obj (mk₁ f) ⟶ X.opcycles n₀ n₁ hn₁ f g :=
  cokernel.π _

instance : Mono (X.iCycles n₀ n₁ hn₁ f g) := by
  dsimp [iCycles]
  infer_instance

instance : Epi (X.pOpcycles n₀ n₁ hn₁ f g) := by
  dsimp [pOpcycles]
  infer_instance

@[reassoc (attr := simp)]
lemma iCycles_δ : X.iCycles n₀ n₁ hn₁ f g ≫ X.δ n₀ n₁ hn₁ f g = 0 := by
  simp [iCycles]

@[reassoc (attr := simp)]
lemma δ_pOpcycles : X.δ n₀ n₁ hn₁ f g ≫ X.pOpcycles n₀ n₁ hn₁ f g = 0 := by
  simp [pOpcycles]

@[simps, pp_dot]
noncomputable def kernelSequenceCycles :
    ShortComplex C :=
  ShortComplex.mk _ _ (X.iCycles_δ n₀ n₁ hn₁ f g)

@[simps, pp_dot]
noncomputable def cokernelSequenceOpcycles :
    ShortComplex C :=
  ShortComplex.mk _ _ (X.δ_pOpcycles n₀ n₁ hn₁ f g)

instance : Mono (X.kernelSequenceCycles n₀ n₁ hn₁ f g).f := by
  dsimp
  infer_instance

instance : Epi (X.cokernelSequenceOpcycles n₀ n₁ hn₁ f g).g := by
  dsimp
  infer_instance

lemma kernelSequenceCycles_exact :
    (X.kernelSequenceCycles n₀ n₁ hn₁ f g).Exact :=
  ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)

lemma cokernelSequenceOpcycles_exact :
    (X.cokernelSequenceOpcycles n₀ n₁ hn₁ f g).Exact :=
  ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)


variable (fg : i ⟶ k) (h : f ≫ g = fg)

noncomputable def cokernelIsoCycles :
    cokernel ((X.H n₀).map (twoδ₂Toδ₁ f g fg h)) ≅ X.cycles n₀ n₁ hn₁ f g :=
  (X.composableArrows₅_exact n₀ n₁ hn₁ f g fg h).cokerIsoKer 0

@[reassoc (attr := simp)]
lemma cokernelIsoCycles_hom_fac :
    cokernel.π _ ≫ (X.cokernelIsoCycles n₀ n₁ hn₁ f g fg h).hom ≫
      X.iCycles n₀ n₁ hn₁ f g = (X.H n₀).map (twoδ₁Toδ₀ f g fg h) :=
  (X.composableArrows₅_exact n₀ n₁ hn₁ f g fg h).cokerIsoKer_hom_fac 0

noncomputable def opcyclesIsoKernel :
    X.opcycles n₀ n₁ hn₁ f g ≅ kernel ((X.H n₁).map (twoδ₁Toδ₀ f g fg h)) :=
  (X.composableArrows₅_exact n₀ n₁ hn₁ f g fg h).cokerIsoKer 2

@[reassoc (attr := simp)]
lemma opcyclesIsoKernel_hom_fac :
    X.pOpcycles n₀ n₁ hn₁ f g ≫ (X.opcyclesIsoKernel n₀ n₁ hn₁ f g fg h).hom ≫
      kernel.ι _ = (X.H n₁).map (twoδ₂Toδ₁ f g fg h) :=
  (X.composableArrows₅_exact n₀ n₁ hn₁ f g fg h).cokerIsoKer_hom_fac 2

noncomputable def toCycles : (X.H n₀).obj (mk₁ fg) ⟶ X.cycles n₀ n₁ hn₁ f g :=
  kernel.lift _ ((X.H n₀).map (twoδ₁Toδ₀ f g fg h)) (by simp)

@[reassoc (attr := simp)]
lemma toCycles_i :
    X.toCycles n₀ n₁ hn₁ f g fg h ≫ X.iCycles n₀ n₁ hn₁ f g =
      (X.H n₀).map (twoδ₁Toδ₀ f g fg h) := by
  apply kernel.lift_ι

noncomputable def fromOpcycles :
    X.opcycles n₀ n₁ hn₁ f g ⟶ (X.H n₁).obj (mk₁ fg) :=
  cokernel.desc _ ((X.H n₁).map (twoδ₂Toδ₁ f g fg h)) (by simp)

@[reassoc (attr := simp)]
lemma p_fromOpcycles :
    X.pOpcycles n₀ n₁ hn₁ f g ≫ X.fromOpcycles n₀ n₁ hn₁ f g fg h =
      (X.H n₁).map (twoδ₂Toδ₁ f g fg h) := by
  apply cokernel.π_desc

end

end SpectralObject

end

end Abelian

end CategoryTheory
