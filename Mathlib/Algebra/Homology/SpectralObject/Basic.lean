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

variable (n₀ : ℤ) {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
  (fg : i ⟶ k) (h : f ≫ g = fg)

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
lemma zero₂ (fg : i ⟶ k) (h : f ≫ g = fg) :
    (X.H n₀).map (twoδ₂Toδ₁ f g fg h) ≫
      (X.H n₀).map (twoδ₁Toδ₀ f g fg h) = 0 :=
  (exact_of_iso (X.iso₂ n₀ f g fg h).symm (X.exact₂' n₀ (mk₂ f g))).zero 0

@[simps]
def sc₂ : ShortComplex C :=
  ShortComplex.mk _ _ (X.zero₂ n₀ f g fg h)

lemma exact₂ : (X.sc₂ n₀ f g fg h).Exact :=
  (exact_of_iso (X.iso₂ n₀ f g fg h).symm (X.exact₂' n₀ (mk₂ f g))).exact 0

end

section

variable (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)

def δ : (X.H n₀).obj (mk₁ g) ⟶ (X.H n₁).obj (mk₁ f) :=
  (X.δ' n₀ n₁ hn₁).app (mk₂ f g)

@[reassoc]
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
  {i' j' k' : ι} (f' : i' ⟶ j') (g' : j' ⟶ k')
  {i'' j'' k'' : ι} (f'' : i'' ⟶ j'') (g'' : j'' ⟶ k'')

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

@[simps]
noncomputable def kernelSequenceCycles : ShortComplex C :=
  ShortComplex.mk _ _ (X.iCycles_δ n₀ n₁ hn₁ f g)

@[simps]
noncomputable def cokernelSequenceOpcycles : ShortComplex C :=
  ShortComplex.mk _ _ (X.δ_pOpcycles n₀ n₁ hn₁ f g)

instance : Mono (X.kernelSequenceCycles n₀ n₁ hn₁ f g).f := by
  dsimp
  infer_instance

instance : Epi (X.cokernelSequenceOpcycles n₀ n₁ hn₁ f g).g := by
  dsimp
  infer_instance

noncomputable def kernelSequenceCycles_exact :
    (X.kernelSequenceCycles n₀ n₁ hn₁ f g).Exact :=
  ShortComplex.kernelSequence_exact _

noncomputable def cokernelSequenceOpcycles_exact :
    (X.cokernelSequenceOpcycles n₀ n₁ hn₁ f g).Exact :=
  ShortComplex.cokernelSequence_exact _

section

variable {A : C} (x : A ⟶ (X.H n₀).obj (mk₁ g)) (hx : x ≫ X.δ n₀ n₁ hn₁ f g = 0)

noncomputable def liftCycles :
    A ⟶ X.cycles n₀ n₁ hn₁ f g :=
  kernel.lift _ x hx

@[reassoc (attr := simp)]
lemma liftCycles_i : X.liftCycles n₀ n₁ hn₁ f g x hx ≫ X.iCycles n₀ n₁ hn₁ f g = x := by
  apply kernel.lift_ι

end

section

variable {A : C} (x : (X.H n₁).obj (mk₁ f) ⟶ A) (hx : X.δ n₀ n₁ hn₁ f g ≫ x = 0)

noncomputable def descOpcycles :
    X.opcycles n₀ n₁ hn₁ f g ⟶ A :=
  cokernel.desc _ x hx

@[reassoc (attr := simp)]
lemma p_descOpcycles : X.pOpcycles n₀ n₁ hn₁ f g ≫ X.descOpcycles n₀ n₁ hn₁ f g x hx = x := by
  apply cokernel.π_desc

end

noncomputable def cyclesMap (α : mk₂ f g ⟶ mk₂ f' g') :
    X.cycles n₀ n₁ hn₁ f g ⟶ X.cycles n₀ n₁ hn₁ f' g' :=
  kernel.lift _ (X.iCycles n₀ n₁ hn₁ f g ≫
      (X.H n₀).map (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2))) (by
      rw [assoc, X.δ_naturality n₀ n₁ hn₁ f g f' g'
        (homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1))
          (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2)) rfl, iCycles_δ_assoc, zero_comp])

@[reassoc]
lemma cyclesMap_i (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ g ⟶ mk₁ g')
    (hβ : β = homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2)) :
    X.cyclesMap n₀ n₁ hn₁ f g f' g' α ≫ X.iCycles n₀ n₁ hn₁ f' g' =
      X.iCycles n₀ n₁ hn₁ f g ≫ (X.H n₀).map β := by
  subst hβ
  apply kernel.lift_ι

@[simp]
lemma cyclesMap_id :
    X.cyclesMap n₀ n₁ hn₁ f g f g (𝟙 _) = 𝟙 _ := by
  rw [← cancel_mono (X.iCycles n₀ n₁ hn₁ f g),
    X.cyclesMap_i n₀ n₁ hn₁ f g f g (𝟙 _) (𝟙 _) (by aesop_cat),
    Functor.map_id, comp_id, id_comp]

lemma cyclesMap_comp (α : mk₂ f g ⟶ mk₂ f' g') (α' : mk₂ f' g' ⟶ mk₂ f'' g'')
    (α'' : mk₂ f g ⟶ mk₂ f'' g'') (h : α ≫ α' = α'') :
    X.cyclesMap n₀ n₁ hn₁ f g f' g' α ≫ X.cyclesMap n₀ n₁ hn₁ f' g' f'' g'' α' =
      X.cyclesMap n₀ n₁ hn₁ f g f'' g'' α'' := by
  subst h
  rw [← cancel_mono (X.iCycles n₀ n₁ hn₁ f'' g''), assoc,
    X.cyclesMap_i n₀ n₁ hn₁ f' g' f'' g'' α' _ rfl,
    X.cyclesMap_i_assoc n₀ n₁ hn₁ f g f' g' α _ rfl,
    ← Functor.map_comp]
  symm
  apply X.cyclesMap_i
  aesop_cat

noncomputable def opcyclesMap (α : mk₂ f g ⟶ mk₂ f' g') :
    X.opcycles n₀ n₁ hn₁ f g ⟶ X.opcycles n₀ n₁ hn₁ f' g' :=
  cokernel.desc _
    ((X.H n₁).map (homMk₁ (by exact α.app 0) (by exact α.app 1) (by exact naturality' α 0 1)) ≫
      X.pOpcycles n₀ n₁ hn₁ f' g') (by
        rw [← X.δ_naturality_assoc n₀ n₁ hn₁ f g f' g'
          (homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1))
          (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2)) rfl, δ_pOpcycles, comp_zero])

@[reassoc]
lemma p_opcyclesMap (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ f ⟶ mk₁ f')
    (hβ : β = homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1)) :
    X.pOpcycles n₀ n₁ hn₁ f g ≫ X.opcyclesMap n₀ n₁ hn₁ f g f' g' α =
      (X.H n₁).map β ≫ X.pOpcycles n₀ n₁ hn₁ f' g' := by
  subst hβ
  apply cokernel.π_desc

@[simp]
lemma opcyclesMap_id :
    X.opcyclesMap n₀ n₁ hn₁ f g f g (𝟙 _) = 𝟙 _ := by
  rw [← cancel_epi (X.pOpcycles n₀ n₁ hn₁ f g),
    X.p_opcyclesMap n₀ n₁ hn₁ f g f g (𝟙 _) (𝟙 _) (by aesop_cat),
    Functor.map_id, comp_id, id_comp]

lemma opcyclesMap_comp (α : mk₂ f g ⟶ mk₂ f' g') (α' : mk₂ f' g' ⟶ mk₂ f'' g'')
    (α'' : mk₂ f g ⟶ mk₂ f'' g'') (h : α ≫ α' = α'') :
    X.opcyclesMap n₀ n₁ hn₁ f g f' g' α ≫ X.opcyclesMap n₀ n₁ hn₁ f' g' f'' g'' α' =
      X.opcyclesMap n₀ n₁ hn₁ f g f'' g'' α'' := by
  subst h
  rw [← cancel_epi (X.pOpcycles n₀ n₁ hn₁ f g),
    X.p_opcyclesMap_assoc n₀ n₁ hn₁ f g f' g' α _ rfl,
    X.p_opcyclesMap n₀ n₁ hn₁ f' g' f'' g'' α' _ rfl,
    ← Functor.map_comp_assoc]
  symm
  apply X.p_opcyclesMap
  aesop_cat

variable (fg : i ⟶ k) (h : f ≫ g = fg) (fg' : i' ⟶ k') (h' : f' ≫ g' = fg')

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

instance : Epi (X.toCycles n₀ n₁ hn₁ f g fg h) :=
  (ShortComplex.exact_iff_epi_kernel_lift _).1 (X.exact₃ n₀ n₁ hn₁ f g fg h)

@[reassoc (attr := simp)]
lemma toCycles_i :
    X.toCycles n₀ n₁ hn₁ f g fg h ≫ X.iCycles n₀ n₁ hn₁ f g =
      (X.H n₀).map (twoδ₁Toδ₀ f g fg h) := by
  apply kernel.lift_ι

@[reassoc]
lemma toCycles_cyclesMap (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ fg ⟶ mk₁ fg')
    (hβ₀ : β.app 0 = α.app 0) (hβ₁ : β.app 1 = α.app 2) :
    X.toCycles n₀ n₁ hn₁ f g fg h ≫ X.cyclesMap n₀ n₁ hn₁ f g f' g' α =
      (X.H n₀).map β ≫ X.toCycles n₀ n₁ hn₁ f' g' fg' h' := by
  rw [← cancel_mono (X.iCycles n₀ n₁ hn₁ f' g'), assoc, assoc, toCycles_i,
    X.cyclesMap_i n₀ n₁ hn₁ f g f' g' α (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2)) rfl,
    toCycles_i_assoc, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext
  · dsimp
    rw [hβ₀]
    exact naturality' α 0 1
  · dsimp
    erw [hβ₁, comp_id, id_comp]

noncomputable def fromOpcycles :
    X.opcycles n₀ n₁ hn₁ f g ⟶ (X.H n₁).obj (mk₁ fg) :=
  cokernel.desc _ ((X.H n₁).map (twoδ₂Toδ₁ f g fg h)) (by simp)

instance : Mono (X.fromOpcycles n₀ n₁ hn₁ f g fg h) :=
  (ShortComplex.exact_iff_mono_cokernel_desc _).1 (X.exact₁ n₀ n₁ hn₁ f g fg h)

@[reassoc (attr := simp)]
lemma p_fromOpcycles :
    X.pOpcycles n₀ n₁ hn₁ f g ≫ X.fromOpcycles n₀ n₁ hn₁ f g fg h =
      (X.H n₁).map (twoδ₂Toδ₁ f g fg h) := by
  apply cokernel.π_desc

@[reassoc]
lemma opcyclesMap_fromOpcycles (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ fg ⟶ mk₁ fg')
    (hβ₀ : β.app 0 = α.app 0) (hβ₁ : β.app 1 = α.app 2) :
    X.opcyclesMap n₀ n₁ hn₁ f g f' g' α ≫ X.fromOpcycles n₀ n₁ hn₁ f' g' fg' h' =
      X.fromOpcycles n₀ n₁ hn₁ f g fg h ≫ (X.H n₁).map β := by
  rw [← cancel_epi (X.pOpcycles n₀ n₁ hn₁ f g), p_fromOpcycles_assoc,
    X.p_opcyclesMap_assoc n₀ n₁ hn₁ f g f' g' α (homMk₁ (α.app 0) (α.app 1)
      (naturality' α 0 1)) rfl,
    p_fromOpcycles, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext
  · dsimp
    erw [hβ₀, id_comp, comp_id]
  · dsimp
    rw [hβ₁]
    exact (naturality' α 1 2).symm

@[reassoc (attr := simp)]
lemma H_map_twoδ₂Toδ₁_toCycles :
    (X.H n₀).map (twoδ₂Toδ₁ f g fg h) ≫ X.toCycles n₀ n₁ hn₁ f g fg h = 0 := by
  rw [← cancel_mono (X.iCycles n₀ n₁ hn₁ f g), assoc, toCycles_i, zero₂, zero_comp]

@[reassoc (attr := simp)]
lemma fromOpcycles_H_map_twoδ₁Toδ₀ :
    X.fromOpcycles n₀ n₁ hn₁ f g fg h ≫ (X.H n₁).map (twoδ₁Toδ₀ f g fg h) = 0 := by
  rw [← cancel_epi (X.pOpcycles n₀ n₁ hn₁ f g), p_fromOpcycles_assoc, zero₂, comp_zero]

@[simps]
noncomputable def cokernelSequenceCycles : ShortComplex C :=
  ShortComplex.mk _ _ (X.H_map_twoδ₂Toδ₁_toCycles n₀ n₁ hn₁ f g fg h)

@[simps]
noncomputable def kernelSequenceOpcycles : ShortComplex C :=
  ShortComplex.mk _ _ (X.fromOpcycles_H_map_twoδ₁Toδ₀ n₀ n₁ hn₁ f g fg h)

instance : Epi (X.cokernelSequenceCycles n₀ n₁ hn₁ f g fg h).g := by
  dsimp
  infer_instance

instance : Mono (X.kernelSequenceOpcycles n₀ n₁ hn₁ f g fg h).f := by
  dsimp
  infer_instance

lemma cokernelSequenceCycles_exact :
    (X.cokernelSequenceCycles n₀ n₁ hn₁ f g fg h).Exact := by
  apply ShortComplex.exact_of_g_is_cokernel
  refine' IsColimit.ofIsoColimit (cokernelIsCokernel _)
    (Cofork.ext (X.cokernelIsoCycles n₀ n₁ hn₁ f g fg h) (by
      dsimp
      simp only [← cancel_mono (X.iCycles n₀ n₁ hn₁ f g), assoc,
        cokernelIsoCycles_hom_fac, toCycles_i]))

lemma kernelSequenceOpcycles_exact :
    (X.kernelSequenceOpcycles n₀ n₁ hn₁ f g fg h).Exact := by
  apply ShortComplex.exact_of_f_is_kernel
  refine' IsLimit.ofIsoLimit (kernelIsKernel _)
    (Iso.symm (Fork.ext (X.opcyclesIsoKernel n₀ n₁ hn₁ f g fg h) (by
      dsimp
      simp only [← cancel_epi (X.pOpcycles n₀ n₁ hn₁ f g),
        opcyclesIsoKernel_hom_fac, p_fromOpcycles])))

section

variable {A : C} (x : (X.H n₀).obj (mk₁ fg) ⟶ A)
  (hx : (X.H n₀).map (twoδ₂Toδ₁ f g fg h) ≫ x = 0)

noncomputable def descCycles :
    X.cycles n₀ n₁ hn₁ f g ⟶ A :=
  (X.cokernelSequenceCycles_exact n₀ n₁ hn₁ f g fg h).desc x hx

@[reassoc (attr := simp)]
lemma toCycles_descCycles :
    X.toCycles n₀ n₁ hn₁ f g fg h ≫ X.descCycles n₀ n₁ hn₁ f g fg h x hx = x :=
  (X.cokernelSequenceCycles_exact n₀ n₁ hn₁ f g fg h).g_desc x hx

end

section

variable {A : C} (x : A ⟶ (X.H n₁).obj (mk₁ fg))
  (hx : x ≫ (X.H n₁).map (twoδ₁Toδ₀ f g fg h) = 0)

noncomputable def liftOpcycles :
    A ⟶ X.opcycles n₀ n₁ hn₁ f g :=
  (X.kernelSequenceOpcycles_exact n₀ n₁ hn₁ f g fg h).lift x hx

@[reassoc (attr := simp)]
lemma liftOpcycles_fromOpcycles :
    X.liftOpcycles n₀ n₁ hn₁ f g fg h x hx ≫ X.fromOpcycles n₀ n₁ hn₁ f g fg h = x :=
  (X.kernelSequenceOpcycles_exact n₀ n₁ hn₁ f g fg h).lift_f x hx

end

end

section

variable (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
  {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)

@[simps]
def shortComplexE : ShortComplex C where
  X₁ := (X.H n₀).obj (mk₁ f₃)
  X₂ := (X.H n₁).obj (mk₁ f₂)
  X₃ := (X.H n₂).obj (mk₁ f₁)
  f := X.δ n₀ n₁ hn₁ f₂ f₃
  g := X.δ n₁ n₂ hn₂ f₁ f₂
  zero := by simp

noncomputable def E : C := (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).homology

lemma isZero_E_of_isZero_H (h : IsZero ((X.H n₁).obj (mk₁ f₂))) :
    IsZero (X.E n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃) := by
  erw [← (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).exact_iff_isZero_homology]
  exact ShortComplex.exact_of_isZero_X₂ _ h

end

section

variable (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
  {i j k l : ι}
  {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  {i' j' k' l' : ι} (f₁' : i' ⟶ j') (f₂' : j' ⟶ k') (f₃' : k' ⟶ l')
  {i'' j'' k'' l'' : ι} (f₁'' : i'' ⟶ j'') (f₂'' : j'' ⟶ k'') (f₃'' : k'' ⟶ l'')
  (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂' f₃')
  (β : mk₃ f₁' f₂' f₃' ⟶ mk₃ f₁'' f₂'' f₃'')
  (γ : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁'' f₂'' f₃'')

@[simps]
def shortComplexEMap :
    X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ⟶
      X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁' f₂' f₃' where
  τ₁ := (X.H n₀).map (homMk₁ (α.app 2) (α.app 3) (naturality' α 2 3))
  τ₂ := (X.H n₁).map (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2))
  τ₃ := (X.H n₂).map (homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1))
  comm₁₂ := by
    apply δ_naturality
    rfl
  comm₂₃ := by
    apply δ_naturality
    rfl

lemma shortComplexEMap_id' (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁ f₂ f₃) (hα : α = 𝟙 _) :
    X.shortComplexEMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁ f₂ f₃ α = 𝟙 _ := by
  subst hα
  ext
  all_goals
    dsimp
    convert (X.H _).map_id _
    aesop_cat

@[simp]
lemma shortComplexEMap_id :
    X.shortComplexEMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁ f₂ f₃ (𝟙 _) = 𝟙 _ := by
  apply shortComplexEMap_id'
  rfl

lemma shortComplexEMap_comp' (h : α ≫ β  = γ) :
    X.shortComplexEMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α ≫
      X.shortComplexEMap n₀ n₁ n₂ hn₁ hn₂ f₁' f₂' f₃' f₁'' f₂'' f₃'' β =
        X.shortComplexEMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁'' f₂'' f₃'' γ := by
  subst h
  ext
  all_goals
    dsimp
    rw [← Functor.map_comp]
    congr 1
    aesop_cat

@[reassoc (attr := simp)]
lemma shortComplexEMap_comp :
    X.shortComplexEMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁'' f₂'' f₃'' (α ≫ β) =
    X.shortComplexEMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α ≫
      X.shortComplexEMap n₀ n₁ n₂ hn₁ hn₂ f₁' f₂' f₃' f₁'' f₂'' f₃'' β := by
  symm
  apply shortComplexEMap_comp'
  rfl

noncomputable def EMap :
    X.E n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ⟶ X.E n₀ n₁ n₂ hn₁ hn₂ f₁' f₂' f₃' :=
  ShortComplex.homologyMap (X.shortComplexEMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α)

@[simp]
lemma EMap_id :
    X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁ f₂ f₃ (𝟙 _) = 𝟙 _ := by
  dsimp only [EMap]
  rw [shortComplexEMap_id, ShortComplex.homologyMap_id]
  rfl

lemma EMap_id' (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁ f₂ f₃) (hα : α = 𝟙 _) :
    X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁ f₂ f₃ α = 𝟙 _ := by
  subst hα
  simp only [EMap_id]

@[reassoc (attr := simp)]
lemma EMap_comp :
    X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁'' f₂'' f₃'' (α ≫ β) =
    X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α ≫
      X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁' f₂' f₃' f₁'' f₂'' f₃'' β := by
  dsimp only [EMap]
  rw [shortComplexEMap_comp, ShortComplex.homologyMap_comp]

lemma EMap_comp' (h : α ≫ β  = γ) :
    X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α ≫
      X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁' f₂' f₃' f₁'' f₂'' f₃'' β =
        X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁'' f₂'' f₃'' γ := by
  subst h
  simp only [EMap_comp]

lemma isIso_EMap
    (h₀ : IsIso ((X.H n₀).map ((functorArrows ι 2 3 3).map α)))
    (h₁ : IsIso ((X.H n₁).map ((functorArrows ι 1 2 3).map α)))
    (h₂ : IsIso ((X.H n₂).map ((functorArrows ι 0 1 3).map α))) :
    IsIso (X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α) := by
  have : IsIso (shortComplexEMap X n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α) :=
    @ShortComplex.isIso_of_isIso _ _ _ _ _ _ h₀ h₁ h₂
  dsimp [EMap]
  infer_instance

end

section

variable (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
  {i j k l : ι}
  {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  {i' j' k' l' : ι} (f₁' : i' ⟶ j') (f₂' : j' ⟶ k') (f₃' : k' ⟶ l')

lemma EMap_eqToHom (h : mk₃ f₁ f₂ f₃ = mk₃ f₁' f₂' f₃') :
    X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' (eqToHom h) = eqToHom (by
      obtain rfl : i = i' := Functor.congr_obj h 0
      obtain rfl : j = j' := Functor.congr_obj h 1
      obtain rfl : k = k' := Functor.congr_obj h 2
      obtain rfl : l = l' := Functor.congr_obj h 3
      have h₁ := naturality' (eqToHom h) 0 1
      have h₂ := naturality' (eqToHom h) 1 2
      have h₃ := naturality' (eqToHom h) 2 3
      dsimp at h₁ h₂ h₃
      erw [eqToHom_app, eqToHom_app, eqToHom_refl, eqToHom_refl, id_comp, comp_id] at h₁ h₂ h₃
      subst h₁ h₂ h₃
      rfl) := by
  obtain rfl : i = i' := Functor.congr_obj h 0
  obtain rfl : j = j' := Functor.congr_obj h 1
  obtain rfl : k = k' := Functor.congr_obj h 2
  obtain rfl : l = l' := Functor.congr_obj h 3
  have h₁ := naturality' (eqToHom h) 0 1
  have h₂ := naturality' (eqToHom h) 1 2
  have h₃ := naturality' (eqToHom h) 2 3
  dsimp at h₁ h₂ h₃
  erw [eqToHom_app, eqToHom_app, eqToHom_refl, eqToHom_refl, id_comp, comp_id] at h₁ h₂ h₃
  subst h₁ h₂ h₃
  simp only [eqToHom_refl, EMap_id]

end

section

variable (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁)
  {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)

lemma δ_eq_zero_of_isIso₁ (hf : IsIso f) :
    X.δ n₀ n₁ hn₁ f g = 0 := by
  have : IsIso (twoδ₁Toδ₀ f g _ rfl) := by
    rw [isIso_iff₁]
    dsimp
    constructor <;> infer_instance
  simpa only [Preadditive.IsIso.comp_left_eq_zero] using X.zero₃ n₀ n₁ hn₁ f g _ rfl

lemma δ_eq_zero_of_isIso₂ (hg : IsIso g) :
    X.δ n₀ n₁ hn₁ f g = 0 := by
  have : IsIso (twoδ₂Toδ₁ f g _ rfl) := by
    rw [isIso_iff₁]
    dsimp
    constructor <;> infer_instance
  simpa only [Preadditive.IsIso.comp_right_eq_zero] using X.zero₁ n₀ n₁ hn₁ f g _ rfl

end

lemma isZero_H_obj_of_isIso (n : ℤ) {i j : ι} (f : i ⟶ j) (hf : IsIso f) :
    IsZero ((X.H n).obj (mk₁ f)) := by
  have e : mk₁ (𝟙 i) ≅ mk₁ f := isoMk₁ (Iso.refl _) (asIso f) (by simp)
  refine' IsZero.of_iso _ ((X.H n).mapIso e.symm)
  have h := X.zero₂ n (𝟙 i) (𝟙 i) (𝟙 i) (by simp)
  rw [← Functor.map_comp] at h
  rw [IsZero.iff_id_eq_zero, ← Functor.map_id, ← h]
  congr 1
  aesop_cat

section

variable (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
  {i j : ι} (f : i ⟶ j) {i' j' : ι} (f' : i' ⟶ j')

noncomputable def EIsoH :
    X.E n₀ n₁ n₂ hn₁ hn₂ (𝟙 i) f (𝟙 j) ≅ (X.H n₁).obj (mk₁ f) :=
  (ShortComplex.HomologyData.ofZeros (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ (𝟙 i) f (𝟙 j))
    (X.δ_eq_zero_of_isIso₂ n₀ n₁ hn₁ f (𝟙 j) inferInstance)
    (X.δ_eq_zero_of_isIso₁ n₁ n₂ hn₂ (𝟙 i) f inferInstance)).left.homologyIso

noncomputable def cycles'IsoH :
    (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ (𝟙 i) f (𝟙 j)).cycles ≅ (X.H n₁).obj (mk₁ f) :=
  (ShortComplex.HomologyData.ofZeros (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ (𝟙 i) f (𝟙 j))
    (X.δ_eq_zero_of_isIso₂ n₀ n₁ hn₁ f (𝟙 j) inferInstance)
    (X.δ_eq_zero_of_isIso₁ n₁ n₂ hn₂ (𝟙 i) f inferInstance)).left.cyclesIso

@[reassoc (attr := simp)]
lemma cycles'IsoH_inv_iCycles :
    (X.cycles'IsoH n₀ n₁ n₂ hn₁ hn₂ f).inv ≫
      (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ (𝟙 i) f (𝟙 j)).iCycles = 𝟙 _ := by
  simp [cycles'IsoH]

@[reassoc (attr := simp)]
lemma homologyπ_EIsoH_hom :
    (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ (𝟙 i) f (𝟙 j)).homologyπ ≫
      (X.EIsoH n₀ n₁ n₂ hn₁ hn₂ f).hom =
      (X.cycles'IsoH n₀ n₁ n₂ hn₁ hn₂ f).hom := by
  simp [EIsoH, cycles'IsoH]

lemma EIsoH_hom_naturality (α : mk₁ f ⟶ mk₁ f') (β : mk₃ (𝟙 _) f (𝟙 _) ⟶ mk₃ (𝟙 _) f' (𝟙 _))
    (hβ : β = homMk₃ (α.app 0) (α.app 0) (α.app 1) (α.app 1)
      (by simp) (naturality' α 0 1) (by simp)) :
  X.EMap n₀ n₁ n₂ hn₁ hn₂ (𝟙 _) f (𝟙 _) (𝟙 _) f' (𝟙 _) β ≫
    (X.EIsoH n₀ n₁ n₂ hn₁ hn₂ f').hom =
    (X.EIsoH n₀ n₁ n₂ hn₁ hn₂ f).hom ≫ (X.H n₁).map α := by
  have : α = homMk₁ (β.app 1) (β.app 2) (naturality' β 1 2 ) := by
    subst hβ
    exact hom_ext₁ rfl rfl
  subst this
  exact (ShortComplex.LeftHomologyMapData.ofZeros
    (X.shortComplexEMap n₀ n₁ n₂ hn₁ hn₂ _ _ _ _ _ _ β) _ _ _ _).homologyMap_comm

end

end SpectralObject

end

end Abelian

end CategoryTheory
