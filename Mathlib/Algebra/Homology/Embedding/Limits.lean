import Mathlib.CategoryTheory.Limits.Shapes.Kernels

namespace CategoryTheory

open Category Limits

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
