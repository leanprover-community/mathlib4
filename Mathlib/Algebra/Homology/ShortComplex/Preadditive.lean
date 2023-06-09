import Mathlib.Algebra.Homology.ShortComplex.QuasiIso
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Opposite

namespace CategoryTheory

open Category Limits Preadditive

variable {C : Type _} [Category C] [Preadditive C]

lemma mono_of_isZero_kernel' {X Y : C} {f : X ⟶ Y} (c : KernelFork f) (hc : IsLimit c)
    (h : IsZero c.pt) : Mono f := ⟨fun g₁ g₂ eq => by
  rw [← sub_eq_zero, ← Preadditive.sub_comp] at eq
  obtain ⟨a, ha⟩ := KernelFork.IsLimit.lift' hc _ eq
  rw [← sub_eq_zero, ← ha, h.eq_of_tgt a 0, zero_comp]⟩

lemma mono_of_isZero_kernel {X Y : C} (f : X ⟶ Y) [HasKernel f] (h : IsZero (kernel f)) :
    Mono f :=
  mono_of_isZero_kernel' _ (kernelIsKernel _) h

lemma epi_of_isZero_cokernel' {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f) (hc : IsColimit c)
    (h : IsZero c.pt) : Epi f := ⟨fun g₁ g₂ eq => by
  rw [← sub_eq_zero, ← Preadditive.comp_sub] at eq
  obtain ⟨a, ha⟩ := CokernelCofork.IsColimit.desc' hc _ eq
  rw [← sub_eq_zero, ← ha, h.eq_of_src a 0, comp_zero]⟩

lemma epi_of_isZero_cokernel {X Y : C} (f : X ⟶ Y) [HasCokernel f] (h : IsZero (cokernel f)) :
    Epi f :=
  epi_of_isZero_cokernel' _ (cokernelIsCokernel _) h

namespace ShortComplex

variable {S₁ S₂ S₃ : ShortComplex C}

attribute [local simp] Hom.comm₁₂ Hom.comm₂₃

instance : Add (S₁ ⟶ S₂) where
  add φ φ' :=
  { τ₁ := φ.τ₁ + φ'.τ₁
    τ₂ := φ.τ₂ + φ'.τ₂
    τ₃ := φ.τ₃ + φ'.τ₃ }

instance : Sub (S₁ ⟶ S₂) where
  sub φ φ' :=
  { τ₁ := φ.τ₁ - φ'.τ₁
    τ₂ := φ.τ₂ - φ'.τ₂
    τ₃ := φ.τ₃ - φ'.τ₃ }

instance : Neg (S₁ ⟶ S₂) where
  neg φ :=
  { τ₁ := -φ.τ₁
    τ₂ := -φ.τ₂
    τ₃ := -φ.τ₃ }

instance : AddCommGroup (S₁ ⟶ S₂) where
  add_assoc := fun a b c => by ext <;> apply add_assoc
  add_zero := fun a => by ext <;> apply add_zero
  zero_add := fun a => by ext <;> apply zero_add
  add_left_neg := fun a => by ext <;> apply add_left_neg
  add_comm := fun a b => by ext <;> apply add_comm
  sub_eq_add_neg := fun a b => by ext <;> apply sub_eq_add_neg

@[simp] lemma add_τ₁ (φ φ' : S₁ ⟶ S₂) : (φ + φ').τ₁ = φ.τ₁ + φ'.τ₁ := rfl
@[simp] lemma add_τ₂ (φ φ' : S₁ ⟶ S₂) : (φ + φ').τ₂ = φ.τ₂ + φ'.τ₂ := rfl
@[simp] lemma add_τ₃ (φ φ' : S₁ ⟶ S₂) : (φ + φ').τ₃ = φ.τ₃ + φ'.τ₃ := rfl
@[simp] lemma sub_τ₁ (φ φ' : S₁ ⟶ S₂) : (φ - φ').τ₁ = φ.τ₁ - φ'.τ₁ := rfl
@[simp] lemma sub_τ₂ (φ φ' : S₁ ⟶ S₂) : (φ - φ').τ₂ = φ.τ₂ - φ'.τ₂ := rfl
@[simp] lemma sub_τ₃ (φ φ' : S₁ ⟶ S₂) : (φ - φ').τ₃ = φ.τ₃ - φ'.τ₃ := rfl
@[simp] lemma neg_τ₁ (φ : S₁ ⟶ S₂) : (-φ).τ₁ = -φ.τ₁ := rfl
@[simp] lemma neg_τ₂ (φ : S₁ ⟶ S₂) : (-φ).τ₂ = -φ.τ₂ := rfl
@[simp] lemma neg_τ₃ (φ : S₁ ⟶ S₂) : (-φ).τ₃ = -φ.τ₃ := rfl

instance : Preadditive (ShortComplex C) where
  add_comp := by intros ; ext <;> dsimp <;> simp
  comp_add := by intros ; ext <;> dsimp <;> simp

section LeftHomology

variable {φ φ' : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}

namespace LeftHomologyMapData

variable (γ : LeftHomologyMapData φ h₁ h₂) (γ' : LeftHomologyMapData φ' h₁ h₂)

@[simps]
def neg : LeftHomologyMapData (-φ) h₁ h₂ where
  φK := -γ.φK
  φH := -γ.φH

@[simps]
def add : LeftHomologyMapData (φ + φ') h₁ h₂ where
  φK := γ.φK + γ'.φK
  φH := γ.φH + γ'.φH

end LeftHomologyMapData

variable (h₁ h₂)

@[simp]
lemma leftHomologyMap'_neg :
    leftHomologyMap' (-φ) h₁ h₂ = -leftHomologyMap' φ h₁ h₂ := by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  simp only [γ.leftHomologyMap'_eq, γ.neg.leftHomologyMap'_eq, LeftHomologyMapData.neg_φH]

@[simp]
lemma cyclesMap'_neg :
    cyclesMap' (-φ) h₁ h₂ = -cyclesMap' φ h₁ h₂ := by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  simp only [γ.cyclesMap'_eq, γ.neg.cyclesMap'_eq, LeftHomologyMapData.neg_φK]

@[simp]
lemma leftHomologyMap'_add :
    leftHomologyMap' (φ + φ') h₁ h₂ = leftHomologyMap' φ h₁ h₂ +
      leftHomologyMap' φ' h₁ h₂ := by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  have γ' : LeftHomologyMapData φ' h₁ h₂ := default
  simp only [γ.leftHomologyMap'_eq, γ'.leftHomologyMap'_eq,
    (γ.add γ').leftHomologyMap'_eq, LeftHomologyMapData.add_φH]

@[simp]
lemma cyclesMap'_add :
    cyclesMap' (φ + φ') h₁ h₂ = cyclesMap' φ h₁ h₂ +
      cyclesMap' φ' h₁ h₂ := by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  have γ' : LeftHomologyMapData φ' h₁ h₂ := default
  simp only [γ.cyclesMap'_eq, γ'.cyclesMap'_eq,
    (γ.add γ').cyclesMap'_eq, LeftHomologyMapData.add_φK]

@[simp]
lemma leftHomologyMap'_sub :
    leftHomologyMap' (φ - φ') h₁ h₂ = leftHomologyMap' φ h₁ h₂ -
      leftHomologyMap' φ' h₁ h₂ := by
  simp only [sub_eq_add_neg, leftHomologyMap'_add, leftHomologyMap'_neg]

@[simp]
lemma cyclesMap'_sub :
    cyclesMap' (φ - φ') h₁ h₂ = cyclesMap' φ h₁ h₂ -
      cyclesMap' φ' h₁ h₂ := by
  simp only [sub_eq_add_neg, cyclesMap'_add, cyclesMap'_neg]

variable (φ φ')

section

variable [S₁.HasLeftHomology] [S₂.HasLeftHomology]

@[simp]
lemma leftHomologyMap_neg : leftHomologyMap (-φ)  = -leftHomologyMap φ :=
  leftHomologyMap'_neg _ _

@[simp]
lemma cyclesMap_neg : cyclesMap (-φ) = -cyclesMap φ :=
  cyclesMap'_neg _ _

@[simp]
lemma leftHomologyMap_add : leftHomologyMap (φ + φ')  = leftHomologyMap φ + leftHomologyMap φ' :=
  leftHomologyMap'_add _ _

@[simp]
lemma cyclesMap_add : cyclesMap (φ + φ') = cyclesMap φ + cyclesMap φ' :=
  cyclesMap'_add _ _

@[simp]
lemma leftHomologyMap_sub : leftHomologyMap (φ - φ') = leftHomologyMap φ - leftHomologyMap φ' :=
  leftHomologyMap'_sub  _ _

@[simp]
lemma cyclesMap_sub : cyclesMap (φ - φ') = cyclesMap φ - cyclesMap φ' :=
  cyclesMap'_sub _ _

end

instance leftHomologyFunctor_additive [HasKernels C] [HasCokernels C] :
  (leftHomologyFunctor C).Additive where

instance cyclesFunctor_additive [HasKernels C] [HasCokernels C] :
  (cyclesFunctor C).Additive where

end LeftHomology

section RightHomology

variable {φ φ' : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}

namespace RightHomologyMapData

variable (γ : RightHomologyMapData φ h₁ h₂) (γ' : RightHomologyMapData φ' h₁ h₂)

@[simps]
def neg : RightHomologyMapData (-φ) h₁ h₂ where
  φQ := -γ.φQ
  φH := -γ.φH

@[simps]
def add : RightHomologyMapData (φ + φ') h₁ h₂ where
  φQ := γ.φQ + γ'.φQ
  φH := γ.φH + γ'.φH

end RightHomologyMapData

variable (h₁ h₂)

@[simp]
lemma rightHomologyMap'_neg :
    rightHomologyMap' (-φ) h₁ h₂ = -rightHomologyMap' φ h₁ h₂ := by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  simp only [γ.rightHomologyMap'_eq, γ.neg.rightHomologyMap'_eq, RightHomologyMapData.neg_φH]

@[simp]
lemma opcyclesMap'_neg :
    opcyclesMap' (-φ) h₁ h₂ = -opcyclesMap' φ h₁ h₂ := by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  simp only [γ.opcyclesMap'_eq, γ.neg.opcyclesMap'_eq, RightHomologyMapData.neg_φQ]

@[simp]
lemma rightHomologyMap'_add :
    rightHomologyMap' (φ + φ') h₁ h₂ = rightHomologyMap' φ h₁ h₂ +
      rightHomologyMap' φ' h₁ h₂ := by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  have γ' : RightHomologyMapData φ' h₁ h₂ := default
  simp only [γ.rightHomologyMap'_eq, γ'.rightHomologyMap'_eq,
    (γ.add γ').rightHomologyMap'_eq, RightHomologyMapData.add_φH]

@[simp]
lemma opcyclesMap'_add :
    opcyclesMap' (φ + φ') h₁ h₂ = opcyclesMap' φ h₁ h₂ +
      opcyclesMap' φ' h₁ h₂ := by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  have γ' : RightHomologyMapData φ' h₁ h₂ := default
  simp only [γ.opcyclesMap'_eq, γ'.opcyclesMap'_eq,
    (γ.add γ').opcyclesMap'_eq, RightHomologyMapData.add_φQ]

@[simp]
lemma rightHomologyMap'_sub :
    rightHomologyMap' (φ - φ') h₁ h₂ = rightHomologyMap' φ h₁ h₂ -
      rightHomologyMap' φ' h₁ h₂ := by
  simp only [sub_eq_add_neg, rightHomologyMap'_add, rightHomologyMap'_neg]

@[simp]
lemma opcyclesMap'_sub :
    opcyclesMap' (φ - φ') h₁ h₂ = opcyclesMap' φ h₁ h₂ -
      opcyclesMap' φ' h₁ h₂ := by
  simp only [sub_eq_add_neg, opcyclesMap'_add, opcyclesMap'_neg]

variable (φ φ')

section

variable [S₁.HasRightHomology] [S₂.HasRightHomology]

@[simp]
lemma rightHomologyMap_neg : rightHomologyMap (-φ)  = -rightHomologyMap φ :=
  rightHomologyMap'_neg _ _

@[simp]
lemma opcyclesMap_neg : opcyclesMap (-φ) = -opcyclesMap φ :=
  opcyclesMap'_neg _ _

@[simp]
lemma rightHomologyMap_add : rightHomologyMap (φ + φ')  = rightHomologyMap φ + rightHomologyMap φ' :=
  rightHomologyMap'_add _ _

@[simp]
lemma opcyclesMap_add : opcyclesMap (φ + φ') = opcyclesMap φ + opcyclesMap φ' :=
  opcyclesMap'_add _ _

@[simp]
lemma rightHomologyMap_sub : rightHomologyMap (φ - φ') = rightHomologyMap φ - rightHomologyMap φ' :=
  rightHomologyMap'_sub  _ _

@[simp]
lemma opcyclesMap_sub : opcyclesMap (φ - φ') = opcyclesMap φ - opcyclesMap φ' :=
  opcyclesMap'_sub _ _

end

instance rightHomologyFunctor_additive [HasKernels C] [HasCokernels C] :
  (rightHomologyFunctor C).Additive where

instance opcyclesFunctor_additive [HasKernels C] [HasCokernels C] :
  (opcyclesFunctor C).Additive where

end RightHomology

section Homology

variable {φ φ' : S₁ ⟶ S₂} {h₁ : S₁.HomologyData} {h₂ : S₂.HomologyData}

namespace HomologyMapData

variable (γ : HomologyMapData φ h₁ h₂) (γ' : HomologyMapData φ' h₁ h₂)

@[simps]
def neg : HomologyMapData (-φ) h₁ h₂ where
  left := γ.left.neg
  right := γ.right.neg

@[simps]
def add : HomologyMapData (φ + φ') h₁ h₂ where
  left := γ.left.add γ'.left
  right := γ.right.add γ'.right

end HomologyMapData

variable (h₁ h₂)

@[simp]
lemma homologyMap'_neg :
    homologyMap' (-φ) h₁ h₂ = -homologyMap' φ h₁ h₂ :=
  leftHomologyMap'_neg _ _

@[simp]
lemma homologyMap'_add :
    homologyMap' (φ + φ') h₁ h₂ = homologyMap' φ h₁ h₂ +
      homologyMap' φ' h₁ h₂ :=
  leftHomologyMap'_add _ _

@[simp]
lemma homologyMap'_sub :
    homologyMap' (φ - φ') h₁ h₂ = homologyMap' φ h₁ h₂ -
      homologyMap' φ' h₁ h₂ :=
  leftHomologyMap'_sub _ _

variable (φ φ')

section

variable [S₁.HasHomology] [S₂.HasHomology]

@[simp]
lemma homologyMap_neg : homologyMap (-φ)  = -homologyMap φ :=
  homologyMap'_neg _ _

@[simp]
lemma homologyMap_add : homologyMap (φ + φ')  = homologyMap φ + homologyMap φ' :=
  homologyMap'_add _ _

@[simp]
lemma homologyMap_sub : homologyMap (φ - φ') = homologyMap φ - homologyMap φ' :=
  homologyMap'_sub  _ _

end

instance homologyFunctor_additive [CategoryWithHomology C] :
  (homologyFunctor C).Additive where

end Homology

section Homotopy

variable (φ₁ φ₂ φ₃ : S₁ ⟶ S₂)

@[ext]
structure Homotopy where
  h₀ : S₁.X₁ ⟶ S₂.X₁
  h₀_f : h₀ ≫ S₂.f = 0 := by aesop_cat
  h₁ : S₁.X₂ ⟶ S₂.X₁
  h₂ : S₁.X₃ ⟶ S₂.X₂
  h₃ : S₁.X₃ ⟶ S₂.X₃
  g_h₃ : S₁.g ≫ h₃ = 0 := by aesop_cat
  comm₁ : φ₁.τ₁ = S₁.f ≫ h₁ + h₀ + φ₂.τ₁ := by aesop_cat
  comm₂ : φ₁.τ₂ = S₁.g ≫ h₂ + h₁ ≫ S₂.f + φ₂.τ₂ := by aesop_cat
  comm₃ : φ₁.τ₃ = h₃ + h₂ ≫ S₂.g + φ₂.τ₃ := by aesop_cat

attribute [reassoc (attr := simp)] Homotopy.h₀_f Homotopy.g_h₃

variable (S₁ S₂)

@[simps]
def nullHomotopic (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
    (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
    S₁ ⟶ S₂ where
  τ₁ := h₀ + S₁.f ≫ h₁
  τ₂ := h₁ ≫ S₂.f + S₁.g ≫ h₂
  τ₃ := h₂ ≫ S₂.g + h₃

namespace Homotopy

attribute [local simp] neg_comp

variable {S₁ S₂ φ₁ φ₂ φ₃}

@[simps]
def ofEq (h : φ₁ = φ₂) : Homotopy φ₁ φ₂ where
  h₀ := 0
  h₁ := 0
  h₂ := 0
  h₃ := 0

@[simps!]
def refl (φ : S₁ ⟶ S₂) : Homotopy φ φ := ofEq rfl

@[simps]
def symm (h : Homotopy φ₁ φ₂) : Homotopy φ₂ φ₁ where
  h₀ := -h.h₀
  h₁ := -h.h₁
  h₂ := -h.h₂
  h₃ := -h.h₃
  comm₁ := by rw [h.comm₁, comp_neg] ; abel
  comm₂ := by rw [h.comm₂, comp_neg, neg_comp] ; abel
  comm₃ := by rw [h.comm₃, neg_comp] ; abel

@[simps]
def neg (h : Homotopy φ₁ φ₂) : Homotopy (-φ₁) (-φ₂) where
  h₀ := -h.h₀
  h₁ := -h.h₁
  h₂ := -h.h₂
  h₃ := -h.h₃
  comm₁ := by rw [neg_τ₁, neg_τ₁, h.comm₁, neg_add_rev, comp_neg] ; abel
  comm₂ := by rw [neg_τ₂, neg_τ₂, h.comm₂, neg_add_rev, comp_neg, neg_comp] ; abel
  comm₃ := by rw [neg_τ₃, neg_τ₃, h.comm₃, neg_comp] ; abel

@[simps]
def trans (h₁₂ : Homotopy φ₁ φ₂) (h₂₃ : Homotopy φ₂ φ₃) : Homotopy φ₁ φ₃ where
  h₀ := h₁₂.h₀ + h₂₃.h₀
  h₁ := h₁₂.h₁ + h₂₃.h₁
  h₂ := h₁₂.h₂ + h₂₃.h₂
  h₃ := h₁₂.h₃ + h₂₃.h₃
  comm₁ := by rw [h₁₂.comm₁, h₂₃.comm₁, comp_add] ; abel
  comm₂ := by rw [h₁₂.comm₂, h₂₃.comm₂, comp_add, add_comp] ; abel
  comm₃ := by rw [h₁₂.comm₃, h₂₃.comm₃, add_comp] ; abel

@[simps]
def add (h : Homotopy φ₁ φ₂) (h' : Homotopy φ₃ φ₄) : Homotopy (φ₁ + φ₃) (φ₂ + φ₄) where
  h₀ := h.h₀ + h'.h₀
  h₁ := h.h₁ + h'.h₁
  h₂ := h.h₂ + h'.h₂
  h₃ := h.h₃ + h'.h₃
  comm₁ := by rw [add_τ₁, add_τ₁, h.comm₁, h'.comm₁, comp_add] ; abel
  comm₂ := by rw [add_τ₂, add_τ₂, h.comm₂, h'.comm₂, comp_add, add_comp] ; abel
  comm₃ := by rw [add_τ₃, add_τ₃, h.comm₃, h'.comm₃, add_comp] ; abel

@[simps]
def sub (h : Homotopy φ₁ φ₂) (h' : Homotopy φ₃ φ₄) : Homotopy (φ₁ - φ₃) (φ₂ - φ₄) where
  h₀ := h.h₀ - h'.h₀
  h₁ := h.h₁ - h'.h₁
  h₂ := h.h₂ - h'.h₂
  h₃ := h.h₃ - h'.h₃
  comm₁ := by rw [sub_τ₁, sub_τ₁, h.comm₁, h'.comm₁, comp_sub] ; abel
  comm₂ := by rw [sub_τ₂, sub_τ₂, h.comm₂, h'.comm₂, comp_sub, sub_comp] ; abel
  comm₃ := by rw [sub_τ₃, sub_τ₃, h.comm₃, h'.comm₃, sub_comp] ; abel

@[simps]
def comp_left (h : Homotopy φ₁ φ₂) (ψ : S₃ ⟶ S₁) : Homotopy (ψ ≫ φ₁) (ψ ≫ φ₂) where
  h₀ := ψ.τ₁ ≫ h.h₀
  h₁ := ψ.τ₂ ≫ h.h₁
  h₂ := ψ.τ₃ ≫ h.h₂
  h₃ := ψ.τ₃ ≫ h.h₃
  g_h₃ := by rw [← ψ.comm₂₃_assoc, h.g_h₃, comp_zero]
  comm₁ := by rw [comp_τ₁, comp_τ₁, h.comm₁, comp_add, comp_add, add_left_inj, ψ.comm₁₂_assoc]
  comm₂ := by rw [comp_τ₂, comp_τ₂, h.comm₂, comp_add, comp_add, assoc, ψ.comm₂₃_assoc]
  comm₃ := by rw [comp_τ₃, comp_τ₃, h.comm₃, comp_add, comp_add, assoc]

@[simps]
def comp_right (h : Homotopy φ₁ φ₂) (ψ : S₂ ⟶ S₃) : Homotopy (φ₁ ≫ ψ) (φ₂ ≫ ψ) where
  h₀ := h.h₀ ≫ ψ.τ₁
  h₁ := h.h₁ ≫ ψ.τ₁
  h₂ := h.h₂ ≫ ψ.τ₂
  h₃ := h.h₃ ≫ ψ.τ₃
  comm₁ := by rw [comp_τ₁, comp_τ₁, h.comm₁, add_comp, add_comp, assoc]
  comm₂ := by rw [comp_τ₂, comp_τ₂, h.comm₂, add_comp, add_comp, assoc, assoc, assoc, ψ.comm₁₂]
  comm₃ := by rw [comp_τ₃, comp_τ₃, h.comm₃, add_comp, add_comp, assoc, assoc, ψ.comm₂₃]

@[simps]
def op (h : Homotopy φ₁ φ₂) : Homotopy (opMap φ₁) (opMap φ₂) where
  h₀ := h.h₃.op
  h₁ := h.h₂.op
  h₂ := h.h₁.op
  h₃ := h.h₀.op
  h₀_f := Quiver.Hom.unop_inj h.g_h₃
  g_h₃ := Quiver.Hom.unop_inj h.h₀_f
  comm₁ := Quiver.Hom.unop_inj (by dsimp ; rw [h.comm₃] ; abel)
  comm₂ := Quiver.Hom.unop_inj (by dsimp ; rw [h.comm₂] ; abel)
  comm₃ := Quiver.Hom.unop_inj (by dsimp ; rw [h.comm₁] ; abel)

@[simps]
def unop {S₁ S₂ : ShortComplex Cᵒᵖ} {φ₁ φ₂ : S₁ ⟶ S₂}  (h : Homotopy φ₁ φ₂) :
    Homotopy (unopMap φ₁) (unopMap φ₂) where
  h₀ := h.h₃.unop
  h₁ := h.h₂.unop
  h₂ := h.h₁.unop
  h₃ := h.h₀.unop
  h₀_f := Quiver.Hom.op_inj h.g_h₃
  g_h₃ := Quiver.Hom.op_inj h.h₀_f
  comm₁ := Quiver.Hom.op_inj (by dsimp ; rw [h.comm₃] ; abel)
  comm₂ := Quiver.Hom.op_inj (by dsimp ; rw [h.comm₂] ; abel)
  comm₃ := Quiver.Hom.op_inj (by dsimp ; rw [h.comm₁] ; abel)

variable (φ₁ φ₂)

@[simps]
def equivSubZero : Homotopy φ₁ φ₂ ≃ Homotopy (φ₁ - φ₂) 0 where
  toFun h := (h.sub (refl φ₂)).trans (ofEq (sub_self φ₂))
  invFun h := ((ofEq (sub_add_cancel φ₁ φ₂).symm).trans
    (h.add (refl φ₂))).trans (ofEq (zero_add φ₂))
  left_inv := by aesop_cat
  right_inv := by aesop_cat

variable {φ₁ φ₂}

lemma eq_add_null_homotopic (h : Homotopy φ₁ φ₂) :
    φ₁ = φ₂ + nullHomotopic _ _ h.h₀ h.h₀_f h.h₁ h.h₂ h.h₃ h.g_h₃ := by
  ext
  . dsimp ; rw [h.comm₁] ; abel
  . dsimp ; rw [h.comm₂] ; abel
  . dsimp ; rw [h.comm₃] ; abel

variable (S₁ S₂)

@[simps]
def ofNullHomotopic (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
  (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
  Homotopy (nullHomotopic _ _ h₀ h₀_f h₁ h₂ h₃ g_h₃) 0 where
  h₀ := h₀
  h₁ := h₁
  h₂ := h₂
  h₃ := h₃
  h₀_f := h₀_f
  g_h₃ := g_h₃
  comm₁ := by rw [nullHomotopic_τ₁, zero_τ₁, add_zero] ; abel
  comm₂ := by rw [nullHomotopic_τ₂, zero_τ₂, add_zero] ; abel
  comm₃ := by rw [nullHomotopic_τ₃, zero_τ₃, add_zero] ; abel

end Homotopy

variable {S₁ S₂}

def LeftHomologyMapData.ofNullHomotopic
    (H₁ : S₁.LeftHomologyData) (H₂ : S₂.LeftHomologyData)
    (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
    (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
    LeftHomologyMapData (nullHomotopic _ _ h₀ h₀_f h₁ h₂ h₃ g_h₃) H₁ H₂ where
  φK := H₂.liftK (H₁.i ≫ h₁ ≫ S₂.f) (by simp)
  φH := 0
  commf' := by
    rw [← cancel_mono H₂.i, assoc, LeftHomologyData.liftK_i, LeftHomologyData.f'_i_assoc,
      nullHomotopic_τ₁, add_comp, add_comp, assoc, assoc, assoc, LeftHomologyData.f'_i,
      self_eq_add_left, h₀_f]
  commπ := by
    rw [H₂.liftK_π_eq_zero_of_boundary (H₁.i ≫ h₁ ≫ S₂.f) (H₁.i ≫ h₁) (by rw [assoc]), comp_zero]

def RightHomologyMapData.ofNullHomotopic
    (H₁ : S₁.RightHomologyData) (H₂ : S₂.RightHomologyData)
    (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
    (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
    RightHomologyMapData (nullHomotopic _ _ h₀ h₀_f h₁ h₂ h₃ g_h₃) H₁ H₂ where
  φQ := H₁.descQ (S₁.g ≫ h₂ ≫ H₂.p) (by simp)
  φH := 0
  commg' := by
    rw [← cancel_epi H₁.p, RightHomologyData.p_descQ_assoc, RightHomologyData.p_g'_assoc,
      nullHomotopic_τ₃, comp_add, assoc, assoc, RightHomologyData.p_g', g_h₃, add_zero]
  commι := by
    rw [H₁.ι_descQ_eq_zero_of_boundary (S₁.g ≫ h₂ ≫ H₂.p) (h₂ ≫ H₂.p) rfl, zero_comp]

@[simp]
lemma leftHomologyMap'_nullHomotopic
    (H₁ : S₁.LeftHomologyData) (H₂ : S₂.LeftHomologyData)
    (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
    (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
    leftHomologyMap' (nullHomotopic _ _ h₀ h₀_f h₁ h₂ h₃ g_h₃) H₁ H₂ = 0 :=
  (LeftHomologyMapData.ofNullHomotopic H₁ H₂ h₀ h₀_f h₁ h₂ h₃ g_h₃).leftHomologyMap'_eq

@[simp]
lemma rightHomologyMap'_nullHomotopic
    (H₁ : S₁.RightHomologyData) (H₂ : S₂.RightHomologyData)
    (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
    (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
    rightHomologyMap' (nullHomotopic _ _ h₀ h₀_f h₁ h₂ h₃ g_h₃) H₁ H₂ = 0 :=
  (RightHomologyMapData.ofNullHomotopic H₁ H₂ h₀ h₀_f h₁ h₂ h₃ g_h₃).rightHomologyMap'_eq

@[simp]
lemma homologyMap'_nullHomotopic
    (H₁ : S₁.HomologyData) (H₂ : S₂.HomologyData)
    (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
    (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
    homologyMap' (nullHomotopic _ _ h₀ h₀_f h₁ h₂ h₃ g_h₃) H₁ H₂ = 0 :=
  by apply leftHomologyMap'_nullHomotopic

variable (S₁ S₂)

@[simp]
lemma leftHomologyMap_nullHomotopic [S₁.HasLeftHomology] [S₂.HasLeftHomology]
    (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
    (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
    leftHomologyMap (nullHomotopic _ _ h₀ h₀_f h₁ h₂ h₃ g_h₃) = 0 :=
  by apply leftHomologyMap'_nullHomotopic

@[simp]
lemma rightHomologyMap_nullHomotopic [S₁.HasRightHomology] [S₂.HasRightHomology]
    (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
    (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
    rightHomologyMap (nullHomotopic _ _ h₀ h₀_f h₁ h₂ h₃ g_h₃) = 0 :=
  by apply rightHomologyMap'_nullHomotopic

@[simp]
lemma homologyMap_nullHomotopic [S₁.HasHomology] [S₂.HasHomology]
    (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
    (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
    homologyMap (nullHomotopic _ _ h₀ h₀_f h₁ h₂ h₃ g_h₃) = 0 :=
  by apply homologyMap'_nullHomotopic

namespace Homotopy

variable {φ₁ φ₂ S₁ S₂}

lemma congr_leftHomologyMap' (h : Homotopy φ₁ φ₂) (h₁ : S₁.LeftHomologyData)
    (h₂ : S₂.LeftHomologyData) : leftHomologyMap' φ₁ h₁ h₂ = leftHomologyMap' φ₂ h₁ h₂ := by
  rw [h.eq_add_null_homotopic, leftHomologyMap'_add, leftHomologyMap'_nullHomotopic, add_zero]

lemma congr_rightHomologyMap' (h : Homotopy φ₁ φ₂) (h₁ : S₁.RightHomologyData)
    (h₂ : S₂.RightHomologyData) : rightHomologyMap' φ₁ h₁ h₂ = rightHomologyMap' φ₂ h₁ h₂ := by
  rw [h.eq_add_null_homotopic, rightHomologyMap'_add, rightHomologyMap'_nullHomotopic, add_zero]

lemma congr_homologyMap' (h : Homotopy φ₁ φ₂) (h₁ : S₁.HomologyData)
    (h₂ : S₂.HomologyData) : homologyMap' φ₁ h₁ h₂ = homologyMap' φ₂ h₁ h₂ := by
  rw [h.eq_add_null_homotopic, homologyMap'_add, homologyMap'_nullHomotopic, add_zero]

lemma congr_leftHomologyMap (h : Homotopy φ₁ φ₂) [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    leftHomologyMap φ₁ = leftHomologyMap φ₂ :=
  h.congr_leftHomologyMap' _ _

lemma congr_rightHomologyMap (h : Homotopy φ₁ φ₂) [S₁.HasRightHomology] [S₂.HasRightHomology] :
    rightHomologyMap φ₁ = rightHomologyMap φ₂ :=
  h.congr_rightHomologyMap' _ _

lemma congr_homologyMap (h : Homotopy φ₁ φ₂) [S₁.HasHomology] [S₂.HasHomology] :
    homologyMap φ₁ = homologyMap φ₂ :=
  h.congr_homologyMap' _ _

end Homotopy

@[ext]
structure HomotopyEquiv where
  hom : S₁ ⟶ S₂
  inv : S₂ ⟶ S₁
  homotopyHomInvId : Homotopy (hom ≫ inv) (𝟙 S₁)
  homotopyInvHomId : Homotopy (inv ≫ hom) (𝟙 S₂)

namespace HomotopyEquiv

variable {S₁ S₂}


@[simps]
def refl (S : ShortComplex C) : HomotopyEquiv S S where
  hom := 𝟙 S
  inv := 𝟙 S
  homotopyHomInvId := Homotopy.ofEq (by simp)
  homotopyInvHomId := Homotopy.ofEq (by simp)

@[simps]
def symm (e : HomotopyEquiv S₁ S₂) : HomotopyEquiv S₂ S₁ where
  hom := e.inv
  inv := e.hom
  homotopyHomInvId := e.homotopyInvHomId
  homotopyInvHomId := e.homotopyHomInvId

@[simps]
def trans (e : HomotopyEquiv S₁ S₂) (e' : HomotopyEquiv S₂ S₃) :
    HomotopyEquiv S₁ S₃ where
  hom := e.hom ≫ e'.hom
  inv := e'.inv ≫ e.inv
  homotopyHomInvId := (Homotopy.ofEq (by simp)).trans
    (((e'.homotopyHomInvId.comp_right e.inv).comp_left e.hom).trans
      ((Homotopy.ofEq (by simp)).trans e.homotopyHomInvId))
  homotopyInvHomId := (Homotopy.ofEq (by simp)).trans
    (((e.homotopyInvHomId.comp_right e'.hom).comp_left e'.inv).trans
      ((Homotopy.ofEq (by simp)).trans e'.homotopyInvHomId))

variable (e : HomotopyEquiv S₁ S₂)

@[simps]
def leftHomologyIso' (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    h₁.H ≅ h₂.H where
  hom := leftHomologyMap' e.hom h₁ h₂
  inv := leftHomologyMap' e.inv h₂ h₁
  hom_inv_id := by
    rw [← leftHomologyMap'_comp, e.homotopyHomInvId.congr_leftHomologyMap',
      leftHomologyMap'_id]
  inv_hom_id := by
    rw [← leftHomologyMap'_comp, e.homotopyInvHomId.congr_leftHomologyMap',
      leftHomologyMap'_id]

@[simps]
def rightHomologyIso' (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    h₁.H ≅ h₂.H where
  hom := rightHomologyMap' e.hom h₁ h₂
  inv := rightHomologyMap' e.inv h₂ h₁
  hom_inv_id := by
    rw [← rightHomologyMap'_comp, e.homotopyHomInvId.congr_rightHomologyMap',
      rightHomologyMap'_id]
  inv_hom_id := by
    rw [← rightHomologyMap'_comp, e.homotopyInvHomId.congr_rightHomologyMap',
      rightHomologyMap'_id]

@[simps]
def homologyIso' (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) :
    h₁.left.H ≅ h₂.left.H where
  hom := homologyMap' e.hom h₁ h₂
  inv := homologyMap' e.inv h₂ h₁
  hom_inv_id := by
    rw [← homologyMap'_comp, e.homotopyHomInvId.congr_homologyMap', homologyMap'_id]
  inv_hom_id := by
    rw [← homologyMap'_comp, e.homotopyInvHomId.congr_homologyMap', homologyMap'_id]

@[simps]
noncomputable def leftHomologyIso [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    S₁.leftHomology ≅ S₂.leftHomology where
  hom := leftHomologyMap e.hom
  inv := leftHomologyMap e.inv
  hom_inv_id := (e.leftHomologyIso' _ _).hom_inv_id
  inv_hom_id := (e.leftHomologyIso' _ _).inv_hom_id

@[simps]
noncomputable def rightHomologyIso [S₁.HasRightHomology] [S₂.HasRightHomology] :
    S₁.rightHomology ≅ S₂.rightHomology where
  hom := rightHomologyMap e.hom
  inv := rightHomologyMap e.inv
  hom_inv_id := (e.rightHomologyIso' _ _).hom_inv_id
  inv_hom_id := (e.rightHomologyIso' _ _).inv_hom_id

@[simps]
noncomputable def homologyIso [S₁.HasHomology] [S₂.HasHomology] :
    S₁.homology ≅ S₂.homology where
  hom := homologyMap e.hom
  inv := homologyMap e.inv
  hom_inv_id := (e.homologyIso' _ _).hom_inv_id
  inv_hom_id := (e.homologyIso' _ _).inv_hom_id

instance quasiIso_hom [S₁.HasHomology] [S₂.HasHomology] : QuasiIso e.hom := by
  rw [quasiIso_iff]
  change IsIso e.homologyIso.hom
  infer_instance

instance quasiIso_inv [S₁.HasHomology] [S₂.HasHomology] : QuasiIso e.inv :=
  (inferInstance : QuasiIso (e.symm).hom)

end HomotopyEquiv

end Homotopy

variable (S : ShortComplex C)

lemma add_liftCycles {A : C} (k k' : A ⟶ S.X₂) (hk : k ≫ S.g = 0) (hk' : k' ≫ S.g = 0)
    [S.HasLeftHomology] : S.liftCycles k hk + S.liftCycles k' hk' =
      S.liftCycles (k + k') (by rw [add_comp, hk, hk', add_zero]) := by
  simp only [← cancel_mono S.iCycles, liftCycles_i, add_comp]

lemma sub_liftCycles {A : C} (k k' : A ⟶ S.X₂) (hk : k ≫ S.g = 0) (hk' : k' ≫ S.g = 0)
    [S.HasLeftHomology] : S.liftCycles k hk - S.liftCycles k' hk' =
      S.liftCycles (k - k') (by rw [sub_comp, hk, hk', sub_zero]) := by
  simp only [← cancel_mono S.iCycles, liftCycles_i, sub_comp]

end ShortComplex

end CategoryTheory
