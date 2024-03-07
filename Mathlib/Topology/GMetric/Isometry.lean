import Mathlib.Topology.GMetric.Basic

open GMetric

variable {α₁ α₂ γ :Type*} [CompleteLinearOrder γ] [AddCommMonoid γ]
variable [CovariantClass γ γ (. + .) (. ≤ .)] {T₁ T₂:Type*} [FunLike T₁ α₁ (α₁ → γ)]
variable [FunLike T₂ α₂ (α₂ → γ)] [GPseudoMetricClass T₁ α₁ γ] [GPseudoMetricClass T₂ α₂ γ]

structure GIsometry (gdist₁:T₁) (gdist₂:T₂) :=
  toFun : α₁ → α₂
  map_dist :∀ x y, gdist₁ x y = (gdist₂ (toFun x) (toFun y))

instance GIsometry.instFunLike {gdist₁:T₁} {gdist₂:T₂} :FunLike (GIsometry gdist₁ gdist₂) α₁ α₂ where
  coe := toFun
  coe_injective' := fun φ₁ φ₂ h => by
    cases φ₁;cases φ₂; congr

@[ext]
lemma GIsometry.ext
    {gdist₁:T₁} {gdist₂:T₂} ⦃f:GIsometry gdist₁ gdist₂⦄ ⦃g: GIsometry gdist₁ gdist₂⦄
    (h:∀ x, f x = g x): f = g :=
  DFunLike.ext _ _ h


class GIsometryClass (T₃:Type*) [FunLike T₃ α₁ α₂] (gdist₁: T₁) (gdist₂: T₂) where
  map_dist' : ∀ φ:T₃,∀ x y, ⇑gdist₁ x y = ⇑gdist₂ (φ x) (φ y)

instance GIsometry.instGIsometryClass
    (gdist₁:T₁) (gdist₂:T₂): GIsometryClass (GIsometry gdist₁ gdist₂) gdist₁ gdist₂ where
      map_dist' := GIsometry.map_dist

variable {T:Type*} [FunLike T α₁ α₂] {gdist₁:T₁} {gdist₂:T₂} [GIsometryClass T gdist₁ gdist₂]

@[coe]
def GIsometryClass.toGIsometry [GIsometryClass T gdist₁ gdist₂] (f:T) :
    GIsometry gdist₁ gdist₂ where
  toFun := f
  map_dist := GIsometryClass.map_dist' f


instance [GIsometryClass T gdist₁ gdist₂] : CoeTC T (GIsometry gdist₁ gdist₂) :=
  ⟨GIsometryClass.toGIsometry⟩

@[simp]
theorem GIsometry.coe_coe
  [GIsometryClass T gdist₁ gdist₂] (f : T) :
  ((f : GIsometry gdist₁ gdist₂) : α₁ → α₂) = f := rfl

@[simp]
theorem GIsometry.coe_mk
  (f : α₁ → α₂) (map_dist: ∀ x y, ⇑gdist₁ x y = ⇑gdist₂ (f x) (f y)):
  (GIsometry.mk f map_dist : α₁ → α₂) = f := rfl

protected def GIsometry.copy (f : GIsometry gdist₁ gdist₂) (f' : α₁ → α₂) (h : f' = f) :
    GIsometry gdist₁ gdist₂ where
  toFun := f'
  map_dist := h.symm ▸ f.map_dist

@[simp]
theorem GIsometry.coe_copy (f : GIsometry gdist₁ gdist₂) (f' : α₁ → α₂) (h : f' = f) :
    (f.copy f' h) = f' := rfl

theorem GIsometry.coe_copy_eq
    (f :GIsometry gdist₁ gdist₂) (f' : α₁ → α₂) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

@[simps]
def GIsometry.id (gdist₁:T₁) : GIsometry gdist₁ gdist₁ := {
  toFun := fun x => x
  map_dist := by simp
}

variable {α₃:Type*} {T₃:Type*} [FunLike T₃ α₃ (α₃ → γ)] [GPseudoMetricClass T₃ α₃ γ] {gdist₃ : T₃}
def GIsometry.comp
    (hnp : GIsometry gdist₂ gdist₃) (hmn : GIsometry gdist₁ gdist₂) : GIsometry gdist₁ gdist₃ := {
  toFun := hnp ∘ hmn
  map_dist := by
    intro x y
    rw [hmn.map_dist]
    rw [hnp.map_dist]
    rfl
}

@[simp]
theorem GIsometry.coe_comp (g : GIsometry gdist₂ gdist₃) (f : GIsometry gdist₁ gdist₂) :
    ↑(g.comp f) = g ∘ f := rfl

theorem GIsometry.comp_apply (g : GIsometry gdist₂ gdist₃) (f : GIsometry gdist₁ gdist₂) (x : α₁) :
    g.comp f x = g (f x) := rfl

theorem GIsometry.comp_assoc {α₄:Type*} {T₄:Type*} [FunLike T₄ α₄ (α₄ → γ)]
    [GPseudoMetricClass T₄ α₄ γ] (gdist₄:T₄)
    (f : GIsometry gdist₁ gdist₂) (g : GIsometry gdist₂ gdist₃) (h : GIsometry gdist₃ gdist₄) :
    (h.comp g).comp f = h.comp ((g.comp f)) := rfl


theorem GIsometry.cancel_right {g₁ g₂ : GIsometry gdist₂ gdist₃} {f : GIsometry gdist₁ gdist₂}
    (hf : Function.Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => GIsometry.ext <| hf.forall.2 (DFunLike.ext_iff.1 h), fun h => h ▸ rfl⟩


theorem GIsometry.cancel_left {g : GIsometry gdist₂ gdist₃} {f₁ f₂ : GIsometry gdist₁ gdist₂}
    (hg : Function.Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => GIsometry.ext fun x => hg <| by rw [← GIsometry.comp_apply, h, GIsometry.comp_apply],
    fun h => h ▸ rfl⟩

@[simp]
theorem GIsometry.comp_id (f : GIsometry gdist₁ gdist₂) : f.comp (GIsometry.id gdist₁) = f :=
  GIsometry.ext fun _ => rfl

@[simp]
theorem GIsometry.id_comp (f : GIsometry gdist₁ gdist₂) : (GIsometry.id gdist₂).comp f = f :=
  GIsometry.ext fun _ => rfl
