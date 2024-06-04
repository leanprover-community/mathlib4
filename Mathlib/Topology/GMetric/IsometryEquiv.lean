import Mathlib.Topology.GMetric.Isometry
variable {α₁ α₂ γ :Type*} [CompleteLinearOrder γ] [AddCommMonoid γ]
variable [CovariantClass γ γ (. + .) (. ≤ .)] {T₁ T₂:Type*} [FunLike T₁ α₁ (α₁ → γ)]
variable [FunLike T₂ α₂ (α₂ → γ)] [GPseudoMetricClass T₁ α₁ γ] [GPseudoMetricClass T₂ α₂ γ]
variable {gdist₁:T₁} {gdist₂:T₂}

@[simps]
def GIsometry.inverse (f:GIsometry gdist₁ gdist₂) (g: α₂ → α₁) (h₁ : Function.RightInverse g f) :
  GIsometry gdist₂ gdist₁ := {
    toFun := g
    map_dist := fun x y =>
      calc
        gdist₂ x y = gdist₂ (f (g x)) (f (g y)) := by
          nth_rw 1 [← h₁ x, ← h₁ y]
        _ = gdist₁ (g x) (g y) := by
          rw [f.map_dist]; rfl
  }

structure GIsometryEquiv [GPseudoMetricClass T₁ α₁ γ] [GPseudoMetricClass T₂ α₂ γ]
  (gdist₁:T₁) (gdist₂:T₂) extends α₁ ≃ α₂, GIsometry gdist₁ gdist₂

class GIsometryEquivClass (T:Type*)
  {γ :outParam Type*} [LinearOrder γ] [AddCommMonoid γ] [CovariantClass γ γ (. + .) (.≤.)]
  {α₁:outParam Type*} {α₂:outParam Type*}
  {T₁ T₂:outParam Type*}
  [FunLike T₁ α₁ (α₁ → γ)] [GPseudoMetricClass T₁ α₁ γ]
  [FunLike T₂ α₂ (α₂ → γ)] [GPseudoMetricClass T₂ α₂ γ]
  (gdist₁: outParam T₁) (gdist₂: outParam T₂) [EquivLike T α₁ α₂]
  extends GIsometryClass T gdist₁ gdist₂

-- do or don't declare this instance? don't because loops.

namespace GIsometryEquiv

-- doing this without the `{...} with` gives an error
-- while porting this from an old version, i couldn't figure out how to do this.
-- this is my temp solution
instance instEquivLike : EquivLike (GIsometryEquiv gdist₁ gdist₂) α₁ α₂ where
  coe := fun f => f.toFun
  inv := fun f => f.invFun
  left_inv := fun f => f.left_inv
  right_inv := fun f => f.right_inv
  coe_injective' := fun f g h => by cases f; cases g; congr; simp_all


instance instGIsometryEquivClass : GIsometryEquivClass (GIsometryEquiv gdist₁ gdist₂) gdist₁ gdist₂ where
  map_dist' := fun f => f.map_dist

@[ext]
theorem ext ⦃f g : GIsometryEquiv gdist₁ gdist₂⦄ (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

protected def copy (f : GIsometryEquiv gdist₁ gdist₂) (f' : α₁ → α₂)
  (f_inv : α₂ → α₁) (hf : f' = ↑f) (hf_inv : f_inv = ⇑f.toEquiv.symm) :
    GIsometryEquiv gdist₁ gdist₂ := {
      f.toGIsometry.copy f' hf with
      invFun := f_inv
      left_inv := by
        simp_rw [hf, hf_inv]
        exact f.left_inv
      right_inv := by
        simp_rw [hf_inv,hf]
        exact f.right_inv
    }
end GIsometryEquiv


variable {T:Type*} [EquivLike T α₁ α₂] [GIsometryEquivClass T gdist₁ gdist₂]

@[coe]
def GIsometryEquivClass.toGIsometryEquiv (f : T) : GIsometryEquiv gdist₁ gdist₂:={
  EquivLike.toEquiv f,  GIsometryClass.toGIsometry f with}

instance [GIsometryEquivClass T gdist₁ gdist₂] : CoeTC T (GIsometryEquiv gdist₁ gdist₂) :=
  ⟨GIsometryEquivClass.toGIsometryEquiv⟩


namespace GIsometryEquiv

@[simp]
theorem toEquiv_eq_coe (f :GIsometryEquiv gdist₁ gdist₂) : f.toEquiv = f :=
  rfl

@[simp]
theorem toGIsometry_eq_coe (f : GIsometryEquiv gdist₁ gdist₂) : f.toGIsometry = ↑f :=
  rfl

@[simp]
theorem coe_toEquiv (f : GIsometryEquiv gdist₁ gdist₂) : ⇑(f : α₁ ≃ α₂) = f := rfl


@[simp 1100]
theorem coe_toGIsometry {f : GIsometryEquiv gdist₁ gdist₂} : (f.toGIsometry : α₁ → α₂) = f := rfl

def mk'
    (f : α₁ ≃ α₂)
    (h : ∀ x y, gdist₁ x y = gdist₂ (f x) (f y)) :
    GIsometryEquiv gdist₁ gdist₂ := ⟨f, h⟩

protected theorem bijective
    (f : GIsometryEquiv gdist₁ gdist₂) : Function.Bijective f :=
  EquivLike.bijective f

protected theorem injective
    (f : GIsometryEquiv gdist₁ gdist₂) : Function.Injective f :=
  EquivLike.injective f

protected theorem surjective
    (f : GIsometryEquiv gdist₁ gdist₂) : Function.Surjective f :=
  EquivLike.surjective f

@[refl]
def refl (gdist₁ : T₁) : GIsometryEquiv gdist₁ gdist₁ :=
  { Equiv.refl _ with map_dist := fun _ _ => rfl }

instance : Inhabited (GIsometryEquiv gdist₁ gdist₁) := ⟨refl gdist₁⟩

lemma symm_map_dist
    (h : GIsometryEquiv gdist₁ gdist₂) (x y : α₂) :
    gdist₂ x y = gdist₁ (h.symm x) (h.symm y) :=
  (h.toGIsometry.inverse h.toEquiv.symm h.right_inv).map_dist x y

@[symm]
def symm (h : GIsometryEquiv gdist₁ gdist₂) : GIsometryEquiv gdist₂ gdist₁ :=
  ⟨h.toEquiv.symm, h.symm_map_dist⟩

theorem invFun_eq_symm {f : GIsometryEquiv gdist₁ gdist₂} : f.invFun = f.symm := rfl

@[simp]
theorem coe_toEquiv_symm
    (f : GIsometryEquiv gdist₁ gdist₂) : ((f : α₁ ≃ α₂).symm : α₂→ α₁) = f.symm := rfl

@[simp]
theorem equivLike_inv_eq_symm
    (f : GIsometryEquiv gdist₁ gdist₂) : EquivLike.inv f = f.symm := rfl

@[simp]
theorem toEquiv_symm
    (f : GIsometryEquiv gdist₁ gdist₂) : (f.symm : α₂ ≃ α₁) = (f : α₁ ≃ α₂).symm := rfl

@[simp]
theorem coe_mk
    (f : α₁ ≃ α₂) (hf : ∀ x y, gdist₁ x y = gdist₂ (f x) (f y)) :
    (mk f hf : α₁ → α₂) = f := rfl

@[simp]
theorem symm_symm (f : GIsometryEquiv gdist₁ gdist₂) : f.symm.symm = f := rfl

theorem symm_bijective :
    Function.Bijective
      (symm : (GIsometryEquiv gdist₁ gdist₂) → GIsometryEquiv gdist₂ gdist₁) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
theorem symm_mk
    (f : α₁ ≃ α₂) (h : ∀ x y, gdist₁ x y = gdist₂ (f x) (f y)) :
    (mk f h).symm = ⟨f.symm, (mk f h).symm_map_dist⟩ := rfl

@[simp]
theorem refl_symm : (refl gdist₁).symm = refl gdist₁ := rfl

@[simp]
theorem coe_copy
    (f : GIsometryEquiv gdist₁ gdist₂) (f' : α₁ → α₂) (f_inv : α₂ → α₁) (hf : f' = ↑f)
    (hf_inv : f_inv = ⇑f.symm) : (f.copy f' f_inv hf hf_inv) = f' := rfl

theorem coe_copy_eq
    (f : GIsometryEquiv gdist₁ gdist₂) (f' : α₁ → α₂) (f_inv : α₂ → α₁) (hf : f' = ↑f)
    (hf_inv : f_inv = ⇑f.symm) : (f.copy f' f_inv hf hf_inv) = f := by
  apply DFunLike.ext'
  rw [coe_copy,hf]


variable {α₃ T₃ :Type*} {gdist₃:T₃}
variable--? [GPseudoMetricClass T₃ α₃ γ] =>
  [FunLike T₃ α₃ (α₃ → γ)] [GPseudoMetricClass T₃ α₃ γ]

@[trans]
def trans (h1 : GIsometryEquiv gdist₁ gdist₂) (h2 : GIsometryEquiv gdist₂ gdist₃) : GIsometryEquiv gdist₁ gdist₃ :=
  { h1.toEquiv.trans h2.toEquiv with
    map_dist := fun x y => show gdist₁ x y = gdist₃ (h2 (h1 x)) (h2 (h1 y)) by
      rw [h1.map_dist, h2.map_dist] ;rfl}

@[simp]
theorem apply_symm_apply (f : GIsometryEquiv gdist₁ gdist₂ ) (y : α₂) : f (f.symm y) = y :=
  f.toEquiv.apply_symm_apply y

@[simp]
theorem symm_apply_apply (f : GIsometryEquiv gdist₁ gdist₂) (x : α₁) : f.symm (f x) = x :=
  f.toEquiv.symm_apply_apply x

@[simp]
theorem symm_comp_self (f : GIsometryEquiv gdist₁ gdist₂) : f.symm ∘ f = id :=
  funext f.symm_apply_apply

@[simp]
theorem self_comp_symm (f : GIsometryEquiv gdist₁ gdist₂) : f ∘ f.symm = id :=
  funext f.apply_symm_apply

@[simp]
theorem coe_refl : ↑(refl gdist₁) = id := rfl

@[simp]
theorem refl_apply (x : α₁) : refl gdist₁ x = x := rfl

@[simp]
theorem coe_trans
    (f₁ : GIsometryEquiv gdist₁ gdist₂) (f₂ : GIsometryEquiv gdist₂ gdist₃) :
  ↑(f₁.trans f₂) = f₂ ∘ f₁ := rfl

@[simp]
theorem trans_apply
    (f₁ : GIsometryEquiv gdist₁ gdist₂) (f₂ : GIsometryEquiv gdist₂ gdist₃) (x : α₁) :
    f₁.trans f₂ x = f₂ (f₁ x) := rfl

@[simp]
theorem symm_trans_apply
    (f₁ : GIsometryEquiv gdist₁ gdist₂) (f₂ : GIsometryEquiv gdist₂ gdist₃) (y : α₃) :
    (f₁.trans f₂).symm y = f₁.symm (f₂.symm y) := rfl

-- simp can prove this
theorem apply_eq_iff_eq
    (f : GIsometryEquiv gdist₁ gdist₂ ) {x y : α₁} :
  f x = f y ↔ x = y := f.injective.eq_iff

theorem apply_eq_iff_symm_apply
    (f : GIsometryEquiv gdist₁ gdist₂) {x : α₁} {y : α₂} :
  f x = y ↔ x = f.symm y := f.toEquiv.apply_eq_iff_eq_symm_apply

theorem symm_apply_eq
    (f : GIsometryEquiv gdist₁ gdist₂) {x y} :
  f.symm x = y ↔ x = f y := f.toEquiv.symm_apply_eq

theorem eq_symm_apply
    (f : GIsometryEquiv gdist₁ gdist₂) {x y} :
  y = f.symm x ↔ f y = x := f.toEquiv.eq_symm_apply

theorem eq_comp_symm
    {α : Type*} (e : GIsometryEquiv gdist₁ gdist₂) (f : α₂ → α) (g : α₁ → α) :
  f = g ∘ e.symm ↔ f ∘ e = g :=
  e.toEquiv.eq_comp_symm f g

theorem comp_symm_eq
    {α : Type*} (e : GIsometryEquiv gdist₁ gdist₂) (f : α₂ → α) (g : α₁ → α) :
  g ∘ e.symm = f ↔ g = f ∘ e := e.toEquiv.comp_symm_eq f g

theorem eq_symm_comp
    {α : Type*} (e : GIsometryEquiv gdist₁ gdist₂) (f : α → α₁) (g : α → α₂) :
  f = e.symm ∘ g ↔ e ∘ f = g := e.toEquiv.eq_symm_comp f g

theorem symm_comp_eq
    {α : Type*} (e : GIsometryEquiv gdist₁ gdist₂) (f : α → α₁) (g : α → α₂) :
  e.symm ∘ g = f ↔ g = e ∘ f := e.toEquiv.symm_comp_eq f g

@[simp]
theorem symm_trans_self
    (f : GIsometryEquiv gdist₁ gdist₂):
  f.symm.trans f = refl gdist₂ := DFunLike.ext _ _ f.apply_symm_apply

@[simp]
theorem self_trans_symm
    (f : GIsometryEquiv gdist₁ gdist₂) :
  f.trans f.symm = refl gdist₁ := DFunLike.ext _ _ f.symm_apply_apply

theorem ext_iff {f g : GIsometryEquiv gdist₁ gdist₂} : f = g ↔ ∀ x, f x = g x :=
  DFunLike.ext_iff

@[simp]
theorem mk_coe
    (f : GIsometryEquiv gdist₁ gdist₂) (f' h₁ h₂ h₃) :
  (⟨⟨f, f', h₁, h₂⟩, h₃⟩ : GIsometryEquiv gdist₁ gdist₂) = f := ext fun _ => rfl

@[simp]
theorem mk_coe' (f : GIsometryEquiv gdist₁ gdist₂) (g h₁ h₂ h₃) :
    (GIsometryEquiv.mk ⟨g, f, h₁, h₂⟩ h₃ : GIsometryEquiv gdist₂ gdist₁) = f.symm :=
  symm_bijective.injective <| ext fun _ => rfl

protected theorem congr_arg
    {f : GIsometryEquiv gdist₁ gdist₂} {x x' : α₁} :
  x = x' → f x = f x' := DFunLike.congr_arg f

protected theorem congr_fun
    {f g : GIsometryEquiv gdist₁ gdist₂} (h : f = g) (x : α₁) :
  f x = g x := DFunLike.congr_fun h x
