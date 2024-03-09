import Mathlib.InformationTheory.Code.Linear.Basic
import Mathlib.InformationTheory.Code.Hom

open Set

variable (T:Type*)

variable {γ : Type*} [Semiring γ] [CompleteLinearOrder γ] [Nontrivial γ]
variable (K : Type*) [Field K] {Tₖ : Type*} (gdist_k:Tₖ)
variable {M : Type*} {Tₘ : Type*} (gdist_m:Tₘ) [AddCommMonoid M] [Module K M]
variable (s : Submodule K M)
variable--? [_LinearCode γ K gdist_k gdist_m s] =>
  [CovariantClass γ γ (fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1] [FunLike Tₖ K (K → γ)]
  [GPseudoMetricClass Tₖ K γ] [AddGNorm K γ gdist_k] [FunLike Tₘ M (M → γ)]
  [GPseudoMetricClass Tₘ M γ] [AddGNorm M γ gdist_m] [IsDelone gdist_m ↑s] [PosMulMono γ]
  [MulPosMono γ] [ZeroLEOneClass γ] [StrictModuleGNorm K K gdist_k gdist_k]
  [StrictModuleGNorm K M gdist_k gdist_m]
variable {M₂ : Type*} {Tₘ₂ : Type*} (gdist_m₂:Tₘ₂) [AddCommMonoid M₂] [Module K M₂]
variable (s₂ : Submodule K M₂)
variable--? [_LinearCode γ K gdist_k gdist_m₂ s₂] =>
  [FunLike Tₘ₂ M₂ (M₂ → γ)]
  [GPseudoMetricClass Tₘ₂ M₂ γ] [AddGNorm M₂ γ gdist_m₂] [IsDelone gdist_m₂ ↑s₂]
  [StrictModuleGNorm K M₂ gdist_k gdist_m₂]
variable--? [CodeHomClass T₃ gdist_m s gdist_m₂ s₂] =>
  [FunLike T M M₂]
  [GIsometryClass T gdist_m gdist_m₂] [CodeHomClass T gdist_m s gdist_m₂ s₂]

structure LinearCodeHom [_LinearCode γ K gdist_k gdist_m s] [_LinearCode γ K gdist_k gdist_m₂ s₂]
  extends CodeHom gdist_m s gdist_m₂ s₂,LinearMap (RingHom.id K) M M₂ where

class _LinearCodeHomClass
    [_LinearCode γ K gdist_k gdist_m s]
    [_LinearCode γ K gdist_k gdist_m₂ s₂]
    [CodeHomClass T gdist_m s gdist_m₂ s₂]
    [LinearMapClass T K M M₂] : Prop
    where

namespace LinearCodeHom

instance instFunLike :
    FunLike (LinearCodeHom K gdist_k gdist_m s gdist_m₂ s₂) M M₂ where
  coe := fun φ => ⇑φ.toCodeHom
  coe_injective' := fun φ₁ φ₂ h => by
    cases φ₁; cases φ₂; simp_all only [DFunLike.coe_fn_eq]
section

variable {K gdist_k gdist_m s gdist_m₂ s₂}

@[ext]
lemma ext
    ⦃φ:LinearCodeHom K gdist_k gdist_m s gdist_m₂ s₂⦄
    ⦃φ₂:LinearCodeHom K gdist_k gdist_m s gdist_m₂ s₂⦄
    (h:∀ x,φ x = φ₂ x) : φ = φ₂ := DFunLike.ext _ _ h
end
instance instSemiLinearMapClass :
    LinearMapClass (LinearCodeHom K gdist_k gdist_m s gdist_m₂ s₂) K M M₂ where
  map_add := fun φ => by apply φ.map_add'
  map_smulₛₗ := fun φ => by apply φ.map_smul'

instance instGIsometryClass :
    GIsometryClass (LinearCodeHom K gdist_k gdist_m s gdist_m₂ s₂) gdist_m gdist_m₂ where
  map_dist' := fun φ => φ.toCodeHom.map_dist

instance instCodeHomClass :
    CodeHomClass (LinearCodeHom K gdist_k gdist_m s gdist_m₂ s₂) gdist_m s gdist_m₂ s₂ where
  map_code' := fun φ => φ.toCodeHom.map_code

-- @[abbrev_class]
/-- this class doesn't really do anything
there is no extra info needed on top of the parameters,
but it does help remind you what instances you need in order to have the property
this represents.
it also allows `variable? [LinearCodeHomClass T₃ K gdist_k gdist_m s gdist_m₂ s₂]` to
expand into all the right variables
don't extend, rather just take as a parameter. also don't make new instances.-/

-- LinearCodeHom.inst_LinearCodeHomClass is redundant with this
instance inst_LinearCodeHomClass
    [_LinearCode γ K gdist_k gdist_m s]
    [_LinearCode γ K gdist_k gdist_m₂ s₂]
    [CodeHomClass T gdist_m s gdist_m₂ s₂]
    [LinearMapClass T K M M₂] : _LinearCodeHomClass T K gdist_k gdist_m s gdist_m₂ s₂ where

end LinearCodeHom
variable {T K gdist_k gdist_m s gdist_m₂ s₂}
variable--? [_LinearCodeHomClass T₃ K gdist_k gdist_m s gdist_m₂ s₂] =>
  [LinearMapClass T K M M₂]

@[coe]
def _LinearCodeHomClass.toLinearCodeHom
    [_LinearCodeHomClass T K gdist_k gdist_m s gdist_m₂ s₂] (φ:T):
  LinearCodeHom K gdist_k gdist_m s gdist_m₂ s₂ := {
    CodeHomClass.toCodeHom φ,LinearMapClass.linearMap φ with
  }

instance
    [_LinearCodeHomClass T K gdist_k gdist_m s gdist_m₂ s₂] :
    CoeTC T (LinearCodeHom K gdist_k gdist_m s gdist_m₂ s₂) :=
  ⟨_LinearCodeHomClass.toLinearCodeHom⟩

namespace LinearCodeHom
@[simp]
theorem coe_coe
    [_LinearCodeHomClass T K gdist_k gdist_m s gdist_m₂ s₂] (f : T) :
    ((f : LinearCodeHom K gdist_k gdist_m s gdist_m₂ s₂) : M → M₂) = f := rfl

@[simp]
theorem coe_mk
    [_LinearCode γ K gdist_k gdist_m s]
    [_LinearCode γ K gdist_k gdist_m₂ s₂]
    (f : CodeHom gdist_m s gdist_m₂ s₂)
    (map_add : ∀ (x y : M), f (x + y) = f x + f y)
    (map_smul : ∀ (r : K) (x : M), f (r • x) = (RingHom.id K) r • f x):
    ((@LinearCodeHom.mk γ _ _ _ K _ Tₖ gdist_k) f map_add map_smul : M → M₂) = f := rfl

protected def copy
    (f : LinearCodeHom K gdist_k gdist_m s gdist_m₂ s₂) (f' : M → M₂) (h : f' = f) :
    LinearCodeHom K gdist_k gdist_m s gdist_m₂ s₂ := {
  f.toCodeHom.copy f' h, f.toLinearMap.copy f' h with}

@[simp]
theorem coe_copy
    (f : LinearCodeHom K gdist_k gdist_m s gdist_m₂ s₂) (f' : M → M₂) (h : f' = f) :
    (f.copy f' h) = f' := rfl

theorem coe_copy_eq (f :LinearCodeHom K gdist_k gdist_m s gdist_m₂ s₂) (f' : M → M₂)
  (h : f' = f) : f.copy f' h = f := DFunLike.ext' h

variable {T₃ M₃:Type*} {gdist_m₃:T₃} [AddCommMonoid M₃] [Module K M₃] {s₃ : Submodule K M₃}
variable--? [_LinearCode γ K gdist_k gdist_m₃ s₃] =>
  [FunLike T₃ M₃ (M₃ → γ)] [GPseudoMetricClass T₃ M₃ γ] [AddGNorm M₃ γ gdist_m₃]
  [IsDelone gdist_m₃ ↑s₃] [StrictModuleGNorm K M₃ gdist_k gdist_m₃]


section
variable (K gdist_k gdist_m s)
@[simps!] -- not sure if this should or shouldn't be simps
def id
  [_LinearCode γ K gdist_k gdist_m s] : LinearCodeHom K gdist_k gdist_m s gdist_m s := {
    CodeHom.id gdist_m s, LinearMap.id with
  }
end
def comp
    (φ: LinearCodeHom K gdist_k gdist_m₂ s₂ gdist_m₃ s₃)
    (φ₂ : LinearCodeHom K gdist_k gdist_m s gdist_m₂ s₂) :
    LinearCodeHom K gdist_k gdist_m s gdist_m₃ s₃ := {
      φ.toCodeHom.comp φ₂.toCodeHom, φ.toLinearMap.comp φ₂.toLinearMap with}


@[simp]
theorem coe_comp (g : LinearCodeHom K gdist_k gdist_m₂ s₂ gdist_m₃ s₃)
    (f : LinearCodeHom K gdist_k gdist_m s gdist_m₂ s₂) :
    ↑(g.comp f) = g ∘ f := rfl

theorem comp_apply (g : LinearCodeHom K gdist_k gdist_m₂ s₂ gdist_m₃ s₃)
    (f : LinearCodeHom K gdist_k gdist_m s gdist_m₂ s₂) (x : M) :
    g.comp f x = g (f x) := rfl

variable {M₄:Type*} {T₄:Type*} {gdist_m₄:T₄} [AddCommMonoid M₄] [Module K M₄] {s₄:Submodule K M₄}
variable--? [_LinearCode γ K gdist_k gdist_m₄ s₄] =>
  [FunLike T₄ M₄ (M₄ → γ)] [GPseudoMetricClass T₄ M₄ γ] [AddGNorm M₄ γ gdist_m₄]
  [IsDelone gdist_m₄ ↑s₄] [StrictModuleGNorm K M₄ gdist_k gdist_m₄]

theorem comp_assoc
    (f : LinearCodeHom K gdist_k gdist_m s gdist_m₂ s₂)
    (g : LinearCodeHom K gdist_k gdist_m₂ s₂ gdist_m₃ s₃)
    (h : LinearCodeHom K gdist_k gdist_m₃ s₃ gdist_m₄ s₄) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

theorem cancel_right
    {g₁ g₂ : LinearCodeHom K gdist_k gdist_m₂ s₂ gdist_m₃ s₃}
    {f : LinearCodeHom K gdist_k gdist_m s gdist_m₂ s₂}
    (hf : Function.Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 (DFunLike.ext_iff.1 h), fun h => h ▸ rfl⟩


theorem cancel_left
    {g : LinearCodeHom K gdist_k gdist_m₂ s₂ gdist_m₃ s₃}
    {f₁ f₂ : LinearCodeHom K gdist_k gdist_m s gdist_m₂ s₂}
    (hg : Function.Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun x => hg <| by rw [← comp_apply, h,
    comp_apply],fun h => h ▸ rfl⟩

@[simp]
theorem comp_id (f : LinearCodeHom K gdist_k gdist_m s gdist_m₂ s₂) :
  f.comp (id K gdist_k gdist_m s) = f :=
  ext fun _ => rfl

@[simp]
theorem id_comp (f : LinearCodeHom K gdist_k gdist_m s gdist_m₂ s₂) :
  (id K gdist_k gdist_m₂ s₂).comp f = f :=
  ext fun _ => rfl

end LinearCodeHom
