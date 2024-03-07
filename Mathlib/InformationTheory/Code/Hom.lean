import Mathlib.InformationTheory.Code.Basic
import Mathlib.Topology.GMetric.Isometry
import Mathlib.Topology.GMetric.GNorm
open Set
open GMetric
open GIsometry
open Code

section code
variable (T₃:Type*)
variable {γ :Type*} [CompleteLinearOrder γ] [AddCommMonoid γ]

variable {α T:Type*} (gdist:T) (s:Set α)
variable--? [_Code γ gdist s] =>
  [CovariantClass γ γ (fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1]
  [FunLike T α (α → γ)] [GPseudoMetricClass T α γ] [IsDelone gdist s]

variable {α₂ T₂ :Type*} (gdist₂:T₂) (s₂ : Set α₂)
variable--? [_Code γ gdist₂ s₂] =>
  [FunLike T₂ α₂ (α₂ → γ)] [GPseudoMetricClass T₂ α₂ γ]
  [IsDelone gdist₂ s₂]


variable [FunLike T₃ α α₂] [GIsometryClass T₃ gdist gdist₂]

structure CodeHom [_Code γ gdist s] [_Code γ gdist₂ s₂] extends GIsometry gdist gdist₂ where
  map_code : ∀ x ∈ s, toFun x ∈ s₂

section
variable {gdist s gdist₂ s₂}
instance CodeHom.instFunLike : FunLike (CodeHom gdist s gdist₂ s₂) α α₂ where
  coe := fun φ => φ.toGIsometry
  coe_injective' := fun φ₁ φ₂ h => by
    cases φ₁; cases φ₂; congr; simp_all

@[ext]
lemma CodeHom.ext ⦃φ:CodeHom gdist s gdist₂ s₂⦄ ⦃φ₂:CodeHom gdist s gdist₂ s₂⦄
    (h:∀ x, φ x = φ₂ x): φ = φ₂ := DFunLike.ext _ _ h
end

instance CodeHom.instGIsometryClass : GIsometryClass (CodeHom gdist s gdist₂ s₂) gdist gdist₂ where
  map_dist' := fun φ => φ.map_dist

class CodeHomClass [_Code γ gdist s] [_Code γ gdist₂ s₂]
    [GIsometryClass T₃ gdist gdist₂] :Prop where
  map_code' : ∀ (φ:T₃), ∀ x ∈ s, φ x ∈ s₂
variable {T₃ gdist s gdist₂ s₂}

instance CodeHom.instCodeHomClass :
    CodeHomClass (CodeHom gdist s gdist₂ s₂) gdist s gdist₂ s₂ where
  map_code' := fun φ => φ.map_code

def CodeHomClass.toCodeHom
    [CodeHomClass T₃ gdist s gdist₂ s₂] (φ:T₃) : CodeHom gdist s gdist₂ s₂ where
  toFun := φ
  map_dist := GIsometryClass.map_dist' φ
  map_code := map_code' γ gdist gdist₂ φ

instance [CodeHomClass T₃ gdist s gdist₂ s₂]: CoeTC T₃ (CodeHom gdist s gdist₂ s₂) :=
  ⟨CodeHomClass.toCodeHom⟩

instance [CodeHomClass T₃ gdist s gdist₂ s₂] : CoeTC T₃ ( CodeHom gdist s gdist₂ s₂) :=
  ⟨CodeHomClass.toCodeHom⟩

@[simp]
theorem CodeHom.coe_coe
    [CodeHomClass T₃ gdist s gdist₂ s₂] (φ:T₃) : ((φ : CodeHom gdist s gdist₂ s₂):α → α₂) = φ := by
  rfl

@[simp]
theorem CodeHom.coe_mk
  (f : GIsometry gdist gdist₂) (map_code: ∀ x ∈ s, f x ∈ s₂) :
  (CodeHom.mk f map_code : α → α₂) = f := rfl

section
variable {T₃ α₃ :Type*} {gdist₃:T₃} {s₃:Set α₃}
variable--? [_Code γ gdist₃ s₃] =>
  [FunLike T₃ α₃ (α₃ → γ)] [GPseudoMetricClass T₃ α₃ γ] [IsDelone gdist₃ s₃]

variable (gdist s)
def CodeHom.id [_Code γ gdist s] : CodeHom gdist s gdist s := {
  GIsometry.id gdist with
  map_code := fun _ a ↦ a
}

variable {gdist s}
def CodeHom.comp
    (φ₂: CodeHom gdist₂ s₂ gdist₃ s₃) (φ: CodeHom gdist s gdist₂ s₂) : CodeHom gdist s gdist₃ s₃ := {
  φ₂.toGIsometry.comp φ.toGIsometry with
  map_code := fun x hx => φ₂.map_code (φ x) <| φ.map_code x hx
  }

@[simp]
theorem CodeHom.coe_comp (g : CodeHom gdist₂ s₂ gdist₃ s₃) (f : CodeHom gdist s gdist₂ s₂) :
    ↑(g.comp f) = g ∘ f := rfl

theorem CodeHom.comp_apply
    (g : CodeHom gdist₂ s₂ gdist₃ s₃) (f : CodeHom gdist s gdist₂ s₂) (x : α):
  g.comp f x = g (f x) := rfl

variable {α₄ T₄:Type} {gdist₄:T₄} {s₄:Set α₄}
variable--? [_Code γ gdist₄ s₄] =>
  [FunLike T₄ α₄ (α₄ → γ)] [GPseudoMetricClass T₄ α₄ γ] [IsDelone gdist₄ s₄]


theorem CodeHom.comp_assoc (h: CodeHom gdist₃ s₃ gdist₄ s₄)
    (g : CodeHom gdist₂ s₂ gdist₃ s₃) (f : CodeHom gdist s gdist₂ s₂):
    (h.comp g).comp f = h.comp (g.comp f) := rfl

theorem CodeHom.cancel_right {g₁ g₂ : CodeHom gdist₂ s₂ gdist₃ s₃} {f : CodeHom gdist s gdist₂ s₂}
    (hf : Function.Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ := by
  constructor
  . intro h
    apply CodeHom.ext
    intro y
    apply (@Function.Surjective.forall α α₂ f hf (fun y => g₁ y = g₂ y)).2
    intro x
    rw [← CodeHom.comp_apply,h,CodeHom.comp_apply]
  . exact fun h => h ▸ rfl

@[simp]
theorem CodeHom.comp_id (f : CodeHom gdist s gdist₂ s₂) : f.comp (CodeHom.id gdist s) = f :=
  CodeHom.ext fun _ => rfl

@[simp]
theorem MyHom.id_comp (f : CodeHom gdist s gdist₂ s₂) : (CodeHom.id gdist₂ s₂).comp f = f :=
  CodeHom.ext fun _ => rfl


end
end code

section linear_code
variable (T₃:Type*)

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
  [FunLike T₃ M M₂]
  [GIsometryClass T₃ gdist_m gdist_m₂] [CodeHomClass T₃ gdist_m s gdist_m₂ s₂]

structure LinearCodeHom [_LinearCode γ K gdist_k gdist_m s] [_LinearCode γ K gdist_k gdist_m₂ s₂]
  extends CodeHom gdist_m s gdist_m₂ s₂,LinearMap (RingHom.id K) M M₂ where

instance LinearCodeHom.instFunLike :
    FunLike (LinearCodeHom K gdist_k gdist_m s gdist_m₂ s₂) M M₂ where
  coe := fun φ => ⇑φ.toCodeHom
  coe_injective' := fun φ₁ φ₂ h => by
    cases φ₁; cases φ₂; simp_all only [DFunLike.coe_fn_eq]

@[ext]
lemma LinearCodeHom.ext
    ⦃φ:LinearCodeHom K gdist_k gdist_m s gdist_m₂ s₂⦄
    ⦃φ₂:LinearCodeHom K gdist_k gdist_m s gdist_m₂ s₂⦄
    (h:∀ x,φ x = φ₂ x) : φ = φ₂ := DFunLike.ext _ _ h

instance LinearCodeHom.instSemiLinearMapClass :
    LinearMapClass (LinearCodeHom K gdist_k gdist_m s gdist_m₂ s₂) K M M₂ where
  map_add := fun φ => by apply φ.map_add'
  map_smulₛₗ := fun φ => by apply φ.map_smul'

instance LinearCodeHom.instGIsometryClass :
    GIsometryClass (LinearCodeHom K gdist_k gdist_m s gdist_m₂ s₂) gdist_m gdist_m₂ where
  map_dist' := fun φ => φ.toCodeHom.map_dist

instance LinearCodeHom.instCodeHomClass :
    CodeHomClass (LinearCodeHom K gdist_k gdist_m s gdist_m₂ s₂) gdist_m s gdist_m₂ s₂ where
  map_code' := fun φ => φ.toCodeHom.map_code

-- @[abbrev_class]
/-- this class doesn't really do anything
there is no extra info needed on top of the parameters,
but it does help remind you what instances you need in order to have the property
this represents.
it also allows `variable? [LinearCodeHomClass T₃ K gdist_k gdist_m s gdist_m₂ s₂]` to
expand into all the right variables
don't extend, rather just take as a parameter. also don't make new instances.
-/
class _LinearCodeHomClass
    [_LinearCode γ K gdist_k gdist_m s]
    [_LinearCode γ K gdist_k gdist_m₂ s₂]
    [CodeHomClass T₃ gdist_m s gdist_m₂ s₂]
    [LinearMapClass T₃ K M M₂] : Prop
    where

instance inst_LinearCodeHomClass
    [_LinearCode γ K gdist_k gdist_m s]
    [_LinearCode γ K gdist_k gdist_m₂ s₂]
    [CodeHomClass T₃ gdist_m s gdist_m₂ s₂]
    [LinearMapClass T₃ K M M₂] : _LinearCodeHomClass T₃ K gdist_k gdist_m s gdist_m₂ s₂ where

section
variable {T₃ M₃:Type} {gdist_m₃:T₃} [AddCommMonoid M₃] [Module K M₃] {s₃ : Submodule K M₃}
variable--? [_LinearCode γ K gdist_k gdist_m₃ s₃] =>
  [FunLike T₃ M₃ (M₃ → γ)] [GPseudoMetricClass T₃ M₃ γ] [AddGNorm M₃ γ gdist_m₃]
  [IsDelone gdist_m₃ ↑s₃] [StrictModuleGNorm K M₃ gdist_k gdist_m₃]

def LinearCodeHom.id
  [_LinearCode γ K gdist_k gdist_m s] : LinearCodeHom K gdist_k gdist_m s gdist_m s := {
    CodeHom.id gdist_m s, LinearMap.id with
  }

def LinearCodeHom.comp
    (φ: LinearCodeHom K gdist_k gdist_m₂ s₂ gdist_m₃ s₃)
    (φ₂ : LinearCodeHom K gdist_k gdist_m s gdist_m₂ s₂) :
    LinearCodeHom K gdist_k gdist_m s gdist_m₃ s₃ := {
      φ.toCodeHom.comp φ₂.toCodeHom, φ.toLinearMap.comp φ₂.toLinearMap with}
-- TODO: prove simple lemmas about these things
end




end linear_code
