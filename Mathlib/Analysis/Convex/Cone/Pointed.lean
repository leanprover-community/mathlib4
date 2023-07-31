import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Algebra.Order.Nonneg.Ring
import Mathlib.Algebra.DirectSum.Module

structure PointedCone (𝕜 : Type _) (E : Type _) [OrderedSemiring 𝕜] [AddCommMonoid E]
     [SMul 𝕜 E] extends ConvexCone 𝕜 E where
  zero_mem' : 0 ∈ carrier

namespace PointedCone

variable {𝕜} [OrderedSemiring 𝕜]

section SMul
variable {E} [AddCommMonoid E] [SMul 𝕜 E]

instance : Coe (PointedCone 𝕜 E) (ConvexCone 𝕜 E) :=
  ⟨fun K => K.1⟩

theorem ext' : Function.Injective ((↑) : PointedCone 𝕜 E → ConvexCone 𝕜 E) := fun S T h => by
  cases S; cases T; congr

instance : SetLike (PointedCone 𝕜 E) E where
  coe K := K.carrier
  coe_injective' _ _ h := PointedCone.ext' (SetLike.coe_injective h)

@[ext]
theorem ext {S T : PointedCone 𝕜 E} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

@[simp]
theorem mem_coe {x : E} {S : PointedCone 𝕜 E} : x ∈ (S : ConvexCone 𝕜 E) ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem zero_mem (S : PointedCone 𝕜 E) : 0 ∈ S :=
  S.zero_mem'

instance (S : PointedCone 𝕜 E) : Zero S := ⟨
  0, S.zero_mem⟩

protected theorem nonempty (S : PointedCone 𝕜 E) : (S : Set E).Nonempty :=
  ⟨0, S.zero_mem⟩

end SMul

section PositiveCone

variable (𝕜 E)
variable [OrderedSemiring 𝕜] [OrderedAddCommGroup E] [Module 𝕜 E] [OrderedSMul 𝕜 E]

/-- The positive cone is the proper cone formed by the set of nonnegative elements in an ordered
module. -/
def positive : PointedCone 𝕜 E where
  toConvexCone := ConvexCone.positive 𝕜 E
  zero_mem' := ConvexCone.pointed_positive _ _

@[simp]
theorem mem_positive {x : E} : x ∈ positive 𝕜 E ↔ 0 ≤ x :=
  Iff.rfl

@[simp]
theorem coe_positive : ↑(positive 𝕜 E) = ConvexCone.positive 𝕜 E :=
  rfl

end PositiveCone

section Module

variable [AddCommMonoid E] [Module 𝕜 E]
variable {S : PointedCone 𝕜 E}

set_option quotPrecheck false in
scoped notation "𝕜≥0" => { c : 𝕜 // 0 ≤ c }

instance : Module 𝕜≥0 E := Module.compHom E (@Nonneg.coeRingHom 𝕜 _)

protected theorem smul_mem {c : 𝕜} {x : E} (hc : 0 ≤ c) (hx : x ∈ S) : c • x ∈ S := by
  cases' eq_or_lt_of_le hc with hzero hpos
  . rw [← hzero, zero_smul]
    exact S.zero_mem
  . exact @ConvexCone.smul_mem _ E _ _ _ S _ _ hpos hx

instance hasSmul : SMul 𝕜≥0 S where
  smul := fun ⟨c, hc⟩ ⟨x, hx⟩ => ⟨c • x, S.smul_mem hc hx⟩

instance hasNsmul : SMul ℕ S where
  smul := fun n x => (n : 𝕜≥0) • x

@[simp]
protected theorem coe_smul (x : S) (n : 𝕜≥0) : n • x = n • (x : E) :=
  rfl

@[simp]
protected theorem nsmul_eq_smul_cast (x : S) (n : ℕ) : n • (x : E) = (n : 𝕜≥0) • (x : E) :=
  nsmul_eq_smul_cast _ _ _

@[simp]
theorem coe_nsmul (x : S) (n : ℕ) : (n • x : E) = n • (x : E) := by
  simp_rw [PointedCone.coe_smul, PointedCone.nsmul_eq_smul_cast] ; rfl

@[simp]
theorem coe_add : ∀ (x y : { x // x ∈ S }), (x + y : E) = ↑x + ↑y := by
  aesop

theorem add_mem ⦃x⦄ (hx : x ∈ S) ⦃y⦄ (hy : y ∈ S) : x + y ∈ S :=
  S.add_mem' hx hy

instance : AddMemClass (PointedCone 𝕜 E) E where
  add_mem ha hb := add_mem ha hb

instance : AddCommMonoid S :=
  Function.Injective.addCommMonoid (Subtype.val : S → E) Subtype.coe_injective rfl coe_add coe_nsmul

def subtype.addMonoidHom : S →+ E where
  toFun := Subtype.val
  map_zero' := rfl
  map_add' := by aesop

@[simp]
theorem coeSubtype.addMonoidHom : (subtype.addMonoidHom : S → E) = Subtype.val := rfl

instance : Module 𝕜≥0 S := by
  apply Function.Injective.module (𝕜≥0) subtype.addMonoidHom
  simp only [coeSubtype.addMonoidHom, Subtype.coe_injective]
  simp only [coeSubtype.addMonoidHom, PointedCone.coe_smul, Subtype.forall, implies_true, forall_const] -- a single `simp` does not work!

def subtype.linearMap : S →ₗ[𝕜≥0] E where
  toFun := Subtype.val
  map_add' := by simp
  map_smul' := by simp

end Module


section ofModule

variable {E M}
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid M] [Module { c : 𝕜 // 0 ≤ c } M] -- notation not working

def ofModule (f : M →ₗ[𝕜≥0] E) : ConvexCone 𝕜 E where
  carrier := Set.range f
  smul_mem' := fun c hc _ ⟨y, _⟩ => ⟨(⟨c, le_of_lt hc⟩ : 𝕜≥0) • y, by aesop⟩
  add_mem' := fun x1 ⟨y1, hy1⟩ x2 ⟨y2, hy2⟩ => ⟨y1 + y2, by aesop⟩

theorem isPointed (f : M →ₗ[𝕜≥0] E) : (ofModule f).Pointed :=
  ⟨0, LinearMap.map_zero f⟩

def map {F} [AddCommMonoid F] [Module 𝕜 F] (f : M →ₗ[𝕜≥0] E) (g : E →ₗ[𝕜≥0] F) :
    ConvexCone 𝕜 F :=
  ofModule (g.comp f)

end ofModule

section DirectSum

variable {ι : Type _} [dec_ι : DecidableEq ι]

open DirectSum Set

variable {E : ι → Type _} [∀ i, AddCommMonoid (E i)] [∀ i, Module 𝕜 (E i)]

variable {S : ∀ i, PointedCone 𝕜 (E i)}

def DirectSum : ConvexCone 𝕜 (⨁ (i : ι), E i) :=
  ofModule <| DFinsupp.mapRange.linearMap <| fun i => subtype.linearMap (S := S i)

end DirectSum


end PointedCone
