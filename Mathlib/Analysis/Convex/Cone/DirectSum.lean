import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Algebra.Order.Nonneg.Ring
import Mathlib.Algebra.DirectSum.Module

namespace ConvexCone.Pointed

variable {𝕜} [OrderedSemiring 𝕜] [Nontrivial 𝕜]

set_option quotPrecheck false in
notation "𝕜≥0" => { c : 𝕜 // 0 ≤ c }

section Module

variable {E} [AddCommMonoid E] [Module 𝕜 E]

instance : Module 𝕜≥0 E := Module.compHom E (@Nonneg.coeRingHom 𝕜 _)

variable {S} {S : ConvexCone 𝕜 E} [hS : Fact S.Pointed]

@[simp]
theorem zero_mem : (0 ∈ S) := hS.elim

instance : Zero S where
  zero := ⟨0, hS.elim⟩

instance hasSmul : SMul 𝕜≥0 S where
  smul := fun ⟨c, hc⟩ ⟨x, hx⟩ => ⟨c • x, by
    cases' eq_or_lt_of_le hc with hzero hpos
    . simp_rw [← hzero, zero_smul, zero_mem]
    . exact S.smul_mem hpos hx⟩

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
  simp_rw [Pointed.coe_smul, Pointed.nsmul_eq_smul_cast] ; rfl

@[simp]
theorem coe_add : ∀ (x y : { x // x ∈ S }), (x + y : E) = ↑x + ↑y := by
  aesop

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
  simp_rw [coeSubtype.addMonoidHom, Subtype.coe_injective]
  simp -- a single `simp [coeSubtype, Subtype.coe_injective]` does not work!

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

variable {S : ∀ i, ConvexCone 𝕜 (E i)} [hS : ∀ i, Fact (S i).Pointed]

def DirectSum : ConvexCone 𝕜 (⨁ (i : ι), E i) :=
  ofModule <| DFinsupp.mapRange.linearMap <| fun i => subtype.linearMap (S := S i)

end DirectSum

end ConvexCone.Pointed
