import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Algebra.Order.Nonneg.Ring
import Mathlib.Algebra.DirectSum.Module

open Set LinearMap


structure PointedCone (𝕜 : Type _) (E : Type _) [OrderedSemiring 𝕜] [AddCommMonoid E]
     [SMul 𝕜 E] extends ConvexCone 𝕜 E where
  zero_mem' : 0 ∈ carrier

namespace PointedCone


section SMul
variable {𝕜} [OrderedSemiring 𝕜]
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
variable [OrderedSemiring 𝕜]
variable [OrderedAddCommGroup E]
variable [Module 𝕜 E] [OrderedSMul 𝕜 E]

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

variable {𝕜 E}
variable [OrderedSemiring 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable {S : PointedCone 𝕜 E}

instance : Module { c : 𝕜 // 0 ≤ c } E := Module.compHom E (@Nonneg.coeRingHom 𝕜 _)

protected theorem smul_mem {c : 𝕜} {x : E} (hc : 0 ≤ c) (hx : x ∈ S) : c • x ∈ S := by
  cases' eq_or_lt_of_le hc with hzero hpos
  . rw [← hzero, zero_smul]
    exact S.zero_mem
  . exact @ConvexCone.smul_mem _ E _ _ _ S _ _ hpos hx

instance hasSmul : SMul { c : 𝕜 // 0 ≤ c } S where
  smul := fun ⟨c, hc⟩ ⟨x, hx⟩ => ⟨c • x, S.smul_mem hc hx⟩

instance hasNsmul : SMul ℕ S where
  smul := fun n x => (n : { c : 𝕜 // 0 ≤ c }) • x

@[simp]
protected theorem coe_smul (x : S) (n : { c : 𝕜 // 0 ≤ c }) : n • x = n • (x : E) :=
  rfl

@[simp]
protected theorem nsmul_eq_smul_cast (x : S) (n : ℕ) : n • (x : E) = (n : { c : 𝕜 // 0 ≤ c }) • (x : E) :=
  nsmul_eq_smul_cast _ _ _

@[simp]
theorem coe_nsmul (x : S) (n : ℕ) : (n • x : E) = n • (x : E) := by
  simp_rw [PointedCone.coe_smul, PointedCone.nsmul_eq_smul_cast] ; rfl

theorem add_mem ⦃x⦄ (hx : x ∈ S) ⦃y⦄ (hy : y ∈ S) : x + y ∈ S :=
  S.add_mem' hx hy

instance : AddMemClass (PointedCone 𝕜 E) E where
  add_mem ha hb := add_mem ha hb

instance : AddCommMonoid S :=
  Function.Injective.addCommMonoid (Subtype.val : S → E) Subtype.coe_injective rfl (by aesop) coe_nsmul

def subtype.addMonoidHom : S →+ E where
  toFun := Subtype.val
  map_zero' := rfl
  map_add' := by aesop

@[simp]
theorem coeSubtype.addMonoidHom : (subtype.addMonoidHom : S → E) = Subtype.val := rfl

instance : Module { c : 𝕜 // 0 ≤ c } S := by
  apply Function.Injective.module ({ c : 𝕜 // 0 ≤ c }) subtype.addMonoidHom
  simp only [coeSubtype.addMonoidHom, Subtype.coe_injective]
  simp only [coeSubtype.addMonoidHom, PointedCone.coe_smul, Subtype.forall, implies_true, forall_const] -- a single `simp` does not work!

def subtype.linearMap : S →ₗ[{ c : 𝕜 // 0 ≤ c }] E where
  toFun := Subtype.val
  map_add' := by simp
  map_smul' := by simp

end Module

section map

variable [LinearOrderedField 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid F] [Module 𝕜 F]
variable [AddCommMonoid G] [Module 𝕜 G]

def map (f : E →ₗ[𝕜] F) (S : PointedCone 𝕜 E) : PointedCone 𝕜 F where
  toConvexCone := (S.toConvexCone).map f
  zero_mem' := ⟨0, S.zero_mem, f.map_zero⟩

@[simp]
theorem mem_map {f : E →ₗ[𝕜] F} {S : PointedCone 𝕜 E} {y : F} : y ∈ S.map f ↔ ∃ x ∈ S, f x = y :=
  Set.mem_image f S y


theorem map_map (g : F →ₗ[𝕜] G) (f : E →ₗ[𝕜] F) (S : PointedCone 𝕜 E) :
    (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| image_image g f S

@[simp]
theorem map_id (S : PointedCone 𝕜 E) : S.map LinearMap.id = S :=
  SetLike.coe_injective <| image_id _

/-- The preimage of a proper cone under a `𝕜`-linear map is a convex cone. -/
def comap (f : E →ₗ[𝕜] F) (S : PointedCone 𝕜 F) : PointedCone 𝕜 E where
  toConvexCone := (S.toConvexCone).comap f
  zero_mem' := by
    simp_rw [ConvexCone.comap, mem_preimage, map_zero, SetLike.mem_coe, mem_coe, zero_mem]

@[simp]
theorem coe_comap (f : E →ₗ[𝕜] F) (S : PointedCone 𝕜 F) : (S.comap f : Set E) = f ⁻¹' S :=
  rfl

@[simp]
theorem comap_id (S : PointedCone 𝕜 E) : S.comap LinearMap.id = S :=
  rfl

theorem comap_comap (g : F →ₗ[𝕜] G) (f : E →ₗ[𝕜] F) (S : PointedCone 𝕜 G) :
    (S.comap g).comap f = S.comap (g.comp f) :=
  rfl

@[simp]
theorem mem_comap {f : E →ₗ[𝕜] F} {S : PointedCone 𝕜 F} {x : E} : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl

end map

section ofModule

variable [OrderedSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid M] [Module { c : 𝕜 // 0 ≤ c } M] -- notation not working

def ofModule (f : M →ₗ[{ c : 𝕜 // 0 ≤ c }] E) : PointedCone 𝕜 E where
  carrier := Set.range f
  smul_mem' := fun c hc _ ⟨y, _⟩ => ⟨(⟨c, le_of_lt hc⟩ : { c : 𝕜 // 0 ≤ c }) • y, by aesop⟩
  add_mem' := fun x1 ⟨y1, hy1⟩ x2 ⟨y2, hy2⟩ => ⟨y1 + y2, by aesop⟩
  zero_mem' := ⟨0, LinearMap.map_zero f⟩

end ofModule

section DirectSum

variable {ι : Type _} [dec_ι : DecidableEq ι]

open DirectSum Set

variable [OrderedSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]
variable {E : ι → Type _} [∀ i, AddCommMonoid (E i)] [∀ i, Module 𝕜 (E i)]
variable {S : ∀ i, PointedCone 𝕜 (E i)}

protected def DirectSum : PointedCone 𝕜 (⨁ (i : ι), E i) :=
  ofModule <| DFinsupp.mapRange.linearMap <| fun i => subtype.linearMap (S := S i)

end DirectSum


end PointedCone
