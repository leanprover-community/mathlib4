import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Algebra.Order.Nonneg.Ring

structure PointedCone (𝕜 : Type _) (E : Type _) [OrderedSemiring 𝕜] [AddCommMonoid E]
     [SMul 𝕜 E] extends ConvexCone 𝕜 E where
  zero_mem' : 0 ∈ carrier

namespace PointedCone

variable {𝕜} [OrderedSemiring 𝕜]
variable {E} [AddCommMonoid E] [SMul 𝕜 E]

instance : Coe (PointedCone 𝕜 E) (ConvexCone 𝕜 E) :=
  ⟨fun K => K.1⟩

theorem ext' : Function.Injective ((↑) : PointedCone 𝕜 E → ConvexCone 𝕜 E) := fun S T h => by
  cases S; cases T; congr

instance : SetLike (PointedCone 𝕜 E) E where
  coe K := K.carrier
  coe_injective' _ _ h := PointedCone.ext' (SetLike.coe_injective h)


instance : ZeroMemClass (PointedCone 𝕜 E) E where
  zero_mem := zero_mem'

section Module

variable [Module 𝕜 E]
variable (S : PointedCone 𝕜 E)

set_option quotPrecheck false in
notation "𝕜≥0" => { c : 𝕜 // 0 ≤ c }

-- instance : Zero S where
--   zero := ⟨0, S.zero_mem'⟩


set_option pp.coercions false in
instance hasSmul : SMul 𝕜≥0 S where
  smul := fun ⟨c, hc⟩ ⟨x, hx⟩ => ⟨c • x, by
    cases' eq_or_lt_of_le hc with hzero hpos
    . simp_rw [← hzero]
      /-
      tactic 'rewrite' failed, did not find instance of the pattern in the target expression
        OfNat.ofNat 0 • ?m

      case inl
      𝕜: Type ?u.6679
      inst✝³: OrderedSemiring 𝕜
      E: Type ?u.6685
      inst✝²: AddCommMonoid E
      inst✝¹: SMul 𝕜 E
      inst✝: Module 𝕜 E
      S: PointedCone 𝕜 E
      x✝¹: { c // OfNat.ofNat 0 ≤ c }
      x✝: { x // x ∈ S }
      c: 𝕜
      hc: OfNat.ofNat 0 ≤ c
      x: E
      hx: x ∈ S
      hzero: OfNat.ofNat 0 = c
      ⊢ OfNat.ofNat 0 • x ∈ S
      -/
      rw [zero_smul]
    . exact S.smul_mem hpos hx⟩

end Module

end PointedCone
