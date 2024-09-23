import Mathlib.RepresentationTheory.GroupCohomology.Basic
import Mathlib.RepresentationTheory.GroupCohomology.blehfgh
import Mathlib.RepresentationTheory.GroupCohomology.LowDegree
import Mathlib.RepresentationTheory.GroupCohomology.LowDegreeHomology

universe v u

namespace Rep
open CategoryTheory

variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (A : Rep k G)

lemma ρ_norm_eq (g : G) (x : A) : A.ρ g (hom (norm A) x) = hom (norm A) x := by
  simpa using Fintype.sum_bijective (α := A) (g * ·)
    (Group.mulLeft_bijective g) _ _ fun x => by simp

lemma norm_ρ_eq (g : G) (x : A) : hom (norm A) (A.ρ g x) = hom (norm A) x := by
  simpa using Fintype.sum_bijective (α := A) (· * g)
    (Group.mulRight_bijective g) _ _ fun x => by simp

noncomputable def norm2 : A.ρ.coinvariants →ₗ[k] A.ρ.invariants :=
  A.ρ.coinvariantsLift ((hom <| norm A).codRestrict _
    fun a g => ρ_norm_eq A g a) fun g => by
      ext x; exact norm_ρ_eq A g x

noncomputable def TateCohomology [DecidableEq G] (i : ℤ) : ModuleCat k :=
  match i with
  | 0 => ModuleCat.of k (A.ρ.invariants ⧸ (LinearMap.range (norm2 A)))
  | (n + 1 : ℕ) => groupCohomology A (n + 1)
  | -1 => ModuleCat.of k (LinearMap.ker (norm2 A))
  | -(n + 2 : ℕ) => groupHomology A (n + 1)

end Rep
