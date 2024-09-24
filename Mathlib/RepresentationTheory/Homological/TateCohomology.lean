import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree

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

-- lol
noncomputable def TateCohomology2 [DecidableEq G] (i : ℤ) : ModuleCat k :=
  match i with
  | 0 => ModuleCat.of k (A.ρ.invariants ⧸ (LinearMap.range (norm2 A)))
  | 1 => ModuleCat.of k (groupCohomology.H1 A)
  | 2 => ModuleCat.of k (groupCohomology.H2 A)
  | (n + 3 : ℕ) => groupCohomology A (n + 3)
  | -1 => ModuleCat.of k (LinearMap.ker (norm2 A))
  | -2 => ModuleCat.of k (groupHomology.H1 A)
  | -3 => ModuleCat.of k (groupHomology.H2 A)
  | -(n + 4 : ℕ) => groupHomology A (n + 3)


end Rep
