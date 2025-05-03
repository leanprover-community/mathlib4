import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.RingTheory.Regular.Depth

namespace CategoryTheory

universe w v u

open Abelian Limits ZeroObject

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {X : C} {S : ShortComplex C} (hS : S.ShortExact) [Projective S.X₂]
  (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (h0 : n₀ ≠ 0)

noncomputable def dim_shifting (n : ℕ) : Ext X S.X₃ n₀ ≃+ Ext X S.X₁ n₁ := by
  refine AddEquiv.ofBijective (hS.extClass.postcomp X h) ⟨?_, ?_⟩
  · sorry--apply (AddMonoidHom.ker_eq_bot_iff (hS.extClass.postcomp X h)).mpr
  · sorry

end CategoryTheory

universe v u

open IsLocalRing
open RingTheory.Sequence Ideal CategoryTheory CategoryTheory.Abelian

variable {R : Type u} [CommRing R] [Small.{v} R]

lemma proj_mod_over_local_ring_is_free [IsLocalRing R] (M : ModuleCat.{v} R) [Module.Finite R M] [Module.Projective R M]: Module.Free R M:= by
  -- Add your proof here
  sorry

local instance : CategoryTheory.HasExt.{max u v} (ModuleCat.{v} R) :=
  --CategoryTheory.HasExt.standard (ModuleCat.{v} R)
  CategoryTheory.hasExt_of_enoughProjectives.{max u v} (ModuleCat.{v} R)

open scoped Classical in
theorem AuslanderBuchsbaum [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{v} R) [Nontrivial M] [Module.Finite R M]
    [Small.{v} (R ⧸ (IsLocalRing.maximalIdeal R))]
    (hfinprojdim : ∃ i : ℕ, CategoryTheory.HasProjectiveDimensionLE M i) :
    Nat.find hfinprojdim + IsLocalRing.depth M = IsLocalRing.depth (ModuleCat.of R R) := by
    generalize h: Nat.find hfinprojdim = n
    induction' n
    · simp
      have pdz: HasProjectiveDimensionLE M (Nat.find hfinprojdim) := Nat.find_spec hfinprojdim
      simp [h, HasProjectiveDimensionLE, hasProjectiveDimensionLT_iff M  1] at pdz
      have pm: Module.Projective R M := by
        sorry
      sorry
    · sorry
