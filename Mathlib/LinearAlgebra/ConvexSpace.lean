import Mathlib.Data.Finsupp.SMulWithZero
import Mathlib.Data.Finsupp.Sigma
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Bound
import Mathlib

universe u v

noncomputable section

structure FiniteProbability (R : Type u) [LE R] [AddCommMonoid R] [One R] (ι : Type v)
    extends weights : ι →₀ R where
  nonneg : ∀ m, 0 ≤ weights m
  total : weights.sum (fun _ r => r) = 1

namespace FiniteProbability

variable {R : Type u} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]
  {κ : Type v} {ι : κ → Type v}

open Classical in
def single {ι : Type v} (i : ι) : FiniteProbability R ι where
  weights := Finsupp.single i 1
  nonneg m := by
    rw [Finsupp.single_apply]
    split
    · exact zero_le_one' R
    · grind
  total := by simp

def duple {x y : R} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x + y = 1) : FiniteProbability R (Fin 2) where
  weights := Finsupp.single 0 x + Finsupp.single 1 y
  nonneg := by
    simp
    grind
  total := by
    simpa [Finsupp.sum_add_index]

def comp (f : FiniteProbability R κ) (g : (k : κ) → FiniteProbability R (ι k)) :
    FiniteProbability R (Σ k, ι k) where
  weights := f.sum (fun m r => (r • (g m).weights).embDomain <| .sigmaMk m)
  nonneg := by
    intro ⟨k, i⟩
    simp only [Finsupp.sum, Finsupp.coe_finset_sum, Finset.sum_apply]
    refine (Finset.sum_nonneg (fun k hk => ?_))
    simp [Finsupp.embDomain]
    have := f.nonneg
    have := (g k).nonneg
    bound
  total := by
    -- This proof was minimally cleaned up from a proof by Aristotle.
    have h_total : (f.sum fun m r => (r • (g m).weights).embDomain (.sigmaMk m)) =
        (f.sum fun m r => Finsupp.single m r).sum
          fun m r => (r • (g m).weights).embDomain (.sigmaMk m) := by simp
    have h_sum : ∀ m, ((f.weights m • (g m).weights).embDomain (.sigmaMk m)).sum (fun x r => r) =
        f.weights m * (g m).weights.sum (fun x r => r) := by
      intro m
      rw [Finsupp.sum_embDomain]
      simp only [Finsupp.sum, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum _ _ _,
        Finset.sum_subset (show _ ⊆ ((g m).weights.support) from
          fun x hx => by aesop) fun x hx₁ hx₂ => by aesop]
    have h_final : (f.sum fun m r => (r • (g m).weights).embDomain (.sigmaMk m)).sum
        (fun x r => r) = (f.sum fun (m : κ) (r : R) => Finsupp.single m r).sum fun m r => r := by
      rw [h_total, Finsupp.sum_sum_index];
      · have h_g_sum : ∀ m : κ, (g m).weights.sum (fun x r => r) = 1 := by
          intro m
          apply (g m).total
        simp_all only [Finsupp.sum_single, mul_one]
        exact Finset.sum_congr rfl fun m hm => h_sum m
      · exact fun _ => rfl
      · exact fun _ _ _ => rfl
    convert f.total using 1
    convert h_final using 1
    rw [Finsupp.sum_sum_index] <;> aesop

end FiniteProbability

/--
A set equipped with an operation of finite convex combinations,
where the coefficients must be non-negative and sum to 1.
-/
class ConvexSpace (R : Type u) (M : Type v)
    [PartialOrder R] [Semiring R] [IsStrictOrderedRing R] where
  convexCombination {ι : Type v} (f : FiniteProbability R ι) (xs : ι → M) : M
  /-- Associativity of convex combination. -/
  assoc
    {κ : Type v} (f₀ : FiniteProbability R κ)
    {ι : κ → Type v} (f₁ : (k : κ) → FiniteProbability R (ι k))
    (xs : (k : κ) → (ι k) → M) :
    convexCombination f₀ (fun m => convexCombination (f₁ m) (xs m)) =
      convexCombination (f₀.comp f₁) (fun ⟨k, i⟩ => xs k i)
  /-- A convex combination of a single point is that point. -/
  single {ι : Type v} (i : ι) (x : M) : convexCombination (.single i) (fun _ => x) = x
  /-- Convex combinations are determined by the points with non-zero weights. -/
  -- Perhaps this follows from `assoc`, but I don't see how.
  ext {ι : Type v} (f : FiniteProbability R ι) (xs xs' : ι → M)
    (h : ∀ i, i ∈ f.support → xs i = xs' i) : convexCombination f xs = convexCombination f xs'

open ConvexSpace

variable {R M} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R] [ConvexSpace R M]

/-- Take a convex combination of two points. -/
def convexCombo₂ (s t : R) (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) (x y : M) : M :=
  convexCombination (.duple hs ht h) (fun | 0 => x | 1 => y)

proof_wanted convexCombo₂_zero {x y : M} :
  convexCombo₂ (0 : R) 1 (by simp) (by simp) (by simp) x y = y

proof_wanted convexCombo₂_one {x y : M} :
  convexCombo₂ (1 : R) 0 (by simp) (by simp) (by simp) x y = x

proof_wanted convexCombo₂_same {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) {x : M} :
  convexCombo₂ s t hs ht h x x = x

-- TODO: show that an `AffineSpace` is a `ConvexSpace`.
-- TODO: show that `lineMap` agrees with `convexCombo₂` where defined.
-- TODO: show the usual associativity law for binary convex combinations follows from the
-- `assoc` axiom.
-- TODO: decide if the `ext` axiom is necessary (via a counterexample), or derive it from `assoc`.
