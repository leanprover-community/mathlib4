-- import Mathlib.Algebra.Clone.Instances
import Mathlib.Data.ENat.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.BooleanRing

/-!
Post's Lattice, rough sketch

Every Boolean function clone is equal to one of the named clones in Post's lattice.
-/

/-- The type naming one element in Post's lattice. This naming is injective,
in the sense that each clone has a unique name, with the exception of the
infinite T0 and T1 sequences: `T0[...,k=0]` corresponds to `T1[P0=false,...]`,
and setting `P1=true` corresponds to `T1[k=1]`, and vice versa. This is quotiented
out in the type `PostLattice`. -/
inductive PostCloneName
| Id
| EssUnary (P0 : Bool) (P1 : Bool)
| Conjunctive (P0 : Bool) (P1 : Bool)
| Disjunctive (P0 : Bool) (P1 : Bool)
| Affine (P0 : Bool) (P1 : Bool)
| Dual
| EssUnaryDual
| AffineDual
| DualMono
| DualP
| T0 (Mono : Bool) (P1 : Bool) (k : ENat)
| T1 (Mono : Bool) (P0 : Bool) (k : ENat)
deriving DecidableEq, Inhabited

/-- The relation on `PostCloneName` saying that they are two names for the same
clone. -/
instance postSetoid : Setoid PostCloneName where
  r x y := match x, y with
    | .T0 m₁ p₁ k₁, .T1 m₂ p₀ k₂ =>
      m₁ = m₂ ∧ k₂ = (if p₁ then 1 else 0) ∧ k₁ = (if p₀ then 1 else 0)
    | .T1 m₁ p₀ k₂ , .T0 m₂ p₁ k₁=>
      m₁ = m₂ ∧ k₂ = (if p₁ then 1 else 0) ∧ k₁ = (if p₀ then 1 else 0)
    | x, y => x = y
  iseqv := {
    refl x := by simp
    symm {x y} h := by
      cases x
      <;> cases y
      <;> simp at h ⊢
      all_goals tauto
    trans {x y z} h₁ h₂ := by
      cases x
      <;> cases y
      <;> simp at h₁
      <;> cases z
      <;> simp at h₂ ⊢
      all_goals {
        try rcases h₁ with ⟨rfl, rfl⟩
        try rcases h₁ with ⟨rfl, rfl, rfl⟩
        try assumption
        try cases ‹Bool› <;> simp at h₂ ⊢ <;> tauto
      }
  }

--####
--these properties are defined in Instances.lean I'm just copying them here for an example
def kWisePropPreserving {α t : Type*} (k : WithTop ℕ) (P : t → Prop) (f : (α → t) → t) : Prop :=
  ∀ {m : ℕ} (_ : m ≤ k) (kts : Fin m → (α → t)),
    (∀ i, ∃ j, P ((kts j) i)) → ∃ j, P (f (kts j))

def Function.EssentiallyUnary {α t : Type*} (f : (α → t) → t) : Prop :=
  ∃(i : α) (fi : t → t), ∀ts, f ts = fi (ts i)

def Function.Conjunctive {α β : Type*} [Min α] [Min β] (f : α → β) : Prop :=
  ∀ ⦃a b⦄, f (min a b) = min (f a) (f b)

def Function.Disjunctive {α β : Type*} [Max α] [Max β] (f : α → β) : Prop :=
  ∀ ⦃a b⦄, f (max a b) = max (f a) (f b)

def Function.CommutesWithEndo {α t : Type*} (φ : t → t) (f : (α → t) → t) : Prop :=
  ∀ ts, φ (f ts) = f (fun i ↦ φ (ts i))

def Function.IsMultiargAffine {α t : Type*} [Fintype α]
    [NonUnitalNonAssocSemiring t] (f : (α → t) → t) : Prop :=
  ∃ c, ∃ (cs : α → t), ∀ x, f x = c + ∑ i, (cs i) * (x i)
--#####

/-- Get the function clone named. This is a `Set` of functions which obey the appropriate
closure properties, and so gets a `Clone` instance. -/
def PostCloneName.toClone (clone : PostCloneName) : ((k : ℕ) → Set ((Fin k → Bool) → Bool)) :=
  fun _ ↦ match clone with
  | .Id => .univ
  | .EssUnary P0 P1 =>
    Function.EssentiallyUnary
    ∩ kWisePropPreserving P0.toNat (· = false)
    ∩ kWisePropPreserving P1.toNat (· = true)
  | .Conjunctive P0 P1 =>
    Function.Conjunctive
    ∩ kWisePropPreserving P0.toNat (· = false)
    ∩ kWisePropPreserving P1.toNat (· = true)
  | .Disjunctive P0 P1 =>
    Function.Disjunctive
    ∩ kWisePropPreserving P0.toNat (· = false)
    ∩ kWisePropPreserving P1.toNat (· = true)
  | .Affine P0 P1 =>
      Function.IsMultiargAffine
    ∩ kWisePropPreserving P0.toNat (· = false)
    ∩ kWisePropPreserving P1.toNat (· = true)
  | .Dual => Function.CommutesWithEndo not
  | .EssUnaryDual => Function.EssentiallyUnary ∩ Function.CommutesWithEndo not
  | .AffineDual => Function.IsMultiargAffine ∩ Function.CommutesWithEndo not
  | .DualMono => Function.CommutesWithEndo not ∩ Monotone
  | .DualP => Function.CommutesWithEndo not
    ∩ kWisePropPreserving 1 (· = false)
    ∩ kWisePropPreserving 1 (· = true)
  | .T0 mono P1 k =>
    (if mono then Monotone else .univ)
    ∩ kWisePropPreserving P1.toNat (· = true)
    ∩ kWisePropPreserving k (· = false)
  | .T1 mono P0 k =>
    (if mono then Monotone else .univ)
    ∩ kWisePropPreserving P0.toNat (· = false)
    ∩ kWisePropPreserving k (· = true)

/-- The type of elements in Post's Lattice -/
def PostLattice : Type := Quotient postSetoid

/-- Get the function clone named by this element of Post's lattice -/
def PostLattice.toClone (l : PostLattice) : ((k : ℕ) → Set ((Fin k → Bool) → Bool)) :=
  Quotient.lift PostCloneName.toClone (by sorry) l

-- instance (l : PostLattice) : Clone l.toClone where
  -- ...

/-- Every function clone on Booleans is equal to some element of Post's Lattice. -/
theorem bool_clone_exists_post_lattice
    (f : (k : ℕ) → Set ((Fin k → Bool) → Bool)) [Clone f]
    : ∃ (l : PostLattice), l.toClone = f := by
  sorry
