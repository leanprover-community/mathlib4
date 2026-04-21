/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Totally split algebras

An `R`-algebra `S` is finite (totally) split if it is isomorphic to `Fin n → R` for some `n`.
Geometrically, this corresponds to a trivial covering.

Every totally split algebra is finite étale and conversely, every finite étale covering is étale
locally totally split (TODO, @chrisflav).
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

open TensorProduct

/-- `S` is a finite, totally split `R`-algebra if `S` is isomorphic to `Fin n → R` for some `n`.
Geometrically, this is a trivial cover of degree `n`. -/
class Algebra.IsFiniteSplit (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] : Prop where
  nonempty_algEquiv_fun (R S) : ∃ n : ℕ, Nonempty (S ≃ₐ[R] Fin n → R)

namespace Algebra.IsFiniteSplit

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

instance {T : Type*} [CommRing T] [Algebra R T] [IsFiniteSplit R S] :
    IsFiniteSplit T (T ⊗[R] S) := by
  obtain ⟨n, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun R S
  refine ⟨n, ⟨?_⟩⟩
  exact (TensorProduct.congr AlgEquiv.refl e).trans
    ((TensorProduct.piRight R T T (fun _ : Fin n ↦ R)).trans <|
      AlgEquiv.piCongrRight fun i ↦ TensorProduct.rid R T T)

instance {ι : Type*} [Finite ι] : IsFiniteSplit R (ι → R) where
  nonempty_algEquiv_fun := by
    cases nonempty_fintype ι
    exact ⟨_, ⟨AlgEquiv.piCongrLeft' _ _ (Fintype.equivFin ι)⟩⟩

lemma of_algEquiv {S' : Type*} [CommRing S'] [Algebra R S'] (e : S ≃ₐ[R] S') [IsFiniteSplit R S] :
    IsFiniteSplit R S' := by
  obtain ⟨n, ⟨f⟩⟩ := nonempty_algEquiv_fun R S
  exact ⟨n, ⟨e.symm.trans f⟩⟩

instance : IsFiniteSplit R R :=
  .of_algEquiv (AlgEquiv.funUnique (ι := Fin 1) _ _)

lemma of_subsingleton [Subsingleton R] : IsFiniteSplit R S := by
  have : Subsingleton S := RingHom.codomain_trivial (algebraMap R S)
  exact ⟨0, ⟨default⟩⟩

instance [IsFiniteSplit R S] : Module.Free R S := by
  obtain ⟨n, ⟨e⟩⟩ := nonempty_algEquiv_fun R S
  exact Module.Free.of_equiv e.symm.toLinearEquiv

instance [IsFiniteSplit R S] : Module.FinitePresentation R S := by
  obtain ⟨n, ⟨e⟩⟩ := nonempty_algEquiv_fun R S
  apply Module.FinitePresentation.of_equiv e.symm.toLinearEquiv

instance [IsFiniteSplit R S] : Etale R S := by
  obtain ⟨n, ⟨e⟩⟩ := nonempty_algEquiv_fun R S
  exact .of_equiv e.symm

end IsFiniteSplit

end Algebra
