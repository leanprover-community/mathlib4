module

public import Mathlib.LinearAlgebra.Matrix.Cartan.Realisation
public import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Basis

noncomputable section

variable (k : Type*) [Field k] [CharZero k] (n : ℕ)

namespace Matrix.IsFiniteCartan

variable {l : Type*} [Fintype l] [DecidableEq l] {M : Matrix l l ℤ} (hM : M.IsFiniteCartan)
include hM

theorem exists_A_or_B_or_C_or_D_or_E_or_F_or_G (hM' : M.IsIndecomposable) :
    (∃ n e, M.reindex e e = CartanMatrix.A n) ∨
    (∃ n e, M.reindex e e = CartanMatrix.B n) ∨
    (∃ n e, M.reindex e e = CartanMatrix.C n) ∨
    (∃ n e, M.reindex e e = CartanMatrix.D n) ∨
    (∃ e, M.reindex e e = CartanMatrix.E 6) ∨
    (∃ e, M.reindex e e = CartanMatrix.E 7) ∨
    (∃ e, M.reindex e e = CartanMatrix.E 8) ∨
    (∃ e, M.reindex e e = CartanMatrix.F₄) ∨
    (∃ e, M.reindex e e = CartanMatrix.G₂) := sorry

end Matrix.IsFiniteCartan

namespace CartanMatrix

theorem isFiniteCartan_a : (A n).IsFiniteCartan := sorry

theorem isFiniteCartan_b : (B n).IsFiniteCartan := sorry

theorem isFiniteCartan_c : (C n).IsFiniteCartan := sorry

theorem isFiniteCartan_d : (D n).IsFiniteCartan := sorry

theorem isFiniteCartan_e₆ : (E 6).IsFiniteCartan := sorry

theorem isFiniteCartan_e₇ : (E 7).IsFiniteCartan := sorry

theorem isFiniteCartan_e₈ : (E 8).IsFiniteCartan := sorry

theorem isFiniteCartan_f₄ : F₄.IsFiniteCartan := sorry

theorem isFiniteCartan_g₂ : G₂.IsFiniteCartan := sorry

end CartanMatrix

namespace RootPairing

abbrev a := (CartanMatrix.isFiniteCartan_a n).toRootPairing k
abbrev a_base : (a k n).Base := (CartanMatrix.isFiniteCartan_a n).rootPairingBase k

abbrev b := (CartanMatrix.isFiniteCartan_b n).toRootPairing k
abbrev b_base : (b k n).Base := (CartanMatrix.isFiniteCartan_b n).rootPairingBase k

abbrev c := (CartanMatrix.isFiniteCartan_c n).toRootPairing k
abbrev c_base : (c k n).Base := (CartanMatrix.isFiniteCartan_c n).rootPairingBase k

abbrev d := (CartanMatrix.isFiniteCartan_d n).toRootPairing k
abbrev d_base : (d k n).Base := (CartanMatrix.isFiniteCartan_d n).rootPairingBase k

abbrev e₆ := CartanMatrix.isFiniteCartan_e₆.toRootPairing k
abbrev e₆_base : (e₆ k).Base := CartanMatrix.isFiniteCartan_e₆.rootPairingBase k

abbrev e₇ := CartanMatrix.isFiniteCartan_e₇.toRootPairing k
abbrev e₇_base : (e₇ k).Base := CartanMatrix.isFiniteCartan_e₇.rootPairingBase k

abbrev e₈ := CartanMatrix.isFiniteCartan_e₈.toRootPairing k
abbrev e₈_base : (e₈ k).Base := CartanMatrix.isFiniteCartan_e₈.rootPairingBase k

abbrev f₄ := CartanMatrix.isFiniteCartan_f₄.toRootPairing k
abbrev f₄_base : (f₄ k).Base := CartanMatrix.isFiniteCartan_f₄.rootPairingBase k

abbrev g₂ := CartanMatrix.isFiniteCartan_g₂.toRootPairing k
abbrev g₂_base : (g₂ k).Base := CartanMatrix.isFiniteCartan_g₂.rootPairingBase k

theorem exists_A_or_B_or_C_or_D_or_E_or_F_or_G {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    (P : RootPairing ι k M N)
    [P.IsReduced] [P.IsCrystallographic] [P.IsRootSystem] [P.IsIrreducible] :
    (∃ n, Nonempty (P.Equiv <| a k n)) ∨
    (∃ n, Nonempty (P.Equiv <| b k n)) ∨
    (∃ n, Nonempty (P.Equiv <| c k n)) ∨
    (∃ n, Nonempty (P.Equiv <| d k n)) ∨
    Nonempty (P.Equiv <| e₆ k) ∨
    Nonempty (P.Equiv <| e₇ k) ∨
    Nonempty (P.Equiv <| e₈ k) ∨
    Nonempty (P.Equiv <| f₄ k) ∨
    Nonempty (P.Equiv <| g₂ k) := by
  classical
  obtain ⟨b⟩ := P.nonempty_base
  have aux : ∀ {m : ℕ} {A : Matrix (Fin m) (Fin m) ℤ} (hA : A.IsFiniteCartan)
      (f : b.support ≃ Fin m), b.cartanMatrix.reindex f f = A →
      Nonempty (P.Equiv <| hA.toRootPairing k) := by
    refine fun {m A} hA f hf ↦ ⟨b.equivOfCartanMatrixEq (hA.rootPairingBase k)
      (f.trans (hA.rootPairingBaseEquiv k)) fun i j ↦ ?_⟩
    replace h₂ := congr_fun₂ (hA.rootPairingBase_cartanMatrix_eq k) (f i) (f j)
    aesop
  rcases b.cartanMatrix_isFiniteCartan.exists_A_or_B_or_C_or_D_or_E_or_F_or_G
      b.cartanMatrix_isIndecomposable with
      ⟨m, f, h⟩ | ⟨m, f, h⟩ | ⟨m, f, h⟩ | ⟨m, f, h⟩ | ⟨f, h⟩ | ⟨f, h⟩ | ⟨f, h⟩ | ⟨f, h⟩ | ⟨f, h⟩
  · exact .inl ⟨m, aux _ f h⟩
  · exact .inr <| .inl ⟨m, aux _ f h⟩
  · exact .inr <| .inr <| .inl ⟨m, aux _ f h⟩
  · exact .inr <| .inr <| .inr <| .inl ⟨m, aux _ f h⟩
  · exact .inr <| .inr <| .inr <| .inr <| .inl <| aux _ f h
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inl <| aux _ f h
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl <| aux _ f h
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl <| aux _ f h
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| aux _ f h

end RootPairing

namespace LieAlgebra

set_option linter.style.openClassical false
open scoped Classical
attribute [local instance] Fintype.ofFinite

def a := RootPairing.GeckConstruction.lieAlgebra <| RootPairing.a_base k n

def b := RootPairing.GeckConstruction.lieAlgebra <| RootPairing.b_base k n

def c := RootPairing.GeckConstruction.lieAlgebra <| RootPairing.c_base k n

def d := RootPairing.GeckConstruction.lieAlgebra <| RootPairing.d_base k n

def e₆ := RootPairing.GeckConstruction.lieAlgebra <| RootPairing.e₆_base k

def e₇ := RootPairing.GeckConstruction.lieAlgebra <| RootPairing.e₇_base k

def e₈ := RootPairing.GeckConstruction.lieAlgebra <| RootPairing.e₈_base k

def f₄ := RootPairing.GeckConstruction.lieAlgebra <| RootPairing.f₄_base k

def g₂ := RootPairing.GeckConstruction.lieAlgebra <| RootPairing.g₂_base k

open IsKilling RootPairing.GeckConstruction in
theorem exists_A_or_B_or_C_or_D_or_E_or_F_or_G [IsAlgClosed k]
    {L : Type*} [LieRing L] [LieAlgebra k L] [FiniteDimensional k L] [IsSimple k L] :
    (∃ n, Nonempty (L ≃ₗ⁅k⁆ a k n)) ∨
    (∃ n, Nonempty (L ≃ₗ⁅k⁆ b k n)) ∨
    (∃ n, Nonempty (L ≃ₗ⁅k⁆ c k n)) ∨
    (∃ n, Nonempty (L ≃ₗ⁅k⁆ d k n)) ∨
    Nonempty (L ≃ₗ⁅k⁆ e₆ k) ∨
    Nonempty (L ≃ₗ⁅k⁆ e₇ k) ∨
    Nonempty (L ≃ₗ⁅k⁆ e₈ k) ∨
    Nonempty (L ≃ₗ⁅k⁆ f₄ k) ∨
    Nonempty (L ≃ₗ⁅k⁆ g₂ k) := by
  obtain ⟨x, hx⟩ := exists_isCartanSubalgebra_engel k L
  let P := rootSystem <| LieSubalgebra.engel k x
  have aux : ∀ {m : ℕ} {A : Matrix (Fin m) (Fin m) ℤ} (hA : A.IsFiniteCartan),
      Nonempty (P.Equiv <| hA.toRootPairing k) →
      Nonempty (L ≃ₗ⁅k⁆ lieAlgebra <| hA.rootPairingBase k) := by
    refine fun {m A} hA h ↦ h.map fun e ↦ ?_
    have : (hA.toRootPairing k).IsIrreducible := e.isIrreducible
    exact equivOfRootSystemEquiv <| .comp (equivRootSystem <| hA.rootPairingBase k) e
  rcases P.exists_A_or_B_or_C_or_D_or_E_or_F_or_G with
      ⟨m, h⟩ | ⟨m, h⟩ | ⟨m, h⟩ | ⟨m, h⟩ | h | h | h | h | h
  · exact .inl ⟨m, aux _ h⟩
  · exact .inr <| .inl ⟨m, aux _ h⟩
  · exact .inr <| .inr <| .inl ⟨m, aux _ h⟩
  · exact .inr <| .inr <| .inr <| .inl ⟨m, aux _ h⟩
  · exact .inr <| .inr <| .inr <| .inr <| .inl <| aux _ h
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inl <| aux _ h
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl <| aux _ h
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl <| aux _ h
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| aux _ h

end LieAlgebra
