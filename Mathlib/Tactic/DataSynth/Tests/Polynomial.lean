import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib

import Mathlib.Tactic.DataSynth

variable {R : Type*} [Semiring R]

@[data_synth out p]
def IsPolynomial (f : R → R) (p : Polynomial R) :=
  f = p.eval

open Polynomial

@[data_synth]
theorem isPolynomial_id : IsPolynomial (fun x : R => x) X := by
  simp [IsPolynomial]

@[data_synth]
theorem isPolynomial_const (y : R) : IsPolynomial (fun _ : R => y) (C y) := by
  simp [IsPolynomial]

@[data_synth]
theorem isPolynomial_comp {R : Type*} [CommSemiring R]
    (f g : R → R) {p q} (hf : IsPolynomial f p) (hg : IsPolynomial g q) :
    IsPolynomial (fun x : R => f (g x)) (p.comp q) := by
  simp_all [IsPolynomial]

@[data_synth]
theorem isPolynomial_add
    (f g : R → R) {p q} (hf : IsPolynomial f p) (hg : IsPolynomial g q) :
    IsPolynomial (fun x : R => f x + g x) (p + q) := by
  simp_all [IsPolynomial]

@[data_synth]
theorem isPolynomial_mul {R : Type*} [CommSemiring R]
    (f g : R → R) {p q} (hf : IsPolynomial f p) (hg : IsPolynomial g q) :
    IsPolynomial (fun x : R => f x * g x) (p * q) := by
  simp_all [IsPolynomial]

set_option pp.proofs false

#check (by data_synth : IsPolynomial (fun x : ℝ => 0) _)
#check (by data_synth : IsPolynomial (fun x : ℝ => 1) _)
#check (by data_synth : IsPolynomial (fun x : ℝ => x) _)
#check (by data_synth +norm_simp : IsPolynomial (fun x : ℝ => 1+x*3*x+4*x) _)
