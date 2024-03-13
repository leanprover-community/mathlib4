import Mathlib.InformationTheory.Code.Linear.HexaCode.F4
import Mathlib.InformationTheory.Code.HammingCode

open F4

abbrev F_4_6 := Fin 6 → F4

def b₁ : F_4_6 := ![ω,ω⁻¹,ω⁻¹,ω,ω⁻¹,ω]
def b₂ : F_4_6 := ![ω⁻¹,ω,ω,ω⁻¹,ω⁻¹,ω]
def b₃ : F_4_6 := ![ω⁻¹,ω,ω⁻¹,ω,ω,ω⁻¹]

def a₁ : F_4_6 := ![ω,ω⁻¹,ω,ω⁻¹,ω,ω⁻¹]
abbrev hexacodeBasis : Set F_4_6 := {b₁,b₂,b₃}

instance HexacodeBasis.Nonempty : Inhabited hexacodeBasis := {
  default := ⟨b₁,by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or]⟩}

def hexaCode : Submodule F4 F_4_6 := Submodule.span (F4) hexacodeBasis

#synth _LinearCode ℕ∞ F4 trivdist hdist hexaCode
