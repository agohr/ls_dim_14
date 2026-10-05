import QuaternionicSymmetry.ComplexProjectiveDiagonalRegularFamily
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-! Distinct integral Laurent monomials are linearly independent as
complex-valued functions on the actual complex torus. -/

namespace QuaternionicSymmetry.ComplexTorusCharacterIndependent

open TorusLaurentRepresentation
noncomputable section

variable {r : ℕ}

def scalarCharacter (μ : Fin r → ℤ) : ComplexTorus r →* ℂ :=
  (Units.coeHom ℂ).comp (complexWeightCharacter μ)

theorem scalarCharacter_injective :
    Function.Injective (scalarCharacter (r := r)) := by
  intro μ ν h
  apply funext
  intro i
  let z : ComplexTorus r := fun j =>
    if j = i then Units.mk0 (2 : ℂ) (by norm_num) else 1
  have hz := congrArg (fun χ : ComplexTorus r →* ℂ => χ z) h
  simp [scalarCharacter, complexWeightCharacter, z,
    Finset.prod_ite, Finset.mem_univ] at hz
  have hz' : ((2 : ℂ) ^ μ i) = (2 : ℂ) ^ ν i := by
    simpa using hz
  have hr : (2 : ℝ) ^ μ i = (2 : ℝ) ^ ν i := by
    exact Complex.ofReal_injective (by simpa [Complex.ofReal_zpow] using hz')
  exact (zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (2 : ℝ) ≠ 1)) hr

theorem scalarCharacter_linearIndependent :
    LinearIndependent ℂ (fun μ : Fin r → ℤ =>
      (scalarCharacter μ : ComplexTorus r → ℂ)) :=
  (linearIndependent_monoidHom (ComplexTorus r) ℂ).comp
    scalarCharacter scalarCharacter_injective

/-- A finite Laurent sum vanishing at every complex-torus point has each
coefficient zero, after equal weights have been grouped together. -/
theorem coefficient_zero_of_laurent_sum
    (s : Finset (Fin r → ℤ)) (c : (Fin r → ℤ) → ℂ)
    (h : ∀ z : ComplexTorus r,
      ∑ μ ∈ s, c μ * (complexWeightCharacter μ z : ℂ) = 0)
    (μ : Fin r → ℤ) (hμ : μ ∈ s) : c μ = 0 := by
  apply (linearIndependent_iff'.mp
    (scalarCharacter_linearIndependent (r := r))) s c
  · ext z
    simpa [scalarCharacter, Pi.zero_apply, smul_eq_mul] using h z
  · exact hμ

end
end QuaternionicSymmetry.ComplexTorusCharacterIndependent
