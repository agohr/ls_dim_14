import QuaternionicSymmetry.ComplexTorusCharacterHolomorphic

/-! The finite-section Laurent representation has genuinely holomorphic
matrix coefficients in its actual eigenbasis. This is a concrete
finite-dimensional regularity fact, independent of any Lie atlas on the
full twistor automorphism group. -/

namespace QuaternionicSymmetry.TorusLaurentMatrixHolomorphic

open TorusLaurentRepresentation ComplexTorusCharacterHolomorphic
open scoped Manifold ContDiff
noncomputable section

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup V] [Module ℂ V]
  (b : Module.Basis ι ℂ V) {r : ℕ} (μ : ι → Fin r → ℤ)

def matrixCoefficient (i j : ι) (z : ComplexTorus r) : ℂ :=
  b.repr (complexRepresentation b μ z (b j)) i

theorem matrixCoefficient_eq (i j : ι) (z : ComplexTorus r) :
    matrixCoefficient b μ i j z =
      if i = j then (complexWeightCharacter (μ j) z : ℂ) else 0 := by
  simp only [matrixCoefficient, complexRepresentation_basis, map_smul,
    b.repr_self, Finsupp.smul_single, smul_eq_mul]
  by_cases hij : i = j
  · subst i
    simp
  · simp [Finsupp.single_apply, hij, eq_comm]

theorem matrixCoefficient_holomorphic (i j : ι) :
    ContMDiff 𝓘(ℂ, Fin r → ℂ) 𝓘(ℂ, ℂ) ∞
      (matrixCoefficient b μ i j) := by
  classical
  by_cases hij : i = j
  · subst i
    have hfun : matrixCoefficient b μ j j =
        (fun z : ComplexTorus r => (complexWeightCharacter (μ j) z : ℂ)) := by
      funext z
      simpa using matrixCoefficient_eq b μ j j z
    rw [hfun]
    exact complexWeightCharacter_holomorphic (μ j)
  · have hfun : matrixCoefficient b μ i j =
        (fun _ : ComplexTorus r => (0 : ℂ)) := by
      funext z
      simpa [hij] using matrixCoefficient_eq b μ i j z
    rw [hfun]
    exact contMDiff_const

end
end QuaternionicSymmetry.TorusLaurentMatrixHolomorphic
