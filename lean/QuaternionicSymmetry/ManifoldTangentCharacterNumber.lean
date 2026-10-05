import QuaternionicSymmetry.TangentAhatCharacterDensity
import QuaternionicSymmetry.FormalExponentialSeries
import QuaternionicSymmetry.ManifoldIntegratedRecoveredCertificates
import Mathlib.Algebra.Module.Rat

/-! A real-valued Chern-Weil character functional on the actual manifold.
It integrates the full formal A-hat series of normalized tangent curvature
half traces against the character expansion in the actual quarter class.
No equality with a holomorphic Euler characteristic or analytic index is
asserted here; that is the remaining index-theorem comparison. -/
namespace QuaternionicSymmetry.ManifoldTangentCharacterNumber
open ManifoldEvenCharacteristicAlgebra ManifoldTangentTraceRootCandidates
open ManifoldIntegratedDensityCertificates ManifoldIntegratedRecoveredCertificates
open ManifoldRecoveredCharacteristicCertificates
open TangentAhatCharacterDensity RecoveredLogAhat
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

local instance : Algebra ℚ (Total (E := E) (M := M)) :=
  ManifoldTangentTraceRootCandidates.rationalAlgebra

theorem standard_evaluation (qdim : ℕ) (P : DimensionElevenTwelveDensity.P) :
    MvPolynomial.aeval (standardValues qdim (quarterUTotal Q D)
      (normalizedTangentHalfTrace Q D qdim)) P = evaluateSix Q D qdim P := by
  change MvPolynomial.aeval _ P = MvPolynomial.aeval _ P
  apply congrArg (fun v : Fin 6 → Total (E := E) (M := M) => MvPolynomial.aeval v P)
  funext i
  fin_cases i
  · rfl
  · exact candidatePower_eq_of_class Q D qdim 1
  · exact candidatePower_eq_of_class Q D qdim 2
  · exact candidatePower_eq_of_class Q D qdim 3
  · exact candidatePower_eq_of_class Q D qdim 4
  · exact candidatePower_eq_of_class Q D qdim 5

omit [Nontrivial E] in
/-- This is an actual formal exponential, with every tangent coefficient
retained, rather than a supplied truncation of the characteristic series. -/
theorem tangentAhatCoefficient_eq_series (qdim j : ℕ) :
    tangentAhatCoefficient (normalizedTangentHalfTrace Q D qdim) j =
      PowerSeries.coeff j (FormalExponentialSeries.exponential
        (fun m => algebraMap ℚ (Total (E := E) (M := M)) (LogAhat.ell m) *
          normalizedTangentHalfTrace Q D qdim m)) :=
  (FormalExponentialSeries.exponential_coefficient _ _).symm

variable [MeasurableSpace E] [BorelSpace E]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]

def characteristicFunctional (qdim k : ℕ) (hdim : 4*(k+1) = Module.finrank ℝ E) :
    LaurentPolynomial ℚ →ₗ[ℚ] ℝ :=
  (((integrateGrade Q k hdim).comp
    (DirectSum.component ℝ ℕ (Grade (E := E) (M := M)) (k+1))).restrictScalars ℚ).comp
      (characterDensity (k+1) (quarterUTotal Q D) (normalizedTangentHalfTrace Q D qdim))

theorem virtual11_eq_recovered (hdim : 44 = Module.finrank ℝ E) :
    characteristicFunctional Q D 11 10 hdim (Characters.virtual 11) =
      sixCandidateNumber Q D 11 10 hdim DimensionElevenTwelveDensity.density11 := by
  unfold characteristicFunctional
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  rw [characterDensity_11, standard_evaluation]
  rfl

theorem virtual12_eq_recovered (hdim : 48 = Module.finrank ℝ E) :
    characteristicFunctional Q D 12 11 hdim (Characters.virtual 12) =
      sixCandidateNumber Q D 12 11 hdim DimensionElevenTwelveDensity.density12 := by
  unfold characteristicFunctional
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  rw [characterDensity_12, standard_evaluation]
  rfl

end
end QuaternionicSymmetry.ManifoldTangentCharacterNumber
