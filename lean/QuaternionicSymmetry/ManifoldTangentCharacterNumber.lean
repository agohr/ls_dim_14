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

-- Keep the polynomial and character abstract while passing through integration.
-- Specializing them before this bridge makes kernel reduction expand the
-- dimension-specific polynomial inside the concrete de Rham algebra.
private theorem characteristicFunctional_eq_of_density (qdim k : ℕ)
    (hdim : 4*(k+1) = Module.finrank ℝ E)
    (p : LaurentPolynomial ℚ) (P : DimensionElevenTwelveDensity.P)
    (h : characterDensity (k+1) (quarterUTotal Q D)
      (normalizedTangentHalfTrace Q D qdim) p =
        MvPolynomial.aeval (standardValues qdim (quarterUTotal Q D)
          (normalizedTangentHalfTrace Q D qdim)) P) :
    characteristicFunctional Q D qdim k hdim p =
      sixCandidateNumber Q D qdim k hdim P := by
  exact congrArg
    (fun x : Total (E := E) (M := M) => integrateGrade Q k hdim
      (DirectSum.component ℝ ℕ (Grade (E := E) (M := M)) (k+1) x))
    (h.trans (standard_evaluation Q D qdim P))

theorem virtual11_eq_recovered (hdim : 44 = Module.finrank ℝ E) :
    characteristicFunctional Q D 11 10 hdim (Characters.virtual 11) =
      sixCandidateNumber Q D 11 10 hdim DimensionElevenTwelveDensity.density11 := by
  exact characteristicFunctional_eq_of_density Q D 11 10 hdim _ _
    (characterDensity_11 (quarterUTotal Q D) (normalizedTangentHalfTrace Q D 11))

theorem virtual12_eq_recovered (hdim : 48 = Module.finrank ℝ E) :
    characteristicFunctional Q D 12 11 hdim (Characters.virtual 12) =
      sixCandidateNumber Q D 12 11 hdim DimensionElevenTwelveDensity.density12 := by
  exact characteristicFunctional_eq_of_density Q D 12 11 hdim _ _
    (characterDensity_12 (quarterUTotal Q D) (normalizedTangentHalfTrace Q D 12))

end
end QuaternionicSymmetry.ManifoldTangentCharacterNumber
