import QuaternionicSymmetry.ManifoldQuaternionicCanonicalIntegration
import QuaternionicSymmetry.ManifoldSixVariableScaledDensity
import QuaternionicSymmetry.ManifoldSevenVariableCurvatureEvaluation

/-! The checked polynomial certificates as actual de Rham integrals.
These are raw/scaled curvature substitutions; their identification with the
paper's standard-bundle roots and the geometric index remains separate. -/
namespace QuaternionicSymmetry.ManifoldIntegratedDensityCertificates

open ManifoldEvenCharacteristicAlgebra ManifoldQuaternionicMetric
  ManifoldQuaternionicConnection ManifoldQuaternionicCanonicalIntegration
open scoped Manifold ContDiff Topology
noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

def integrateGrade (k : ℕ) (hdim : 4 * (k + 1) = Module.finrank ℝ E) :
    Grade (E := E) (M := M) (k + 1) →ₗ[ℝ] ℝ :=
  integrateClass Q (n := 4 * k + 3) (by omega)

def sixVariableNumber (D : CompatibleTangentConnection Q) (s : Fin 6 → ℝ)
    (k : ℕ) (hdim : 4 * (k + 1) = Module.finrank ℝ E)
    (P : DimensionElevenTwelveDensity.P) : ℝ :=
  integrateGrade Q k hdim (ManifoldSixVariableScaledDensity.homogeneousScaledClass Q D s (k + 1) P)

def sevenVariableNumber (D : CompatibleTangentConnection Q) (s : Fin 7 → ℝ)
    (k : ℕ) (hdim : 4 * (k + 1) = Module.finrank ℝ E)
    (P : DimensionThirteenFourteenDensity.P) : ℝ :=
  integrateGrade Q k hdim
    (ManifoldSevenVariableCurvatureEvaluation.homogeneousScaledClass Q D s (k + 1) P)

theorem sixVariableNumber_connection_independent
    (D D' : CompatibleTangentConnection Q) (s : Fin 6 → ℝ)
    (k : ℕ) (hdim : 4 * (k + 1) = Module.finrank ℝ E)
    (P : DimensionElevenTwelveDensity.P) :
    sixVariableNumber Q D' s k hdim P = sixVariableNumber Q D s k hdim P := by
  unfold sixVariableNumber
  rw [ManifoldSixVariableScaledDensity.homogeneousScaledClass_connection_independent Q D s D']

theorem sevenVariableNumber_connection_independent
    (D D' : CompatibleTangentConnection Q) (s : Fin 7 → ℝ)
    (k : ℕ) (hdim : 4 * (k + 1) = Module.finrank ℝ E)
    (P : DimensionThirteenFourteenDensity.P) :
    sevenVariableNumber Q D' s k hdim P = sevenVariableNumber Q D s k hdim P := by
  unfold sevenVariableNumber
  rw [ManifoldSevenVariableCurvatureEvaluation.homogeneousScaledClass_connection_independent Q D s D']

theorem density11_integrated (D : CompatibleTangentConnection Q) (s : Fin 6 → ℝ)
    (hdim : 44 = Module.finrank ℝ E) :
    sixVariableNumber Q D s 10 hdim DimensionElevenTwelveDensity.density11 =
      sixVariableNumber Q D s 10 hdim DimensionElevenTwelveDensity.printed11 := by
  unfold sixVariableNumber
  rw [ManifoldSixVariableScaledDensity.density11_printed_class Q D s]

theorem density12_integrated (D : CompatibleTangentConnection Q) (s : Fin 6 → ℝ)
    (hdim : 48 = Module.finrank ℝ E) :
    sixVariableNumber Q D s 11 hdim DimensionElevenTwelveDensity.density12 =
      sixVariableNumber Q D s 11 hdim DimensionElevenTwelveDensity.printed12 := by
  unfold sixVariableNumber
  rw [ManifoldSixVariableScaledDensity.density12_printed_class Q D s]

theorem density13_integrated (D : CompatibleTangentConnection Q) (s : Fin 7 → ℝ)
    (hdim : 52 = Module.finrank ℝ E) :
    sevenVariableNumber Q D s 12 hdim DimensionThirteenFourteenDensity.density13 =
      sevenVariableNumber Q D s 12 hdim DimensionThirteenFourteenDensity.printed13 := by
  unfold sevenVariableNumber
  rw [ManifoldSevenVariableCurvatureEvaluation.density13_printed_class Q D s]

theorem density14_integrated (D : CompatibleTangentConnection Q) (s : Fin 7 → ℝ)
    (hdim : 56 = Module.finrank ℝ E) :
    sevenVariableNumber Q D s 13 hdim DimensionThirteenFourteenDensity.density14 =
      sevenVariableNumber Q D s 13 hdim DimensionThirteenFourteenDensity.printed14 := by
  unfold sevenVariableNumber
  rw [ManifoldSevenVariableCurvatureEvaluation.density14_printed_class Q D s]

end
end QuaternionicSymmetry.ManifoldIntegratedDensityCertificates
