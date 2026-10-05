import QuaternionicSymmetry.ManifoldIntegratedDensityCertificates
import QuaternionicSymmetry.ManifoldRecoveredElevenTwelveWeights

/-!
The exact dimension-11–14 certificates as canonical de Rham integrals of
the normalized, triangularly recovered analytic characteristic candidates.
The top-grade purity theorems ensure that component extraction discards no
part of each density. Identification of these numbers with Salamon's
twistor/Dirac index remains a geometric and analytic obligation.
-/

namespace QuaternionicSymmetry.ManifoldIntegratedRecoveredCertificates

open QuaternionicSymmetry.ManifoldEvenCharacteristicAlgebra
  QuaternionicSymmetry.ManifoldIntegratedDensityCertificates
  QuaternionicSymmetry.ManifoldRecoveredCharacteristicCertificates
  QuaternionicSymmetry.ManifoldRecoveredElevenTwelveWeights
  QuaternionicSymmetry.ManifoldQuaternionicMetric
  QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped Manifold ContDiff Topology

noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]

variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q) (qdim : ℕ)

/-- Canonical integration of the recovered six-variable top component. -/
def sixCandidateNumber (k : ℕ) (hdim : 4 * (k + 1) = Module.finrank ℝ E)
    (p : QuaternionicSymmetry.DimensionElevenTwelveDensity.P) : ℝ :=
  integrateGrade Q k hdim
    (DirectSum.component ℝ ℕ (Grade (E := E) (M := M)) (k + 1)
      (evaluateSix Q D qdim p))

/-- Canonical integration of the recovered seven-variable top component. -/
def sevenCandidateNumber (k : ℕ) (hdim : 4 * (k + 1) = Module.finrank ℝ E)
    (p : QuaternionicSymmetry.DimensionThirteenFourteenDensity.P) : ℝ :=
  integrateGrade Q k hdim
    (DirectSum.component ℝ ℕ (Grade (E := E) (M := M)) (k + 1)
      (evaluateSeven Q D qdim p))

theorem sixCandidateNumber_connection_independent
    (D' : CompatibleTangentConnection Q) (k : ℕ)
    (hdim : 4 * (k + 1) = Module.finrank ℝ E)
    (p : QuaternionicSymmetry.DimensionElevenTwelveDensity.P) :
    sixCandidateNumber Q D' qdim k hdim p =
      sixCandidateNumber Q D qdim k hdim p := by
  unfold sixCandidateNumber
  rw [evaluateSix_connection_independent Q D qdim D' p]

theorem sevenCandidateNumber_connection_independent
    (D' : CompatibleTangentConnection Q) (k : ℕ)
    (hdim : 4 * (k + 1) = Module.finrank ℝ E)
    (p : QuaternionicSymmetry.DimensionThirteenFourteenDensity.P) :
    sevenCandidateNumber Q D' qdim k hdim p =
      sevenCandidateNumber Q D qdim k hdim p := by
  unfold sevenCandidateNumber
  rw [evaluateSeven_connection_independent Q D qdim D' p]

theorem density11_integrated (hdim : 44 = Module.finrank ℝ E) :
    sixCandidateNumber Q D 11 10 hdim
        QuaternionicSymmetry.DimensionElevenTwelveDensity.density11 =
      sixCandidateNumber Q D 11 10 hdim
        QuaternionicSymmetry.DimensionElevenTwelveDensity.printed11 := by
  unfold sixCandidateNumber
  rw [ManifoldRecoveredCharacteristicCertificates.density11_printed Q D 11]

theorem density12_integrated (hdim : 48 = Module.finrank ℝ E) :
    sixCandidateNumber Q D 12 11 hdim
        QuaternionicSymmetry.DimensionElevenTwelveDensity.density12 =
      sixCandidateNumber Q D 12 11 hdim
        QuaternionicSymmetry.DimensionElevenTwelveDensity.printed12 := by
  unfold sixCandidateNumber
  rw [ManifoldRecoveredCharacteristicCertificates.density12_printed Q D 12]

theorem density13_integrated (hdim : 52 = Module.finrank ℝ E) :
    sevenCandidateNumber Q D 13 12 hdim
        QuaternionicSymmetry.DimensionThirteenFourteenDensity.density13 =
      sevenCandidateNumber Q D 13 12 hdim
        QuaternionicSymmetry.DimensionThirteenFourteenDensity.printed13 := by
  unfold sevenCandidateNumber
  rw [ManifoldRecoveredCharacteristicCertificates.density13_printed Q D 13]

theorem density14_integrated (hdim : 56 = Module.finrank ℝ E) :
    sevenCandidateNumber Q D 14 13 hdim
        QuaternionicSymmetry.DimensionThirteenFourteenDensity.density14 =
      sevenCandidateNumber Q D 14 13 hdim
        QuaternionicSymmetry.DimensionThirteenFourteenDensity.printed14 := by
  unfold sevenCandidateNumber
  rw [ManifoldRecoveredCharacteristicCertificates.density14_printed Q D 14]

theorem density13_witness_integrated (hdim : 52 = Module.finrank ℝ E) :
    sevenCandidateNumber Q D 13 12 hdim
        QuaternionicSymmetry.DimensionThirteenFourteenDensity.density13 =
      sevenCandidateNumber Q D 13 12 hdim
        QuaternionicSymmetry.H2WitnessThirteen.witness := by
  unfold sevenCandidateNumber
  rw [ManifoldRecoveredCharacteristicCertificates.density13_witness Q D 13]

theorem density14_witness_integrated (hdim : 56 = Module.finrank ℝ E) :
    sevenCandidateNumber Q D 14 13 hdim
        QuaternionicSymmetry.DimensionThirteenFourteenDensity.density14 =
      sevenCandidateNumber Q D 14 13 hdim
        QuaternionicSymmetry.H2WitnessFourteen.witness := by
  unfold sevenCandidateNumber
  rw [ManifoldRecoveredCharacteristicCertificates.density14_witness Q D 14]

end
end QuaternionicSymmetry.ManifoldIntegratedRecoveredCertificates
