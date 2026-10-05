import QuaternionicSymmetry.ManifoldTangentCharacterNumber
import QuaternionicSymmetry.TangentAhatLowerDensities

/-! Canonical integration of the actual tangent A-hat/character calculation
in dimensions two through ten, and independence of the compatible connection. -/
namespace QuaternionicSymmetry.ManifoldTangentCharacterNumber
open ManifoldEvenCharacteristicAlgebra ManifoldTangentTraceRootCandidates
open ManifoldIntegratedDensityCertificates ManifoldIntegratedRecoveredCertificates
open ManifoldRecoveredCharacteristicCertificates TangentAhatLowerDensities
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

local instance : Algebra ℚ (Total (E := E) (M := M)) :=
  ManifoldTangentTraceRootCandidates.rationalAlgebra

theorem characteristicFunctional_connection_independent
    (D' : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    (qdim k : ℕ) (hdim : 4*(k+1) = Module.finrank ℝ E) :
    characteristicFunctional Q D' qdim k hdim =
      characteristicFunctional Q D qdim k hdim := by
  unfold characteristicFunctional
  rw [quarterUTotal_connection_independent Q D D',
    normalizedTangentHalfTrace_connection_independent Q D qdim D']

theorem virtual2_eq_recovered (hdim : 8 = Module.finrank ℝ E) :
    characteristicFunctional Q D 2 1 hdim (Characters.virtual 2) =
      sixCandidateNumber Q D 2 1 hdim
        (DimensionElevenTwelveDensity.old AlgebraCertificates.K₂) := by
  unfold characteristicFunctional
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  rw [characterDensity_2, standard_evaluation]
  rfl

theorem virtual3_eq_recovered (hdim : 12 = Module.finrank ℝ E) :
    characteristicFunctional Q D 3 2 hdim (Characters.virtual 3) =
      sixCandidateNumber Q D 3 2 hdim
        (DimensionElevenTwelveDensity.old AlgebraCertificates.K₃) := by
  unfold characteristicFunctional
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  rw [characterDensity_3, standard_evaluation]
  rfl

theorem virtual4_eq_recovered (hdim : 16 = Module.finrank ℝ E) :
    characteristicFunctional Q D 4 3 hdim (Characters.virtual 4) =
      sixCandidateNumber Q D 4 3 hdim
        (DimensionElevenTwelveDensity.old AlgebraCertificates.K₄) := by
  unfold characteristicFunctional
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  rw [characterDensity_4, standard_evaluation]
  rfl

theorem virtual5_eq_recovered (hdim : 20 = Module.finrank ℝ E) :
    characteristicFunctional Q D 5 4 hdim (Characters.virtual 5) =
      sixCandidateNumber Q D 5 4 hdim
        (DimensionElevenTwelveDensity.old AlgebraCertificates.K₅) := by
  unfold characteristicFunctional
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  rw [characterDensity_5, standard_evaluation]
  rfl

theorem virtual6_eq_recovered (hdim : 24 = Module.finrank ℝ E) :
    characteristicFunctional Q D 6 5 hdim (Characters.virtual 6) =
      sixCandidateNumber Q D 6 5 hdim
        (DimensionElevenTwelveDensity.old AlgebraCertificates.K₆) := by
  unfold characteristicFunctional
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  rw [characterDensity_6, standard_evaluation]
  rfl

theorem virtual7_eq_recovered (hdim : 28 = Module.finrank ℝ E) :
    characteristicFunctional Q D 7 6 hdim (Characters.virtual 7) =
      sixCandidateNumber Q D 7 6 hdim
        (DimensionElevenTwelveDensity.old AlgebraCertificates.K₇) := by
  unfold characteristicFunctional
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  rw [characterDensity_7, standard_evaluation]
  rfl

theorem virtual8_eq_recovered (hdim : 32 = Module.finrank ℝ E) :
    characteristicFunctional Q D 8 7 hdim (Characters.virtual 8) =
      sixCandidateNumber Q D 8 7 hdim
        (DimensionElevenTwelveDensity.old AlgebraCertificates.K₈) := by
  unfold characteristicFunctional
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  rw [characterDensity_8, standard_evaluation]
  rfl

theorem virtual9_eq_recovered (hdim : 36 = Module.finrank ℝ E) :
    characteristicFunctional Q D 9 8 hdim (Characters.virtual 9) =
      sixCandidateNumber Q D 9 8 hdim
        (DimensionElevenTwelveDensity.old AlgebraCertificates.K₉) := by
  unfold characteristicFunctional
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  rw [characterDensity_9, standard_evaluation]
  rfl

theorem virtual10_eq_recovered (hdim : 40 = Module.finrank ℝ E) :
    characteristicFunctional Q D 10 9 hdim (Characters.virtual 10) =
      sixCandidateNumber Q D 10 9 hdim
        (DimensionElevenTwelveDensity.old AlgebraCertificates.K₁₀) := by
  unfold characteristicFunctional
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  rw [characterDensity_10, standard_evaluation]
  rfl

end
end QuaternionicSymmetry.ManifoldTangentCharacterNumber
