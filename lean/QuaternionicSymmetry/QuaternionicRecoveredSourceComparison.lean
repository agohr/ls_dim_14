import QuaternionicSymmetry.QuaternionicStandardSourceNormalizedValue
import QuaternionicSymmetry.QuaternionicRecoveredFormActualValue
import QuaternionicSymmetry.QuaternionicRecoveredNumberAssembly
import QuaternionicSymmetry.QuaternionicStructureIsometryTransport

/-! The genuine standard source forms at zero correction equal the recovered
closed tangent-root forms through weight six. Their classes agree at every
correction parameter; consequently so do all polynomial characteristic numbers.
No curvature decomposition or literature premise is required here. -/
namespace QuaternionicSymmetry.QuaternionicRecoveredSourceComparison
open QuaternionicStandardSourceNormalizedValue QuaternionicRecoveredFormActualValue
open QuaternionicRecoveredComparisonAssembly QuaternionicRecoveredNumberAssembly
open QuaternionicStructureIsometryTransport QuaternionicActualSpCurvatureCoordinates
open QuaternionicClosedSourceGenerators QuaternionicClosedSourceNumbers
open ManifoldClosedRecoveredClassComparison ManifoldClosedPolynomialComparison
open ManifoldEvenClosedClassMap ManifoldIntegratedRecoveredCertificates
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem sourceGrade_zero_eq_recovered (k : ℕ) (hk : k < 6) :
    sourceGrade S Q D 0 k =
      recoveredForm Q D S.quaternionicDimension ⟨k+1, by omega⟩ := by
  apply sourceGrade_eq_recovered_of_values S Q D k hk
  intro x
  rw [sourceGrade_zero_normalized S Q D x _ (mem_extChartAt_target x) k]
  rw [quaternionicDimension_eq S (chartStructure Q x)]
  exact (recoveredForm_actual_value Q D x _ (mem_extChartAt_target x)
    ⟨k+1, by omega⟩).symm

theorem sourceGrade_class_eq_candidate (k : ℕ) (hk : k < 6) (t : ℝ) :
    classGrade (k+1) (sourceGrade S Q D t k) =
      ManifoldTangentTraceRootCandidates.candidatePowerClass Q D S.quaternionicDimension
        ⟨k+1, by omega⟩ :=
  sourceGrade_class_eq_recovered S Q D k hk t
    (sourceGrade_zero_eq_recovered S Q D k hk)

theorem classGenerators_eq_candidate (t : ℝ) :
    classGenerators (generators S Q D t) =
      ManifoldTangentTraceRootCandidates.candidateGenerators Q D S.quaternionicDimension :=
  classGenerators_eq_candidate_of_forms S Q D (sourceGrade_zero_eq_recovered S Q D) t

variable [MeasurableSpace E] [BorelSpace E]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]

theorem sourceNumber_eq_sevenCandidate (t : ℝ) (k : ℕ)
    (hdim : 4*(k+1) = Module.finrank ℝ E)
    (P : DimensionThirteenFourteenDensity.P) :
    sourcePolynomialNumber S Q D t k hdim P =
      sevenCandidateNumber Q D S.quaternionicDimension k hdim P :=
  sourceNumber_eq_sevenCandidate_of_forms S Q D
    (sourceGrade_zero_eq_recovered S Q D) t k hdim P

theorem sourceNumber_eq_sixCandidate (t : ℝ) (k : ℕ)
    (hdim : 4*(k+1) = Module.finrank ℝ E)
    (P : DimensionElevenTwelveDensity.P) :
    sourcePolynomialNumber S Q D t k hdim (DimensionThirteenFourteenDensity.lift P) =
      sixCandidateNumber Q D S.quaternionicDimension k hdim P :=
  sourceNumber_eq_sixCandidate_of_forms S Q D
    (sourceGrade_zero_eq_recovered S Q D) t k hdim P

end
end QuaternionicSymmetry.QuaternionicRecoveredSourceComparison
