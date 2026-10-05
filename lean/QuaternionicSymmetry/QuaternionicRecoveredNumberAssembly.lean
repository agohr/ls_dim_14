import QuaternionicSymmetry.QuaternionicRecoveredComparisonAssembly
import QuaternionicSymmetry.QuaternionicClosedSourceNumbers
import QuaternionicSymmetry.ManifoldIntegratedRecoveredCertificates

/-! Once the actual source/recovered forms agree, canonical integration
transports every polynomial certificate to the recovered characteristic numbers. -/
namespace QuaternionicSymmetry.QuaternionicRecoveredNumberAssembly
open QuaternionicClosedSourceGenerators QuaternionicClosedSourceNumbers
open ManifoldClosedRecoveredClassComparison QuaternionicRecoveredComparisonAssembly
open ManifoldIntegratedRecoveredCertificates
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem sourceNumber_eq_sevenCandidate_of_forms
    (h : ∀ (j : ℕ) (hj : j < 6), sourceGrade S Q D 0 j =
      recoveredForm Q D S.quaternionicDimension ⟨j+1, by omega⟩)
    (t : ℝ) (k : ℕ) (hdim : 4*(k+1) = Module.finrank ℝ E)
    (P : DimensionThirteenFourteenDensity.P) :
    sourcePolynomialNumber S Q D t k hdim P =
      sevenCandidateNumber Q D S.quaternionicDimension k hdim P := by
  unfold sourcePolynomialNumber
  rw [classGenerators_eq_candidate_of_forms S Q D h t]
  rfl

theorem sourceNumber_eq_sixCandidate_of_forms
    (h : ∀ (j : ℕ) (hj : j < 6), sourceGrade S Q D 0 j =
      recoveredForm Q D S.quaternionicDimension ⟨j+1, by omega⟩)
    (t : ℝ) (k : ℕ) (hdim : 4*(k+1) = Module.finrank ℝ E)
    (P : DimensionElevenTwelveDensity.P) :
    sourcePolynomialNumber S Q D t k hdim (DimensionThirteenFourteenDensity.lift P) =
      sixCandidateNumber Q D S.quaternionicDimension k hdim P := by
  rw [sourceNumber_eq_sevenCandidate_of_forms S Q D h]
  unfold sevenCandidateNumber sixCandidateNumber
  rw [ManifoldRecoveredCharacteristicCertificates.evaluateSeven_lift]

end
end QuaternionicSymmetry.QuaternionicRecoveredNumberAssembly
