import QuaternionicSymmetry.QuaternionicClosedSourceClassInvariance
import QuaternionicSymmetry.ManifoldIntegratedDensityCertificates

/-! Canonical characteristic numbers of the actual corrected source forms.
These use the constructed manifold measure and closed/exact quotient. -/
namespace QuaternionicSymmetry.QuaternionicClosedSourceNumbers
open QuaternionicClosedSourceGenerators QuaternionicClosedSourceClassInvariance
open ManifoldClosedPolynomialComparison ManifoldClosedPolynomialRepresentative
open ManifoldEvenClosedClassMap ManifoldIntegratedDensityCertificates
open ManifoldQuaternionicCanonicalIntegration ManifoldDifferentialForms
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

def sourcePolynomialNumber (t : ℝ) (k : ℕ)
    (hdim : 4*(k+1) = Module.finrank ℝ E) (P : DimensionThirteenFourteenDensity.P) : ℝ :=
  integrateGrade Q k hdim (ManifoldSevenVariableGradedEvaluation.homogeneousClass
    (classGenerators (generators S Q D t)) (k+1) P)

theorem sourcePolynomialNumber_parameter_independent (s t : ℝ) (k : ℕ)
    (hdim : 4*(k+1) = Module.finrank ℝ E) (P : DimensionThirteenFourteenDensity.P) :
    sourcePolynomialNumber S Q D t k hdim P =
      sourcePolynomialNumber S Q D s k hdim P := by
  unfold sourcePolynomialNumber
  rw [classGenerators_eq S Q D s t]

theorem sourcePolynomialNumber_representative (t : ℝ) (k : ℕ)
    (hdim : 4*(k+1) = Module.finrank ℝ E) (P : DimensionThirteenFourteenDensity.P)
    (hP : MvPolynomial.IsWeightedHomogeneous
      ManifoldSevenVariableClosedEvaluation.slotGrade P (k+1)) :
    sourcePolynomialNumber S Q D t k hdim P =
      integral Q ⟨ManifoldDeRhamWedge.castForm (by omega)
        (closedRepresentative (generators S Q D t) P hP).val.val,
        ManifoldDeRhamWedge.chartSmooth_castForm _ _
          (closedRepresentative (generators S Q D t) P hP).val.property⟩ := by
  have hc : ManifoldSevenVariableGradedEvaluation.homogeneousClass
      (classGenerators (generators S Q D t)) (k+1) P =
      classGrade (k+1) (closedRepresentative (generators S Q D t) P hP) := by
    unfold ManifoldSevenVariableGradedEvaluation.homogeneousClass
    rw [class_evaluate_eq_of _ P hP]
    exact DirectSum.component.lof_self _ _ _
  unfold sourcePolynomialNumber
  rw [hc]
  exact integrateClass_representative Q (by omega) _

end
end QuaternionicSymmetry.QuaternionicClosedSourceNumbers
