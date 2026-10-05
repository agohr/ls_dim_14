import QuaternionicSymmetry.ManifoldClosedRecoveredPointwise
import QuaternionicSymmetry.ManifoldClosedGradeReflection
import QuaternionicSymmetry.QuaternionicClosedSourceClassInvariance

/-! Internal assembly of a pointwise source/recovery identity into equality
of the actual global forms and parameter-independent generator classes. -/
namespace QuaternionicSymmetry.QuaternionicRecoveredComparisonAssembly
open ManifoldClosedRecoveredClassComparison ManifoldClosedGradeReflection
open ManifoldEvenClosedEvaluation ManifoldEvenClosedClassMap
open QuaternionicClosedSourceGenerators QuaternionicClosedSourceClassInvariance
open ManifoldClosedPolynomialComparison
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem sourceGrade_eq_recovered_of_values (k : ℕ) (hk : k < 6)
    (h : ∀ x : M,
      gradeValue x (extChartAt 𝓘(ℝ,E) x x) (ContinuousLinearMap.id ℝ E) (k+1)
        (sourceGrade S Q D 0 k) =
      gradeValue x (extChartAt 𝓘(ℝ,E) x x) (ContinuousLinearMap.id ℝ E) (k+1)
        (recoveredForm Q D S.quaternionicDimension ⟨k+1, by omega⟩)) :
    sourceGrade S Q D 0 k = recoveredForm Q D S.quaternionicDimension ⟨k+1, by omega⟩ :=
  eq_of_center_values k _ _ (fun _ => ContinuousLinearEquiv.refl ℝ E) h

theorem sourceGrade_class_eq_recovered (k : ℕ) (hk : k < 6) (t : ℝ)
    (h : sourceGrade S Q D 0 k =
      recoveredForm Q D S.quaternionicDimension ⟨k+1, by omega⟩) :
    classGrade (k+1) (sourceGrade S Q D t k) =
      ManifoldTangentTraceRootCandidates.candidatePowerClass Q D S.quaternionicDimension
        ⟨k+1, by omega⟩ := by
  rw [sourceGrade_class_eq S Q D 0 t k, h]
  exact recoveredForm_class Q D S.quaternionicDimension ⟨k+1, by omega⟩

theorem classGenerators_eq_candidate_of_forms
    (h : ∀ (k : ℕ) (hk : k < 6), sourceGrade S Q D 0 k =
      recoveredForm Q D S.quaternionicDimension ⟨k+1, by omega⟩) (t : ℝ) :
    classGenerators (generators S Q D t) =
      ManifoldTangentTraceRootCandidates.candidateGenerators Q D S.quaternionicDimension := by
  unfold classGenerators generators ManifoldTangentTraceRootCandidates.candidateGenerators
  congr 1
  · exact ManifoldClosedTangentGenerators.quarterForm_class Q D
  · exact sourceGrade_class_eq_recovered S Q D 0 (by omega) t (h 0 (by omega))
  · exact sourceGrade_class_eq_recovered S Q D 1 (by omega) t (h 1 (by omega))
  · exact sourceGrade_class_eq_recovered S Q D 2 (by omega) t (h 2 (by omega))
  · exact sourceGrade_class_eq_recovered S Q D 3 (by omega) t (h 3 (by omega))
  · exact sourceGrade_class_eq_recovered S Q D 4 (by omega) t (h 4 (by omega))
  · exact sourceGrade_class_eq_recovered S Q D 5 (by omega) t (h 5 (by omega))

end
end QuaternionicSymmetry.QuaternionicRecoveredComparisonAssembly
