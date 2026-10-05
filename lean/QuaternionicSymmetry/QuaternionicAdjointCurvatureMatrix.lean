import QuaternionicSymmetry.QuaternionicAdjointMatrixCoordinates
import QuaternionicSymmetry.ManifoldQuaternionicSymplecticCurvature
import QuaternionicSymmetry.ManifoldQuaternionicCurvatureProjection
import QuaternionicSymmetry.ManifoldQuaternionicAdjointCurvature

/-! Exact real matrix coordinates of actual induced rank-three curvature. -/
namespace QuaternionicSymmetry.QuaternionicAdjointCurvatureMatrix
open QuaternionicAdjointMatrixCoordinates QuaternionicUniversalEvenTrace
  QuaternionicLieAlgebraProjection ManifoldQuaternionicAdjointConnection
  ManifoldQuaternionicAdjointCurvature
  ManifoldQuaternionicSymplecticCurvature
  VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped ContDiff Manifold
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

theorem adjointRepresentation_matrix_of_commutes (S : QuaternionicStructure E)
    (A : E →L[ℝ] E)
    (hsp : ∀ a, symplecticProjection S A * synth S a =
      synth S a * symplecticProjection S A) :
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin 3)) (Pi.basisFun ℝ (Fin 3))
      (adjointRepresentation S A).toLinearMap =
        adjointMatrix (axialProjection (adjointRepresentation S A)) := by
  have hz : adjointRepresentation S (symplecticProjection S A) = 0 :=
    adjointRepresentation_eq_zero_of_commutes S _ hsp
  have hs := congrArg (adjointRepresentation S) (projection_sum S A)
  rw [map_add, hz, zero_add] at hs
  calc
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin 3)) (Pi.basisFun ℝ (Fin 3))
        (adjointRepresentation S A).toLinearMap =
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin 3)) (Pi.basisFun ℝ (Fin 3))
        (adjointRepresentation S (scalarProjection S A)).toLinearMap := by rw [hs]
    _ = adjointMatrix (axialProjection (adjointRepresentation S A)) := by
      change LinearMap.toMatrix' (adjointRepresentation S
        (synth S (axialProjection (adjointRepresentation S A)))).toLinearMap = _
      rw [adjointRepresentation_synth_matrix]
      simp

variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem inducedCurvature_matrix (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin 3)) (Pi.basisFun ℝ (Fin 3))
      (inducedCurvature Q D p y u v).toLinearMap =
        adjointMatrix (axialProjection (adjointRepresentation
          (Q.reduction.Q (achart E p)) (D.curvature Q p y u v))) := by
  rw [inducedCurvature_eq_adjoint Q D p y u v hy]
  exact adjointRepresentation_matrix_of_commutes _ _
    (by
      intro a
      rw [← ManifoldQuaternionicCurvatureProjection.symplecticCurvature_eq_projection
        Q D p y u v hy]
      exact symplecticCurvature_commutes Q D p y u v hy a)

end
end QuaternionicSymmetry.QuaternionicAdjointCurvatureMatrix
