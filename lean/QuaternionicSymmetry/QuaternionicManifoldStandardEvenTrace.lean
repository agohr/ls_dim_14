import QuaternionicSymmetry.QuaternionicScalarLineTracePowers
import QuaternionicSymmetry.QuaternionicManifoldStandardCurvatureRepresentation
import QuaternionicSymmetry.QuaternionicFixedModelTracePowers
import QuaternionicSymmetry.QuaternionicManifoldStandardTraceSquare

/-! Numerical even trace powers of actual projective-standard curvature at a
chart point. These identities precede the exterior-power polarization needed
for global Chern--Weil forms. -/
namespace QuaternionicSymmetry.QuaternionicManifoldStandardEvenTrace
open QuaternionicScalarLineTracePowers
  QuaternionicManifoldStandardCurvatureRepresentation
  QuaternionicManifoldProjectiveStandardConnection
  QuaternionicManifoldModelProjection
  QuaternionicProjectiveStandardLie
  QuaternionicLieAlgebraProjection
  ManifoldQuaternionicConnection
  ManifoldQuaternionicAdjointConnection
  ManifoldQuaternionicCurvatureProjection
  ManifoldQuaternionicSymplecticCurvature
  ManifoldQuaternionicAdjointCurvature
  ManifoldQuaternionicConnectionSplitting
  QuaternionicFixedModelTracePowers
  LocalEndomorphismTrace
open scoped ContDiff Manifold Quaternion
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

set_option maxHeartbeats 800000 in
theorem standardCurvature_even_trace (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) (j : ℕ) :
    traceCLM ((LocalConnection.curvature
      (standardConnection S Q D p) y u v) ^ (2 * j)) =
      traceCLM ((symplecticProjection S
        (fixedTangentConjugation S Q p (D.curvature Q p y u v))) ^ (2 * j)) +
      4 * (-(∑ i : Fin 3,
        (axialProjection (adjointRepresentation S
          (fixedTangentConjugation S Q p (D.curvature Q p y u v)))) i *
        (axialProjection (adjointRepresentation S
          (fixedTangentConjugation S Q p (D.curvature Q p y u v)))) i)) ^ j := by
  rw [standardCurvature_eq_representation S Q D p y u v hy]
  exact standardLie_even_trace S _ j

set_option maxHeartbeats 800000 in
theorem standardCurvature_even_trace_rankThree (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) (j : ℕ) (hj : 0 < j) :
    (4 : ℝ) ^ j * traceCLM ((LocalConnection.curvature
      (standardConnection S Q D p) y u v) ^ (2 * j)) =
      (4 : ℝ) ^ j * traceCLM ((LocalConnection.curvature
        (symplecticConnection Q D p) y u v) ^ (2 * j)) +
      2 * traceCLM ((inducedCurvature Q D p y u v) ^ (2 * j)) := by
  rw [standardCurvature_eq_representation S Q D p y u v hy]
  let T := Q.reduction.Q (achart E p)
  let A := D.curvature Q p y u v
  have hA : ∀ c, symplecticProjection T A *
      VectorBundleFrameTransitions.QuaternionicFrameReduction.synth T c =
        VectorBundleFrameTransitions.QuaternionicFrameReduction.synth T c *
          symplecticProjection T A := by
    intro c
    rw [← symplecticCurvature_eq_projection Q D p y u v hy]
    exact symplecticCurvature_commutes Q D p y u v hy c
  have ht := standardLie_fixed_even_trace S T A hA j hj
  rw [← symplecticCurvature_eq_projection Q D p y u v hy] at ht
  rw [inducedCurvature_eq_adjoint Q D p y u v hy]
  exact ht

end
end QuaternionicSymmetry.QuaternionicManifoldStandardEvenTrace
