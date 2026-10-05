import QuaternionicSymmetry.QuaternionicTangentEvenBinomial
import QuaternionicSymmetry.ManifoldQuaternionicSymplecticCurvature
import QuaternionicSymmetry.ManifoldQuaternionicCurvatureProjection

/-! Pointwise tangent trace recurrence for the actual compatible connection.
The global exterior-form version requires the matrix/wedge coefficient bridge. -/
namespace QuaternionicSymmetry.QuaternionicManifoldTangentEvenBinomial
open QuaternionicTangentEvenBinomial
  ManifoldQuaternionicConnection ManifoldQuaternionicSymplecticCurvature
  ManifoldQuaternionicCurvatureProjection ManifoldQuaternionicConnectionSplitting
  QuaternionicLieAlgebraProjection ManifoldQuaternionicAdjointConnection
  VectorBundleFrameTransitions.QuaternionicFrameReduction
  LocalEndomorphismTrace
open scoped ContDiff Manifold
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

set_option maxHeartbeats 800000 in
theorem tangentCurvature_even_trace_binomial (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) (j : ℕ) :
    let T := Q.reduction.Q (achart E p)
    let A := D.curvature Q p y u v
    let P := symplecticProjection T A
    let a := axialProjection (adjointRepresentation T A)
    traceCLM (A ^ (2 * j)) =
      ∑ m ∈ Finset.range (2 * j + 1),
        (if Even (2 * j - m) then
          (-(∑ i : Fin 3, a i * a i)) ^ ((2 * j - m) / 2) *
            traceCLM (P ^ m)
         else 0) * (Nat.choose (2 * j) m : ℝ) := by
  let T := Q.reduction.Q (achart E p)
  let A := D.curvature Q p y u v
  let P := symplecticProjection T A
  let a := axialProjection (adjointRepresentation T A)
  have hP : ∀ b, P * synth T b = synth T b * P := by
    intro b
    simpa only [P, T, A, ← symplecticCurvature_eq_projection Q D p y u v hy] using
      symplecticCurvature_commutes Q D p y u v hy b
  have hsum : P + synth T a = A := projection_sum T A
  have h := trace_binomial_even T a P hP j
  rw [hsum] at h
  exact h

end
end QuaternionicSymmetry.QuaternionicManifoldTangentEvenBinomial
