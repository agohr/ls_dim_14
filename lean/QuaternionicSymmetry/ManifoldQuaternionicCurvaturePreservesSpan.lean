import QuaternionicSymmetry.ManifoldQuaternionicSymplecticCurvature
import QuaternionicSymmetry.ManifoldQuaternionicAdjointCurvature

/-! The curvature of the actual tangent connection preserves the quaternionic
three-plane, and its induced rank-three curvature is its commutator there. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicCurvaturePreservesSpan

open ManifoldQuaternionicConnectionSplitting ManifoldQuaternionicConnection
  ManifoldQuaternionicAdjointConnection ManifoldQuaternionicAdjointCurvature
  ManifoldQuaternionicCurvatureProjection ManifoldQuaternionicSymplecticCurvature
  QuaternionicLieAlgebraProjection ManifoldQuaternionicRankThreeOrientation
  VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞)) (D : CompatibleTangentConnection Q)

theorem tangentCurvature_preservesSpan (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    PreservesSpan (Q.reduction.Q (achart E p)) (D.curvature Q p y u v) := by
  let S := Q.reduction.Q (achart E p)
  let R := D.curvature Q p y u v
  have hsp (a : Fin 3 → ℝ) :
      symplecticProjection S R * synth S a = synth S a * symplecticProjection S R := by
    rw [← symplecticCurvature_eq_projection Q D p y u v hy]
    exact symplecticCurvature_commutes Q D p y u v hy a
  intro T hT
  rw [← synth_coeff_of_mem S T hT]
  change R * synth S (coeff S T) - synth S (coeff S T) * R ∈ quaternionicSpan S
  have he : R * synth S (coeff S T) - synth S (coeff S T) * R =
      scalarProjection S R * synth S (coeff S T) - synth S (coeff S T) * scalarProjection S R := by
    calc
      _ = (symplecticProjection S R + scalarProjection S R) * synth S (coeff S T) -
          synth S (coeff S T) * (symplecticProjection S R + scalarProjection S R) := by
            rw [projection_sum]
      _ = _ := by rw [add_mul, mul_add, hsp]; abel
  rw [he]
  change synth S _ * synth S (coeff S T) - synth S (coeff S T) * synth S _ ∈ quaternionicSpan S
  rw [synth_commutator_cross]
  exact (quaternionicSpan S).smul_mem _ (synth_mem S _)

theorem synth_inducedCurvature (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) (a : Fin 3 → ℝ) :
    synth (Q.reduction.Q (achart E p)) (inducedCurvature Q D p y u v a) =
      D.curvature Q p y u v * synth (Q.reduction.Q (achart E p)) a -
        synth (Q.reduction.Q (achart E p)) a * D.curvature Q p y u v := by
  rw [inducedCurvature_eq_adjoint Q D p y u v hy]
  exact synth_adjointRepresentation _ _ (tangentCurvature_preservesSpan Q D p y u v hy) a

end
end QuaternionicSymmetry.ManifoldQuaternionicCurvaturePreservesSpan
