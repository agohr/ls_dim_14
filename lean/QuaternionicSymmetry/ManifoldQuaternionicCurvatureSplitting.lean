import QuaternionicSymmetry.ManifoldQuaternionicConnectionSplitting
import QuaternionicSymmetry.LocalConnectionCommutingSplit

/-! The curvature of a compatible tangent connection is the sum of the
curvatures of its actual quaternion-linear and scalar connection parts. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicCurvatureSplitting

open ManifoldQuaternionicConnectionSplitting ManifoldQuaternionicConnection
  QuaternionicInfinitesimalSplitting ManifoldQuaternionicFourFormConnection
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞)) (D : CompatibleTangentConnection Q)

theorem connection_parts_commute (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    symplecticConnection Q D p y u * scalarConnection Q D p y v =
      scalarConnection Q D p y v * symplecticConnection Q D p y u := by
  rw [scalarConnection_apply]
  exact symplecticConnection_commutes Q D p y u hy
    (scalarCoefficients (inducedMatrix Q D p y v))

theorem curvature_split (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    D.curvature Q p y =
      LocalConnection.curvature (symplecticConnection Q D p) y +
        LocalConnection.curvature (scalarConnection Q D p) y := by
  have hs : DifferentiableAt ℝ (symplecticConnection Q D p) y :=
    ((symplecticConnection_smooth Q D p).differentiableOn (by norm_num)).differentiableAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).mem_nhds hy)
  have ht : DifferentiableAt ℝ (scalarConnection Q D p) y :=
    ((scalarConnection_smooth Q D p).differentiableOn (by norm_num)).differentiableAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).mem_nhds hy)
  have heq : D.form p = symplecticConnection Q D p + scalarConnection Q D p := by
    funext z
    exact (connection_sum Q D p z).symm
  change LocalConnection.curvature (D.form p) y = _
  rw [heq]
  exact LocalConnection.curvature_add_of_commuting _ _ y hs ht
    (fun u v => connection_parts_commute Q D p y u v hy)

end
end QuaternionicSymmetry.ManifoldQuaternionicCurvatureSplitting
