import QuaternionicSymmetry.ManifoldTangentCharacterNumber

/-! The full actual A-hat/character characteristic functional is intrinsic to
the de Rham curvature classes of the tangent and rank-three bundles; its
value does not depend on the compatible tangent connection used to represent
those classes. This does not assert an equality with a topological index. -/
namespace QuaternionicSymmetry.ManifoldTangentCharacterConnectionIndependence
open ManifoldTangentCharacterNumber ManifoldTangentTraceRootCandidates
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem characteristicFunctional_connection_independent
    (D' : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    (qdim k : ℕ) (hdim : 4*(k+1) = Module.finrank ℝ E) :
    characteristicFunctional Q D' qdim k hdim =
      characteristicFunctional Q D qdim k hdim := by
  unfold characteristicFunctional
  rw [quarterUTotal_connection_independent Q D D',
    normalizedTangentHalfTrace_connection_independent Q D qdim D']

end
end QuaternionicSymmetry.ManifoldTangentCharacterConnectionIndependence
