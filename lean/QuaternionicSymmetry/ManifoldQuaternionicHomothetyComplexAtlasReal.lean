import QuaternionicSymmetry.ManifoldQuaternionicHomothetyComplexAtlasCharts

/-! Real smooth compatibility internal to the pulled-back normalized complex
atlas, using the actual homothety twistor diffeomorphism. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyComplexAtlasReal
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyConnection
open ManifoldQuaternionicHomothetyTwistorSmooth
open ManifoldQuaternionicHomothetyComplexAtlasCharts
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

/-- The same pulled-back charts are also real smooth charts. -/
def realManifold (s : ℝ) (hs : s ≠ 0) (n : ℕ)
    (A : CompatibleComplexAtlas (rescaleMetric Q s hs)
      (rescaleConnection Q D s hs) n) :
    letI := charts Q D s hs n A
    IsManifold 𝓘(ℝ,ComplexTwistorModel n) ∞ (SphereBundleTotal Q) := by
  letI := A.charts
  letI := A.realManifold
  exact HomeomorphLieAtlasTransfer.manifold
    (sphereTotalDiffeomorph Q s hs).symm.toHomeomorph

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyComplexAtlasReal
