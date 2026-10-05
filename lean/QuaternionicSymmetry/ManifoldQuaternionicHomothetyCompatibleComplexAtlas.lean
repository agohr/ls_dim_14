import QuaternionicSymmetry.ManifoldQuaternionicHomothetyComplexAtlasTangentI

/-! Actual complex-atlas transport under constant metric homothety. The
resulting atlas realizes the original twistor tensor and is smoothly
compatible with its independently constructed real sphere-bundle atlas. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyCompatibleComplexAtlas
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyConnection
open ManifoldTwistorLeBrunComplexAtlas
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

/-- A normalized compatible complex twistor atlas induces a genuine
compatible complex atlas for the original homothetic metric. -/
def compatibleAtlas (s : ℝ) (hs : s ≠ 0) (n : ℕ)
    (A : CompatibleComplexAtlas (rescaleMetric Q s hs)
      (rescaleConnection Q D s hs) n) : CompatibleComplexAtlas Q D n where
  charts := ManifoldQuaternionicHomothetyComplexAtlasCharts.charts Q D s hs n A
  complexManifold := ManifoldQuaternionicHomothetyComplexAtlasCharts.manifold Q D s hs n A
  realManifold := ManifoldQuaternionicHomothetyComplexAtlasReal.realManifold Q D s hs n A
  smoothToExisting :=
    ManifoldQuaternionicHomothetyComplexAtlasSmoothTo.smoothToExisting Q D s hs n A
  smoothFromExisting :=
    ManifoldQuaternionicHomothetyComplexAtlasSmoothFrom.smoothFromExisting Q D s hs n A
  tangentI := ManifoldQuaternionicHomothetyComplexAtlasTangentI.tangentI Q D s hs n A

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyCompatibleComplexAtlas
