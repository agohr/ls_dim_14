import QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas
import QuaternionicSymmetry.ManifoldQuaternionicHomothetyTwistorSmooth
import QuaternionicSymmetry.ComplexHomeomorphLieAtlasTransfer

/-! Pull the normalized twistor complex charts to the original twistor
through the actual homothety sphere-bundle diffeomorphism. This constructs
the complex atlas only; its compatibility with the original real atlas and
twistor almost-complex tensor is a separate obligation. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyComplexAtlasCharts
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyConnection
open ManifoldQuaternionicHomothetyTwistorSmooth
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

/-- The literal pullback of a normalized complex atlas along the inverse
homothety twistor diffeomorphism. -/
def charts (s : ℝ) (hs : s ≠ 0) (n : ℕ)
    (A : CompatibleComplexAtlas (rescaleMetric Q s hs)
      (rescaleConnection Q D s hs) n) :
    ChartedSpace (ComplexTwistorModel n) (SphereBundleTotal Q) := by
  letI := A.charts
  exact ComplexHomeomorphLieAtlasTransfer.charts
    (sphereTotalDiffeomorph Q s hs).symm.toHomeomorph

/-- The pulled-back charts form a genuine complex manifold. -/
def manifold (s : ℝ) (hs : s ≠ 0) (n : ℕ)
    (A : CompatibleComplexAtlas (rescaleMetric Q s hs)
      (rescaleConnection Q D s hs) n) :
    letI := charts Q D s hs n A
    IsManifold 𝓘(ℂ,ComplexTwistorModel n) ∞ (SphereBundleTotal Q) := by
  letI := A.charts
  letI := A.complexManifold
  exact ComplexHomeomorphLieAtlasTransfer.manifold
    (sphereTotalDiffeomorph Q s hs).symm.toHomeomorph

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyComplexAtlasCharts
