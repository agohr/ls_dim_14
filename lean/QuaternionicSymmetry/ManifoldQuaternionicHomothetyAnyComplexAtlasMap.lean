import QuaternionicSymmetry.ManifoldQuaternionicHomothetyCompatibleComplexAtlas
import QuaternionicSymmetry.ManifoldTwistorCompatibleAtlasIdentity

/-! The actual homothety twistor diffeomorphism is biholomorphic not only
for its pulled atlas, but for any independently selected compatible atlas
on the unscaled twistor. Both charted-space arguments are explicit. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyAnyComplexAtlasMap
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyConnection
open ManifoldQuaternionicHomothetyTwistorSmooth
open ManifoldQuaternionicHomothetyCompatibleComplexAtlas
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

theorem holomorphic_forward (s : ℝ) (hs : s ≠ 0) {n : ℕ}
    (A : CompatibleComplexAtlas (rescaleMetric Q s hs)
      (rescaleConnection Q D s hs) n)
    (B : CompatibleComplexAtlas Q D n) :
    @ContMDiff ℂ _ _ _ _ _ _ 𝓘(ℂ,ComplexTwistorModel n)
      (SphereBundleTotal (rescaleMetric Q s hs)) _ A.charts
      _ _ _ _ _ 𝓘(ℂ,ComplexTwistorModel n)
      (SphereBundleTotal Q) _ B.charts ∞
      (sphereTotalDiffeomorph Q s hs) := by
  let A' := compatibleAtlas Q D s hs n A
  letI := A.charts
  letI := A.complexManifold
  letI := A'.charts
  letI := A'.complexManifold
  let e := (sphereTotalDiffeomorph Q s hs).symm.toHomeomorph
  have hPhi : @ContMDiff ℂ _ _ _ _ _ _ 𝓘(ℂ,ComplexTwistorModel n)
      (SphereBundleTotal (rescaleMetric Q s hs)) _ A.charts
      _ _ _ _ _ 𝓘(ℂ,ComplexTwistorModel n)
      (SphereBundleTotal Q) _ A'.charts ∞
      (sphereTotalDiffeomorph Q s hs) := by
    exact ComplexHomeomorphLieAtlasTransfer.holomorphic_invFun e
  have hId := ManifoldTwistorCompatibleAtlasIdentity.holomorphic_identity Q D B A'
  exact @ContMDiff.comp ℂ _
    (ComplexTwistorModel n) _ _ (ComplexTwistorModel n) _
    𝓘(ℂ,ComplexTwistorModel n)
    (SphereBundleTotal (rescaleMetric Q s hs)) _
    (ComplexTwistorModel n) _ _ (ComplexTwistorModel n) _
    𝓘(ℂ,ComplexTwistorModel n) (SphereBundleTotal Q) _
    (ComplexTwistorModel n) _ _ (ComplexTwistorModel n) _
    𝓘(ℂ,ComplexTwistorModel n) (SphereBundleTotal Q) _
    A.charts A'.charts B.charts _ _ _ hId hPhi

theorem holomorphic_backward (s : ℝ) (hs : s ≠ 0) {n : ℕ}
    (A : CompatibleComplexAtlas (rescaleMetric Q s hs)
      (rescaleConnection Q D s hs) n)
    (B : CompatibleComplexAtlas Q D n) :
    @ContMDiff ℂ _ _ _ _ _ _ 𝓘(ℂ,ComplexTwistorModel n)
      (SphereBundleTotal Q) _ B.charts
      _ _ _ _ _ 𝓘(ℂ,ComplexTwistorModel n)
      (SphereBundleTotal (rescaleMetric Q s hs)) _ A.charts ∞
      (sphereTotalDiffeomorph Q s hs).symm := by
  let A' := compatibleAtlas Q D s hs n A
  letI := A.charts
  letI := A.complexManifold
  letI := A'.charts
  letI := A'.complexManifold
  let e := (sphereTotalDiffeomorph Q s hs).symm.toHomeomorph
  have hId := ManifoldTwistorCompatibleAtlasIdentity.holomorphic_identity Q D A' B
  have hPhi : @ContMDiff ℂ _ _ _ _ _ _ 𝓘(ℂ,ComplexTwistorModel n)
      (SphereBundleTotal Q) _ A'.charts
      _ _ _ _ _ 𝓘(ℂ,ComplexTwistorModel n)
      (SphereBundleTotal (rescaleMetric Q s hs)) _ A.charts ∞
      (sphereTotalDiffeomorph Q s hs).symm := by
    exact ComplexHomeomorphLieAtlasTransfer.holomorphic_toFun e
  exact @ContMDiff.comp ℂ _
    (ComplexTwistorModel n) _ _ (ComplexTwistorModel n) _
    𝓘(ℂ,ComplexTwistorModel n) (SphereBundleTotal Q) _
    (ComplexTwistorModel n) _ _ (ComplexTwistorModel n) _
    𝓘(ℂ,ComplexTwistorModel n) (SphereBundleTotal Q) _
    (ComplexTwistorModel n) _ _ (ComplexTwistorModel n) _
    𝓘(ℂ,ComplexTwistorModel n)
    (SphereBundleTotal (rescaleMetric Q s hs)) _
    B.charts A'.charts A.charts _ _ _ hPhi hId

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyAnyComplexAtlasMap
