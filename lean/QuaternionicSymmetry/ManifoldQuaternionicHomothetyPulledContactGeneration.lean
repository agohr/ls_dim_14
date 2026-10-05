import QuaternionicSymmetry.ManifoldQuaternionicHomothetyPulledContactLine
import QuaternionicSymmetry.HolomorphicLineCorePullbackSections

/-! Global generation of the actual normalized contact line persists on
its represented pullback along the homothety biholomorphism. This does not
yet identify that pullback with the unscaled intrinsic contact quotient. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyPulledContactGeneration
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyConnection
open ManifoldQuaternionicHomothetyTwistorSmooth
open ManifoldQuaternionicHomothetyCompatibleComplexAtlas
open ManifoldQuaternionicHomothetyPulledContactLine
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorLineCoreClasses
open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem pulledContactLine_globallyGenerated (s : ℝ) (hs : s ≠ 0) (n : ℕ)
    (A : CompatibleComplexAtlas (rescaleMetric Q s hs)
      (rescaleConnection Q D s hs) n)
    (L : HolomorphicContactLine (rescaleMetric Q s hs)
      (rescaleConnection Q D s hs) n A)
    (hGen : letI := A.charts
      GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore (rescaleMetric Q s hs)
          (rescaleConnection Q D s hs) L)) :
    letI := (compatibleAtlas Q D s hs n A).charts
    GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
      (pulledContactLine Q D s hs n A L) := by
  letI := A.charts
  letI := A.complexManifold
  let A' := compatibleAtlas Q D s hs n A
  letI := A'.charts
  letI := A'.complexManifold
  let e := (sphereTotalDiffeomorph Q s hs).symm.toHomeomorph
  have he : ContMDiff 𝓘(ℂ,ComplexTwistorModel n)
      𝓘(ℂ,ComplexTwistorModel n) ∞ e :=
    ComplexHomeomorphLieAtlasTransfer.holomorphic_toFun e
  exact globallyGenerated_pullback 𝓘(ℂ,ComplexTwistorModel n)
    𝓘(ℂ,ComplexTwistorModel n)
    (contactLineCore (rescaleMetric Q s hs) (rescaleConnection Q D s hs) L)
    e he hGen

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyPulledContactGeneration
