import QuaternionicSymmetry.ManifoldQuaternionicHomothetyCompatibleComplexAtlas
import QuaternionicSymmetry.ManifoldTwistorLineCoreClasses
import QuaternionicSymmetry.HolomorphicLineCorePullback

/-! The normalized contact line pulled back to the original twistor by the
actual biholomorphic homothety map. This is a represented holomorphic line;
its quotient/contact-form identification is proved separately. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyPulledContactLine
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyConnection
open ManifoldQuaternionicHomothetyTwistorSmooth
open ManifoldQuaternionicHomothetyCompatibleComplexAtlas
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

def pulledContactLine (s : ℝ) (hs : s ≠ 0) (n : ℕ)
    (A : CompatibleComplexAtlas (rescaleMetric Q s hs)
      (rescaleConnection Q D s hs) n)
    (L : HolomorphicContactLine (rescaleMetric Q s hs)
      (rescaleConnection Q D s hs) n A) :
    letI := (compatibleAtlas Q D s hs n A).charts
    LineCore.{0} (B := ManifoldTwistorSphereCore.SphereBundleTotal Q)
      𝓘(ℂ,ComplexTwistorModel n) := by
  letI := A.charts
  letI := A.complexManifold
  let A' := compatibleAtlas Q D s hs n A
  letI := A'.charts
  letI := A'.complexManifold
  let e := (sphereTotalDiffeomorph Q s hs).symm.toHomeomorph
  have he : ContMDiff 𝓘(ℂ,ComplexTwistorModel n)
      𝓘(ℂ,ComplexTwistorModel n) ∞ e :=
    ComplexHomeomorphLieAtlasTransfer.holomorphic_toFun e
  exact pullbackLineCore 𝓘(ℂ,ComplexTwistorModel n)
    𝓘(ℂ,ComplexTwistorModel n)
    (contactLineCore (rescaleMetric Q s hs) (rescaleConnection Q D s hs) L) e he

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyPulledContactLine
