import QuaternionicSymmetry.ManifoldQuaternionicHomothetyAnyComplexAtlasMap
import QuaternionicSymmetry.HolomorphicAutomorphismTransitivityTransport
import QuaternionicSymmetry.ManifoldTwistorFullAutomorphisms

/-! A normalized twistor's holomorphic homogeneity transports to the
literal unscaled twistor in any compatible complex atlas. No contact-line
quotient comparison or global generation assumption enters this step. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyHolomorphicTransitivity
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyConnection
open ManifoldQuaternionicHomothetyTwistorSmooth
open ManifoldQuaternionicHomothetyAnyComplexAtlasMap
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorFullAutomorphisms
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

def complexDiffeomorph (s : ℝ) (hs : s ≠ 0) {n : ℕ}
    (A : CompatibleComplexAtlas (rescaleMetric Q s hs)
      (rescaleConnection Q D s hs) n)
    (B : CompatibleComplexAtlas Q D n) :
    @Diffeomorph ℂ _
      (ComplexTwistorModel n) _ _ (ComplexTwistorModel n) _ _
      (ComplexTwistorModel n) _ (ComplexTwistorModel n) _
      𝓘(ℂ,ComplexTwistorModel n) 𝓘(ℂ,ComplexTwistorModel n)
      (SphereBundleTotal (rescaleMetric Q s hs)) _ A.charts
      (SphereBundleTotal Q) _ B.charts ∞ := by
  letI := A.charts
  letI := A.complexManifold
  letI := B.charts
  letI := B.complexManifold
  exact {
    toEquiv := (sphereTotalDiffeomorph Q s hs).toEquiv
    contMDiff_toFun := holomorphic_forward Q D s hs A B
    contMDiff_invFun := holomorphic_backward Q D s hs A B }

theorem fullAut_transitive (s : ℝ) (hs : s ≠ 0) {n : ℕ}
    (A : CompatibleComplexAtlas (rescaleMetric Q s hs)
      (rescaleConnection Q D s hs) n)
    (B : CompatibleComplexAtlas Q D n)
    (hTrans : ∀ z w : SphereBundleTotal (rescaleMetric Q s hs),
      ∃ f : TwistorHolomorphicAutomorphisms
        (rescaleMetric Q s hs) (rescaleConnection Q D s hs) A,
        f.1 z = w) :
    ∀ z w : SphereBundleTotal Q,
      ∃ f : TwistorHolomorphicAutomorphisms Q D B,
        f.1 z = w := by
  letI := A.charts
  letI := A.complexManifold
  letI := B.charts
  letI := B.complexManifold
  exact HolomorphicAutomorphismTransitivityTransport.transitive_of_biholomorph
    (complexDiffeomorph Q D s hs A B) hTrans

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyHolomorphicTransitivity
