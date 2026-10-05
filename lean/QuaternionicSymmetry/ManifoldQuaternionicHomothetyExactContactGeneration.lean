import QuaternionicSymmetry.ManifoldQuaternionicHomothetyHolomorphicTransitivity
import QuaternionicSymmetry.ManifoldTwistorFullAutHomogeneityGeneration

/-! Normalized holomorphic twistor transitivity yields global generation of
the *exact selected unscaled* contact quotient line. The target line and
atlas are arbitrary actual compatible data; there is no pullback-line
identification premise. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyExactContactGeneration
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyConnection
open ManifoldQuaternionicHomothetyHolomorphicTransitivity
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorFullAutomorphisms
open ManifoldTwistorFullAutHomogeneityGeneration
open ManifoldTwistorLineCoreClasses
open ManifoldPositiveQuaternionicKahlerGeometry
open GeneralHolomorphicTransitiveOrbitSource
open GeneralHolomorphicFullAutomorphismLieSource
open HolomorphicLineCorePullback
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exact_contactLine_generated_of_normalized_fullAut_transitive
    (hLee : LeeHolomorphicTransitiveOrbitSubmersion)
    (hKob : KobayashiCompactAutomorphismTransformation)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (s : ℝ) (hs : s ≠ 0) {n : ℕ}
    (A : CompatibleComplexAtlas (rescaleMetric P.tangent s hs)
      (rescaleConnection P.tangent P.connection s hs) n)
    (B : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n B)
    (hTrans : ∀ z w : SphereBundleTotal (rescaleMetric P.tangent s hs),
      ∃ f : TwistorHolomorphicAutomorphisms
        (rescaleMetric P.tangent s hs)
        (rescaleConnection P.tangent P.connection s hs) A,
        f.1 z = w) :
    letI := B.charts
    GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
      (contactLineCore P.tangent P.connection C.contact.line) := by
  have hTarget := fullAut_transitive P.tangent P.connection s hs A B hTrans
  exact actual_contactLine_generated_of_fullAut_transitive
    hLee hKob P B C hTarget

/-- Generation using the retained BWW transformation source. -/
theorem exact_contactLine_generated_of_normalized_fullAut_transitive_of_reductive
    (hLee : LeeHolomorphicTransitiveOrbitSubmersion)
    (hAutSource : ManifoldTwistorBWW66ReductiveTransformationSource.FullAutReductiveTransformationSource)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (s : ℝ) (hs : s ≠ 0) {n : ℕ}
    (A : CompatibleComplexAtlas (rescaleMetric P.tangent s hs)
      (rescaleConnection P.tangent P.connection s hs) n)
    (B : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n B)
    (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (hTrans : ∀ z w : SphereBundleTotal (rescaleMetric P.tangent s hs),
      ∃ f : TwistorHolomorphicAutomorphisms
        (rescaleMetric P.tangent s hs)
        (rescaleConnection P.tangent P.connection s hs) A,
        f.1 z = w) :
    letI := B.charts
    GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
      (contactLineCore P.tangent P.connection C.contact.line) := by
  have hTarget := fullAut_transitive P.tangent P.connection s hs A B hTrans
  exact actual_contactLine_generated_of_fullAut_transitive_of_reductive
    hLee hAutSource P B C hn hDim hTarget

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyExactContactGeneration
