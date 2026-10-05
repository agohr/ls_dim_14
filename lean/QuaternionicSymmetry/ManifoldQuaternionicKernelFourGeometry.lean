import QuaternionicSymmetry.ManifoldQuaternionicKernelQTriviality
import QuaternionicSymmetry.ManifoldQuaternionicFixedFourGeometry

/-! Four-dimensional connected character-kernel fixed components. The
actual vertical weight supplies pointwise triviality, BG-R3 propagates it,
and the separate orientation-compatible T4 source supplies the Einstein and
Weyl geometry. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicKernelFourGeometry
open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicTorusAction
open ManifoldQuaternionicKernelQTriviality
open ManifoldQuaternionicVerticalWeightKernel
open ManifoldQuaternionicFixedFourGeometry
open ManifoldQuaternionicFourSubmanifoldInput
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldPositiveTwistorCompatibleFourGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldRiemannianFixedComponentInput
open ManifoldRiemannianIsometryLieInput
open ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

/-- Direct actual four-dimensional counterpart of the higher-dimensional
induced-geometry theorem. The source boundary is the registered m=1 T4
curvature statement, not a hidden claim about integrability of S(Q). -/
theorem verticalWeight_exists_induced_compact_four_geometry
    {E M : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    [CompactSpace M] [T3Space M] [SecondCountableTopology M]
    [PreconnectedSpace M] [Nonempty M]
    (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (hR3 : IsometryLieSource.{0,0})
    (hT4four : PositiveFourQuaternionicSubmanifoldSource)
    {r : ℕ} (A : ContinuousTorusAction P.tangent r)
    (z : SphereBundleTotal P.tangent)
    (hz : ∀ t, A.representation t • z = z)
    (μ : Fin r → ℤ)
    (hweight : HasVerticalWeight P.tangent A z hz μ)
    (C : FixedComponentAtlas P.tangent
      (ContinuousTorusAction.connectedKernelImage P.tangent A μ) z.1 4) :
    ∃ C' : FixedComponentAtlas P.tangent
      (ContinuousTorusAction.connectedKernelImage P.tangent A μ) z.1 4,
    letI := C'.charts
    letI := C'.manifold
    ∃ R : CompactConnectedPositiveTwistorCompatibleFourGeometry
        (E := EuclideanSpace ℝ (Fin 4))
        (M := FixedComponent P.tangent
          (ContinuousTorusAction.connectedKernelImage P.tangent A μ) z.1),
      IsInducedQuaternionicGeometry P
        R.toPositiveTwistorCompatibleFourGeometry.toPositiveQuaternionicKahlerGeometry
        Subtype.val := by
  have hQ := connectedKernel_coefficientAction_everywhere P.tangent
    hR3 A μ z.1 (base_mem_connectedKernelFixedSet P.tangent A z hz μ)
      (connectedKernel_coefficient_trivial P.tangent A z hz μ hweight)
  exact exists_induced_compact_four_geometry P n hn hDim
    (ContinuousTorusAction.connectedKernelImage P.tangent A μ) z.1 C hQ hT4four

end
end QuaternionicSymmetry.ManifoldQuaternionicKernelFourGeometry
