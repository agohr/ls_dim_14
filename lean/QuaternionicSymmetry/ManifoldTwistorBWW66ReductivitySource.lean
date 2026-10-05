import QuaternionicSymmetry.ManifoldTwistorFullAutReductiveLieTarget
import QuaternionicSymmetry.ManifoldTwistorPositiveRicciInput

/-! BWW Theorem 6.6, restricted to the actual positive quaternionic-Kähler
twistor selected by T1. BWW asserts reductivity of the *full* automorphism
group even in the projective-space case. Here its finite-dimensional complex
Lie-group and characteristic-zero Lie-algebra consequences are typed on the
already constructed compact-open full biholomorphism group.

The selected T1 metric supplies an actual positive Chern-Ricci witness; it
does not currently encode the Kähler--Einstein equation. BWW 6.6 is invoked
as its own registered theorem on the positive twistor, not as an internal
application of Matsushima to this weaker metric record. -/

namespace QuaternionicSymmetry.ManifoldTwistorBWW66ReductivitySource

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorPositiveRicciInput
open ManifoldTwistorFullAutReductiveLieTarget
open HolomorphicVectorHermitianMetric
open scoped Manifold ContDiff
noncomputable section

/-- Precisely BWW 6.6 on T1-selected actual positive twistor data, stated
universally as a literature-source contract rather than an axiom. Its
conclusion is the genuine central-radical condition on the tangent Lie
algebra of the full biholomorphism group. -/
def FullAutReductivitySource : Prop :=
  ∀ {E M : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nontrivial E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ), 2 ≤ n → Module.finrank ℝ E = 4*n →
    ∀ (A : CompatibleComplexAtlas P.tangent P.connection n)
      (_C : NondegenerateHolomorphicContactData
        P.tangent P.connection n A),
      letI := A.charts
      ∀ (m : HermitianBundleMetric (E := ComplexTwistorModel n)
          (A.complexTangentCore P.tangent P.connection)),
        m.PositiveChernRicci (A.complexTangentCore P.tangent P.connection) →
        FullAutReductiveLieConclusion P.tangent P.connection A

/-- The exact T1-selected atlas, contact datum, and positive-Ricci metric
discharge the geometric inputs of the BWW 6.6 source contract. No
projective-space exception is imposed here. -/
theorem exists_normalized_reductive_fullAut
    (hT1 : NormalizedPositiveRicciContactExistence)
    (hBWW66 : FullAutReductivitySource)
    {E M : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nontrivial E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (hScalar : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      ManifoldQuaternionicScalarCurvature.localScalarCurvature
        P.tangent P.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2)) :
    ∃ A : CompatibleComplexAtlas P.tangent P.connection n,
      ∃ _C : NondegenerateHolomorphicContactData
        P.tangent P.connection n A,
        FullAutReductiveLieConclusion P.tangent P.connection A := by
  obtain ⟨A,C,m,hm⟩ := hT1 P n hn hDim hScalar
  exact ⟨A,C,hBWW66 P n hn hDim A C m hm⟩

end
end QuaternionicSymmetry.ManifoldTwistorBWW66ReductivitySource
