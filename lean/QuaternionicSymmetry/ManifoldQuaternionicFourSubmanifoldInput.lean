import QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourGeometry
import QuaternionicSymmetry.ManifoldQuaternionicSubmanifoldInput

/-! The four-dimensional part of T4 is kept separate from the ordinary
dimension-at-least-eight quaternionic-submanifold statement. The cited
Goertsches–Loiudice Proposition 5.1 proof and Alekseevsky–Marchiafava
Corollary 1.10 proof give a quaternionic, totally geodesic four-submanifold
the induced positive Einstein metric and the orientation-compatible Weyl
condition. This source boundary says nothing about a chosen fixed component,
torus weight, complex atlas, Kähler structure, or classification. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicFourSubmanifoldInput
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldPositiveTwistorCompatibleFourGeometry
open ManifoldQuaternionicSubmanifoldInput
open scoped Manifold ContDiff
noncomputable section

/-- T4 in real dimension four, with the actual embedded inclusion, invariant
tangent range, induced metric and restricted rank-three span. The curvature
conclusion uses the Weyl-half convention compatible with the actual `S(Q)`
twistor construction. -/
def PositiveFourQuaternionicSubmanifoldSource : Prop :=
  ∀ {E F M N : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [Nontrivial E]
    [FiniteDimensional ℝ F] [Nontrivial F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
    [T3Space M] [SecondCountableTopology M]
    [T3Space N] [SecondCountableTopology N],
    ∀ (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
      (n : ℕ), 2 ≤ n → Module.finrank ℝ E = 4*n →
      Module.finrank ℝ F = 4 →
    ∀ ι : N → M, ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι → Topology.IsEmbedding ι →
      (∀ x, Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x)) →
      QuaternionicTangentRange (F := F) P ι →
      ∃ B : CompatibleSubmanifoldAtlas (E := E) (F := F) inferInstance ι,
        letI := B.charts
        letI := B.manifold
        ∃ R : PositiveTwistorCompatibleFourGeometry (E := F) (M := N),
          IsInducedQuaternionicGeometry P
            R.toPositiveQuaternionicKahlerGeometry ι

end
end QuaternionicSymmetry.ManifoldQuaternionicFourSubmanifoldInput
