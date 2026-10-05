import QuaternionicSymmetry.ManifoldTwistorFullAutReductiveTransformationTarget
import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerGeometry

/-!
# BWW--Matsushima--Kobayashi derived transformation source

BWW, accepted author manuscript arXiv:1802.05002v3, Theorem 6.6, p.59
(user-approved authoritative version, 28 September 2026; final journal PDF
uninspected), proves reductivity for the actual full automorphism group
of a positive quaternionic-Kähler twistor using Salamon's twistor
Kähler--Einstein metric and Matsushima's theorem on its holomorphic vector
fields. Matsushima (1957), §1 and Theorem 1, identifies the complex Lie
algebra of those fields and proves its reductivity. Kobayashi, Chapter III,
§1, Theorem 1.1, installs the compact-open full automorphism group as a
complex Lie transformation group. The resulting central radical and joint
holomorphic evaluation therefore belong to this *same* automorphism Lie
structure. This is an explicitly derived published-literature contract, not
an internal proof of those theorems. A merely positive-Chern-Ricci metric
is not used as a substitute for Salamon's Kähler--Einstein metric.
-/

namespace QuaternionicSymmetry.ManifoldTwistorBWW66ReductiveTransformationSource

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorFullAutReductiveTransformationTarget
open scoped Manifold ContDiff

/-- The genuine positive twistor has a single reductive full-automorphism
complex Lie transformation atlas. The actual base, not a freely supplied
complex contact manifold, is the geometric premise. -/
def FullAutReductiveTransformationSource : Prop :=
  ∀ {E M : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nontrivial E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ), 2 ≤ n → Module.finrank ℝ E = 4*n →
    ∀ (A : CompatibleComplexAtlas P.tangent P.connection n),
      FullAutReductiveTransformationConclusion P.tangent P.connection A

end QuaternionicSymmetry.ManifoldTwistorBWW66ReductiveTransformationSource
