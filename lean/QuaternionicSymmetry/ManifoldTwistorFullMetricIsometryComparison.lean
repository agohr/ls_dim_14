import QuaternionicSymmetry.ManifoldTwistorFullAutUniversalComplexificationTarget
import QuaternionicSymmetry.ManifoldQuaternionicIsometryPreservationInput
import QuaternionicSymmetry.IdentityComponentEquivTransfer
import QuaternionicSymmetry.UniversalComplexificationEquivTransfer

/-! The ordinary full metric-isometry identity component and the actual
quaternionic-isometry identity component are homeomorphically isomorphic,
using exactly BG-Q1 and Myers–Steenrod. The natural full-twistor lift is
transported through that equivalence, before BWW 6.5 is applied. -/

namespace QuaternionicSymmetry.ManifoldTwistorFullMetricIsometryComparison

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicIsometryPreservationInput
open ManifoldQuaternionicRiemannianDistance
open ManifoldRiemannianMyersSteenrodInput
open ManifoldQuaternionicIsometryTopology
open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicFullIsometryEmbedding
open MetricIsometryCompactness
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorFullAutomorphisms
open ManifoldTwistorFullAutomorphismIdentityComponent
open ManifoldTwistorFullAutUniversalComplexificationTarget
open IdentityComponentLie IdentityComponentEquivTransfer
open CompactRealFormUniversalComplexification UniversalComplexificationEquivTransfer
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
  (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
  (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
  (hQ : FullMetricSpanPreservation P.tangent)
  (hMS : MyersSteenrodSource.{0,0})

def identityComponentEquiv :
    letI : MetricSpace M := riemannianMetricSpace P.tangent
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
    Component (QuaternionicIsometries P.tangent) ≃*
      Component (M ≃ᵢ M) := by
  letI : MetricSpace M := riemannianMetricSpace P.tangent
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
  exact componentEquiv (fullMetricIsometryEquiv P n hn hDim hQ hMS)
    (toFullMetricIsometry_continuous P.tangent)
    (fullMetricIsometryEquiv_symm_continuous P n hn hDim hQ hMS)

theorem identityComponentEquiv_continuous :
    letI : MetricSpace M := riemannianMetricSpace P.tangent
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
    Continuous (identityComponentEquiv P n hn hDim hQ hMS) := by
  letI : MetricSpace M := riemannianMetricSpace P.tangent
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
  exact continuous_componentEquiv
    (fullMetricIsometryEquiv P n hn hDim hQ hMS)
    (toFullMetricIsometry_continuous P.tangent)
    (fullMetricIsometryEquiv_symm_continuous P n hn hDim hQ hMS)

theorem identityComponentEquiv_symm_continuous :
    letI : MetricSpace M := riemannianMetricSpace P.tangent
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
    Continuous (identityComponentEquiv P n hn hDim hQ hMS).symm := by
  letI : MetricSpace M := riemannianMetricSpace P.tangent
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
  exact continuous_componentEquiv_symm
    (fullMetricIsometryEquiv P n hn hDim hQ hMS)
    (toFullMetricIsometry_continuous P.tangent)
    (fullMetricIsometryEquiv_symm_continuous P n hn hDim hQ hMS)

variable (D : ManifoldQuaternionicConnection.CompatibleTangentConnection P.tangent)
  (B : CompatibleComplexAtlas P.tangent D n)
  (L : HolomorphicContactLine P.tangent D n B)
  (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})

/-- Actual ordinary metric-isometry lift, obtained only after the
BG-Q1/Myers–Steenrod identification. -/
def fullMetricIdentityLift :
    letI : MetricSpace M := riemannianMetricSpace P.tangent
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
    Component (M ≃ᵢ M) →*
      Component (TwistorHolomorphicAutomorphisms P.tangent D B) := by
  letI : MetricSpace M := riemannianMetricSpace P.tangent
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
  exact (isometryIdentityLift P.tangent D B L hR3).comp
    (identityComponentEquiv P n hn hDim hQ hMS).symm.toMonoidHom

theorem fullMetricIdentityLift_comp_equiv :
    letI : MetricSpace M := riemannianMetricSpace P.tangent
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
    (fullMetricIdentityLift P n hn hDim hQ hMS D B L hR3).comp
      (identityComponentEquiv P n hn hDim hQ hMS).toMonoidHom =
      isometryIdentityLift P.tangent D B L hR3 := by
  letI : MetricSpace M := riemannianMetricSpace P.tangent
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : IsTopologicalGroup (M ≃ᵢ M) := isometryEquiv_topologicalGroup (X := M)
  apply MonoidHom.ext
  intro x
  simp [fullMetricIdentityLift, MonoidHom.comp_apply]

end
end QuaternionicSymmetry.ManifoldTwistorFullMetricIsometryComparison
