import QuaternionicSymmetry.ManifoldRiemannianMaximalTorus
import QuaternionicSymmetry.CompactLieTorusEquivTransfer
import QuaternionicSymmetry.ManifoldQuaternionicIsometryPreservationInput

/-! The full metric-isometry maximal torus transfers through the actual
geometry-specific preservation/Myers–Steenrod topological group identification to a maximal
torus among quaternionic-preserving isometries. No claim about maximality
in the complex contact automorphism group is made. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicMaximalTorus

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicFullIsometryEmbedding
open ManifoldQuaternionicIsometryPreservationInput
open ManifoldRiemannianMyersSteenrodInput ManifoldRiemannianIsometryLieInput
open ManifoldQuaternionicRiemannianDistance MetricIsometryCompactness
open ManifoldQuaternionicKillingFields CompactLieTorusInputs
open CompactLieTorusEquivTransfer
open scoped Manifold ContDiff
noncomputable section
universe uMax vMax

variable {E : Type uMax} {M : Type vMax}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
variable (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))

theorem exists_maximal_torus_of_killing_dimension
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4 * n)
    (hQ : FullMetricSpanPreservation P.tangent)
    (hMS : MyersSteenrodSource.{uMax,vMax})
    (hR3 : IsometryLieSource.{uMax,vMax})
    (hR4 : KillingLieSource.{uMax,vMax})
    (hTorus : MaximalTorusSource.{0,vMax})
    (hRankOne : CompactRankOneDimensionSource.{0,vMax})
    (hdim : 3 < killingDimension P.tangent) :
    ∃ r : ℕ, 2 ≤ r ∧
      ∃ T : TorusEmbedding (QuaternionicIsometries P.tangent) r,
        T.IsMaximal (QuaternionicIsometries P.tangent) := by
  letI : MetricSpace M := riemannianMetricSpace P.tangent
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  obtain ⟨r,hr,T,hMax⟩ :=
    ManifoldRiemannianMaximalTorus.full_isometry_maximal_torus_of_killing_dimension
      P.tangent hR3 hR4 hTorus hRankOne hdim
  let e := fullMetricIsometryEquiv P n hn hDim hQ hMS
  have he : Continuous e := toFullMetricIsometry_continuous P.tangent
  have he' : Continuous e.symm :=
    fullMetricIsometryEquiv_symm_continuous P n hn hDim hQ hMS
  let Tq := transport e.symm he' T
  exact ⟨r,hr,Tq,transport_maximal e.symm he' he T hMax⟩

end
end QuaternionicSymmetry.ManifoldQuaternionicMaximalTorus
