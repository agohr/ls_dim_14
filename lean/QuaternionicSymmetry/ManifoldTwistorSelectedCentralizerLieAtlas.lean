import QuaternionicSymmetry.ManifoldTwistorSelectedMetricCentralizer
import QuaternionicSymmetry.GeneralClosedSubgroupLieSource
import QuaternionicSymmetry.ComplexLieRealCompanion
import QuaternionicSymmetry.GeneralHolomorphicAutomorphismSecondCountable

/-! The actual closed centralizer of the selected compact metric torus
receives an embedded finite-dimensional real Lie atlas from registered
Lee BG-L3. Its model dimension is existential; no maximality is assumed. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedCentralizerLieAtlas

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryPreservationInput
open ManifoldRiemannianMyersSteenrodInput
open ManifoldQuaternionicRiemannianDistance MetricIsometryCompactness
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorFullAutomorphisms
open ManifoldTwistorComplexIdentityAutAction
open ManifoldTwistorSelectedMetricCentralizer
open ManifoldQuaternionicMaximalTorusAction
open ManifoldQuaternionicTorusAction
open ManifoldQuaternionicTwistorIsometryAction
open CompactLieTorusInputs IdentityComponentLie TorusLaurentRepresentation
open GeneralClosedSubgroupLieSource ComplexLieRealCompanion
open scoped Manifold ContDiff
noncomputable section

variable {E M VC : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
  [NormedAddCommGroup VC] [NormedSpace ℂ VC] [FiniteDimensional ℂ VC]
  (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
  (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
  (hQ : FullMetricSpanPreservation P.tangent)
  (hMS : MyersSteenrodSource.{0,0})
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection P.tangent)
  (B : CompatibleComplexAtlas P.tangent D n)
  (C : HolomorphicContactData P.tangent D n B)
  (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
  {r : ℕ} (T : TorusEmbedding (QuaternionicIsometries P.tangent) r)
  (ρ : ComplexTorus r →* Equiv.Perm (SphereBundleTotal P.tangent))
  (hJoint : letI := B.charts
    ContMDiff (𝓘(ℂ, Fin r → ℂ).prod 𝓘(ℂ, ComplexTwistorModel n))
      𝓘(ℂ, ComplexTwistorModel n) ∞
      (fun p : ComplexTorus r × SphereBundleTotal P.tangent => ρ p.1 p.2))
  (hRestrict : ∀ (t : Torus r) (z : SphereBundleTotal P.tangent),
    ρ (compactInclusion r t) z =
      sphereTotalMap P.tangent
        ((actionOfEmbedding P.tangent T).representation t) z)
  (hComplexChart : letI := B.charts
    letI := B.complexManifold
    ChartedSpace VC (TwistorHolomorphicAutomorphisms P.tangent D B))
  (hComplexLie : letI := B.charts
    letI := B.complexManifold
    letI : ChartedSpace VC
      (TwistorHolomorphicAutomorphisms P.tangent D B) := hComplexChart
    LieGroup 𝓘(ℂ,VC) ∞
      (TwistorHolomorphicAutomorphisms P.tangent D B))

include hComplexLie

theorem exists_selected_centralizer_atlas
    (hClosed : LeeClosedEmbeddingTheorem) :
    letI := B.charts
    letI := B.complexManifold
    letI : ChartedSpace VC
      (TwistorHolomorphicAutomorphisms P.tangent D B) := hComplexChart
    letI : ChartedSpace VC
      (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
      ComplexIdentityComponentLie.charts VC
        (TwistorHolomorphicAutomorphisms P.tangent D B)
    let H := selectedMetricCentralizer P n D B C T ρ hJoint hRestrict
    ∃ d : ℕ, Nonempty (EmbeddedRealLieAtlas VC H
      (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) H.subtype d) := by
  letI := B.charts
  letI := B.complexManifold
  letI : T2Space (SphereBundleTotal P.tangent) := inferInstance
  letI : LocallyCompactSpace (SphereBundleTotal P.tangent) := inferInstance
  letI : SecondCountableTopology (SphereBundleTotal P.tangent) := inferInstance
  letI : T2Space (TwistorHolomorphicAutomorphisms P.tangent D B) := by
    unfold TwistorHolomorphicAutomorphisms
    infer_instance
  letI : SecondCountableTopology
      (TwistorHolomorphicAutomorphisms P.tangent D B) := by
    unfold TwistorHolomorphicAutomorphisms
    infer_instance
  letI : SecondCountableTopology
      (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  letI : ChartedSpace VC
    (TwistorHolomorphicAutomorphisms P.tangent D B) := hComplexChart
  letI : LieGroup 𝓘(ℂ,VC) ∞
    (TwistorHolomorphicAutomorphisms P.tangent D B) := hComplexLie
  letI : ChartedSpace VC
    (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
    ComplexIdentityComponentLie.charts VC _
  letI : IsManifold 𝓘(ℂ,VC) ∞
    (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
    ComplexIdentityComponentLie.manifold VC _
  letI : LieGroup 𝓘(ℂ,VC) ∞
    (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
    ComplexIdentityComponentLie.lieGroup VC _
  letI : IsManifold 𝓘(ℝ,VC) ∞
    (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
    ComplexLieRealCompanion.realManifold
  letI : LieGroup 𝓘(ℝ,VC) ∞
    (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
    ComplexLieRealCompanion.realLieGroup
  let H := selectedMetricCentralizer P n D B C T ρ hJoint hRestrict
  have hH : IsClosed (H : Set
      (Component (TwistorHolomorphicAutomorphisms P.tangent D B))) :=
    selectedMetricCentralizer_isClosed P n D B C T ρ hJoint hRestrict
  exact hClosed H.subtype hH.isClosedEmbedding_subtypeVal

end
end QuaternionicSymmetry.ManifoldTwistorSelectedCentralizerLieAtlas
