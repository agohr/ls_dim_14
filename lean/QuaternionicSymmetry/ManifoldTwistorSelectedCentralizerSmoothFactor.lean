import QuaternionicSymmetry.ManifoldTwistorSelectedCentralizerLieAtlas
import QuaternionicSymmetry.ManifoldTwistorComplexIdentityAutRealSmooth
import QuaternionicSymmetry.InjectiveLieHomImmersion
import QuaternionicSymmetry.ManifoldImmersionSmooth

/-! The constructed complex torus action factors as a real-smooth group
homomorphism into the actual BG-L3 Lie atlas on the closed selected compact
centralizer. This does not assert holomorphicity of the parametrization. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedCentralizerSmoothFactor

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryPreservationInput
open ManifoldRiemannianMyersSteenrodInput
open ManifoldQuaternionicRiemannianDistance MetricIsometryCompactness
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorFullAutomorphisms
open ManifoldTwistorComplexIdentityAutAction
open ManifoldTwistorComplexIdentityAutRealSmooth
open ManifoldTwistorSelectedMetricCentralizer
open ManifoldQuaternionicMaximalTorusAction
open ManifoldQuaternionicTorusAction
open ManifoldQuaternionicTwistorIsometryAction
open CompactLieTorusInputs IdentityComponentLie TorusLaurentRepresentation
open ComplexTorusHolomorphicStructure
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open ComplexLieRealCompanion InjectiveLieHomImmersion ManifoldImmersionSmooth
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
  {r d : ℕ} (T : TorusEmbedding (QuaternionicIsometries P.tangent) r)
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

theorem complexActionIntoCentralizer_realSmooth
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (g : letI := B.charts
      letI := B.complexManifold
      letI : ChartedSpace VC
        (TwistorHolomorphicAutomorphisms P.tangent D B) := hComplexChart
      letI : ChartedSpace VC
        (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
        ComplexIdentityComponentLie.charts VC
          (TwistorHolomorphicAutomorphisms P.tangent D B)
      let H := selectedMetricCentralizer P n D B C T ρ hJoint hRestrict
      EmbeddedRealLieAtlas VC H
        (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) H.subtype d) :
    letI := B.charts
    letI := B.complexManifold
    letI : ChartedSpace VC
      (TwistorHolomorphicAutomorphisms P.tangent D B) := hComplexChart
    letI : ChartedSpace VC
      (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
      ComplexIdentityComponentLie.charts VC
        (TwistorHolomorphicAutomorphisms P.tangent D B)
    letI := g.charts
    ContMDiff 𝓘(ℝ,Fin r → ℂ) 𝓘(ℝ,Fin d → ℝ) ∞
      (complexActionIntoCentralizer P n D B C T ρ hJoint hRestrict) := by
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
  letI : T2Space
      (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
    inferInstance
  letI : SecondCountableTopology
      (Component (TwistorHolomorphicAutomorphisms P.tangent D B)) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  letI : T2Space (ComplexTorus r) :=
    (torusVal_isOpenEmbedding r).t2Space
  letI : SecondCountableTopology (ComplexTorus r) :=
    (torusVal_isOpenEmbedding r).secondCountableTopology
  letI : IsManifold 𝓘(ℝ,Fin r → ℂ) ∞ (ComplexTorus r) :=
    ComplexLieRealCompanion.realManifold
  let H := selectedMetricCentralizer P n D B C T ρ hJoint hRestrict
  letI : T2Space H := inferInstance
  letI : SecondCountableTopology H :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  letI := g.charts
  letI : IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ H := g.manifold
  letI : LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ H := g.lieGroup
  have hιSmooth : ContMDiff 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,VC) ∞ H.subtype :=
    ManifoldImmersionSmooth.smoothEmbedding_contMDiff g.smoothEmbedding
  have hιInj (x : H) : Function.Injective
      (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,VC) H.subtype x) :=
    smooth_injective_hom_immersion H.subtype hImm hιSmooth
      g.smoothEmbedding.isEmbedding.injective x
  have hφSmooth := complexIdentityAutAction_realSmooth P.tangent D B C
    (actionOfEmbedding P.tangent T) ρ hJoint hRestrict
    hComplexChart hComplexLie hClosed hImm hLee
  have hComp : ContMDiff 𝓘(ℝ,Fin r → ℂ) 𝓘(ℝ,VC) ∞
      (H.subtype ∘ complexActionIntoCentralizer P n D B C T ρ hJoint hRestrict) := by
    exact hφSmooth
  exact hLee H.subtype
    (complexActionIntoCentralizer P n D B C T ρ hJoint hRestrict)
    g.smoothEmbedding.isEmbedding hιSmooth hιInj hComp

end
end QuaternionicSymmetry.ManifoldTwistorSelectedCentralizerSmoothFactor
