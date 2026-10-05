import QuaternionicSymmetry.ManifoldTwistorComplexFullAutRealSmooth
import QuaternionicSymmetry.ContinuousComplexLieHomImmersion

/-! Faithfulness of the actual complex contact action makes its real
derivative injective in the SAME BWW-selected full-Aut Lie atlas. This is
the genuine tangent map of the constructed action, not a supplied Lie
algebra map. -/

namespace QuaternionicSymmetry.ManifoldTwistorComplexFullAutImmersion

open ManifoldQuaternionicTorusAction
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorFullAutomorphisms ManifoldTwistorComplexFullAutAction
open GeneralHolomorphicDistributionAutomorphisms
open GeneralHolomorphicDistributionAutomorphismTopology
open GeneralHolomorphicAutomorphismSecondCountable
open GeneralHolomorphicFullAutomorphisms
open ContinuousComplexLieHomImmersion
open ComplexTorusHolomorphicStructure ComplexTorusLieGroup
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open TorusLaurentRepresentation
open scoped Manifold ContDiff
noncomputable section

variable {E M VC : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [NormedAddCommGroup VC] [NormedSpace ℂ VC] [FiniteDimensional ℂ VC]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)
  (C : HolomorphicContactData Q D n B)
  {r : ℕ} (A : ContinuousTorusAction Q r)
  (ρ : ComplexTorus r →* Equiv.Perm (SphereBundleTotal Q))
  (hJoint : letI := B.charts
    ContMDiff (𝓘(ℂ, Fin r → ℂ).prod 𝓘(ℂ, ComplexTwistorModel n))
      𝓘(ℂ, ComplexTwistorModel n) ∞
      (fun p : ComplexTorus r × SphereBundleTotal Q => ρ p.1 p.2))
  (hRestrict : ∀ (t : Torus r) (z : SphereBundleTotal Q),
    ρ (compactInclusion r t) z = sphereTotalMap Q (A.representation t) z)
  (hChart : letI := B.charts
    letI := B.complexManifold
    ChartedSpace VC (TwistorHolomorphicAutomorphisms Q D B))
  (hLie : letI := B.charts
    letI := B.complexManifold
    letI : ChartedSpace VC (TwistorHolomorphicAutomorphisms Q D B) := hChart
    LieGroup 𝓘(ℂ,VC) ∞ (TwistorHolomorphicAutomorphisms Q D B))

include hLie in
theorem complexFullAutAction_derivative_injective
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (hInj : Function.Injective
      (complexFullAutAction Q D B C A ρ hJoint hRestrict))
    (z : ComplexTorus r) :
    letI := B.charts
    letI := B.complexManifold
    letI : ChartedSpace VC (TwistorHolomorphicAutomorphisms Q D B) := hChart
    Function.Injective (mfderiv 𝓘(ℝ,Fin r → ℂ) 𝓘(ℝ,VC)
      (complexFullAutAction Q D B C A ρ hJoint hRestrict) z) := by
  letI := B.charts
  letI := B.complexManifold
  letI : ChartedSpace VC (TwistorHolomorphicAutomorphisms Q D B) := hChart
  letI : LieGroup 𝓘(ℂ,VC) ∞
      (TwistorHolomorphicAutomorphisms Q D B) := hLie
  letI : T2Space (ComplexTorus r) :=
    (torusVal_isOpenEmbedding r).t2Space
  letI : SecondCountableTopology (ComplexTorus r) :=
    (torusVal_isOpenEmbedding r).secondCountableTopology
  letI : T2Space (SphereBundleTotal Q) := inferInstance
  letI : LocallyCompactSpace (SphereBundleTotal Q) := inferInstance
  letI : SecondCountableTopology (SphereBundleTotal Q) := inferInstance
  letI : T2Space (TwistorHolomorphicAutomorphisms Q D B) := by
    unfold TwistorHolomorphicAutomorphisms
    infer_instance
  letI : SecondCountableTopology
      (TwistorHolomorphicAutomorphisms Q D B) := by
    unfold TwistorHolomorphicAutomorphisms
    infer_instance
  have hCont := complexFullAutAction_continuous Q D B C A ρ hJoint hRestrict
  exact continuous_injective_hom_real_immersion
    (complexFullAutAction Q D B C A ρ hJoint hRestrict)
    hClosed hImm hLee hCont hInj z

end
end QuaternionicSymmetry.ManifoldTwistorComplexFullAutImmersion
