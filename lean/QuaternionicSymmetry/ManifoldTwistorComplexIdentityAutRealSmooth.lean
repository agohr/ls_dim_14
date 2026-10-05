import QuaternionicSymmetry.ManifoldTwistorComplexIdentityAutAction
import QuaternionicSymmetry.ManifoldTwistorComplexFullAutRealSmooth
/-! The actual identity-component-valued complex action is real smooth in
the SAME inherited complex Lie atlas. The proof only restricts the known
real smooth map to an open codomain; holomorphicity is not inferred. -/

namespace QuaternionicSymmetry.ManifoldTwistorComplexIdentityAutRealSmooth

open ManifoldQuaternionicTorusAction
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorFullAutomorphisms ManifoldTwistorComplexFullAutAction
open GeneralHolomorphicDistributionAutomorphisms
open GeneralHolomorphicDistributionAutomorphismTopology
open GeneralHolomorphicAutomorphismSecondCountable
open GeneralHolomorphicFullAutomorphisms
open ContinuousComplexLieHomRealSmooth
open ComplexTorusHolomorphicStructure ComplexTorusLieGroup
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open TorusLaurentRepresentation
open ManifoldTwistorComplexFullAutRealSmooth
open ManifoldTwistorComplexIdentityAutAction IdentityComponentLie
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
theorem complexIdentityAutAction_realSmooth
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem) :
    letI := B.charts
    letI := B.complexManifold
    letI : ChartedSpace VC (TwistorHolomorphicAutomorphisms Q D B) := hChart
    letI : ChartedSpace VC
        (Component (TwistorHolomorphicAutomorphisms Q D B)) :=
      ComplexIdentityComponentLie.charts VC
        (TwistorHolomorphicAutomorphisms Q D B)
    ContMDiff 𝓘(ℝ,Fin r → ℂ) 𝓘(ℝ,VC) ∞
      (complexIdentityAutAction Q D B C A ρ hJoint hRestrict) := by
  letI := B.charts
  letI := B.complexManifold
  letI : ChartedSpace VC (TwistorHolomorphicAutomorphisms Q D B) := hChart
  let U : TopologicalSpace.Opens (TwistorHolomorphicAutomorphisms Q D B) :=
    ⟨Component (TwistorHolomorphicAutomorphisms Q D B),
      ComplexIdentityComponentLie.isOpen_component VC _⟩
  have hf := complexFullAutAction_realSmooth Q D B C A ρ hJoint hRestrict
    hChart hLie hClosed hImm hLee
  exact OpenSubgroupLie.contMDiff_codRestrict_opens (U := U) hf
    (fun z => (complexIdentityAutAction Q D B C A ρ hJoint hRestrict z).property)

end
end QuaternionicSymmetry.ManifoldTwistorComplexIdentityAutRealSmooth
