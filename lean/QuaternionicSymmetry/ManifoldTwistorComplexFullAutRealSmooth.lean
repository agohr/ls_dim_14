import QuaternionicSymmetry.ManifoldTwistorComplexFullAutAction
import QuaternionicSymmetry.ContinuousComplexLieHomRealSmooth
import QuaternionicSymmetry.ComplexTorusLieGroup
import QuaternionicSymmetry.GeneralHolomorphicAutomorphismSecondCountable
import QuaternionicSymmetry.ManifoldTwistorCompactHausdorff

/-! The actual Laurent/contact complex-torus action is real-C∞ as a map
into any finite-dimensional complex Lie atlas on the actual compact-open
full twistor automorphism group. This follows from the internal continuous-
homomorphism graph theorem, not a new BWW regularity premise. Complex
holomorphicity of this map into the full-Aut atlas is still separate. -/

namespace QuaternionicSymmetry.ManifoldTwistorComplexFullAutRealSmooth

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
theorem complexFullAutAction_realSmooth
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem) :
    letI := B.charts
    letI := B.complexManifold
    letI : ChartedSpace VC (TwistorHolomorphicAutomorphisms Q D B) := hChart
    ContMDiff 𝓘(ℝ,Fin r → ℂ) 𝓘(ℝ,VC) ∞
      (complexFullAutAction Q D B C A ρ hJoint hRestrict) := by
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
  exact continuous_hom_real_smooth
    (complexFullAutAction Q D B C A ρ hJoint hRestrict)
    hClosed hImm hLee hCont

end
end QuaternionicSymmetry.ManifoldTwistorComplexFullAutRealSmooth
