import QuaternionicSymmetry.ManifoldTwistorComplexIdentityAutRealSmooth
import QuaternionicSymmetry.ComplexIdentityComponentTangentIdentity
import QuaternionicSymmetry.ManifoldTwistorComplexFullAutImmersion
/-! The actual component-valued and full-Aut actions have the same
real derivative in their inherited atlas coordinates. Injectivity is
therefore inherited from the already checked faithful full action. -/

namespace QuaternionicSymmetry.ManifoldTwistorComplexIdentityAutDerivative

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
open ManifoldTwistorComplexIdentityAutRealSmooth
open ManifoldComplexHolomorphicFactorization ComplexLieRealCompanion
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
theorem complexIdentityAutAction_mfderiv_eq_full
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem) (z : ComplexTorus r) :
    letI := B.charts
    letI := B.complexManifold
    letI : ChartedSpace VC (TwistorHolomorphicAutomorphisms Q D B) := hChart
    letI : ChartedSpace VC
        (Component (TwistorHolomorphicAutomorphisms Q D B)) :=
      ComplexIdentityComponentLie.charts VC
        (TwistorHolomorphicAutomorphisms Q D B)
    mfderiv 𝓘(ℝ,Fin r → ℂ) 𝓘(ℝ,VC)
      (complexIdentityAutAction Q D B C A ρ hJoint hRestrict) z =
      mfderiv 𝓘(ℝ,Fin r → ℂ) 𝓘(ℝ,VC)
        (complexFullAutAction Q D B C A ρ hJoint hRestrict) z := by
  letI := B.charts
  letI := B.complexManifold
  letI : ChartedSpace VC (TwistorHolomorphicAutomorphisms Q D B) := hChart
  letI : LieGroup 𝓘(ℂ,VC) ∞
      (TwistorHolomorphicAutomorphisms Q D B) := hLie
  letI : ChartedSpace VC
      (Component (TwistorHolomorphicAutomorphisms Q D B)) :=
    ComplexIdentityComponentLie.charts VC _
  letI : IsManifold 𝓘(ℂ,VC) ∞
      (Component (TwistorHolomorphicAutomorphisms Q D B)) :=
    ComplexIdentityComponentLie.manifold VC _
  letI : IsManifold 𝓘(ℝ,VC) ∞
      (Component (TwistorHolomorphicAutomorphisms Q D B)) := realManifold
  letI : IsManifold 𝓘(ℝ,VC) ∞
      (TwistorHolomorphicAutomorphisms Q D B) := realManifold
  have hInc : ContMDiff 𝓘(ℝ,VC) 𝓘(ℝ,VC) ∞
      (Subtype.val : Component (TwistorHolomorphicAutomorphisms Q D B) →
        TwistorHolomorphicAutomorphisms Q D B) :=
    holomorphic_is_real_smooth (ComplexIdentityComponentLie.inclusion_holomorphic VC _)
  have hc := complexIdentityAutAction_realSmooth Q D B C A ρ hJoint hRestrict
    hChart hLie hClosed hImm hLee
  have hcomp := mfderiv_comp (I := 𝓘(ℝ,Fin r → ℂ))
    (I' := 𝓘(ℝ,VC)) (I'' := 𝓘(ℝ,VC)) (x := z)
    (hInc.mdifferentiableAt (by simp)) (hc.mdifferentiableAt (by simp))
  rw [ComplexIdentityComponentTangentIdentity.inclusion_mfderiv_eq_id] at hcomp
  simpa only [ContinuousLinearMap.id_comp] using hcomp.symm

include hLie in
theorem complexIdentityAutAction_derivative_injective
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (hInj : Function.Injective
      (complexFullAutAction Q D B C A ρ hJoint hRestrict))
    (z : ComplexTorus r) :
    letI := B.charts
    letI := B.complexManifold
    letI : ChartedSpace VC (TwistorHolomorphicAutomorphisms Q D B) := hChart
    letI : ChartedSpace VC
        (Component (TwistorHolomorphicAutomorphisms Q D B)) :=
      ComplexIdentityComponentLie.charts VC
        (TwistorHolomorphicAutomorphisms Q D B)
    Function.Injective (mfderiv 𝓘(ℝ,Fin r → ℂ) 𝓘(ℝ,VC)
      (complexIdentityAutAction Q D B C A ρ hJoint hRestrict) z) := by
  letI := B.charts
  letI := B.complexManifold
  letI : ChartedSpace VC (TwistorHolomorphicAutomorphisms Q D B) := hChart
  letI : ChartedSpace VC
      (Component (TwistorHolomorphicAutomorphisms Q D B)) :=
    ComplexIdentityComponentLie.charts VC _
  rw [complexIdentityAutAction_mfderiv_eq_full Q D B C A ρ hJoint hRestrict
    hChart hLie hClosed hImm hLee]
  exact ManifoldTwistorComplexFullAutImmersion.complexFullAutAction_derivative_injective
    Q D B C A ρ hJoint hRestrict hChart hLie hClosed hImm hLee hInj z

end
end QuaternionicSymmetry.ManifoldTwistorComplexIdentityAutDerivative
