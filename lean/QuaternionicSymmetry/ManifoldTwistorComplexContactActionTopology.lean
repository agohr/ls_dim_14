import QuaternionicSymmetry.ManifoldTwistorComplexContactAction
import QuaternionicSymmetry.ManifoldTwistorContactAutomorphismTopology

/-! The constructed complex-torus contact action is continuous for the
independent compact-open automorphism topology. Its compact restriction is
faithful whenever the original quaternionic-isometry action is faithful. -/

namespace QuaternionicSymmetry.ManifoldTwistorComplexContactActionTopology

open ManifoldQuaternionicTorusAction ManifoldQuaternionicTwistorIsometryAction
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorContactAutomorphisms ManifoldTwistorComplexContactAction
open ManifoldTwistorContactAutomorphismTopology
open GeneralHolomorphicDistributionAutomorphismTopology
open TorusLaurentRepresentation ComplexTorusHolomorphicStructure
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
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

theorem complexContactAction_continuous :
    Continuous (complexContactAction Q D B C A ρ hJoint hRestrict) := by
  letI := B.charts
  letI := B.complexManifold
  apply continuous_representation_of_action (contactDistribution Q D B C.line)
    (complexContactAction Q D B C A ρ hJoint hRestrict)
  exact hJoint.continuous

theorem compact_restriction_injective (hA : A.Faithful) :
    Function.Injective ((complexContactAction Q D B C A ρ hJoint hRestrict).comp
      (compactInclusion r)) := by
  intro s t h
  apply hA
  apply isometryContactLift_injective Q D B C.line
  simpa only [MonoidHom.comp_apply, complexContactAction_compact] using h

end
end QuaternionicSymmetry.ManifoldTwistorComplexContactActionTopology
