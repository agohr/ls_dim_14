import QuaternionicSymmetry.ManifoldTwistorComplexFullAutAction
import QuaternionicSymmetry.ComplexTorusIdentityComponentLift

/-! The constructed complex action takes values in the actual full-Aut
identity component. This factorization is derived from connectedness of
the complex torus and continuity of the same action, not a source premise. -/

namespace QuaternionicSymmetry.ManifoldTwistorComplexIdentityAutAction

open ManifoldQuaternionicTorusAction
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorContactAutomorphisms
open ManifoldTwistorFullAutomorphisms ManifoldTwistorFullAutomorphismLift
open ManifoldTwistorComplexContactAction
open GeneralHolomorphicDistributionAutomorphismTopology
open TorusLaurentRepresentation ComplexTorusHolomorphicStructure
open ManifoldTwistorComplexFullAutAction IdentityComponentLie
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
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

def complexIdentityAutAction : ComplexTorus r →*
    Component (TwistorHolomorphicAutomorphisms Q D B) :=
  ComplexTorusIdentityComponentLift.lift
    (complexFullAutAction Q D B C A ρ hJoint hRestrict)
    (complexFullAutAction_continuous Q D B C A ρ hJoint hRestrict)

@[simp] theorem complexIdentityAutAction_coe (z : ComplexTorus r) :
    (complexIdentityAutAction Q D B C A ρ hJoint hRestrict z :
      TwistorHolomorphicAutomorphisms Q D B) =
      complexFullAutAction Q D B C A ρ hJoint hRestrict z := rfl

theorem complexIdentityAutAction_continuous :
    Continuous (complexIdentityAutAction Q D B C A ρ hJoint hRestrict) :=
  ComplexTorusIdentityComponentLift.lift_continuous _ _

theorem complexIdentityAutAction_injective
    (hInj : Function.Injective
      (complexFullAutAction Q D B C A ρ hJoint hRestrict)) :
    Function.Injective (complexIdentityAutAction Q D B C A ρ hJoint hRestrict) :=
  ComplexTorusIdentityComponentLift.lift_injective _ _ hInj

theorem inclusion_comp_complexIdentityAutAction :
    (Component (TwistorHolomorphicAutomorphisms Q D B)).subtype.comp
      (complexIdentityAutAction Q D B C A ρ hJoint hRestrict) =
      complexFullAutAction Q D B C A ρ hJoint hRestrict :=
  ComplexTorusIdentityComponentLift.inclusion_comp_lift _ _

end
end QuaternionicSymmetry.ManifoldTwistorComplexIdentityAutAction
