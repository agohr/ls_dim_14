import QuaternionicSymmetry.ManifoldTwistorComplexContactActionTopology
import QuaternionicSymmetry.ManifoldTwistorFullAutomorphismLift

/-! The already constructed holomorphic contact complex-torus action,
viewed as an honest homomorphism into the full biholomorphism group.
It agrees exactly with the natural isometry lift on the compact real torus.
No assertion about holomorphicity of the induced map into a later BWW
complex Lie atlas is made here. -/

namespace QuaternionicSymmetry.ManifoldTwistorComplexFullAutAction

open ManifoldQuaternionicTorusAction
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorContactAutomorphisms
open ManifoldTwistorFullAutomorphisms ManifoldTwistorFullAutomorphismLift
open ManifoldTwistorComplexContactAction
open GeneralHolomorphicDistributionAutomorphismTopology
open TorusLaurentRepresentation ComplexTorusHolomorphicStructure
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
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

def complexFullAutAction : ComplexTorus r →*
    TwistorHolomorphicAutomorphisms Q D B :=
  (contactForget Q D B C.line).comp
    (complexContactAction Q D B C A ρ hJoint hRestrict)

theorem complexFullAutAction_compact (t : Torus r) :
    complexFullAutAction Q D B C A ρ hJoint hRestrict
      (compactInclusion r t) =
      isometryFullLift Q D B C.line (A.representation t) := by
  simp only [complexFullAutAction, MonoidHom.comp_apply,
    complexContactAction_compact, isometryFullLift]

theorem complexFullAutAction_continuous :
    Continuous (complexFullAutAction Q D B C A ρ hJoint hRestrict) := by
  letI := B.charts
  letI := B.complexManifold
  apply continuous_representation_of_action
    (GeneralHolomorphicFullAutomorphisms.fullDistribution
      (V := ComplexTwistorModel n) (Z := SphereBundleTotal Q))
    (complexFullAutAction Q D B C A ρ hJoint hRestrict)
  exact hJoint.continuous

end
end QuaternionicSymmetry.ManifoldTwistorComplexFullAutAction
