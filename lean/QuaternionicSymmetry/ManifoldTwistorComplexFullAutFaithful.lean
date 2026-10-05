import QuaternionicSymmetry.ManifoldTwistorComplexFullAutAction

/-! The actual full-Aut complex action retains faithfulness of the
constructed permutation action on twistor points. -/

namespace QuaternionicSymmetry.ManifoldTwistorComplexFullAutFaithful

open ManifoldQuaternionicTorusAction
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorFullAutomorphisms ManifoldTwistorComplexFullAutAction
open ManifoldTwistorComplexContactAction
open TorusLaurentRepresentation
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

theorem fullAutAction_injective_of_rho
    (hρ : Function.Injective ρ) :
    Function.Injective
      (complexFullAutAction Q D B C A ρ hJoint hRestrict) := by
  intro z w heq
  apply hρ
  apply Equiv.ext
  intro x
  have hx := congrArg
    (fun φ : TwistorHolomorphicAutomorphisms Q D B => φ.1 x) heq
  simpa only [complexFullAutAction, MonoidHom.comp_apply,
    complexContactAction_apply] using hx

end
end QuaternionicSymmetry.ManifoldTwistorComplexFullAutFaithful
