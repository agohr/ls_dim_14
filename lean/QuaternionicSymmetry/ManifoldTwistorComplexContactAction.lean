import QuaternionicSymmetry.ManifoldTwistorComplexTorusContactPreservation

/-! The same complex-torus point action now takes values in the actual
holomorphic contact-automorphism group. Neither algebraicity nor maximality
in that group is included in this construction. -/

namespace QuaternionicSymmetry.ManifoldTwistorComplexContactAction

open ManifoldQuaternionicTorusAction ManifoldQuaternionicTwistorIsometryAction
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorContactAutomorphisms ManifoldTwistorComplexTorusContactPreservation
open TorusLaurentRepresentation ComplexTorusHolomorphicStructure
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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

def complexActionDiffeomorph (g : ComplexTorus r) :
    letI := B.charts
    Diffeomorph 𝓘(ℂ, ComplexTwistorModel n) 𝓘(ℂ, ComplexTwistorModel n)
      (SphereBundleTotal Q) (SphereBundleTotal Q) ∞ := by
  letI := B.charts
  refine { toEquiv := ρ g, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · exact hJoint.comp (contMDiff_const.prodMk contMDiff_id)
  · have hInv : (ρ g).symm = ρ g⁻¹ := (map_inv ρ g).symm
    change ContMDiff 𝓘(ℂ, ComplexTwistorModel n) 𝓘(ℂ, ComplexTwistorModel n)
      ∞ ((ρ g).symm : SphereBundleTotal Q → SphereBundleTotal Q)
    rw [hInv]
    exact hJoint.comp (contMDiff_const.prodMk contMDiff_id)

def complexContactAction : ComplexTorus r →* ContactAutomorphisms Q D B C.line := by
  letI := B.charts
  letI := B.complexManifold
  refine {
    toFun := fun g => ⟨complexActionDiffeomorph Q D B ρ hJoint g, ?_⟩
    map_one' := ?_
    map_mul' := ?_ }
  · constructor
    · intro z v hv
      exact complex_action_preserves_contact Q D B C A ρ hJoint hRestrict g z v hv
    · intro z v hv
      change C.line.contactFormComplex Q D ((ρ g).symm z)
        (mfderiv 𝓘(ℂ, ComplexTwistorModel n) 𝓘(ℂ, ComplexTwistorModel n)
          ((ρ g).symm : SphereBundleTotal Q → SphereBundleTotal Q) z v) = 0
      have hInv : (ρ g).symm = ρ g⁻¹ := (map_inv ρ g).symm
      rw [hInv]
      exact complex_action_preserves_contact Q D B C A ρ hJoint hRestrict g⁻¹ z v hv
  · apply Subtype.ext
    apply Diffeomorph.ext
    intro z
    change ρ 1 z = z
    rw [map_one]
    rfl
  · intro g h
    apply Subtype.ext
    apply Diffeomorph.ext
    intro z
    change ρ (g * h) z = ρ g (ρ h z)
    rw [map_mul]
    rfl

theorem complexContactAction_apply (g : ComplexTorus r) (z : SphereBundleTotal Q) :
    ((complexContactAction Q D B C A ρ hJoint hRestrict g).1 :
      SphereBundleTotal Q → SphereBundleTotal Q) z = ρ g z := rfl

theorem complexContactAction_compact (t : Torus r) :
    complexContactAction Q D B C A ρ hJoint hRestrict (compactInclusion r t) =
      isometryContactLift Q D B C.line (A.representation t) := by
  letI := B.charts
  letI := B.complexManifold
  apply Subtype.ext
  apply Diffeomorph.ext
  intro z
  exact hRestrict t z

end
end QuaternionicSymmetry.ManifoldTwistorComplexContactAction
