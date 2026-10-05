import QuaternionicSymmetry.ManifoldTwistorContactAutomorphismFiberOrbit
import QuaternionicSymmetry.HolomorphicParameterTangentLocalSection

/-! The complexified canonical contact-line action carries any local
holomorphic tangent lift to a jointly holomorphic line section over the
parameter/base product. This is stronger than fixed-base orbit
holomorphicity but does not yet claim the whole line-total map is smooth. -/
namespace QuaternionicSymmetry.ManifoldTwistorComplexContactFiberJointSection

open ManifoldTwistorContactAutomorphismFiber
open ManifoldTwistorComplexContactAction
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldQuaternionicTorusAction ManifoldQuaternionicTwistorIsometryAction
open HolomorphicParameterTangentLocalSection
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
    ContMDiff (𝓘(ℂ,Fin r → ℂ).prod 𝓘(ℂ,ComplexTwistorModel n))
      𝓘(ℂ,ComplexTwistorModel n) ∞
      (fun p : ComplexTorus r × SphereBundleTotal Q => ρ p.1 p.2))
  (hRestrict : ∀ (t : Torus r) (z : SphereBundleTotal Q),
    ρ (compactInclusion r t) z = sphereTotalMap Q (A.representation t) z)

theorem contactFiberEquiv_localSection_joint_holomorphic
    (U : Set (SphereBundleTotal Q))
    (σ : letI := B.charts; ∀ z : SphereBundleTotal Q,
      TangentSpace 𝓘(ℂ,ComplexTwistorModel n) z)
    (hσ : letI := B.charts; letI := B.complexManifold
      ContMDiffOn 𝓘(ℂ,ComplexTwistorModel n)
        (𝓘(ℂ,ComplexTwistorModel n)).tangent ∞
        (fun z => (⟨z,σ z⟩ : TangentBundle
          𝓘(ℂ,ComplexTwistorModel n) (SphereBundleTotal Q))) U) :
    letI := B.charts
    ContMDiffOn
      (𝓘(ℂ,Fin r → ℂ).prod 𝓘(ℂ,ComplexTwistorModel n))
      (𝓘(ℂ,ComplexTwistorModel n).prod 𝓘(ℂ,ℂ)) ∞
      (fun q : ComplexTorus r × SphereBundleTotal Q =>
        (⟨ρ q.1 q.2,
          contactFiberEquiv Q D B C.line
            (complexContactAction Q D B C A ρ hJoint hRestrict q.1) q.2
            (C.line.contactFormComplex Q D q.2 (σ q.2))⟩ :
          Bundle.TotalSpace ℂ C.line.core.Fiber))
      (Set.univ ×ˢ U) := by
  letI := B.charts
  letI := B.complexManifold
  letI := C.line.holomorphic
  have hPartial := partialTangent_localSection_contMDiffOn
    (fun q : ComplexTorus r × SphereBundleTotal Q => ρ q.1 q.2)
    hJoint U σ hσ
  have hImage := C.contactHolomorphic.comp_contMDiffOn hPartial
  apply hImage.congr
  intro q hq
  change (⟨ρ q.1 q.2,
    contactFiberEquiv Q D B C.line
      (complexContactAction Q D B C A ρ hJoint hRestrict q.1) q.2
      (C.line.contactFormComplex Q D q.2 (σ q.2))⟩ :
      Bundle.TotalSpace ℂ C.line.core.Fiber) = _
  rw [contactFiberEquiv_contactForm]
  rfl

end
end QuaternionicSymmetry.ManifoldTwistorComplexContactFiberJointSection
