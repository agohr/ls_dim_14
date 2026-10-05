import QuaternionicSymmetry.ManifoldTwistorContactAutomorphismFiber
import QuaternionicSymmetry.ManifoldTwistorComplexContactAction

/-! The canonical contact-line action varies holomorphically along every
orbit of the constructed complex torus. This follows from the joint
tangent map and surjectivity of the actual contact form. -/

namespace QuaternionicSymmetry.ManifoldTwistorContactAutomorphismFiberOrbit

open ManifoldTwistorContactAutomorphisms ManifoldTwistorContactAutomorphismFiber
open ManifoldTwistorComplexContactAction ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore ManifoldQuaternionicTorusAction
open ManifoldQuaternionicTwistorIsometryAction HolomorphicParameterTangent
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

theorem contactFiberEquiv_orbit_holomorphic (z : SphereBundleTotal Q)
    (w : C.line.core.Fiber z) :
    letI := B.charts
    letI := B.complexManifold
    letI := C.line.holomorphic
    ContMDiff 𝓘(ℂ, Fin r → ℂ)
      (𝓘(ℂ, ComplexTwistorModel n).prod 𝓘(ℂ, ℂ)) ∞
      (fun g : ComplexTorus r =>
        (⟨ρ g z, contactFiberEquiv Q D B C.line
          (complexContactAction Q D B C A ρ hJoint hRestrict g) z w⟩ :
            Bundle.TotalSpace ℂ C.line.core.Fiber)) := by
  letI := B.charts
  letI := B.complexManifold
  letI := C.line.holomorphic
  obtain ⟨v, rfl⟩ := C.line.contactFormComplex_surjective Q D z w
  simp_rw [contactFiberEquiv_contactForm]
  exact C.contactHolomorphic.comp
    (parameterTangent_contMDiff
      (fun p : ComplexTorus r × SphereBundleTotal Q => ρ p.1 p.2) hJoint z v)

end
end QuaternionicSymmetry.ManifoldTwistorContactAutomorphismFiberOrbit
