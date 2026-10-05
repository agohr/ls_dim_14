import QuaternionicSymmetry.ManifoldTwistorComplexContactEigenSections

/-! The canonical contact-section representation of the actual complex
torus is the literal Laurent extension in any full compact eigenbasis.
This compares representations on the same genuine section space. -/

namespace QuaternionicSymmetry.ManifoldTwistorComplexContactSectionRepresentation

open ManifoldTwistorContactAutomorphismSections ManifoldTwistorComplexContactAction
open ManifoldTwistorComplexContactEigenSections ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore ManifoldTwistorLineCoreClasses
open ManifoldQuaternionicTorusAction ManifoldQuaternionicTwistorIsometryAction
open HolomorphicLineCorePullback TorusLaurentRepresentation
open ComplexTorusHolomorphicStructure TorusCharacterInput
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

theorem canonicalRepresentation_eq_laurent {ι : Type*}
    (b : letI := B.charts
      Module.Basis ι ℂ (GlobalSections 𝓘(ℂ, ComplexTwistorModel n)
        (contactLineCore Q D C.line)))
    (μ : ι → Fin r → ℤ)
    (hEig : letI := B.charts
      ∀ (t : Torus r) (i : ι),
        ManifoldQuaternionicIsometryContactSections.contactSectionEquiv Q D B C
          (A.representation t) (b i) = (weightCharacter (μ i) t : ℂ) • b i) :
    letI := B.charts
    (contactSectionRepresentation Q D B C).comp
        (complexContactAction Q D B C A ρ hJoint hRestrict) =
      complexRepresentation b μ := by
  letI := B.charts
  apply MonoidHom.ext
  intro g
  apply b.ext
  intro i
  change contactSectionEquiv Q D B C
      (complexContactAction Q D B C A ρ hJoint hRestrict g) (b i) =
    complexRepresentation b μ g (b i)
  rw [complexRepresentation_basis]
  exact contactSectionEquiv_eigenSection Q D B C A ρ hJoint hRestrict
    (μ i) (b i) (fun t => hEig t i) g

end
end QuaternionicSymmetry.ManifoldTwistorComplexContactSectionRepresentation
