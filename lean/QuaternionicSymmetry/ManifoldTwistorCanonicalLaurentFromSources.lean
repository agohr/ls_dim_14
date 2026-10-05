import QuaternionicSymmetry.ManifoldQuaternionicContactSectionsFromSources
import QuaternionicSymmetry.ManifoldTwistorComplexContactSectionRepresentation

/-! The canonical action of the constructed complex contact torus on all
actual H⁰(L) is its integral Laurent representation. The complete eigenbasis
is obtained from the registered sources, not supplied as extra geometric
data. This does not yet identify H⁰(L) with a contact Lie algebra. -/

namespace QuaternionicSymmetry.ManifoldTwistorCanonicalLaurentFromSources

open ManifoldQuaternionicContactSectionsFromSources
open ManifoldTwistorComplexContactSectionRepresentation
open ManifoldTwistorContactAutomorphismSections ManifoldTwistorComplexContactAction
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorLineCoreClasses ManifoldQuaternionicTorusAction
open ManifoldQuaternionicTwistorIsometryAction HolomorphicLineCorePullback
open CompactTorusEigenbasisSource TorusCharacterInput TorusLaurentRepresentation
open ComplexTorusHolomorphicStructure
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T3Space M] [CompactSpace M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

theorem exists_canonical_laurent_representation
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : KnappTorusEigenbasis) (hCircle : CircleCharacterSource)
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
      ρ (compactInclusion r t) z = sphereTotalMap Q (A.representation t) z) :
    letI := B.charts
    ∃ b : Module.Basis
      (Fin (Module.finrank ℂ
        (GlobalSections 𝓘(ℂ, ComplexTwistorModel n) (contactLineCore Q D C.line))))
      ℂ (GlobalSections 𝓘(ℂ, ComplexTwistorModel n) (contactLineCore Q D C.line)),
      ∃ μ : Fin (Module.finrank ℂ
        (GlobalSections 𝓘(ℂ, ComplexTwistorModel n) (contactLineCore Q D C.line))) →
          Fin r → ℤ,
        (contactSectionRepresentation Q D B C).comp
          (complexContactAction Q D B C A ρ hJoint hRestrict) =
            complexRepresentation b μ := by
  letI := B.charts
  obtain ⟨b, μ, hEig⟩ := exists_integral_contact_eigenbasis_from_sources
    Q hR3 hFinite hEigen hCircle A D B C
  exact ⟨b, μ, canonicalRepresentation_eq_laurent Q D B C A ρ hJoint hRestrict
    b μ hEig⟩

end
end QuaternionicSymmetry.ManifoldTwistorCanonicalLaurentFromSources
