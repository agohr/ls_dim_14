import QuaternionicSymmetry.ManifoldPositiveQuaternionicCanonicalContactRepresentation
import QuaternionicSymmetry.ManifoldQuaternionicMaximalTorusAction

/-! Retain the same maximal compact isometry torus in the actual faithful
complex contact action. The assertion below spells out actual groups,
manifolds and sections; it is an output property, never a literature premise.
It does not claim that the complex torus is maximal in the contact group. -/

namespace QuaternionicSymmetry.ManifoldMaximalTorusContactExtension

open ManifoldPositiveQuaternionicCanonicalContactRepresentation
open ManifoldPositiveQuaternionicKahlerGeometry ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicMaximalTorusAction ManifoldQuaternionicSpanSymmetry
open ManifoldTwistorContactAutomorphisms ManifoldTwistorContactAutomorphismTopology
open ManifoldTwistorContactAutomorphismSections ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore ManifoldTwistorLineCoreClasses HolomorphicLineCorePullback
open ManifoldTwistorPositiveRicciInput HolomorphicPositiveLineKodairaSource
open CompactLieTorusInputs CompactTorusEigenbasisSource TorusCharacterInput
open ProjectiveAnalyticAlgebraicSources GeneralSmoothMapSource
open TorusLaurentRepresentation ComplexTorusHolomorphicStructure
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [Nonempty M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- A literal rank-at-least-two contact action with its exact maximal compact
isometry restriction and canonical Laurent action on actual H⁰(L). -/
def HasFaithfulContactTorusExtension
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) : Prop :=
  ∃ r : ℕ, 2 ≤ r ∧
    ∃ T : TorusEmbedding (QuaternionicIsometries P.tangent) r,
      T.IsMaximal (QuaternionicIsometries P.tangent) ∧
      ∃ B : CompatibleComplexAtlas P.tangent P.connection n,
        ∃ C : NondegenerateHolomorphicContactData P.tangent P.connection n B,
          ∃ Φ : ComplexTorus r →*
              ContactAutomorphisms P.tangent P.connection B C.contact.line,
            Continuous Φ ∧ Function.Injective Φ ∧
            (∀ t : ManifoldQuaternionicTorusAction.Torus r,
              Φ (compactInclusion r t) =
                isometryContactLift P.tangent P.connection B C.contact.line (T.hom t)) ∧
            (letI := B.charts;
              ContMDiff (𝓘(ℂ, Fin r → ℂ).prod 𝓘(ℂ, ComplexTwistorModel n))
                𝓘(ℂ, ComplexTwistorModel n) ∞
                (fun p : ComplexTorus r × SphereBundleTotal P.tangent => (Φ p.1).1 p.2)) ∧
            (letI := B.charts;
              ∃ b : Module.Basis
                (Fin (Module.finrank ℂ
                  (GlobalSections 𝓘(ℂ, ComplexTwistorModel n)
                    (contactLineCore P.tangent P.connection C.contact.line))))
                ℂ (GlobalSections 𝓘(ℂ, ComplexTwistorModel n)
                  (contactLineCore P.tangent P.connection C.contact.line)),
                ∃ μ : Fin (Module.finrank ℂ
                  (GlobalSections 𝓘(ℂ, ComplexTwistorModel n)
                    (contactLineCore P.tangent P.connection C.contact.line))) → Fin r → ℤ,
                  (contactSectionRepresentation P.tangent P.connection B C.contact).comp Φ =
                    complexRepresentation b μ)

theorem contact_extension_of_maximal_torus
    (hT1 : NormalizedPositiveRicciContactExistence)
    (hKodaira : PositiveHermitianLineAmpleTheorem.{0,0,0})
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : KnappTorusEigenbasis) (hCircle : CircleCharacterSource)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (hScalar : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature P.tangent P.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2))
    {r : ℕ} (hr : 2 ≤ r)
    (T : TorusEmbedding (QuaternionicIsometries P.tangent) r)
    (hMax : T.IsMaximal (QuaternionicIsometries P.tangent)) :
    HasFaithfulContactTorusExtension P n := by
  letI : CompactSpace M := ⟨P.compact⟩
  obtain ⟨B, C, Φ, hContinuous, hFaithful, hRestrict, hJoint, hLaurent⟩ :=
    exists_normalized_canonical_contact_representation
      hT1 hKodaira hR3 hFinite hEigen hCircle hLee
      P n hn hDim hScalar (actionOfEmbedding P.tangent T)
  exact ⟨r, hr, T, hMax, B, C, Φ, hContinuous,
    hFaithful (actionOfEmbedding_faithful P.tangent T), hRestrict, hJoint, hLaurent⟩

end
end QuaternionicSymmetry.ManifoldMaximalTorusContactExtension
