import QuaternionicSymmetry.ManifoldPositiveQuaternionicComplexTorusJointHolomorphicData
import QuaternionicSymmetry.ManifoldTwistorComplexContactActionTopology

/-! The actual positive quaternionic-Kähler twistor has a continuous
complex-torus representation by genuine holomorphic contact automorphisms,
relative only to the registered sources. The construction uses the same
complete-section projective action and exactly recovers the given compact
quaternionic-isometry action. -/

namespace QuaternionicSymmetry.ManifoldPositiveQuaternionicComplexContactAction

open ManifoldPositiveQuaternionicComplexTorusJointHolomorphicData
open ManifoldTwistorComplexContactAction ManifoldTwistorComplexContactActionTopology
open ManifoldTwistorContactAutomorphisms ManifoldTwistorContactAutomorphismTopology
open ManifoldQuaternionicTorusAction ManifoldQuaternionicTwistorIsometryAction
open ManifoldTwistorPositiveContactAmple ManifoldTwistorPositiveRicciInput
open ManifoldPositiveQuaternionicKahlerGeometry ManifoldQuaternionicScalarCurvature
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open HolomorphicPositiveLineKodairaSource ProjectiveAnalyticAlgebraicSources
open CompactTorusEigenbasisSource TorusCharacterInput
open TorusLaurentRepresentation ComplexTorusHolomorphicStructure GeneralSmoothMapSource
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [Nonempty M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem exists_normalized_twistor_contact_torus_action
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
    {r : ℕ} (A : ContinuousTorusAction P.tangent r) :
    ∃ B : CompatibleComplexAtlas P.tangent P.connection n,
      ∃ C : NondegenerateHolomorphicContactData P.tangent P.connection n B,
        ∃ Φ : ComplexTorus r →*
            ContactAutomorphisms P.tangent P.connection B C.contact.line,
          Continuous Φ ∧
          (∀ t : Torus r, Φ (compactInclusion r t) =
            isometryContactLift P.tangent P.connection B C.contact.line
              (A.representation t)) ∧
          (letI := B.charts;
            ContMDiff (𝓘(ℂ, Fin r → ℂ).prod 𝓘(ℂ, ComplexTwistorModel n))
              𝓘(ℂ, ComplexTwistorModel n) ∞
              (fun p : ComplexTorus r × SphereBundleTotal P.tangent =>
                (Φ p.1).1 p.2)) := by
  obtain ⟨B, C, k, hk, hVery, d, b, hGen, μ, ρ, hEig, hRestrict, hProjective, hJoint⟩ :=
    exists_normalized_twistor_joint_holomorphic_complex_torus_action
      hT1 hKodaira hR3 hFinite hEigen hCircle hLee
      P n hn hDim hScalar A
  let Φ := complexContactAction P.tangent P.connection B C.contact A ρ hJoint hRestrict
  refine ⟨B, C, Φ, ?_, ?_, ?_⟩
  · exact complexContactAction_continuous P.tangent P.connection B C.contact
      A ρ hJoint hRestrict
  · exact complexContactAction_compact P.tangent P.connection B C.contact
      A ρ hJoint hRestrict
  · exact hJoint

end
end QuaternionicSymmetry.ManifoldPositiveQuaternionicComplexContactAction
