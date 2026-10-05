import QuaternionicSymmetry.ManifoldPositiveQuaternionicComplexContactAction
import QuaternionicSymmetry.ManifoldTwistorCanonicalLaurentFromSources
import QuaternionicSymmetry.ComplexProjectiveDiagonalFaithfulness
import QuaternionicSymmetry.ManifoldQuaternionicTwistorActionFaithful

/-! A source-only normalized positive quaternionic-Kähler endpoint retaining
the genuine holomorphic contact-torus action and its canonical representation
on all contact-line sections. Its integral Laurent formula is proved for the
same action and section space, without a supplied eigenbasis or linearization.
Faithfulness of the compact action implies faithfulness of the whole complex
action by its actual projective embedding. Algebraic group structure and the
adjoint/contact Lie algebra comparison remain separate obligations. -/

namespace QuaternionicSymmetry.ManifoldPositiveQuaternionicCanonicalContactRepresentation

open ManifoldPositiveQuaternionicComplexTorusJointHolomorphicData
open ManifoldTwistorCanonicalLaurentFromSources
open ManifoldTwistorComplexContactAction ManifoldTwistorComplexContactActionTopology
open ManifoldTwistorContactAutomorphisms ManifoldTwistorContactAutomorphismTopology
open ManifoldTwistorContactAutomorphismSections
open ManifoldQuaternionicTorusAction ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicTwistorActionFaithful ComplexProjectiveDiagonalFaithfulness
open ManifoldTwistorPositiveContactAmple ManifoldTwistorPositiveRicciInput
open ManifoldPositiveQuaternionicKahlerGeometry ManifoldQuaternionicScalarCurvature
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineTensorPowerClasses HolomorphicLineCoreProjectiveEvaluation
open HolomorphicLineCoreProjectiveBasisChange
open HolomorphicPositiveLineKodairaSource ProjectiveAnalyticAlgebraicSources
open CompactTorusEigenbasisSource TorusCharacterInput
open TorusLaurentRepresentation ComplexTorusHolomorphicStructure GeneralSmoothMapSource
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [Nonempty M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem exists_normalized_canonical_contact_representation
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
          (A.Faithful → Function.Injective Φ) ∧
          (∀ t : Torus r, Φ (compactInclusion r t) =
            isometryContactLift P.tangent P.connection B C.contact.line
              (A.representation t)) ∧
          (letI := B.charts;
            ContMDiff (𝓘(ℂ, Fin r → ℂ).prod 𝓘(ℂ, ComplexTwistorModel n))
              𝓘(ℂ, ComplexTwistorModel n) ∞
              (fun p : ComplexTorus r × SphereBundleTotal P.tangent =>
                (Φ p.1).1 p.2)) ∧
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
                  complexRepresentation b μ) := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI : T3Space M := inferInstance
  obtain ⟨B, C, k, hk, hVery, d, b, hGen, μ, ρ, hEig, hRestrict, hProjective, hJoint⟩ :=
    exists_normalized_twistor_joint_holomorphic_complex_torus_action
      hT1 hKodaira hR3 hFinite hEigen hCircle hLee
      P n hn hDim hScalar A
  letI := B.charts
  letI := B.complexManifold
  let Φ := complexContactAction P.tangent P.connection B C.contact A ρ hJoint hRestrict
  refine ⟨B, C, Φ, ?_, ?_, ?_, hJoint, ?_⟩
  · exact complexContactAction_continuous P.tangent P.connection B C.contact
      A ρ hJoint hRestrict
  · intro hA
    have hCompact : Function.Injective (fun t : Torus r => ρ (compactInclusion r t)) := by
      intro t u h
      apply torus_lift_injective P.tangent A hA
      funext z
      change sphereTotalMap P.tangent (A.representation t) z =
        sphereTotalMap P.tangent (A.representation u) z
      rw [← hRestrict t z, ← hRestrict u z]
      exact congrArg (fun e : Equiv.Perm (SphereBundleTotal P.tangent) => e z) h
    have hρ : Function.Injective ρ := action_injective_of_compact
      (fun i => -(μ i)) ρ
      (projectiveEvaluationOfGenerated 𝓘(ℂ, ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ, ComplexTwistorModel n)
          (contactLineCore P.tangent P.connection C.contact.line) k) d b hGen)
      (veryAmple_projectiveEvaluation_injective 𝓘(ℂ, ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ, ComplexTwistorModel n)
          (contactLineCore P.tangent P.connection C.contact.line) k) hVery d b hGen)
      hProjective hCompact
    intro g h heq
    apply hρ
    apply Equiv.ext
    intro z
    exact congrArg (fun f : ContactAutomorphisms P.tangent P.connection B C.contact.line =>
      f.1 z) heq
  · exact complexContactAction_compact P.tangent P.connection B C.contact
      A ρ hJoint hRestrict
  · exact exists_canonical_laurent_representation P.tangent hR3 hFinite hEigen hCircle
      P.connection B C.contact A ρ hJoint hRestrict

end
end QuaternionicSymmetry.ManifoldPositiveQuaternionicCanonicalContactRepresentation
