import QuaternionicSymmetry.ManifoldQuaternionicContactSchemeClassicalComparison
import QuaternionicSymmetry.ManifoldPositiveQuaternionicComplexTorusJointHolomorphicData

/-! Source-only normalized positive quaternionic-Kähler specialization: the
constructed holomorphic-contact torus action agrees, under one genuine
complete contact-power projective embedding, with the global regular
cone-Proj action on every classical twistor point. No analytic-scheme
equivalence or full contact-group complexification is asserted. -/

namespace QuaternionicSymmetry.ManifoldPositiveQuaternionicContactSchemeClassicalFromSources

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeClassicalPointInjective
open ComplexProjectiveActualConeSpecEvaluationNaturality
open ComplexProjectiveActualConeGlobalSchemeAction
open ManifoldQuaternionicTorusAction ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicContactPowerWeights
open ManifoldQuaternionicContactSchemeClassicalComparison
open ManifoldPositiveQuaternionicComplexTorusJointHolomorphicData
open ManifoldTwistorComplexContactAction
open ManifoldTwistorPositiveContactAmple ManifoldTwistorPositiveRicciInput
open ManifoldPositiveQuaternionicKahlerGeometry ManifoldQuaternionicScalarCurvature
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorLineCoreClasses
open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineTensorPowerClasses HolomorphicLineCoreProjectiveEvaluation
open HolomorphicLineCoreAmpleFiniteMap HolomorphicLineCoreProjectiveAlgebraicImage
open HolomorphicPositiveLineKodairaSource ProjectiveAnalyticAlgebraicSources
open CompactTorusEigenbasisSource TorusCharacterInput
open TorusLaurentRepresentation GeneralSmoothMapSource
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [Nonempty M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_normalized_contact_regular_classical_comparison
    (hT1 : NormalizedPositiveRicciContactExistence)
    (hKodaira : PositiveHermitianLineAmpleTheorem.{0,0,0})
    (hRemmert : RemmertProjectiveImageTheorem)
    (hChow : ChowProjectiveAnalyticTheorem)
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : KnappTorusEigenbasis) (hCircle : CircleCharacterSource)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (hScalar : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature P.tangent P.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2))
    {r : ℕ} (Aₜ : ContinuousTorusAction P.tangent r) :
    letI : CompactSpace M := ⟨P.compact⟩
    letI : PreconnectedSpace M := ⟨P.connected⟩
    letI : T3Space M := inferInstance
    ∃ B : CompatibleComplexAtlas P.tangent P.connection n,
      ∃ C : NondegenerateHolomorphicContactData P.tangent P.connection n B,
        letI := B.charts
        letI := B.complexManifold
        ∃ (k d : ℕ)
          (b : Module.Basis (Fin (d + 1)) ℂ
            (PowerSections P.tangent P.connection B C.contact k))
          (hGen : GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
            (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
              (contactLineCore P.tangent P.connection C.contact.line) k))
          (μ : Fin (d + 1) → Fin r → ℤ)
          (ρ : ComplexTorus r →* Equiv.Perm (SphereBundleTotal P.tangent))
          (hRestrict : ∀ (t : Torus r) (x : SphereBundleTotal P.tangent),
            ρ (compactInclusion r t) x =
              sphereTotalMap P.tangent (Aₜ.representation t) x)
          (hProjective : ∀ (z : ComplexTorus r) (x : SphereBundleTotal P.tangent),
            projectiveEvaluationOfGenerated 𝓘(ℂ,ComplexTwistorModel n)
              (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
                (contactLineCore P.tangent P.connection C.contact.line) k)
              d b hGen (ρ z x) =
            projectiveAction μ z
              (projectiveEvaluationOfGenerated 𝓘(ℂ,ComplexTwistorModel n)
                (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
                  (contactLineCore P.tangent P.connection C.contact.line) k)
                d b hGen x))
          (hJoint : ContMDiff
            (𝓘(ℂ, Fin r → ℂ).prod 𝓘(ℂ,ComplexTwistorModel n))
            𝓘(ℂ,ComplexTwistorModel n) ∞
            (fun q : ComplexTorus r × SphereBundleTotal P.tangent =>
              ρ q.1 q.2)),
          let L := powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
            (contactLineCore P.tangent P.connection C.contact.line) k
          let f := projectiveEvaluationOfGenerated
            𝓘(ℂ,ComplexTwistorModel n) L d b hGen
          let A := Set.range f
          let hA := generated_projective_image_has_equations
            hRemmert hChow L d b hGen
          ∀ (z : ComplexTorus r) (x : SphereBundleTotal P.tangent),
            let hNonempty : A.Nonempty := ⟨f x, ⟨x, rfl⟩⟩
            letI : GradedAlgebra (quotientPiece A) :=
              quotientGradedAlgebra A hA hNonempty
            ∃ p : ↥(pullback
                (Spec.map (CommRingCat.ofHom
                  (algebraMap ℂ (TorusCoordinateRing r))))
                (ComplexProjectiveActualConeComplexStructure.actualConeProjToSpecComplex
                  A hA hNonempty) : Scheme),
              (pullback.fst _ _ : _ ⟶ Spec (CommRingCat.of (TorusCoordinateRing r))) p =
                  specEvaluationPoint (evalTorus z) ∧
              (pullback.snd _ _ : _ ⟶ Proj (quotientPiece A)) p =
                  classicalPointToActualProjFixed A hA hNonempty
                    ⟨f x, ⟨x, rfl⟩⟩ ∧
              (globalSchemeAction μ A hA hNonempty
                (fun t y hy => by
                  obtain ⟨x', rfl⟩ := hy
                  exact ⟨ρ (compactInclusion r t) x', hProjective _ _⟩)) p =
                  classicalPointToActualProjFixed A hA hNonempty
                    ⟨f ((complexContactAction P.tangent P.connection B C.contact
                      Aₜ ρ hJoint hRestrict z).1 x),
                      ⟨(complexContactAction P.tangent P.connection B C.contact
                        Aₜ ρ hJoint hRestrict z).1 x, rfl⟩⟩ := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI : T3Space M := inferInstance
  obtain ⟨B,C,k,hk,hVery,d,b,hGen,μ,ρ,hEig,hRestrict,hProjective,hJoint⟩ :=
    exists_normalized_twistor_joint_holomorphic_complex_torus_action
      hT1 hKodaira hR3 hFinite hEigen hCircle hLee
      P n hn hDim hScalar Aₜ
  letI := B.charts
  letI := B.complexManifold
  refine ⟨B,C,k,d,b,hGen,fun i => -(μ i),ρ,hRestrict,hProjective,hJoint,?_⟩
  dsimp only
  intro z x
  exact contactAction_agrees_with_global_regular_action P.tangent
    hRemmert hChow P.connection B C.contact k Aₜ b hGen
      (fun i => -(μ i)) ρ hProjective hJoint hRestrict z x

end
end QuaternionicSymmetry.ManifoldPositiveQuaternionicContactSchemeClassicalFromSources
