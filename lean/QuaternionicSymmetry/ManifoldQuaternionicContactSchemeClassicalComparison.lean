import QuaternionicSymmetry.ManifoldQuaternionicContactPowerSchemeClassicalComparison
import QuaternionicSymmetry.ManifoldTwistorComplexContactAction

/-! The actual holomorphic-contact complex-torus action is the classical
point action of the genuine regular global cone-Proj morphism under the
complete contact-power projective evaluation. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicContactSchemeClassicalComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeClassicalPointInjective
open ComplexProjectiveActualConeSpecEvaluationNaturality
open ComplexProjectiveActualConeGlobalSchemeAction
open ManifoldQuaternionicTorusAction ManifoldQuaternionicContactPowerWeights
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicContactPowerSchemeClassicalComparison
open ManifoldTwistorComplexContactAction
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorLineCoreClasses
open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineTensorPowerClasses HolomorphicLineCoreProjectiveEvaluation
open HolomorphicLineCoreAmpleFiniteMap HolomorphicLineCoreProjectiveAlgebraicImage
open ProjectiveAnalyticAlgebraicSources
open TorusLaurentRepresentation
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T3Space M] [CompactSpace M]
  [SecondCountableTopology M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem contactAction_agrees_with_global_regular_action
    (hRemmert : RemmertProjectiveImageTheorem)
    (hChow : ChowProjectiveAnalyticTheorem)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) (k : ℕ)
    {r d : ℕ} (Aₜ : ContinuousTorusAction Q r)
    (b : Module.Basis (Fin (d + 1)) ℂ (PowerSections Q D B C k))
    (hGen : letI := B.charts; letI := B.complexManifold
      GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore Q D C.line) k))
    (μ : Fin (d + 1) → Fin r → ℤ)
    (ρ : ComplexTorus r →* Equiv.Perm (SphereBundleTotal Q))
    (hρ : letI := B.charts; letI := B.complexManifold
      ∀ (z : ComplexTorus r) (x : SphereBundleTotal Q),
      projectiveEvaluationOfGenerated 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore Q D C.line) k) d b hGen (ρ z x) =
      projectiveAction μ z
        (projectiveEvaluationOfGenerated 𝓘(ℂ,ComplexTwistorModel n)
          (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
            (contactLineCore Q D C.line) k) d b hGen x))
    (hJoint : letI := B.charts
      ContMDiff (𝓘(ℂ, Fin r → ℂ).prod 𝓘(ℂ, ComplexTwistorModel n))
        𝓘(ℂ, ComplexTwistorModel n) ∞
        (fun p : ComplexTorus r × SphereBundleTotal Q => ρ p.1 p.2))
    (hRestrict : ∀ (t : Torus r) (x : SphereBundleTotal Q),
      ρ (compactInclusion r t) x = sphereTotalMap Q (Aₜ.representation t) x)
    (z : ComplexTorus r) (x : SphereBundleTotal Q) :
    letI := B.charts
    letI := B.complexManifold
    let L := powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
      (contactLineCore Q D C.line) k
    let f := projectiveEvaluationOfGenerated 𝓘(ℂ,ComplexTwistorModel n)
      L d b hGen
    let A := Set.range f
    let hA := generated_projective_image_has_equations hRemmert hChow L d b hGen
    let hNonempty : A.Nonempty := ⟨f x, ⟨x, rfl⟩⟩
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    ∃ p : ↥(pullback
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r))))
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
          exact ⟨ρ (compactInclusion r t) x', hρ _ _⟩)) p =
          classicalPointToActualProjFixed A hA hNonempty
            ⟨f ((complexContactAction Q D B C Aₜ ρ hJoint hRestrict z).1 x),
              ⟨(complexContactAction Q D B C Aₜ ρ hJoint hRestrict z).1 x,
                rfl⟩⟩ := by
  letI := B.charts
  letI := B.complexManifold
  obtain ⟨p,hfst,hsnd,hact⟩ :=
    contactPower_action_agrees_on_classical_scheme_points Q
      hRemmert hChow D B C k b hGen μ ρ hρ z x
  refine ⟨p,hfst,hsnd,?_⟩
  simpa only [complexContactAction_apply] using hact

end
end QuaternionicSymmetry.ManifoldQuaternionicContactSchemeClassicalComparison
