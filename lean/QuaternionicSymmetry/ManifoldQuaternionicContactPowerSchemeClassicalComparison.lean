import QuaternionicSymmetry.ComplexProjectiveActualConeEquivariantClassicalComparison
import QuaternionicSymmetry.ManifoldQuaternionicContactPowerComplexTorusActionData
import QuaternionicSymmetry.HolomorphicLineCoreProjectiveAlgebraicImage

/-! The genuine complete contact-power projective image has the actual
global regular cone-Proj torus action agreeing with its constructed twistor
point action on classical points. This uses the registered Remmert/Chow
sources only for the literal homogeneous equations. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicContactPowerSchemeClassicalComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeClassicalPointInjective
open ComplexProjectiveActualConeSpecEvaluationNaturality
open ComplexProjectiveActualConeGlobalSchemeAction
open ComplexProjectiveActualConeEquivariantClassicalComparison
open ManifoldQuaternionicTorusAction ManifoldTwistorLeBrunComplexAtlas
open ManifoldQuaternionicContactPowerWeights
open ManifoldTwistorSphereCore ManifoldTwistorLineCoreClasses
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

theorem contactPower_action_agrees_on_classical_scheme_points
    (hRemmert : RemmertProjectiveImageTheorem)
    (hChow : ChowProjectiveAnalyticTheorem)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) (k : ℕ)
    {r d : ℕ}
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
            ⟨f (ρ z x), ⟨ρ z x, rfl⟩⟩ := by
  letI := B.charts
  letI := B.complexManifold
  exact exists_schemePoint_for_equivariant_image
    (projectiveEvaluationOfGenerated 𝓘(ℂ,ComplexTwistorModel n)
      (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore Q D C.line) k) d b hGen)
    μ ρ hρ
    (generated_projective_image_has_equations hRemmert hChow _ d b hGen) z x

end
end QuaternionicSymmetry.ManifoldQuaternionicContactPowerSchemeClassicalComparison
