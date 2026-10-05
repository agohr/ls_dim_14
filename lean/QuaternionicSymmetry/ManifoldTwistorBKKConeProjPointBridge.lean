import QuaternionicSymmetry.ManifoldTwistorBKKProjectiveWitness
import QuaternionicSymmetry.HolomorphicLineCoreProjectiveAlgebraicImage
import QuaternionicSymmetry.ComplexProjectiveActualConeClassicalPointInjective
import QuaternionicSymmetry.ComplexProjectiveActualConeProjScheme

/-!
# First concrete Chow-to-Proj link for the same contact-line linear system

The existing source-relative Remmert/Chow theorems give homogeneous
equations for the actual complete-linear-system image. The internal cone
construction then gives a genuine `Scheme`, and every actual twistor point
maps injectively to a point of that very `Proj`. This is **not** a complex
analytification equivalence or a GAGA/Picard comparison; those remain
explicit next obligations before BKK can be applied.
-/

namespace QuaternionicSymmetry.ManifoldTwistorBKKConeProjPointBridge

open AlgebraicGeometry
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjScheme
open ComplexProjectiveActualConeClassicalPointInjective
open ManifoldTwistorBKKProjectiveWitness
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldTwistorPositiveRicciInput
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorLineCoreClasses ManifoldQuaternionicScalarCurvature
open HolomorphicLineCoreClasses HolomorphicLineTensorPowerClasses
open HolomorphicLineCorePullback HolomorphicLineCoreProjectiveEvaluation
open HolomorphicLineCoreAmpleFiniteMap HolomorphicLineCoreProjectiveAlgebraicImage
open ProjectiveAnalyticAlgebraicSources
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- The actual normalized twistor maps injectively into the points
of the explicit cone-quotient `Proj` cut out by the complete linear
system of a positive power of its *same contact line*. The algebraic image
exists by Remmert/Chow on this literal map; no algebraic contact or Picard
data is inferred from the point injection. -/
theorem exists_normalized_contact_coneProj_point_injection
    (hT1 : NormalizedPositiveRicciContactExistence)
    (hKodaira : HolomorphicPositiveLineKodairaSource.PositiveHermitianLineAmpleTheorem.{0,0,0})
    (hRemmert : RemmertProjectiveImageTheorem)
    (hChow : ChowProjectiveAnalyticTheorem)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (hScalar : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature P.tangent P.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2)) :
    ∃ A : CompatibleComplexAtlas P.tangent P.connection n,
      ∃ C : NondegenerateHolomorphicContactData P.tangent P.connection n A,
        letI := A.charts
        letI := A.complexManifold
        let L := contactLineCore P.tangent P.connection C.contact.line
        ∃ (k d : ℕ)
          (b : Module.Basis (Fin (d + 1)) ℂ
            (GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
              (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) L k)))
          (hGen : GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
            (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) L k)),
          0 < k ∧
          let f := projectiveEvaluationOfGenerated 𝓘(ℂ,ComplexTwistorModel n)
            (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) L k) d b hGen
          ∃ (hA : HasHomogeneousEquations (Set.range f))
            (hNonempty : (Set.range f).Nonempty),
            letI : GradedAlgebra (quotientPiece (Set.range f)) :=
              quotientGradedAlgebra (Set.range f) hA hNonempty
            Function.Injective (fun z : SphereBundleTotal P.tangent =>
              classicalPointToActualProjFixed (Set.range f) hA hNonempty
                ⟨f z, ⟨z, rfl⟩⟩) := by
  letI : CompactSpace M := ⟨P.compact⟩
  obtain ⟨A,C,k,d,b,hGen,hk,hSmooth,hEmb,hImm,hClosed⟩ :=
    exists_normalized_closed_contact_projective_embedding
      hT1 hKodaira P n hn hDim hScalar
  refine ⟨A,C,k,d,b,hGen,hk,?_⟩
  letI := A.charts
  letI := A.complexManifold
  let L := powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
    (contactLineCore P.tangent P.connection C.contact.line) k
  let f := projectiveEvaluationOfGenerated 𝓘(ℂ,ComplexTwistorModel n)
    L d b hGen
  let hA : HasHomogeneousEquations (Set.range f) :=
    generated_projective_image_has_equations hRemmert hChow L d b hGen
  let z₀ : SphereBundleTotal P.tangent := Classical.choice inferInstance
  let hNonempty : (Set.range f).Nonempty := ⟨f z₀, ⟨z₀, rfl⟩⟩
  refine ⟨hA,hNonempty,?_⟩
  intro x y hxy
  have hxy' := classicalPointToActualProj_injective (Set.range f)
    hA hNonempty hxy
  exact hEmb.injective (congrArg Subtype.val hxy')

end
end QuaternionicSymmetry.ManifoldTwistorBKKConeProjPointBridge
