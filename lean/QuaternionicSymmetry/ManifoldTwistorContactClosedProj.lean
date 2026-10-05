import QuaternionicSymmetry.ManifoldTwistorContactAlgebraicImage
import QuaternionicSymmetry.ComplexProjectiveRangeClosedPointEquiv

/-! The actual normalized PQK twistor is identified, as a set of points,
with the closed points of its contact-power projective image. The map is
continuous towards the Zariski topology. No inverse continuity, smooth
analytification or algebraic contact-line comparison is asserted. -/

namespace QuaternionicSymmetry.ManifoldTwistorContactClosedProj

open ManifoldTwistorContactAlgebraicImage
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open ManifoldTwistorSphereCore ManifoldTwistorPositiveRicciInput
open ManifoldPositiveQuaternionicKahlerGeometry ManifoldQuaternionicScalarCurvature
open HolomorphicPositiveLineKodairaSource ProjectiveAnalyticAlgebraicSources
open ComplexProjectivePolynomialLocus ComplexProjectiveLineProjPoint
open ComplexProjectiveProjCutoutClosedPointEquiv ComplexProjectiveRangeClosedPointEquiv
open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineCoreProjectiveEvaluation HolomorphicLineCoreAmpleFiniteMap
open HolomorphicLineTensorPowerClasses
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [Nonempty M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_normalized_contact_closed_proj_comparison
    (hRemmert : RemmertProjectiveImageTheorem)
    (hChow : ChowProjectiveAnalyticTheorem)
    (hT1 : NormalizedPositiveRicciContactExistence)
    (hKodaira : PositiveHermitianLineAmpleTheorem.{0,0,0})
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (hScalar : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature P.tangent P.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2)) :
    ∃ B : CompatibleComplexAtlas P.tangent P.connection n,
      ∃ C : NondegenerateHolomorphicContactData P.tangent P.connection n B,
      letI := B.charts
      letI := B.complexManifold
      ∃ k : ℕ, 0 < k ∧
        ∃ (d : ℕ)
          (b : Module.Basis (Fin (d + 1)) ℂ
            (GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
              (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
                (contactLineCore P.tangent P.connection C.contact.line) k)))
          (hGen : GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
            (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
              (contactLineCore P.tangent P.connection C.contact.line) k)),
          let f := projectiveEvaluationOfGenerated 𝓘(ℂ,ComplexTwistorModel n)
            (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
              (contactLineCore P.tangent P.connection C.contact.line) k) d b hGen
          Topology.IsEmbedding f ∧
          (∀ x : SphereBundleTotal P.tangent, Function.Injective
            (mfderiv 𝓘(ℂ,ComplexTwistorModel n) 𝓘(ℂ,Fin d → ℂ) f x)) ∧
          HasHomogeneousEquations (Set.range f) ∧
          ∃ e : SphereBundleTotal P.tangent ≃ ClosedCutoutPoint (Set.range f),
            Continuous e ∧ ∀ x, (e x).1.1 = projectivePointToProj (f x) := by
  obtain ⟨B,C,k,hk,d,b,hGen,hEmb,hImm,hEq⟩ :=
    exists_normalized_contact_algebraic_embedding
      hRemmert hChow hT1 hKodaira P n hn hDim hScalar
  letI := B.charts
  letI := B.complexManifold
  let f := projectiveEvaluationOfGenerated 𝓘(ℂ,ComplexTwistorModel n)
    (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
      (contactLineCore P.tangent P.connection C.contact.line) k) d b hGen
  refine ⟨B,C,k,hk,d,b,hGen,hEmb,hImm,hEq,
    rangeClosedPointEquiv f hEmb.injective hEq, ?_, ?_⟩
  · exact rangeClosedPointEquiv_continuous f hEmb.injective hEq hEmb.continuous
  · exact rangeClosedPointEquiv_apply f hEmb.injective hEq

end
end QuaternionicSymmetry.ManifoldTwistorContactClosedProj
