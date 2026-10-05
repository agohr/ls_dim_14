import QuaternionicSymmetry.GeneralContactFanoPicardProjectiveWitness
import QuaternionicSymmetry.ManifoldTwistorPositiveContactAmple
import QuaternionicSymmetry.ManifoldTwistorCompactHausdorff

/-!
# The actual positive twistor has a closed analytic projective image

This is the concrete analytic entry point for a later BKK application. The
projective map is the positive complete linear system of the *same* selected
holomorphic contact quotient line. The remaining Chow/GAGA algebraization,
Fano scheme and Picard/exception branches are not asserted here.
-/

namespace QuaternionicSymmetry.ManifoldTwistorBKKProjectiveWitness

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldTwistorPositiveContactAmple ManifoldTwistorPositiveRicciInput
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorLineCoreClasses ManifoldQuaternionicScalarCurvature
open GeneralContactFanoPicardProjectiveWitness
open HolomorphicLineCoreClasses HolomorphicLineTensorPowerClasses
open HolomorphicLineCorePullback HolomorphicLineCoreProjectiveEvaluation
open HolomorphicLineCoreAmpleFiniteMap
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- From the existing positive-Ricci twistor and general Kodaira inputs,
the actual twistor sphere bundle embeds holomorphically as a closed analytic
subset of finite-dimensional complex projective space by a positive power
of its genuine contact quotient line. This does not claim that the image is
already an algebraic Fano contact scheme. -/
theorem exists_normalized_closed_contact_projective_embedding
    (hT1 : NormalizedPositiveRicciContactExistence)
    (hKodaira : HolomorphicPositiveLineKodairaSource.PositiveHermitianLineAmpleTheorem.{0,0,0})
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
          ContMDiff 𝓘(ℂ,ComplexTwistorModel n) 𝓘(ℂ, Fin d → ℂ) ∞ f ∧
          Topology.IsEmbedding f ∧
          (∀ x : SphereBundleTotal P.tangent, Function.Injective
            (mfderiv 𝓘(ℂ,ComplexTwistorModel n) 𝓘(ℂ, Fin d → ℂ) f x)) ∧
          IsClosed (Set.range f) := by
  obtain ⟨A, C, hAmple⟩ := exists_normalized_ample_contact_core
    hT1 hKodaira P n hn hDim hScalar
  refine ⟨A, C, ?_⟩
  letI := A.charts
  letI := A.complexManifold
  letI : CompactSpace M := ⟨P.compact⟩
  exact exists_closed_holomorphic_projective_embedding
    (contactLineCore P.tangent P.connection C.contact.line) hAmple

end
end QuaternionicSymmetry.ManifoldTwistorBKKProjectiveWitness
