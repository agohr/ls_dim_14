import QuaternionicSymmetry.ProjectiveAnalyticAlgebraicSources
import QuaternionicSymmetry.HolomorphicLineCoreAmpleness

/-! Apply the two precise general analytic/algebraic inputs to the genuine
complete linear system. Its projective image is not an assumed algebraic
model; the literal homogeneous equations are obtained by source application. -/
namespace QuaternionicSymmetry.HolomorphicLineCoreProjectiveAlgebraicImage

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ProjectiveAnalyticAlgebraicSources
open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineCoreProjectiveEvaluation HolomorphicLineCoreAmpleFiniteMap
open scoped Manifold ContDiff
noncomputable section

variable {X F : Type} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
  [CompactSpace X]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [ChartedSpace F X] [IsManifold 𝓘(ℂ,F) ∞ X]

theorem generated_projective_image_has_equations
    (hRemmert : RemmertProjectiveImageTheorem)
    (hChow : ChowProjectiveAnalyticTheorem)
    (L : LineCore.{0} (B := X) 𝓘(ℂ,F)) (d : ℕ)
    (b : Module.Basis (Fin (d + 1)) ℂ (GlobalSections 𝓘(ℂ,F) L))
    (hGen : GloballyGenerated 𝓘(ℂ,F) L) :
    HasHomogeneousEquations
      (Set.range (projectiveEvaluationOfGenerated 𝓘(ℂ,F) L d b hGen)) :=
  compact_holomorphic_image_has_equations hRemmert hChow d _
    (projectiveEvaluationOfGenerated_contMDiff 𝓘(ℂ,F) L d b hGen)

theorem veryAmple_has_algebraic_embedding
    (hRemmert : RemmertProjectiveImageTheorem)
    (hChow : ChowProjectiveAnalyticTheorem)
    (L : LineCore.{0} (B := X) 𝓘(ℂ,F))
    (hVery : VeryAmpleCore 𝓘(ℂ,F) L) :
    ∃ (d : ℕ) (b : Module.Basis (Fin (d + 1)) ℂ (GlobalSections 𝓘(ℂ,F) L))
      (hGen : GloballyGenerated 𝓘(ℂ,F) L),
      Topology.IsEmbedding (projectiveEvaluationOfGenerated 𝓘(ℂ,F) L d b hGen) ∧
      (∀ x : X, Function.Injective (mfderiv 𝓘(ℂ,F) 𝓘(ℂ,Fin d → ℂ)
        (projectiveEvaluationOfGenerated 𝓘(ℂ,F) L d b hGen) x)) ∧
      HasHomogeneousEquations
        (Set.range (projectiveEvaluationOfGenerated 𝓘(ℂ,F) L d b hGen)) := by
  obtain ⟨d,b,hGen,hEmb,hImm⟩ := hVery
  exact ⟨d,b,hGen,hEmb,hImm,
    generated_projective_image_has_equations hRemmert hChow L d b hGen⟩

end
end QuaternionicSymmetry.HolomorphicLineCoreProjectiveAlgebraicImage
