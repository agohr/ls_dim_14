import QuaternionicSymmetry.HolomorphicLineCoreProjectiveEigenbasis
import QuaternionicSymmetry.HolomorphicLineCoreProjectiveBasisChangeImmersion
import QuaternionicSymmetry.HolomorphicLineCoreProjectiveAlgebraicImage
import QuaternionicSymmetry.ComplexProjectiveImageTorusAction
import QuaternionicSymmetry.ComplexProjectiveAnalyticTorusPreservation
import QuaternionicSymmetry.ComplexProjectiveInvariantImageAction

/-! A very ample genuine holomorphic line with an integral eigenbasis of
all sections yields a complex-torus action on the actual compact manifold.
Local equations of the embedding and analytic continuation give image
preservation; restriction to the original compact action is proved internally. This is
an action on points, with no implicit claim of a smooth scheme action. -/
namespace QuaternionicSymmetry.HolomorphicLineCoreComplexTorusExtension

open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineCoreProjectiveEvaluation HolomorphicLineCoreAmpleFiniteMap
open HolomorphicLineCoreProjectiveEigenbasis HolomorphicLineCoreProjectiveBasisChange
open HolomorphicLineCoreProjectiveAlgebraicImage ProjectiveAnalyticAlgebraicSources
open ComplexProjectiveDiagonalAction ComplexProjectiveImageTorusAction
open ManifoldQuaternionicTorusAction TorusLaurentRepresentation TorusCharacterInput
open scoped Manifold ContDiff
noncomputable section

variable {X F : Type} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
  [CompactSpace X]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [ChartedSpace F X] [IsManifold 𝓘(ℂ,F) ∞ X]

theorem exists_complex_action_of_veryAmple_eigenbasis
    (L : LineCore.{0} (B := X) 𝓘(ℂ,F))
    (hVery : VeryAmpleCore 𝓘(ℂ,F) L)
    {r d : ℕ} (b : Module.Basis (Fin (d + 1)) ℂ (GlobalSections 𝓘(ℂ,F) L))
    (hGen : GloballyGenerated 𝓘(ℂ,F) L)
    (α : Torus r → X → X)
    (Φ : ∀ (t : Torus r) (x : X), L.core.Fiber x ≃ₗ[ℂ] L.core.Fiber (α t x))
    (T : Torus r → GlobalSections 𝓘(ℂ,F) L ≃ₗ[ℂ] GlobalSections 𝓘(ℂ,F) L)
    (hT : ∀ (t : Torus r) (s : GlobalSections 𝓘(ℂ,F) L) (x : X),
      (T t s) (α t x) = Φ t x (s x))
    (μ : Fin (d + 1) → Fin r → ℤ)
    (hEig : ∀ t i, T t (b i) = (weightCharacter (μ i) t : ℂ) • b i) :
    ∃ ρ : ComplexTorus r →* Equiv.Perm X,
      (∀ (t : Torus r) (x : X), ρ (compactInclusion r t) x = α t x) ∧
      ∀ (z : ComplexTorus r) (x : X),
        projectiveEvaluationOfGenerated 𝓘(ℂ,F) L d b hGen (ρ z x) =
          projectiveAction (fun i => -(μ i)) z
            (projectiveEvaluationOfGenerated 𝓘(ℂ,F) L d b hGen x) := by
  let f := projectiveEvaluationOfGenerated 𝓘(ℂ,F) L d b hGen
  have hf : Function.Injective f :=
    veryAmple_projectiveEvaluation_injective 𝓘(ℂ,F) L hVery d b hGen
  have hSmooth := projectiveEvaluationOfGenerated_contMDiff 𝓘(ℂ,F) L d b hGen
  obtain ⟨hEmb,hImm⟩ := HolomorphicLineCoreProjectiveBasisChangeImmersion.veryAmple_projectiveEvaluation_embedding_immersion 𝓘(ℂ,F) L hVery d b hGen
  have hA := HolomorphicEmbeddingLocalEquations.range_localHolomorphicEquations
    hSmooth hEmb hImm
  have hClosed := (isCompact_range hSmooth.continuous).isClosed
  have hα : ∀ t x,
      f (α t x) = projectiveAction (fun i => -(μ i)) (compactInclusion r t) (f x) := by
    intro t x
    exact projectiveEvaluation_diagonal_compact 𝓘(ℂ,F) L b hGen
      (α t) (Φ t) (T t) (hT t) μ t (hEig t) x
  have hPres := ComplexProjectiveAnalyticTorusPreservation.mapsTo_of_compact
    (fun i => -(μ i)) (Set.range f) hA hClosed (compact_range_mapsTo _ f α hα)
  refine ⟨ComplexProjectiveInvariantImageAction.imageAction (fun i => -(μ i)) f hf hPres, ?_, ?_⟩
  · exact ComplexProjectiveInvariantImageAction.imageAction_restrict (fun i => -(μ i)) f hf hPres α hα
  · exact ComplexProjectiveInvariantImageAction.imageAction_equivariant (fun i => -(μ i)) f hf hPres

end
end QuaternionicSymmetry.HolomorphicLineCoreComplexTorusExtension
