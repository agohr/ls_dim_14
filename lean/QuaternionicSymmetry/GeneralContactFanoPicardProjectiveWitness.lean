import QuaternionicSymmetry.HolomorphicLineCoreAmpleness
import QuaternionicSymmetry.ComplexProjectiveHausdorff
import Mathlib.Topology.Compactness.Compact

/-!
# A closed analytic projective image from genuine ampleness

This is an internal prerequisite for applying the published BKK Fano-contact
trichotomy. It extracts the *actual* complete-linear-system map of an ample
represented holomorphic line and proves that its image is closed. It does not
turn the image into an algebraic scheme or assert any Picard conclusion.
-/

namespace QuaternionicSymmetry.GeneralContactFanoPicardProjectiveWitness

open HolomorphicLineCoreClasses HolomorphicLineTensorPowerClasses
open HolomorphicLineCoreAmpleFiniteMap HolomorphicLineCoreProjectiveEvaluation
open HolomorphicLineCorePullback
open ComplexProjectiveTopology
open scoped Manifold ContDiff

noncomputable section
universe uB uF uI

variable {B : Type uB} {F : Type uF}
  [TopologicalSpace B] [CompactSpace B]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [ChartedSpace F B] [IsManifold 𝓘(ℂ,F) ∞ B]

/-- Genuine ampleness gives a closed holomorphic embedding by a positive
complete linear system, with injective manifold differential everywhere.
Closedness uses compactness of the actual source and Hausdorffness of finite
complex projective space. No projective-algebraic presentation is concluded. -/
theorem exists_closed_holomorphic_projective_embedding
    (L : LineCore.{uI} (B := B) 𝓘(ℂ,F))
    (hAmple : AmpleCore 𝓘(ℂ,F) L) :
    ∃ (k d : ℕ)
      (b : Module.Basis (Fin (d + 1)) ℂ
        (GlobalSections 𝓘(ℂ,F) (powerCoreRep 𝓘(ℂ,F) L k)))
      (hGen : GloballyGenerated 𝓘(ℂ,F) (powerCoreRep 𝓘(ℂ,F) L k)),
      0 < k ∧
      let f := projectiveEvaluationOfGenerated 𝓘(ℂ,F)
        (powerCoreRep 𝓘(ℂ,F) L k) d b hGen
      ContMDiff 𝓘(ℂ,F) 𝓘(ℂ, Fin d → ℂ) ∞ f ∧
      Topology.IsEmbedding f ∧
      (∀ x : B, Function.Injective
        (mfderiv 𝓘(ℂ,F) 𝓘(ℂ, Fin d → ℂ) f x)) ∧
      IsClosed (Set.range f) := by
  obtain ⟨k, hk, d, b, hGen, hEmb, hImm⟩ := hAmple
  refine ⟨k, d, b, hGen, hk, ?_, hEmb, hImm, ?_⟩
  · exact projectiveEvaluationOfGenerated_contMDiff
      𝓘(ℂ,F) (powerCoreRep 𝓘(ℂ,F) L k) d b hGen
  · exact (isCompact_range hEmb.continuous).isClosed

end
end QuaternionicSymmetry.GeneralContactFanoPicardProjectiveWitness
