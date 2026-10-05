import QuaternionicSymmetry.HolomorphicLineCoreProjectiveBasisChange
import QuaternionicSymmetry.ComplexProjectiveLinearEquivBiholomorphic

/-! The complete linear-system projective embedding and immersion are
independent of the basis, including a basis of torus eigenvectors. -/

namespace QuaternionicSymmetry.HolomorphicLineCoreProjectiveBasisChangeImmersion

open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineCoreProjectiveEvaluation HolomorphicLineCoreAmpleFiniteMap
open HolomorphicLineCoreProjectiveBasisChange
open ComplexProjectiveTopology
open ComplexProjectiveLinearEquivHolomorphic
open ComplexProjectiveLinearEquivBiholomorphic
open scoped Manifold ContDiff
noncomputable section
universe u

variable {B H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H) [IsManifold IB ∞ B]
  (L : LineCore.{u} (B := B) IB)

theorem veryAmple_projectiveEvaluation_embedding_immersion
    (hVery : VeryAmpleCore IB L) (d : ℕ)
    (b : Module.Basis (Fin (d + 1)) ℂ (GlobalSections IB L))
    (hGen : GloballyGenerated IB L) :
    Topology.IsEmbedding (projectiveEvaluationOfGenerated IB L d b hGen) ∧
      ∀ x : B, Function.Injective
        (mfderiv IB 𝓘(ℂ, Fin d → ℂ)
          (projectiveEvaluationOfGenerated IB L d b hGen) x) := by
  obtain ⟨e,c,hGen',hEmb,hImm⟩ := hVery
  let A := basisCoordinateChange IB L d e b c
  let fb := projectiveEvaluationOfGenerated IB L d b hGen
  let fc := projectiveEvaluationOfGenerated IB L e c hGen
  have hEq : fc = projectiveMap A ∘ fb := by
    funext x
    exact projectiveEvaluation_change IB L d e b c hGen x
  have hEqInv : fb = projectiveMap A.symm ∘ fc := by
    funext x
    calc
      fb x = projectiveMap A.symm (projectiveMap A (fb x)) :=
        (projectiveMap_symm_apply A (fb x)).symm
      _ = projectiveMap A.symm (fc x) := by
        congr 1
        exact (congrFun hEq x).symm
  constructor
  · change Topology.IsEmbedding fb
    rw [hEqInv]
    change Topology.IsEmbedding fc at hEmb
    exact (projectiveMap_isEmbedding A.symm).comp hEmb
  · intro x
    have hc := hImm x
    change Function.Injective (mfderiv IB 𝓘(ℂ, Fin e → ℂ) fc x) at hc
    have hfb := (projectiveEvaluationOfGenerated_contMDiff IB L d b hGen).mdifferentiable
      (by simp) x
    have hpm := (contMDiff_projectiveMap A).mdifferentiable (by simp) (fb x)
    have hchain : mfderiv IB 𝓘(ℂ, Fin e → ℂ) fc x =
        (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ)
          (projectiveMap A) (fb x)).comp
          (mfderiv IB 𝓘(ℂ, Fin d → ℂ) fb x) := by
      rw [hEq]
      exact mfderiv_comp x hpm hfb
    intro v w hvw
    apply hc
    rw [hchain]
    change (mfderiv IB 𝓘(ℂ, Fin d → ℂ) fb x) v =
      (mfderiv IB 𝓘(ℂ, Fin d → ℂ) fb x) w at hvw
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg
        (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ)
          (projectiveMap A) (fb x)) hvw

end
end QuaternionicSymmetry.HolomorphicLineCoreProjectiveBasisChangeImmersion
