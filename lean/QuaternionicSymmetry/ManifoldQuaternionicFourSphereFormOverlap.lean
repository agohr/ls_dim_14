import QuaternionicSymmetry.FourDimensionalExteriorQuaternionicUnitSphere
import QuaternionicSymmetry.ManifoldQuaternionicFourHodgeOverlapExterior

/-! The normalized operator-to-exterior-form map respects the actual
rank-three and tangent frame transitions on the quaternionic manifold. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourSphereFormOverlap

open Module
open FourDimensionalExteriorHodge
open FourDimensionalExteriorQuaternionicHalf
open FourDimensionalExteriorCanonicalHodge
open ManifoldQuaternionicFourHodgeOverlapExterior
open ManifoldQuaternionicMetric
open ManifoldQuaternionicRankThreeOrthogonal
open VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem operatorForm_synth_overlap
    (Q : SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
    (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (b : Basis (Fin 4) ℝ E) (a : Fin 3 → ℝ) :
    pullbackTwoForm b (Q.frames.coordChange i j x).toLinearMap
      (operatorForm b (synth (Q.reduction.Q j)
        (Q.reduction.rankThreeCoordChange i j x a))) =
    operatorForm b (synth (Q.reduction.Q i) a) := by
  apply ExteriorDuality.twoform_ext b
  intro v w
  rw [evaluate_pullbackTwoForm]
  change BilinearExterior.evaluate
      (Q.frames.coordChange i j x v) (Q.frames.coordChange i j x w)
      (HyperholomorphicExterior.form b
        (synth (Q.reduction.Q j)
          (Q.reduction.rankThreeCoordChange i j x a)).toLinearMap) =
    BilinearExterior.evaluate v w
      (HyperholomorphicExterior.form b
        (synth (Q.reduction.Q i) a).toLinearMap)
  rw [HyperholomorphicExterior.evaluate_form b _
      (quaternionicSpan_skew _ _ (synth_mem _ _)),
    HyperholomorphicExterior.evaluate_form b _
      (quaternionicSpan_skew _ _ (synth_mem _ _))]
  have ht := synth_rankThreeCoordChange_eval Q i j x hi hj a v
  change (synth (Q.reduction.Q j)
      (Q.reduction.rankThreeCoordChange i j x a))
        (Q.frames.coordChange i j x v) =
      Q.frames.coordChange i j x (synth (Q.reduction.Q i) a v) at ht
  exact (congrArg (fun z : E => inner ℝ z (Q.frames.coordChange i j x w)) ht).trans
    (Q.transition_inner i j x hi hj (synth (Q.reduction.Q i) a v) w)

theorem normalized_operatorForm_synth_overlap
    (Q : SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
    (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (b : Basis (Fin 4) ℝ E) (a : Fin 3 → ℝ) :
    pullbackTwoForm b (Q.frames.coordChange i j x).toLinearMap
      ((Real.sqrt 2)⁻¹ • operatorForm b (synth (Q.reduction.Q j)
        (Q.reduction.rankThreeCoordChange i j x a))) =
    (Real.sqrt 2)⁻¹ • operatorForm b (synth (Q.reduction.Q i) a) := by
  apply ExteriorDuality.twoform_ext b
  intro v w
  rw [evaluate_pullbackTwoForm]
  simp only [map_smul, smul_eq_mul]
  simpa only [smul_eq_mul, evaluate_pullbackTwoForm] using
    congrArg (fun θ : TwoForm E =>
    (Real.sqrt 2)⁻¹ * BilinearExterior.evaluate v w θ)
    (operatorForm_synth_overlap Q i j x hi hj b a)

end
end QuaternionicSymmetry.ManifoldQuaternionicFourSphereFormOverlap
