import QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereFormSmooth
import QuaternionicSymmetry.ManifoldQuaternionicFourFormLocalCalculus
import QuaternionicSymmetry.ManifoldQuaternionicFourTwistorHodgeFiber

/-! Pointwise comparison of the smooth native alternating two-form with the
algebraic exterior two-covector used for the genuine tangent Hodge sphere. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeExteriorComparison

open Module
open FourDimensionalExteriorHodge
open FourDimensionalExteriorQuaternionicHalf
open ManifoldQuaternionicFourNativeSphereFormSmooth
open ManifoldQuaternionicFourFormTransitions
open ManifoldQuaternionicFourFormLocalCalculus
open ManifoldQuaternionicFourTwistorHodgeFiber
open ManifoldQuaternionicRankThreeOrthogonal
open ManifoldQuaternionicMetric
open ManifoldTwistorSphereBundle
open ManifoldTwistorCoefficientSphere
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (hdim : Module.finrank ℝ E = 4)

theorem nativeSphereForm_evaluate (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (a : geometricSphere) (v w : E) :
    nativeSphereForm Q i (x,a) ![v,w] =
      BilinearExterior.evaluate
        (Q.frames.toFrame i x v) (Q.frames.toFrame i x w)
        ((Real.sqrt 2)⁻¹ • operatorForm (localBasis Q hdim i)
          (synth (Q.reduction.Q i)
            ((EuclideanSpace.equiv (Fin 3) ℝ) a.1))) := by
  let c : Fin 3 → ℝ := (EuclideanSpace.equiv (Fin 3) ℝ) a.1
  have hskew := quaternionicSpan_skew (Q.reduction.Q i)
    (synth (Q.reduction.Q i) c) (synth_mem (Q.reduction.Q i) c)
  rw [map_smul]
  change _ = (Real.sqrt 2)⁻¹ •
    BilinearExterior.evaluate (Q.frames.toFrame i x v) (Q.frames.toFrame i x w)
      (HyperholomorphicExterior.form (localBasis Q hdim i)
        (synth (Q.reduction.Q i) c).toLinearMap)
  rw [HyperholomorphicExterior.evaluate_form (localBasis Q hdim i)
    _ hskew]
  unfold nativeSphereForm
  simp only [Prod.fst, Prod.snd]
  simp_rw [chartKahler_eq_frameKahler Q i x hi]
  simp only [nativeSphereForm, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    smul_eq_mul]
  rw [synth_apply]
  have heval :
      (∑ t : Fin 3, c t • VectorBundleFrameTransitions.quaternionicGenerator
        (Q.reduction.Q i) t) (Q.frames.toFrame i x v) =
      ∑ t : Fin 3, c t • VectorBundleFrameTransitions.quaternionicGenerator
        (Q.reduction.Q i) t (Q.frames.toFrame i x v) := by
    simp
  change _ = (Real.sqrt 2)⁻¹ *
    inner ℝ ((∑ t : Fin 3, c t • VectorBundleFrameTransitions.quaternionicGenerator
      (Q.reduction.Q i) t) (Q.frames.toFrame i x v))
      (Q.frames.toFrame i x w)
  rw [heval, sum_inner]
  simp only [real_inner_smul_left, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  have hframe := frameKahler_apply (Q.reduction.Q i) t
    (fun k : Fin 2 => Q.frames.toFrame i x (![v,w] k))
  rw [show (frameKahler Q i t) (⇑(Q.frames.toFrame i x) ∘ ![v,w]) =
      inner ℝ
        (VectorBundleFrameTransitions.quaternionicGenerator (Q.reduction.Q i) t
          (Q.frames.toFrame i x v)) (Q.frames.toFrame i x w) from by
      simpa [frameKahler, Function.comp_def] using hframe]

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeExteriorComparison
