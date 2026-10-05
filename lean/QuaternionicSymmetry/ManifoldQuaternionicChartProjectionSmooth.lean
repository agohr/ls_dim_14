import QuaternionicSymmetry.ManifoldQuaternionicChartProjection

/-! Differentiability of the genuine Q-plane projection in each preferred
manifold chart, obtained from the already-smooth tangent frame gauges. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicChartProjectionSmooth

open Manifold
open ManifoldQuaternionicReduction
open ManifoldQuaternionicChartProjection
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff Topology
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private abbrev EndE := E →L[ℝ] E

theorem chartProjection_differentiableAt_center (p : M) :
    DifferentiableAt ℝ
      (fun y : E => chartProjection Q (achart E p)
        ((extChartAt 𝓘(ℝ,E) p).symm y))
      (extChartAt 𝓘(ℝ,E) p p) := by
  let i := achart E p
  let σ := (extChartAt 𝓘(ℝ,E) p).symm
  let y₀ := extChartAt 𝓘(ℝ,E) p p
  have hy : y₀ ∈ (extChartAt 𝓘(ℝ,E) p).target :=
    (extChartAt 𝓘(ℝ,E) p).map_source (by simp)
  have hp : σ y₀ = p := (extChartAt 𝓘(ℝ,E) p).left_inv (by simp)
  have hbase : p ∈ (tangentBundleCore 𝓘(ℝ,E) M).baseSet i :=
    (tangentBundleCore 𝓘(ℝ,E) M).mem_baseSet_at p
  have hσ : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ σ y₀ :=
    (contMDiffOn_extChartAt_symm (n := ∞) p y₀ hy).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hy)
  have hTo : DifferentiableAt ℝ (fun y => Q.frames.toFrame i (σ y)) y₀ := by
    have hA : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,EndE (E := E)) ∞
        (Q.frames.toFrame i) (σ y₀) := by
      simpa only [hp] using
        (Q.frames.smooth_to i).contMDiffAt
          ((tangentBundleCore 𝓘(ℝ,E) M).isOpen_baseSet i |>.mem_nhds hbase)
    exact (hA.comp y₀ hσ).contDiffAt.differentiableAt (by norm_num)
  have hFrom : DifferentiableAt ℝ (fun y => Q.frames.fromFrame i (σ y)) y₀ := by
    have hA : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,EndE (E := E)) ∞
        (Q.frames.fromFrame i) (σ y₀) := by
      simpa only [hp] using
        (Q.frames.smooth_from i).contMDiffAt
          ((tangentBundleCore 𝓘(ℝ,E) M).isOpen_baseSet i |>.mem_nhds hbase)
    exact (hA.comp y₀ hσ).contDiffAt.differentiableAt (by norm_num)
  let mul := ContinuousLinearMap.mul ℝ (EndE (E := E))
  have hL : DifferentiableAt ℝ
      (fun y : E => Q.chartConjugation i (σ y)) y₀ := by
    change DifferentiableAt ℝ
      (fun y => (mul (Q.frames.fromFrame i (σ y))).comp
        (mul.flip (Q.frames.toFrame i (σ y)))) y₀
    exact (mul.differentiableAt.comp y₀ hFrom).clm_comp
      (mul.flip.differentiableAt.comp y₀ hTo)
  have hR : DifferentiableAt ℝ
      (fun y : E => inverseChartConjugation Q i (σ y)) y₀ := by
    change DifferentiableAt ℝ
      (fun y => (mul (Q.frames.toFrame i (σ y))).comp
        (mul.flip (Q.frames.fromFrame i (σ y)))) y₀
    exact (mul.differentiableAt.comp y₀ hTo).clm_comp
      (mul.flip.differentiableAt.comp y₀ hFrom)
  let K := (synth (Q.reduction.Q i)).comp (coeff (Q.reduction.Q i))
  have hK : DifferentiableAt ℝ (fun _ : E => K) y₀ := differentiableAt_const K
  have hKR : DifferentiableAt ℝ
      (fun y => K.comp (inverseChartConjugation Q i (σ y))) y₀ :=
    hK.clm_comp hR
  change DifferentiableAt ℝ
    (fun y => (Q.chartConjugation i (σ y)).comp
      (K.comp (inverseChartConjugation Q i (σ y)))) y₀
  exact hL.clm_comp hKR

end
end QuaternionicSymmetry.ManifoldQuaternionicChartProjectionSmooth
