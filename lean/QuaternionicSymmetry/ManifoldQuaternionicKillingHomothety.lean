import QuaternionicSymmetry.ManifoldQuaternionicKillingFields
import QuaternionicSymmetry.ManifoldQuaternionicHomothetyMetric
import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerHomothety

/-! Constant homothety preserves the genuine smooth Killing-field space. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicKillingHomothety
open ManifoldQuaternionicKillingFields
open ManifoldQuaternionicMetric
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyMetric
open ManifoldPositiveQuaternionicKahlerHomothety
open ManifoldPositiveQuaternionicKahlerGeometry
open Bundle
open scoped Manifold ContDiff Bundle
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

omit [FiniteDimensional ℝ E] [Nontrivial E] in
private theorem metric_contraction_mdifferentiable
    (Y Z : SmoothVectorFields (E := E) (M := M)) (x : M) :
    MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ)
      (fun y => Q.tangentMetricForm y (Y y) (Z y)) x := by
  have h := ContMDiff.clm_bundle_apply₂ (F₁ := E) (F₂ := E)
    Q.tangentMetric_contMDiff Y.contMDiff Z.contMDiff
  have hx := h x
  simp only [contMDiffAt_totalSpace] at hx
  exact hx.2.mdifferentiableAt (by simp)

theorem metricLieDerivative_rescale (s : ℝ) (hs : s ≠ 0)
    (X Y Z : SmoothVectorFields (E := E) (M := M)) (x : M) :
    metricLieDerivative (rescaleMetric Q s hs) X Y Z x =
      s^2 * metricLieDerivative Q X Y Z x := by
  have hdiff := metric_contraction_mdifferentiable Q Y Z x
  have hderiv := const_smul_mfderiv hdiff (s^2)
  unfold metricLieDerivative
  simp_rw [tangentMetricForm_rescale Q s hs]
  have hfun : (fun y => (rescaleMetric Q s hs).tangentMetricForm y (Y y) (Z y)) =
      (fun y => s^2 * Q.tangentMetricForm y (Y y) (Z y)) := by
    funext y
    rw [tangentMetricForm_rescale Q s hs]
  rw [hfun]
  rw [show (fun y => s^2 * Q.tangentMetricForm y (Y y) (Z y)) =
      (s^2) • (fun y => Q.tangentMetricForm y (Y y) (Z y)) by rfl]
  rw [hderiv]
  have hsmul : ((s^2) • mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ)
      (fun y => Q.tangentMetricForm y (Y y) (Z y)) x) (X x) =
      s^2 • (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ)
        (fun y => Q.tangentMetricForm y (Y y) (Z y)) x) (X x) := by
    rfl
  unfold TangentSpace at hsmul
  simp only [smul_eq_mul] at hsmul
  unfold TangentSpace
  rw [hsmul]
  ring

theorem killingFields_rescale (s : ℝ) (hs : s ≠ 0) :
    KillingFields (rescaleMetric Q s hs) = KillingFields Q := by
  ext X
  constructor
  · intro h Y Z x
    have hh := h Y Z x
    rw [metricLieDerivative_rescale Q s hs] at hh
    have hs2 : s^2 ≠ 0 := pow_ne_zero _ hs
    exact (mul_eq_zero.mp hh).resolve_left hs2
  · intro h Y Z x
    rw [metricLieDerivative_rescale Q s hs, h Y Z x, mul_zero]

theorem killingDimension_rescale (s : ℝ) (hs : s ≠ 0) :
    killingDimension (rescaleMetric Q s hs) = killingDimension Q := by
  unfold killingDimension
  rw [killingFields_rescale Q s hs]

theorem killingDimension_rescaleCompact
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (s : ℝ) (hs : 0 < s) :
    killingDimension (rescaleCompact P s hs).tangent =
      killingDimension P.tangent := by
  exact killingDimension_rescale P.tangent s (ne_of_gt hs)

end
end QuaternionicSymmetry.ManifoldQuaternionicKillingHomothety
