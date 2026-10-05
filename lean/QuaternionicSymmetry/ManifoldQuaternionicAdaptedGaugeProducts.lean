import QuaternionicSymmetry.ManifoldQuaternionicAdaptedLeviCivitaMetric
import QuaternionicSymmetry.GeneralLeviCivitaChartDerivativeInverse

/-! The actual tangent-core chart derivative, solder gauges, and adapted
frame transition satisfy the exact product identities required by affine
connection descent. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicAdaptedGaugeProducts

open Manifold GeneralLeviCivitaSource
open ManifoldQuaternionicConnection
  (solder adaptedGauge adaptedGaugeInv solder_chartTransition adaptedGauge_inverse)
open ManifoldQuaternionicCoordinateConnection
open GeneralLeviCivitaChartDerivativeInverse
open scoped Manifold ContDiff Topology
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem coordinateInverse_mul_adaptedGauge (p q : M) (y : E)
    (hy : y ∈ chartOverlap p q) :
    coordinateInverse Q q (chartTransition p q y) * adaptedGauge Q p q y =
      chartDerivative p q y * coordinateInverse Q p y := by
  let z := chartTransition p q y
  have hz : z ∈ (extChartAt 𝓘(ℝ,E) q).target :=
    (extChartAt 𝓘(ℝ,E) q).map_source hy.2
  have hpRight := coordinateInverse_right Q p y hy.1
  have hqLeft := coordinateInverse_left Q q z hz
  have hsolder : (solder Q q z) * chartDerivative p q y =
      adaptedGauge Q p q y * solder Q p y := by
    have h := solder_chartTransition Q p q y hy
    ext v
    simpa only [ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.comp_apply] using
      congrArg (fun T : E →L[ℝ] E => T v) h
  calc
    coordinateInverse Q q z * adaptedGauge Q p q y =
      coordinateInverse Q q z *
        (adaptedGauge Q p q y * solder Q p y) *
          coordinateInverse Q p y := by
            simp only [mul_assoc, hpRight, mul_one]
    _ = coordinateInverse Q q z *
          (solder Q q z * chartDerivative p q y) *
            coordinateInverse Q p y := by rw [hsolder]
    _ = chartDerivative p q y * coordinateInverse Q p y := by
          rw [← mul_assoc, hqLeft]
          simp

theorem adaptedGaugeInv_mul_solder (p q : M) (y : E)
    (hy : y ∈ chartOverlap p q) :
    adaptedGaugeInv Q p q y * solder Q q (chartTransition p q y) =
      solder Q p y * chartInverseDerivative p q y := by
  let z := chartTransition p q y
  have hsolder : (solder Q q z) * chartDerivative p q y =
      adaptedGauge Q p q y * solder Q p y := by
    have h := solder_chartTransition Q p q y hy
    ext v
    simpa only [ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.comp_apply] using
      congrArg (fun T : E →L[ℝ] E => T v) h
  have hHG := (adaptedGauge_inverse Q p q y hy).1
  have hCCi := chartDerivative_mul_chartInverseDerivative p q y hy
  calc
    adaptedGaugeInv Q p q y * solder Q q z =
      (adaptedGaugeInv Q p q y * solder Q q z) *
        (chartDerivative p q y * chartInverseDerivative p q y) := by
          rw [hCCi, mul_one]
    _ = adaptedGaugeInv Q p q y *
          (solder Q q z * chartDerivative p q y) *
            chartInverseDerivative p q y := by simp only [mul_assoc]
    _ = adaptedGaugeInv Q p q y *
          (adaptedGauge Q p q y * solder Q p y) *
            chartInverseDerivative p q y := by rw [hsolder]
    _ = solder Q p y * chartInverseDerivative p q y := by
          rw [← mul_assoc, hHG, one_mul]

end
end QuaternionicSymmetry.ManifoldQuaternionicAdaptedGaugeProducts
