import QuaternionicSymmetry.GeneralLeviCivitaSource
import QuaternionicSymmetry.ManifoldQuaternionicConnection

/-! The actual preferred-chart transition derivative and reverse
transition derivative are inverse on every genuine chart overlap. -/

namespace QuaternionicSymmetry.GeneralLeviCivitaChartDerivativeInverse

open Manifold GeneralLeviCivitaSource
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem chartInverseDerivative_mul_chartDerivative (p q : M) (y : E)
    (hy : y ∈ chartOverlap p q) :
    chartInverseDerivative p q y * chartDerivative p q y = 1 := by
  let x := (extChartAt 𝓘(ℝ,E) p).symm y
  let z := chartTransition p q y
  have hp : x ∈ (extChartAt 𝓘(ℝ,E) p).source :=
    (extChartAt 𝓘(ℝ,E) p).map_target hy.1
  have hq : x ∈ (extChartAt 𝓘(ℝ,E) q).source := hy.2
  have hz : z ∈ (extChartAt 𝓘(ℝ,E) q).target :=
    (extChartAt 𝓘(ℝ,E) q).map_source hq
  have hzx : (extChartAt 𝓘(ℝ,E) q).symm z = x :=
    (extChartAt 𝓘(ℝ,E) q).left_inv hq
  have hrev : z ∈ chartOverlap q p := by
    refine ⟨hz, ?_⟩
    simpa only [hzx] using hp
  have hC := ManifoldQuaternionicConnection.chartTransition_derivative_eq_core
    (I := 𝓘(ℝ,E)) p q y hy
  have hCi := ManifoldQuaternionicConnection.chartTransition_derivative_eq_core
    (I := 𝓘(ℝ,E)) q p z hrev
  change fderiv ℝ (chartTransition p q) y = _ at hC
  change fderiv ℝ (chartTransition q p) z = _ at hCi
  rw [chartInverseDerivative, chartDerivative]
  change fderiv ℝ (chartTransition q p) z *
      fderiv ℝ (chartTransition p q) y = 1
  rw [hC, hCi, hzx]
  have hpi : x ∈ (tangentBundleCore 𝓘(ℝ,E) M).baseSet (achart E p) := by
    simpa only [tangentBundleCore_baseSet, coe_achart,
      ← extChartAt_source 𝓘(ℝ,E)] using hp
  have hqi : x ∈ (tangentBundleCore 𝓘(ℝ,E) M).baseSet (achart E q) := by
    simpa only [tangentBundleCore_baseSet, coe_achart,
      ← extChartAt_source 𝓘(ℝ,E)] using hq
  ext v
  change (tangentBundleCore 𝓘(ℝ,E) M).coordChange
      (achart E q) (achart E p) x
      ((tangentBundleCore 𝓘(ℝ,E) M).coordChange
        (achart E p) (achart E q) x v) = v
  rw [(tangentBundleCore 𝓘(ℝ,E) M).coordChange_comp
    (achart E p) (achart E q) (achart E p) x ⟨⟨hpi, hqi⟩, hpi⟩ v,
    (tangentBundleCore 𝓘(ℝ,E) M).coordChange_self
      (achart E p) x hpi]

theorem chartDerivative_mul_chartInverseDerivative (p q : M) (y : E)
    (hy : y ∈ chartOverlap p q) :
    chartDerivative p q y * chartInverseDerivative p q y = 1 := by
  let x := (extChartAt 𝓘(ℝ,E) p).symm y
  let z := chartTransition p q y
  have hp : x ∈ (extChartAt 𝓘(ℝ,E) p).source :=
    (extChartAt 𝓘(ℝ,E) p).map_target hy.1
  have hq : x ∈ (extChartAt 𝓘(ℝ,E) q).source := hy.2
  have hz : z ∈ (extChartAt 𝓘(ℝ,E) q).target :=
    (extChartAt 𝓘(ℝ,E) q).map_source hq
  have hzx : (extChartAt 𝓘(ℝ,E) q).symm z = x :=
    (extChartAt 𝓘(ℝ,E) q).left_inv hq
  have hrev : z ∈ chartOverlap q p := by
    refine ⟨hz, ?_⟩
    simpa only [hzx] using hp
  have h := chartInverseDerivative_mul_chartDerivative q p z hrev
  have hback : chartTransition q p z = y := by
    change extChartAt 𝓘(ℝ,E) p ((extChartAt 𝓘(ℝ,E) q).symm z) = y
    rw [hzx]
    exact (extChartAt 𝓘(ℝ,E) p).right_inv hy.1
  change fderiv ℝ (chartTransition p q) (chartTransition q p z) *
      fderiv ℝ (chartTransition q p) z = 1 at h
  rw [hback] at h
  exact h

end
end QuaternionicSymmetry.GeneralLeviCivitaChartDerivativeInverse
