import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualMixedGauge
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMixedParameterDerivative

/-! The actual mixed first-to-second affine transition transports the
independent horizontal projective connection, including non-overlap poles. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualMixedHorizontal

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveActualMixedGauge
  FourDimensionalHalfSpinProjectiveMixedParameterDerivative
  FourDimensionalHalfSpinProjectiveMixedGaugeAlgebra
  FourDimensionalHalfSpinProjectiveSecondChart
  FourDimensionalHalfSpinMatrixConnection
  FourDimensionalHalfSpinMatrix
  QuaternionicManifoldLocalScalarLifts
  QuaternionicManifoldLocalStandardMaurer
  QuaternionicManifoldProductGaugeDifferential
  ManifoldQuaternionicConnection

noncomputable section

local instance : NormedRing Mat2 := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ Mat2 := Matrix.linftyOpNormedAlgebra
local instance : NormedSpace ℝ Mat2 := NormedAlgebra.toNormedSpace _

private def halfSpinMatrixLinear' : ℍ →ₗ[ℝ] Mat2 where
  toFun := halfSpinMatrix
  map_add' p q := halfSpinMatrix_add p q
  map_smul' c p := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;>
      simp [halfSpinMatrix, first, second, Complex.ext_iff] <;> ring

private theorem halfSpinMatrix_differentiableAt (r : ℍ → ℍ) (y : ℍ)
    (hr : DifferentiableAt ℝ r y) :
    DifferentiableAt ℝ (fun x => halfSpinMatrix (r x)) y := by
  let L : ℍ →L[ℝ] Mat2 := halfSpinMatrixLinear'.toContinuousLinearMap
  exact L.differentiableAt.comp y hr

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

theorem actual_mixed_horizontal_covariance (p q : M) (lift : unitary ℍ)
    (y u : ℍ) (hy : y ∈ chartOverlap (I := 𝓘(ℝ, ℍ)) p q)
    (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift)
    (z : ℂ) :
    let r := scalarChart Q p (achart ℍ p) (achart ℍ q) lift
    let G := fun t => halfSpinMatrix (r t)
    let A := spinorMatrixForm Q D q
      (chartTransition (I := 𝓘(ℝ, ℍ)) p q y)
      (fderiv ℝ (chartTransition (I := 𝓘(ℝ, ℍ)) p q) y u)
    let B := spinorMatrixForm Q D p y u
    mixedDen (G y) z ≠ 0 →
      fderiv ℝ (fun t => mixedMobius (G t) z) y u +
        deriv (mixedMobius (G y)) z * (-(affineGenerator B z)) =
          -(secondChartGenerator A (mixedMobius (G y) z)) := by
  dsimp
  let r := scalarChart Q p (achart ℍ p) (achart ℍ q) lift
  let G : ℍ → Mat2 := fun t => halfSpinMatrix (r t)
  let A := spinorMatrixForm Q D q
    (chartTransition (I := 𝓘(ℝ, ℍ)) p q y)
    (fderiv ℝ (chartTransition (I := 𝓘(ℝ, ℍ)) p q) y u)
  let B := spinorMatrixForm Q D p y u
  intro hden
  have hr : DifferentiableAt ℝ r y :=
    scalarLift_chart_differentiableAt Q p (achart ℍ p) (achart ℍ q)
      lift y hy.1 hx
  have hG : DifferentiableAt ℝ G y :=
    halfSpinMatrix_differentiableAt r y hr
  have hmove := mixed_parameter_fderiv G y u z hG hden
  have hchain := actual_mixed_projective_gauge_chain Q D p q lift
    y u hy hx z hden
  rw [hmove]
  linear_combination -hchain

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualMixedHorizontal
