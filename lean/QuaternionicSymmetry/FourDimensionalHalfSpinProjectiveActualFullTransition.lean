import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFullTransitionDerivative
import QuaternionicSymmetry.ManifoldTwistorRawTransitionDerivative

/-! The block transition in the actual adapted-frame overlap is the
Fréchet derivative of its jointly varying base and projective-fiber map. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualFullTransition

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinMatrix
  FourDimensionalHalfSpinMatrixConnection
  FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveActualTensorOverlap
  FourDimensionalHalfSpinProjectiveFullTransitionDerivative
  FourDimensionalHalfSpinProjectiveGaugeChart
  QuaternionicManifoldLocalScalarLifts
  QuaternionicManifoldLocalStandardMaurer
  QuaternionicManifoldProductGaugeDifferential
  ManifoldTwistorLocalAlmostComplex
  ManifoldQuaternionicConnection
  FourDimensionalHalfSpinProjectiveTensorOverlap

noncomputable section

local instance : NormedRing Mat2 := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ Mat2 := Matrix.linftyOpNormedAlgebra
local instance : NormedSpace ℝ Mat2 := NormedAlgebra.toNormedSpace _

private def halfSpinMatrixLinear : ℍ →ₗ[ℝ] Mat2 where
  toFun := halfSpinMatrix
  map_add' p q := halfSpinMatrix_add p q
  map_smul' c p := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;>
      simp [halfSpinMatrix, first, second, Complex.ext_iff] <;> ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

theorem actual_full_transition_fderiv (p q : M) (lift : unitary ℍ)
    (y : ℍ) (hy : y ∈ chartOverlap (I := 𝓘(ℝ, ℍ)) p q)
    (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift)
    (z : ℂ)
    (hden : chartDen
      (halfSpinMatrix (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) z ≠ 0)
    (v : ℍ × ℂ) :
    let r := scalarChart Q p (achart ℍ p) (achart ℍ q) lift
    let G := fun t => halfSpinMatrix (r t)
    let φ := chartTransition (I := 𝓘(ℝ, ℍ)) p q
    fderiv ℝ (jointProjectiveTransition φ G) (y,z) v =
      tangentTransition (fderiv ℝ φ y).toLinearMap
        (fderiv ℝ (fun t => mobius (G t) z) y).toLinearMap
        (complexMulReal (deriv (mobius (G y)) z)) v := by
  dsimp
  let r := scalarChart Q p (achart ℍ p) (achart ℍ q) lift
  let G : ℍ → Mat2 := fun t => halfSpinMatrix (r t)
  let φ := chartTransition (I := 𝓘(ℝ, ℍ)) p q
  have hφ : DifferentiableAt ℝ φ y :=
    (chartTransition_contDiffAt p q y hy).differentiableAt (by norm_num)
  have hr : DifferentiableAt ℝ r y :=
    scalarLift_chart_differentiableAt Q p (achart ℍ p) (achart ℍ q)
      lift y hy.1 hx
  let L : ℍ →L[ℝ] Mat2 := halfSpinMatrixLinear.toContinuousLinearMap
  have hG : DifferentiableAt ℝ G y := L.differentiableAt.comp y hr
  exact full_transition_fderiv φ G y z hφ hG hden v

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualFullTransition
