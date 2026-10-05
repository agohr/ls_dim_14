import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualMixedTensorOverlap
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMixedFullDerivative
import QuaternionicSymmetry.ManifoldTwistorRawTransitionDerivative

/-! Actual first-to-second projective AHS covariance uses the full
manifold derivative of the literal mixed bundle transition, including
its moving-frame term and pole coordinates. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualMixedMFDeriv

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinMatrix
  FourDimensionalHalfSpinMatrixConnection
  FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveMixedGaugeAlgebra
  FourDimensionalHalfSpinProjectiveMixedFullDerivative
  FourDimensionalHalfSpinProjectiveActualMixedTensorOverlap
  FourDimensionalHalfSpinProjectiveSecondTensor
  FourDimensionalHalfSpinProjectiveLocalAHS
  FourDimensionalHalfSpinProjectiveActualTensorOverlap
  FourDimensionalHalfSpinProjectiveTensorOverlap
  QuaternionicManifoldLocalScalarLifts
  QuaternionicManifoldLocalStandardMaurer
  QuaternionicManifoldProductGaugeDifferential
  ManifoldTwistorLocalAlmostComplex
  ManifoldQuaternionicConnection

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
  (D : CompatibleTangentConnection Q)

theorem actual_mixed_tensor_overlap_mfderiv (p q : M) (lift : unitary ℍ)
    (y : ℍ) (hy : y ∈ chartOverlap (I := 𝓘(ℝ, ℍ)) p q)
    (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift)
    (z : ℂ)
    (hden : mixedDen
      (halfSpinMatrix (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) z ≠ 0)
    (v : ℍ × ℂ) :
    let r := scalarChart Q p (achart ℍ p) (achart ℍ q) lift
    let G := fun t => halfSpinMatrix (r t)
    let φ := chartTransition (I := 𝓘(ℝ, ℍ)) p q
    let T := jointMixedTransition φ G
    mfderiv 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ) T (y,z)
        (localActualProjectiveAHS Q D p y z v) =
      secondLocalActualProjectiveAHS Q D q (φ y)
        (mixedMobius (G y) z)
        (mfderiv 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ) T (y,z) v) := by
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
  rw [mfderiv_eq_fderiv]
  have hleft := mixed_full_transition_fderiv φ G y z hφ hG hden
    (localActualProjectiveAHS Q D p y z v)
  have hright := mixed_full_transition_fderiv φ G y z hφ hG hden v
  have htransport := actual_mixed_tensor_overlap Q D p q lift
    y hy hx z hden v
  dsimp at hleft hright htransport
  exact hleft.trans (htransport.trans (congrArg _ hright.symm))

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualMixedMFDeriv
