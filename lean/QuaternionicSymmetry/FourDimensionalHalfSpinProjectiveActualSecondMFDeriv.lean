import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualSecondTensorOverlap
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondFullDerivative
import QuaternionicSymmetry.ManifoldTwistorRawTransitionDerivative

/-! Second-to-second AHS covariance is for the actual full manifold
derivative of the independently defined base-plus-projective transition,
not merely for a formally specified block map. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualSecondMFDeriv

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinMatrix
  FourDimensionalHalfSpinMatrixConnection
  FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveSecondMobius
  FourDimensionalHalfSpinProjectiveSecondFullDerivative
  FourDimensionalHalfSpinProjectiveActualSecondTensorOverlap
  FourDimensionalHalfSpinProjectiveSecondTensor
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

theorem actual_second_tensor_overlap_mfderiv (p q : M) (lift : unitary ℍ)
    (y : ℍ) (hy : y ∈ chartOverlap (I := 𝓘(ℝ, ℍ)) p q)
    (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift)
    (w : ℂ)
    (hden : secondDen
      (halfSpinMatrix (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) w ≠ 0)
    (v : ℍ × ℂ) :
    let r := scalarChart Q p (achart ℍ p) (achart ℍ q) lift
    let G := fun t => halfSpinMatrix (r t)
    let φ := chartTransition (I := 𝓘(ℝ, ℍ)) p q
    let T := jointSecondTransition φ G
    mfderiv 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ) T (y,w)
        (secondLocalActualProjectiveAHS Q D p y w v) =
      secondLocalActualProjectiveAHS Q D q (φ y)
        (secondMobius (G y) w)
        (mfderiv 𝓘(ℝ, ℍ × ℂ) 𝓘(ℝ, ℍ × ℂ) T (y,w) v) := by
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
  have hleft := second_full_transition_fderiv φ G y w hφ hG hden
    (secondLocalActualProjectiveAHS Q D p y w v)
  have hright := second_full_transition_fderiv φ G y w hφ hG hden v
  have htransport := actual_second_tensor_overlap Q D p q lift
    y hy hx w hden v
  dsimp at hleft hright htransport
  exact hleft.trans (htransport.trans (congrArg _ hright.symm))

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualSecondMFDeriv
