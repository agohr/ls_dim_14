import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualReverseBaseComplex
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualReverseHorizontal
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondTensor
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveTensorOverlap
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualTensorOverlap

/-! The independent local AHS tensors on second source and first target
affine charts intertwine under the full reverse mixed adapted-frame block
differential, including both pole coordinates. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualReverseTensorOverlap

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinProjectiveActualReverseBaseComplex
  FourDimensionalHalfSpinProjectiveActualReverseHorizontal
  FourDimensionalHalfSpinProjectiveReverseMixedGaugeAlgebra
  FourDimensionalHalfSpinProjectiveSecondTensor
  FourDimensionalHalfSpinProjectiveLocalAHS
  FourDimensionalHalfSpinProjectiveTensorOverlap
  FourDimensionalHalfSpinProjectiveActualTensorOverlap
  FourDimensionalHalfSpinMatrixConnection
  FourDimensionalHalfSpinMatrix
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinAntipodalVerticalSign
  QuaternionicManifoldLocalScalarLifts
  QuaternionicManifoldLocalStandardMaurer
  ManifoldTwistorLocalAlmostComplex
  ManifoldQuaternionicConnection

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

theorem actual_reverse_tensor_overlap (p q : M) (lift : unitary ℍ)
    (y : ℍ) (hy : y ∈ chartOverlap (I := 𝓘(ℝ, ℍ)) p q)
    (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift)
    (w : ℂ)
    (hden : reverseDen
      (halfSpinMatrix (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) w ≠ 0)
    (v : ℍ × ℂ) :
    let r := scalarChart Q p (achart ℍ p) (achart ℍ q) lift
    let G := fun s => halfSpinMatrix (r s)
    let z := reverseMobius (G y) w
    let T := (fderiv ℝ (chartTransition (I := 𝓘(ℝ, ℍ)) p q) y).toLinearMap
    let F := (fderiv ℝ (fun s => reverseMobius (G s) w) y).toLinearMap
    let H := complexMulReal (deriv (reverseMobius (G y)) w)
    tangentTransition T F H (secondLocalActualProjectiveAHS Q D p y w v) =
      localActualProjectiveAHS Q D q
        (chartTransition (I := 𝓘(ℝ, ℍ)) p q y) z
        (tangentTransition T F H v) := by
  dsimp
  let r := scalarChart Q p (achart ℍ p) (achart ℍ q) lift
  let G : ℍ → FourDimensionalHalfSpinProjectiveGenerator.Mat2 :=
    fun s => halfSpinMatrix (r s)
  let z := reverseMobius (G y) w
  let T := (fderiv ℝ (chartTransition (I := 𝓘(ℝ, ℍ)) p q) y).toLinearMap
  let F := (fderiv ℝ (fun s => reverseMobius (G s) w) y).toLinearMap
  let H := complexMulReal (deriv (reverseMobius (G y)) w)
  let Jp := (chartBaseComplex Q p y
    (antipodalCoefficient (hopfSphere ![w,1] (by simp)))).toLinearMap
  let Jq := (chartBaseComplex Q q
    (chartTransition (I := 𝓘(ℝ, ℍ)) p q y)
    (antipodalCoefficient (hopfSphere ![1,z] (by simp)))).toLinearMap
  let Kp := secondLocalConnectionGenerator Q D p y w
  let Kq := localConnectionGenerator Q D q
    (chartTransition (I := 𝓘(ℝ, ℍ)) p q y) z
  have hbase : ∀ a, T (Jp a) = Jq (T a) := by
    intro a
    exact actual_reverse_antipodal_baseComplex_mobius Q p q lift
      y a hy hx w hden
  have hvert : ∀ b, H (Complex.I * b) = Complex.I * H b := by
    intro b
    simp [H, complexMulReal]
    ring
  have hhoriz : ∀ a, F a + H (-(Kp a)) = -(Kq (T a)) := by
    intro a
    have h := actual_reverse_horizontal_covariance Q D p q lift
      y a hy hx w hden
    simpa only [F, H, G, T, Kp, Kq, z, complexMulReal,
      localConnectionGenerator_apply,
      secondLocalConnectionGenerator_apply] using h
  change tangentTransition T F H (graphComplex Jp Kp v) =
    graphComplex Jq Kq (tangentTransition T F H v)
  exact graphComplex_overlap Jp Jq T Kp Kq F H hbase hvert hhoriz v

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualReverseTensorOverlap
