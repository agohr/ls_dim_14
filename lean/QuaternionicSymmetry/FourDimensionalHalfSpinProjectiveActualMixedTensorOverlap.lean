import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualMixedBaseComplex
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualMixedHorizontal
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondTensor
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveTensorOverlap
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualTensorOverlap

/-! The independently defined first- and second-affine local projective
almost-complex tensors intertwine under the actual mixed adapted-frame
block differential, even at either chart's pole. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualMixedTensorOverlap

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinProjectiveActualMixedBaseComplex
  FourDimensionalHalfSpinProjectiveActualMixedHorizontal
  FourDimensionalHalfSpinProjectiveMixedGaugeAlgebra
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

theorem actual_mixed_tensor_overlap (p q : M) (lift : unitary ℍ)
    (y : ℍ) (hy : y ∈ chartOverlap (I := 𝓘(ℝ, ℍ)) p q)
    (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift)
    (z : ℂ)
    (hden : mixedDen
      (halfSpinMatrix (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) z ≠ 0)
    (v : ℍ × ℂ) :
    let r := scalarChart Q p (achart ℍ p) (achart ℍ q) lift
    let G := fun s => halfSpinMatrix (r s)
    let w := mixedMobius (G y) z
    let T := (fderiv ℝ (chartTransition (I := 𝓘(ℝ, ℍ)) p q) y).toLinearMap
    let F := (fderiv ℝ (fun s => mixedMobius (G s) z) y).toLinearMap
    let H := complexMulReal (deriv (mixedMobius (G y)) z)
    tangentTransition T F H (localActualProjectiveAHS Q D p y z v) =
      secondLocalActualProjectiveAHS Q D q
        (chartTransition (I := 𝓘(ℝ, ℍ)) p q y) w
        (tangentTransition T F H v) := by
  dsimp
  let r := scalarChart Q p (achart ℍ p) (achart ℍ q) lift
  let G : ℍ → FourDimensionalHalfSpinProjectiveGenerator.Mat2 :=
    fun s => halfSpinMatrix (r s)
  let w := mixedMobius (G y) z
  let T := (fderiv ℝ (chartTransition (I := 𝓘(ℝ, ℍ)) p q) y).toLinearMap
  let F := (fderiv ℝ (fun s => mixedMobius (G s) z) y).toLinearMap
  let H := complexMulReal (deriv (mixedMobius (G y)) z)
  let Jp := (chartBaseComplex Q p y
    (antipodalCoefficient (hopfSphere ![1,z] (by simp)))).toLinearMap
  let Jq := (chartBaseComplex Q q
    (chartTransition (I := 𝓘(ℝ, ℍ)) p q y)
    (antipodalCoefficient (hopfSphere ![w,1] (by simp)))).toLinearMap
  let Kp := localConnectionGenerator Q D p y z
  let Kq := secondLocalConnectionGenerator Q D q
    (chartTransition (I := 𝓘(ℝ, ℍ)) p q y) w
  have hbase : ∀ a, T (Jp a) = Jq (T a) := by
    intro a
    exact actual_mixed_antipodal_baseComplex_mobius Q p q lift
      y a hy hx z hden
  have hvert : ∀ b, H (Complex.I * b) = Complex.I * H b := by
    intro b
    simp [H, complexMulReal]
    ring
  have hhoriz : ∀ a, F a + H (-(Kp a)) = -(Kq (T a)) := by
    intro a
    have h := actual_mixed_horizontal_covariance Q D p q lift
      y a hy hx z hden
    simpa only [F, H, G, T, Kp, Kq, w, complexMulReal,
      localConnectionGenerator_apply,
      secondLocalConnectionGenerator_apply] using h
  change tangentTransition T F H (graphComplex Jp Kp v) =
    graphComplex Jq Kq (tangentTransition T F H v)
  exact graphComplex_overlap Jp Jq T Kp Kq F H hbase hvert hhoriz v

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualMixedTensorOverlap
