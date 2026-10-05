import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualSecondBaseComplex
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualSecondHorizontal
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSecondTensor
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveTensorOverlap
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualTensorOverlap

/-! The independently defined second-affine CP¹ almost-complex tensor
intertwines with the full block differential of a genuine refined adapted
base transition, including the south-pole source coordinate. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualSecondTensorOverlap

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinProjectiveActualSecondBaseComplex
  FourDimensionalHalfSpinProjectiveActualSecondHorizontal
  FourDimensionalHalfSpinProjectiveSecondTensor
  FourDimensionalHalfSpinProjectiveLocalAHS
  FourDimensionalHalfSpinProjectiveSecondMobius
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

theorem actual_second_tensor_overlap (p q : M) (lift : unitary ℍ)
    (y : ℍ) (hy : y ∈ chartOverlap (I := 𝓘(ℝ, ℍ)) p q)
    (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift)
    (w : ℂ)
    (hden : secondDen
      (halfSpinMatrix (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) w ≠ 0)
    (v : ℍ × ℂ) :
    let r := scalarChart Q p (achart ℍ p) (achart ℍ q) lift
    let G := fun t => halfSpinMatrix (r t)
    let t := secondMobius (G y) w
    let T := (fderiv ℝ (chartTransition (I := 𝓘(ℝ, ℍ)) p q) y).toLinearMap
    let F := (fderiv ℝ (fun s => secondMobius (G s) w) y).toLinearMap
    let H := complexMulReal (deriv (secondMobius (G y)) w)
    tangentTransition T F H (secondLocalActualProjectiveAHS Q D p y w v) =
      secondLocalActualProjectiveAHS Q D q
        (chartTransition (I := 𝓘(ℝ, ℍ)) p q y) t
        (tangentTransition T F H v) := by
  dsimp
  let r := scalarChart Q p (achart ℍ p) (achart ℍ q) lift
  let G : ℍ → FourDimensionalHalfSpinProjectiveGenerator.Mat2 :=
    fun s => halfSpinMatrix (r s)
  let t := secondMobius (G y) w
  let T := (fderiv ℝ (chartTransition (I := 𝓘(ℝ, ℍ)) p q) y).toLinearMap
  let F := (fderiv ℝ (fun s => secondMobius (G s) w) y).toLinearMap
  let H := complexMulReal (deriv (secondMobius (G y)) w)
  let Jp := (chartBaseComplex Q p y
    (antipodalCoefficient (hopfSphere ![w,1] (by simp)))).toLinearMap
  let Jq := (chartBaseComplex Q q
    (chartTransition (I := 𝓘(ℝ, ℍ)) p q y)
    (antipodalCoefficient (hopfSphere ![t,1] (by simp)))).toLinearMap
  let Kp := secondLocalConnectionGenerator Q D p y w
  let Kq := secondLocalConnectionGenerator Q D q
    (chartTransition (I := 𝓘(ℝ, ℍ)) p q y) t
  have hbase : ∀ a, T (Jp a) = Jq (T a) := by
    intro a
    exact actual_second_antipodal_baseComplex_mobius Q p q lift
      y a hy hx w hden
  have hvert : ∀ b, H (Complex.I * b) = Complex.I * H b := by
    intro b
    simp [H, complexMulReal]
    ring
  have hhoriz : ∀ a, F a + H (-(Kp a)) = -(Kq (T a)) := by
    intro a
    have h := actual_second_horizontal_covariance Q D p q lift
      y a hy hx w hden
    simpa only [F, H, G, T, Kp, Kq, t, complexMulReal,
      secondLocalConnectionGenerator_apply] using h
  change tangentTransition T F H (graphComplex Jp Kp v) =
    graphComplex Jq Kq (tangentTransition T F H v)
  exact graphComplex_overlap Jp Jq T Kp Kq F H hbase hvert hhoriz v

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualSecondTensorOverlap
