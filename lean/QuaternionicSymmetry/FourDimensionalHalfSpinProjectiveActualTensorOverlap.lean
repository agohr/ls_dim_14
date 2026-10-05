import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualBaseMobius
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualHorizontal
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMobiusRealTangent
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveTensorOverlap

/-! The independently defined local projective almost-complex tensor
intertwines with the full differential of the true adapted-frame CP¹
Möbius transition: raw base derivative, moving-frame vertical derivative,
and holomorphic fiber derivative.  This remains a local chart theorem. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualTensorOverlap

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveGaugeChart
  FourDimensionalHalfSpinProjectiveMobiusDerivative
  FourDimensionalHalfSpinProjectiveMobiusRealTangent
  FourDimensionalHalfSpinProjectiveActualHorizontal
  FourDimensionalHalfSpinProjectiveHorizontalOverlap
  FourDimensionalHalfSpinProjectiveActualBaseMobius
  FourDimensionalHalfSpinProjectiveLocalAHS
  FourDimensionalHalfSpinProjectiveTensorOverlap
  FourDimensionalHalfSpinMatrixConnection
  FourDimensionalHalfSpinMatrix
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinAntipodalVerticalSign
  QuaternionicManifoldLocalScalarLifts
  QuaternionicManifoldLocalStandardMaurer
  ManifoldTwistorLocalAlmostComplex
  ManifoldQuaternionicConnection

noncomputable section

def complexMulReal (c : ℂ) : ℂ →ₗ[ℝ] ℂ where
  toFun w := c * w
  map_add' u v := by simp [mul_add]
  map_smul' r u := by simp [smul_eq_mul]; ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

theorem actual_projective_tensor_overlap (p q : M) (lift : unitary ℍ)
    (y u : ℍ) (hy : y ∈ chartOverlap (I := 𝓘(ℝ, ℍ)) p q)
    (hx : (extChartAt 𝓘(ℝ, ℍ) p).symm y ∈
      liftNeighborhood Q (achart ℍ p) (achart ℍ q) lift)
    (z : ℂ)
    (hden : chartDen
      (halfSpinMatrix (scalarChart Q p (achart ℍ p) (achart ℍ q) lift y)) z ≠ 0)
    (v : ℍ × ℂ) :
    let r := scalarChart Q p (achart ℍ p) (achart ℍ q) lift
    let G := fun t => halfSpinMatrix (r t)
    let w := mobius (G y) z
    let T := (fderiv ℝ (chartTransition (I := 𝓘(ℝ, ℍ)) p q) y).toLinearMap
    let F := (fderiv ℝ (fun t => mobius (G t) z) y).toLinearMap
    let H := complexMulReal (deriv (mobius (G y)) z)
    tangentTransition T F H (localActualProjectiveAHS Q D p y z v) =
      localActualProjectiveAHS Q D q
        (chartTransition (I := 𝓘(ℝ, ℍ)) p q y) w
        (tangentTransition T F H v) := by
  dsimp
  let r := scalarChart Q p (achart ℍ p) (achart ℍ q) lift
  let G : ℍ → Mat2 := fun t => halfSpinMatrix (r t)
  let w := mobius (G y) z
  let T := (fderiv ℝ (chartTransition (I := 𝓘(ℝ, ℍ)) p q) y).toLinearMap
  let F := (fderiv ℝ (fun t => mobius (G t) z) y).toLinearMap
  let H := complexMulReal (deriv (mobius (G y)) z)
  let Jp := (chartBaseComplex Q p y
    (antipodalCoefficient (hopfSphere ![1,z] (by simp)))).toLinearMap
  let Jq := (chartBaseComplex Q q
    (chartTransition (I := 𝓘(ℝ, ℍ)) p q y)
    (antipodalCoefficient (hopfSphere ![1,w] (by simp)))).toLinearMap
  let Kp := localConnectionGenerator Q D p y z
  let Kq := localConnectionGenerator Q D q
    (chartTransition (I := 𝓘(ℝ, ℍ)) p q y) w
  have hbase : ∀ a, T (Jp a) = Jq (T a) := by
    intro a
    exact actual_antipodal_baseComplex_mobius Q p q lift y a hy hx z hden
  have hvert : ∀ b, H (Complex.I * b) = Complex.I * H b := by
    intro b
    simp [H, complexMulReal]
    ring
  have hhoriz : ∀ a, F a + H (-(Kp a)) = -(Kq (T a)) := by
    intro a
    have h := actual_horizontal_mobius_covariance Q D p q lift
      y a hy hx z hden
    simpa only [F, H, G, T, Kp, Kq, w, complexMulReal,
      localConnectionGenerator_apply, projectiveHorizontalVertical] using h
  change tangentTransition T F H (graphComplex Jp Kp v) =
    graphComplex Jq Kq (tangentTransition T F H v)
  exact graphComplex_overlap Jp Jq T Kp Kq F H hbase hvert hhoriz v

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualTensorOverlap
