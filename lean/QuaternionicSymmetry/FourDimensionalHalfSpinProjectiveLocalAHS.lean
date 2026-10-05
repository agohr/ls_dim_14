import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveActualHorizontal
import QuaternionicSymmetry.FourDimensionalHalfSpinCliffordActual
import QuaternionicSymmetry.FourDimensionalHalfSpinAntipodalVerticalSign
import QuaternionicSymmetry.ManifoldTwistorLocalAlmostComplex

/-! Local projective almost-complex algebra.  The fixed-model Clifford
operator is separated from the actual raw manifold-chart operator, which
must conjugate through the smooth adapted tangent frame.  Vertical
directions use multiplication by `i` in the genuine CP¹ affine chart. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveLocalAHS

open scoped Quaternion Matrix Manifold ContDiff
open FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveDescent
  FourDimensionalHalfSpinProjectiveConnection
  FourDimensionalHalfSpinMatrixConnection
  FourDimensionalHalfSpinCliffordActual
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinAntipodalVerticalSign
  ManifoldTwistorLocalAlmostComplex
  QuaternionicUnitScalarIsometries
  QuaternionicUnitQuaternionTransport
  ManifoldQuaternionicConnection

noncomputable section

def graphComplex (J : ℍ →ₗ[ℝ] ℍ) (K : ℍ →ₗ[ℝ] ℂ) :
    (ℍ × ℂ) →ₗ[ℝ] (ℍ × ℂ) where
  toFun v := (J v.1, Complex.I * (v.2 + K v.1) - K (J v.1))
  map_add' v w := by
    apply Prod.ext
    · simp [map_add]
    · simp [map_add]
      ring
  map_smul' c v := by
    apply Prod.ext
    · simp [map_smul]
    · simp [map_smul, smul_eq_mul]
      ring

theorem graphComplex_sq (J : ℍ →ₗ[ℝ] ℍ) (K : ℍ →ₗ[ℝ] ℂ)
    (hJ : ∀ u, J (J u) = -u) (v : ℍ × ℂ) :
    graphComplex J K (graphComplex J K v) = -v := by
  apply Prod.ext
  · exact hJ v.1
  · change Complex.I *
        (Complex.I * (v.2 + K v.1) - K (J v.1) + K (J v.1)) -
        K (J (J v.1)) = -v.2
    rw [hJ, map_neg]
    calc
      Complex.I *
          (Complex.I * (v.2 + K v.1) - K (J v.1) + K (J v.1)) -
          -(K v.1) = Complex.I ^ 2 * (v.2 + K v.1) + K v.1 := by ring
      _ = -v.2 := by rw [Complex.I_sq]; ring

def antipodalBaseComplex (v : Spinor) (hv : v ≠ 0) : ℍ →ₗ[ℝ] ℍ where
  toFun u := -(hopfQuaternion v hv * u)
  map_add' u w := by simp [mul_add]; abel
  map_smul' c u := by
    simp [smul_eq_mul, mul_assoc]

theorem antipodalBaseComplex_sq (v : Spinor) (hv : v ≠ 0) (u : ℍ) :
    antipodalBaseComplex v hv (antipodalBaseComplex v hv u) = -u := by
  have hsq : hopfQuaternion v hv * hopfQuaternion v hv = -1 :=
    imaginaryUnit_sq _ (hopfQuaternion_re v hv)
      (hopfQuaternion_normSq v hv)
  change -(hopfQuaternion v hv *
    (-(hopfQuaternion v hv * u))) = -u
  simp only [mul_neg, neg_neg, ← mul_assoc, hsq, neg_one_mul]

def affineGeneratorRealLinear (z : ℂ) : Mat2 →ₗ[ℝ] ℂ where
  toFun A := affineGenerator A z
  map_add' A B := affineGenerator_add A B z
  map_smul' c A := by
    change affineGenerator ((c : ℂ) • A) z =
      c • affineGenerator A z
    rw [affineGenerator_smul]
    rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

def localConnectionGenerator (p : M) (y : ℍ) (z : ℂ) : ℍ →ₗ[ℝ] ℂ :=
  (affineGeneratorRealLinear z).comp
    (spinorMatrixConnectionForm Q D p y).toLinearMap

theorem localConnectionGenerator_apply (p : M) (y u : ℍ) (z : ℂ) :
    localConnectionGenerator Q D p y z u =
      projectiveConnectionGenerator Q D p y u z := rfl

/-- Fixed quaternionic-model tensor.  The true raw manifold-chart tensor
below additionally conjugates its horizontal base direction by `Q.frames`. -/
def fixedModelProjectiveAHS (p : M) (y : ℍ) (z : ℂ) :
    (ℍ × ℂ) →ₗ[ℝ] (ℍ × ℂ) :=
  graphComplex (antipodalBaseComplex ![1,z] (by simp))
    (localConnectionGenerator Q D p y z)

theorem fixedModelProjectiveAHS_sq (p : M) (y : ℍ) (z : ℂ)
    (v : ℍ × ℂ) :
    fixedModelProjectiveAHS Q D p y z
      (fixedModelProjectiveAHS Q D p y z v) = -v :=
  graphComplex_sq _ _ (antipodalBaseComplex_sq _ _) v

/-- The actual raw-chart projective tensor uses the true frame-conjugated
base complex structure at the antipodal Hopf coefficient.  Its vertical
and connection terms remain independently defined on CP¹ coordinates. -/
def localActualProjectiveAHS (p : M) (y : ℍ) (z : ℂ) :
    (ℍ × ℂ) →ₗ[ℝ] (ℍ × ℂ) :=
  let a := antipodalCoefficient (hopfSphere ![1,z] (by simp))
  graphComplex (chartBaseComplex Q p y a)
    (localConnectionGenerator Q D p y z)

theorem localActualProjectiveAHS_sq (p : M) (y : ℍ)
    (hy : y ∈ (extChartAt 𝓘(ℝ, ℍ) p).target) (z : ℂ)
    (v : ℍ × ℂ) :
    localActualProjectiveAHS Q D p y z
      (localActualProjectiveAHS Q D p y z v) = -v := by
  exact graphComplex_sq _ _
    (chartBaseComplex_sq Q p y hy
      (antipodalCoefficient (hopfSphere ![1,z] (by simp)))) v

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveLocalAHS
