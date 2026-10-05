import QuaternionicSymmetry.ContinuousWedge
import QuaternionicSymmetry.LocalConnectionExterior
import QuaternionicSymmetry.DifferentialFormCoefficient
import QuaternionicSymmetry.ContinuousWedgeInstances
import QuaternionicSymmetry.LocalChernWeilLinear
import QuaternionicSymmetry.LocalContinuousWedgeCommutator

/-!
# Local curvature trace powers in every positive degree

This constructs the actual normalized iterated wedge power of the local
curvature as a continuous alternating form.  The indexing starts with one
curvature factor.  In particular, no degree-zero unit form or global bundle
is needed.  Differentiability and exterior closedness follow from a twice
continuously differentiable connection, the graded covariant wedge rule,
Bianchi, and cyclicity of the coefficient trace.
-/

namespace QuaternionicSymmetry.LocalChernWeilTracePowers

open QuaternionicSymmetry.ContinuousWedge
  QuaternionicSymmetry.LocalConnection
  QuaternionicSymmetry.LocalConnectionForms
  QuaternionicSymmetry.LocalConnectionExterior
  QuaternionicSymmetry.DifferentialFormCoefficient
  QuaternionicSymmetry.LocalChernWeilQuadratic
  QuaternionicSymmetry.LocalChernWeilCubicForm
  QuaternionicSymmetry.ContinuousWedgeInstances
  QuaternionicSymmetry.LocalCovariantExterior
  QuaternionicSymmetry.LocalContinuousWedgeCommutator
  QuaternionicSymmetry.LocalEndomorphismTrace

noncomputable section

variable {E R B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R

/-- The degree of the `(k+1)`-st positive curvature power. -/
def powerDegree : ℕ → ℕ
  | 0 => 2
  | k + 1 => 2 + powerDegree k

theorem powerDegree_eq (k : ℕ) : powerDegree k = 2 * (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [powerDegree, ih]
      omega

/-- The ordered, normalized exterior power `F^(k+1)`.  The order is kept
explicit because coefficient multiplication need not be commutative. -/
def curvaturePowerForm (Γ : Form (E := E) (A := R)) :
    (k : ℕ) → E → E [⋀^Fin (powerDegree k)]→L[ℝ] R
  | 0 => curvatureForm Γ
  | k + 1 => fun x =>
      wedge (ContinuousLinearMap.mul ℝ R)
        (curvatureForm Γ x) (curvaturePowerForm Γ k x)

/-- Apply any continuous linear trace-like functional to a curvature power.
Cyclicity is not needed to construct the form. -/
def tracePowerForm (T : R →L[ℝ] B) (Γ : Form (E := E) (A := R))
    (k : ℕ) : E → E [⋀^Fin (powerDegree k)]→L[ℝ] B :=
  mapForm T (curvaturePowerForm Γ k)

theorem differentiableAt_curvaturePowerForm
    (Γ : Form (E := E) (A := R)) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (k : ℕ) :
    DifferentiableAt ℝ (curvaturePowerForm Γ k) x := by
  have h₁ : DifferentiableAt ℝ Γ x := hΓ.differentiableAt (by norm_num)
  have h₂ : DifferentiableAt ℝ (fderiv ℝ Γ) x :=
    (hΓ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hF : DifferentiableAt ℝ (curvatureForm Γ) x :=
    differentiableAt_curvatureForm Γ x h₁ h₂
  induction k with
  | zero => exact hF
  | succ k ih =>
      exact differentiableAt_wedge (ContinuousLinearMap.mul ℝ R)
        (curvatureForm Γ) (curvaturePowerForm Γ k) x hF ih

theorem differentiableAt_tracePowerForm
    (T : R →L[ℝ] B) (Γ : Form (E := E) (A := R)) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (k : ℕ) :
    DifferentiableAt ℝ (tracePowerForm T Γ k) x :=
  differentiableAt_mapForm T (curvaturePowerForm Γ k) x
    (differentiableAt_curvaturePowerForm Γ x hΓ k)

theorem tracePowerForm_apply
    (T : R →L[ℝ] B) (Γ : Form (E := E) (A := R))
    (k : ℕ) (x : E) (v : Fin (powerDegree k) → E) :
    tracePowerForm T Γ k x v = T (curvaturePowerForm Γ k x v) := rfl

/-- The zeroth recursive index is the already established linear
Chern--Weil two-form `T(F)`. -/
theorem tracePowerForm_zero_eq_characteristicForm
    (T : R →L[ℝ] B) (Γ : Form (E := E) (A := R)) :
    tracePowerForm T Γ 0 =
      QuaternionicSymmetry.LocalChernWeilLinear.characteristicForm T Γ := rfl

/-- Applying a continuous trace to an algebra-valued wedge can be moved to
the coefficient pairing.  This is a statement about actual alternating
forms in arbitrary degrees, with no cyclicity assumption. -/
theorem mapForm_wedge_mul (T : R →L[ℝ] B) {p q : ℕ}
    (α : E [⋀^Fin p]→L[ℝ] R) (β : E [⋀^Fin q]→L[ℝ] R) :
    T.compContinuousAlternatingMap
        (wedge (ContinuousLinearMap.mul ℝ R) α β) =
      wedge (traceProduct T) α β := by
  ext v
  change T (wedge (ContinuousLinearMap.mul ℝ R) α β v) =
    wedge (traceProduct T) α β v
  simp [wedge_apply, traceProduct_apply, _root_.map_sum, map_smul]

/-- The first normalized curvature trace power is the existing quadratic
Chern--Weil four-form. -/
theorem tracePowerForm_one_eq_traceSquareForm
    (T : R →L[ℝ] B) (Γ : Form (E := E) (A := R)) :
    tracePowerForm T Γ 1 = traceSquareForm T Γ := by
  funext x
  change T.compContinuousAlternatingMap
      (wedge (ContinuousLinearMap.mul ℝ R)
        (curvatureForm Γ x) (curvatureForm Γ x)) = _
  rw [mapForm_wedge_mul]
  exact (wedge22_eq (traceProduct T) (curvatureForm Γ x)
    (curvatureForm Γ x)).symm

/-- The second normalized curvature trace power is the existing cubic
Chern--Weil six-form. -/
theorem tracePowerForm_two_eq_traceCubeForm
    (T : R →L[ℝ] B) (Γ : Form (E := E) (A := R)) :
    tracePowerForm T Γ 2 = traceCubeForm T Γ := by
  funext x
  change T.compContinuousAlternatingMap
      (wedge (ContinuousLinearMap.mul ℝ R)
        (curvatureForm Γ x)
        (wedge (ContinuousLinearMap.mul ℝ R)
          (curvatureForm Γ x) (curvatureForm Γ x))) = _
  rw [mapForm_wedge_mul]
  rw [← wedge22_eq (ContinuousLinearMap.mul ℝ R) (curvatureForm Γ x)
    (curvatureForm Γ x)]
  exact (wedge24_eq (traceProduct T) (curvatureForm Γ x)
    (wedge22 (ContinuousLinearMap.mul ℝ R)
      (curvatureForm Γ x) (curvatureForm Γ x))).symm

/-- Bianchi and the graded covariant Leibniz rule annihilate every positive
normalized curvature power.  This is an equality of actual ring-valued
continuous alternating forms, not a pointwise formal polynomial identity. -/
theorem covariantExteriorDerivative_curvaturePowerForm_zero
    (Γ : Form (E := E) (A := R)) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (k : ℕ) :
    covariantExteriorDerivative Γ (curvaturePowerForm Γ k) x = 0 := by
  have h₁ : DifferentiableAt ℝ Γ x := hΓ.differentiableAt (by norm_num)
  have h₂ : DifferentiableAt ℝ (fderiv ℝ Γ) x :=
    (hΓ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hF : DifferentiableAt ℝ (curvatureForm Γ) x :=
    differentiableAt_curvatureForm Γ x h₁ h₂
  induction k with
  | zero => exact LocalCovariantExterior.bianchi Γ x hΓ
  | succ k ih =>
      ext v
      change covariantExteriorDerivative Γ
        (fun y => wedge (ContinuousLinearMap.mul ℝ R)
          (curvatureForm Γ y) (curvaturePowerForm Γ k y)) x v = 0
      rw [covariantExteriorDerivative_wedge_mul_apply Γ
        (curvatureForm Γ) (curvaturePowerForm Γ k) x hF
        (differentiableAt_curvaturePowerForm Γ x hΓ k) v]
      rw [LocalCovariantExterior.bianchi Γ x hΓ, ih]
      simp [wedge_mul_zero_left, wedge_mul_zero_right]

/-- In every positive degree, a cyclic trace of the normalized local
curvature power is closed at a C² connection.  In particular this covers
`tr(F^j)` for all finite `j ≥ 1`, with no higher-order regularity premise. -/
theorem tracePowerForm_closed (T : R →L[ℝ] B)
    (hT : ∀ a b : R, T (a * b) = T (b * a))
    (Γ : Form (E := E) (A := R)) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (k : ℕ) :
    extDeriv (tracePowerForm T Γ k) x = 0 := by
  calc
    extDeriv (tracePowerForm T Γ k) x =
        T.compContinuousAlternatingMap
          (covariantExteriorDerivative Γ (curvaturePowerForm Γ k) x) := by
        exact (cyclic_covariantExteriorDerivative T hT Γ
          (curvaturePowerForm Γ k) x
          (differentiableAt_curvaturePowerForm Γ x hΓ k)).symm
    _ = 0 := by
      rw [covariantExteriorDerivative_curvaturePowerForm_zero Γ x hΓ k]
      ext v
      simp

/-- The previously constructed normalized cubic six-form is closed. -/
theorem traceCubeForm_closed (T : R →L[ℝ] B)
    (hT : ∀ a b : R, T (a * b) = T (b * a))
    (Γ : Form (E := E) (A := R)) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) :
    extDeriv (traceCubeForm T Γ) x = 0 := by
  rw [← tracePowerForm_two_eq_traceCubeForm T Γ]
  exact tracePowerForm_closed T hT Γ x hΓ 2

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

local instance : NormedAddCommGroup (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

/-- The actual finite-dimensional endomorphism trace of every positive
normalized local curvature power. -/
def traceCurvaturePowerForm
    (Γ : Form (E := E) (A := V →L[ℝ] V)) (k : ℕ) :
    E → E [⋀^Fin (powerDegree k)]→L[ℝ] ℝ :=
  tracePowerForm LocalEndomorphismTrace.traceCLM Γ k

theorem traceCurvaturePowerForm_closed
    (Γ : Form (E := E) (A := V →L[ℝ] V)) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (k : ℕ) :
    extDeriv (traceCurvaturePowerForm Γ k) x = 0 :=
  tracePowerForm_closed LocalEndomorphismTrace.traceCLM
    LocalEndomorphismTrace.traceCLM_cyclic Γ x hΓ k

end
end QuaternionicSymmetry.LocalChernWeilTracePowers
