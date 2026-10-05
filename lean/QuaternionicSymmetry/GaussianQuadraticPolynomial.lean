import QuaternionicSymmetry.ComplexGaussianCoordinates
import QuaternionicSymmetry.GaussianPolynomialExpectation
import QuaternionicSymmetry.HermitianPolynomialExt
import Mathlib.Data.Matrix.Mul

/-! Polynomial Gaussian quadratic forms over an arbitrary commutative complex
algebra. Their moments commute with coefficient evaluation, so numerical
identities can subsequently be used in algebras with nilpotents. -/

namespace QuaternionicSymmetry.GaussianQuadraticPolynomial

open MvPolynomial Matrix
open scoped BigOperators

noncomputable section

variable {κ S T : Type*} [Fintype κ]
  [CommRing S] [Algebra ℂ S] [CommRing T] [Algebra ℂ T]

def quadratic (Y : Matrix κ κ S) : MvPolynomial (κ × Fin 2) S :=
  ∑ i, ∑ j, MvPolynomial.map (algebraMap ℂ S) (ComplexGaussianCoordinates.conjugateCoordinate i) *
    C (Y i j) * MvPolynomial.map (algebraMap ℂ S) (ComplexGaussianCoordinates.coordinate j)

def moment (Y : Matrix κ κ S) (k : ℕ) : S :=
  GaussianPolynomialExpectation.expectation (quadratic Y ^ k)

theorem map_quadratic (f : S →ₐ[ℂ] T) (Y : Matrix κ κ S) :
    MvPolynomial.map f.toRingHom (quadratic Y) = quadratic (Y.map f) := by
  simp only [quadratic, map_sum, map_mul, MvPolynomial.map_C, Matrix.map_apply,
    MvPolynomial.map_map]
  have h : f.toRingHom.comp (algebraMap ℂ S) = algebraMap ℂ T := by
    ext z
    exact f.commutes z
  rw [h]
  rfl

theorem map_moment (f : S →ₐ[ℂ] T) (Y : Matrix κ κ S) (k : ℕ) :
    f (moment Y k) = moment (Y.map f) k := by
  unfold moment
  change (f.restrictScalars ℝ) (GaussianPolynomialExpectation.expectation (quadratic Y ^ k)) = _
  rw [GaussianPolynomialExpectation.expectation_map]
  simp only [map_pow]
  rw [show (f.restrictScalars ℝ).toRingHom = f.toRingHom from rfl, map_quadratic]

theorem eval_quadratic (Y : Matrix κ κ S) (ω : (κ × Fin 2) → ℝ) :
    (quadratic Y).eval (fun p => algebraMap ℝ S (ω p)) =
      ∑ i, ∑ j,
        algebraMap ℂ S (star (ComplexGaussianVariable.standardComplex (fun a => ω (i, a)))) *
        Y i j *
        algebraMap ℂ S (ComplexGaussianVariable.standardComplex (fun a => ω (j, a))) := by
  simp only [quadratic, map_sum, map_mul, eval_C]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he (p : MvPolynomial (κ × Fin 2) ℂ) :
      eval (fun a => algebraMap ℝ S (ω a)) (MvPolynomial.map (algebraMap ℂ S) p) =
        algebraMap ℂ S (eval (fun a => (ω a : ℂ)) p) := by
    rw [eval_map]
    exact (eval₂_comp (algebraMap ℂ S) (fun a => (ω a : ℂ)) p).symm
  rw [he, he]
  have hi := ComplexGaussianCoordinates.eval_conjugateCoordinate (fun i a => ω (i, a)) i
  have hj := ComplexGaussianCoordinates.eval_coordinate (fun i a => ω (i, a)) j
  change eval (fun p => (ω p : ℂ)) (ComplexGaussianCoordinates.conjugateCoordinate i) = _ at hi
  change eval (fun p => (ω p : ℂ)) (ComplexGaussianCoordinates.coordinate j) = _ at hj
  rw [hi, hj]
  rfl

theorem eval_quadratic_complex (Y : Matrix κ κ ℂ) (ω : (κ × Fin 2) → ℝ) :
    (quadratic Y).eval (fun p => (ω p : ℂ)) =
      star (fun i => ComplexGaussianVariable.standardComplex (fun a => ω (i, a))) ⬝ᵥ
        (Y *ᵥ fun i => ComplexGaussianVariable.standardComplex (fun a => ω (i, a))) := by
  have h := eval_quadratic Y ω
  change eval (fun p => (ω p : ℂ)) (quadratic Y) = _ at h
  rw [h]
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/-- The matrix whose entries are independent formal variables. -/
def universalMatrix : Matrix κ κ (MvPolynomial (κ × κ) ℂ) := fun i j => X (i, j)

omit [Fintype κ] in
theorem eval_universalMatrix (Y : Matrix κ κ S) :
    universalMatrix.map (aeval (fun p => Y p.1 p.2)) = Y := by
  ext i j
  simp [universalMatrix]

theorem eval_universal_moment (Y : Matrix κ κ S) (k : ℕ) :
    aeval (fun p => Y p.1 p.2) (moment universalMatrix k) = moment Y k := by
  rw [map_moment, eval_universalMatrix]

/-- A moment identity checked on numerical Hermitian matrices holds for every
matrix over a commutative complex algebra. -/
theorem extend_moment_identity (k : ℕ) (p : MvPolynomial (κ × κ) ℂ)
    (h : ∀ Y : Matrix κ κ ℂ, Y.IsHermitian →
      moment Y k = aeval (fun a => Y a.1 a.2) p)
    (Y : Matrix κ κ S) : moment Y k = aeval (fun a => Y a.1 a.2) p := by
  have hp : moment (universalMatrix (κ := κ)) k = p := by
    apply HermitianPolynomialExt.ext
    intro A hA
    change aeval (fun a => A a.1 a.2) (moment universalMatrix k) =
      aeval (fun a => A a.1 a.2) p
    rw [eval_universal_moment]
    exact h A hA
  rw [← eval_universal_moment Y k, hp]

theorem map_trace_pow [DecidableEq κ] (f : S →ₐ[ℂ] T)
    (Y : Matrix κ κ S) (k : ℕ) :
    f (Matrix.trace (Y ^ k)) = Matrix.trace ((Y.map f) ^ k) := by
  rw [AddMonoidHom.map_trace]
  congr 1
  exact map_pow (f.toRingHom.mapMatrix : Matrix κ κ S →+* Matrix κ κ T) Y k

theorem eval_universal_trace_pow [DecidableEq κ] (Y : Matrix κ κ S) (k : ℕ) :
    aeval (fun a : κ × κ => Y a.1 a.2) (Matrix.trace (universalMatrix ^ k)) =
      Matrix.trace (Y ^ k) := by
  rw [map_trace_pow, eval_universalMatrix]

end
end QuaternionicSymmetry.GaussianQuadraticPolynomial
