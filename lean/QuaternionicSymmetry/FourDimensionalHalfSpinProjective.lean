import QuaternionicSymmetry.FourDimensionalHalfSpinMatrix
import QuaternionicSymmetry.ComplexProjectiveTopology

/-! Projectivize the actual complex two-dimensional unit-quaternion matrix
representation.  This gives a source-compatible projective half-spin action
without assuming a global spin bundle.  Its Hopf comparison to the native
negative-Hodge sphere remains a separate obligation. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjective

open scoped Quaternion Matrix
open FourDimensionalHalfSpinMatrix
open ComplexProjectiveTopology

noncomputable section

abbrev Spinor := Fin 2 → ℂ
abbrev ProjectiveSpinor := Space 1

/-- The complex-linear action of a unit quaternion on the genuine local
two-component spinor space. -/
def halfSpinLinearEquiv (q : unitary ℍ) : Spinor ≃ₗ[ℂ] Spinor :=
  Matrix.toLin'OfInv
    (halfSpinGroupHom q).inv_val (halfSpinGroupHom q).val_inv

@[simp] theorem halfSpinLinearEquiv_apply (q : unitary ℍ) (v : Spinor) :
    halfSpinLinearEquiv q v = halfSpinMatrix q *ᵥ v := rfl

theorem halfSpinLinearEquiv_mul (q r : unitary ℍ) :
    halfSpinLinearEquiv (q*r) =
      (halfSpinLinearEquiv r).trans (halfSpinLinearEquiv q) := by
  apply LinearEquiv.ext
  intro v
  simp only [LinearEquiv.trans_apply, halfSpinLinearEquiv_apply]
  change halfSpinMatrix ((q*r : unitary ℍ) : ℍ) *ᵥ v =
    halfSpinMatrix (q : ℍ) *ᵥ (halfSpinMatrix (r : ℍ) *ᵥ v)
  rw [Submonoid.coe_mul, halfSpinMatrix_mul, Matrix.mulVec_mulVec]

/-- The genuine projective complex-line action induced by the local
half-spin representation. -/
def projectiveHalfSpin (q : unitary ℍ) :
    ProjectiveSpinor → ProjectiveSpinor :=
  Projectivization.map (halfSpinLinearEquiv q).toLinearMap
    (halfSpinLinearEquiv q).injective

theorem projectiveHalfSpin_mk (q : unitary ℍ) (v : Spinor) (hv : v ≠ 0) :
    projectiveHalfSpin q (Projectivization.mk ℂ v hv) =
      Projectivization.mk ℂ (halfSpinLinearEquiv q v)
        (by simpa using (halfSpinLinearEquiv q).injective.ne hv) := by
  exact Projectivization.map_mk _ _ v hv

/-- The left action law is inherited from literal matrix multiplication,
not stipulated on projective space. -/
theorem projectiveHalfSpin_mul (q r : unitary ℍ) :
    projectiveHalfSpin (q*r) =
      projectiveHalfSpin q ∘ projectiveHalfSpin r := by
  funext p
  induction p using Projectivization.ind with
  | h v hv =>
    simp only [projectiveHalfSpin_mk]
    congr 1
    exact congrArg (fun f : Spinor ≃ₗ[ℂ] Spinor => f v)
      (halfSpinLinearEquiv_mul q r)

private theorem halfSpinMatrix_neg_one :
    halfSpinMatrix (-1 : ℍ) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [halfSpinMatrix, first, second, Complex.ext_iff]

/-- The simultaneous central sign disappears on projective spinors.
This is the algebraic reason that the associated projective bundle does not
require a global spin lift. -/
theorem projectiveHalfSpin_neg_one :
    projectiveHalfSpin (-1 : unitary ℍ) = id := by
  funext p
  induction p using Projectivization.ind with
  | h v hv =>
    rw [projectiveHalfSpin_mk]
    change Projectivization.mk ℂ
        (halfSpinLinearEquiv (-1 : unitary ℍ) v) _ =
      Projectivization.mk ℂ v hv
    have hm : halfSpinLinearEquiv (-1 : unitary ℍ) v = -v := by
      rw [halfSpinLinearEquiv_apply]
      change halfSpinMatrix (-1 : ℍ) *ᵥ v = -v
      rw [halfSpinMatrix_neg_one]
      ext i
      fin_cases i <;>
        simp [Matrix.mulVec, dotProduct,
          Matrix.one_apply, Pi.neg_apply]
    apply (Projectivization.mk_eq_mk_iff' ℂ
      (halfSpinLinearEquiv (-1 : unitary ℍ) v) v _ hv).2
    refine ⟨-1, ?_⟩
    simp [hm]

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjective
