import QuaternionicSymmetry.QuaternionicProjectiveStandardHilbertStructure

/-! The left quaternionic line action and its real-linear centralizer. -/
namespace QuaternionicSymmetry.QuaternionicLeftLineAction
open QuaternionicProjectiveStandardHilbertStructure QuaternionicUnitQuaternionTransport
open scoped Quaternion
noncomputable section

theorem action_eq_mul (q w : ℍ) : leftLineStructure.action q w = q * w := by
  rw [leftLineStructure.action_apply]
  change q.re • w + q.imI • (basisI * w) + q.imJ • (basisJ * w) +
    q.imK • (basisI * (basisJ * w)) = q * w
  ext <;> simp [basisI, basisJ, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

theorem apply_eq_mul_one (A : ℍ →ₗ[ℝ] ℍ)
    (hI : ∀ w, A (leftLineStructure.I w) = leftLineStructure.I (A w))
    (hJ : ∀ w, A (leftLineStructure.J w) = leftLineStructure.J (A w)) (q : ℍ) :
    A q = q * A 1 := by
  simpa only [action_eq_mul, mul_one] using
    leftLineStructure.action_commutes A hI hJ q 1

end
end QuaternionicSymmetry.QuaternionicLeftLineAction
