import QuaternionicSymmetry.FourDimensionalHalfSpinComplexStabilizer

/-! Equal Hopf directions of unit quaternions differ exactly by right
multiplication by a complex unit.  This is the nontrivial stabilizer step
in injectivity of the projective Hopf map. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfUnitFiber

open scoped Quaternion
open FourDimensionalHalfSpinMatrix
open FourDimensionalHalfSpinComplexStabilizer
open QuaternionicUnitQuaternionTransport

/-- If two unit quaternions give the same oriented Hopf axis, their relative
quaternion lies in the embedded complex line. -/
theorem relative_eq_complex_of_hopf_eq (q r : unitary ℍ)
    (h : (q : ℍ) * basisI * star (q : ℍ) =
      (r : ℍ) * basisI * star (r : ℍ)) :
    star (r : ℍ) * (q : ℍ) =
      (first (star (r : ℍ) * (q : ℍ)) : ℍ) := by
  apply eq_complex_of_commutes_basisI
  have hh := congrArg (fun x : ℍ => star (r : ℍ) * x * (q : ℍ)) h
  simp only [mul_assoc] at hh
  simpa only [q.property.1, r.property.1, mul_one, one_mul,
    ← mul_assoc] using hh

theorem unit_eq_right_complex_mul_of_hopf_eq (q r : unitary ℍ)
    (h : (q : ℍ) * basisI * star (q : ℍ) =
      (r : ℍ) * basisI * star (r : ℍ)) :
    (q : ℍ) = (r : ℍ) *
      (first (star (r : ℍ) * (q : ℍ)) : ℍ) := by
  rw [← relative_eq_complex_of_hopf_eq q r h]
  rw [← mul_assoc, r.property.2, one_mul]

end QuaternionicSymmetry.FourDimensionalHalfSpinHopfUnitFiber
