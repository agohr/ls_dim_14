import QuaternionicSymmetry.FourDimensionalHalfSpinCliffordHorizontal

/-! The concrete complex-linear Clifford matrix on two-component spinors.
For the unit representative `q` of a projective half-spin line, Clifford
multiplication by a tangent quaternion `x` is the genuine complex matrix
`halfSpinMatrix (star x)` acting on that spinor. Its induced horizontal
complex structure is **minus** the current Hopf-selected left quaternionic
complex structure. Thus the antipodal Hopf coefficient gives the horizontal
sign compatible with this explicit Clifford representation. Identifying
this model with Hitchin's named chirality modules remains separately typed. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinCliffordActual

open scoped Quaternion Matrix
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinMatrix
  FourDimensionalHalfSpinQuaternionCoordinates
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinHopfScalar
  QuaternionicUnitQuaternionTransport

noncomputable section

def cliffordMultiply (x : ℍ) (v : Spinor) : Spinor :=
  halfSpinMatrix (star x) *ᵥ v

theorem fromSpinor_cliffordMultiply (x : ℍ) (v : Spinor) :
    fromSpinor (cliffordMultiply x v) = star x * fromSpinor v :=
  fromSpinor_halfSpinMatrix (star x) v

def unitSpinor (v : Spinor) (hv : v ≠ 0) : Spinor :=
  spinorQuaternionEquiv.symm (spinorUnit v hv : ℍ)

theorem fromSpinor_unitSpinor (v : Spinor) (hv : v ≠ 0) :
    fromSpinor (unitSpinor v hv) = spinorUnit v hv :=
  spinorQuaternionEquiv.apply_symm_apply _

theorem clifford_antipodal_horizontal (v : Spinor) (hv : v ≠ 0) (x : ℍ) :
    cliffordMultiply (-(hopfQuaternion v hv * x)) (unitSpinor v hv) =
      Complex.I • cliffordMultiply x (unitSpinor v hv) := by
  apply fromSpinor_injective
  rw [fromSpinor_cliffordMultiply, fromSpinor_smul,
    fromSpinor_cliffordMultiply, fromSpinor_unitSpinor]
  let q := spinorUnit v hv
  have hi : (Complex.I : ℍ) = basisI := by
    ext <;> simp [basisI]
  rw [hi]
  have hstar : star (hopfQuaternion v hv) = -hopfQuaternion v hv :=
    Quaternion.star_eq_neg.mpr (hopfQuaternion_re v hv)
  calc
    star (-(hopfQuaternion v hv * x)) * (q : ℍ) =
        (star x * hopfQuaternion v hv) * (q : ℍ) := by
      rw [star_neg, star_mul, hstar]
      simp only [mul_neg, neg_neg]
    _ = (star x * (q : ℍ)) * basisI := by
      change (star x * ((q : ℍ) * basisI * star (q : ℍ))) * (q : ℍ) = _
      calc
        (star x * ((q : ℍ) * basisI * star (q : ℍ))) * (q : ℍ) =
            (star x * ((q : ℍ) * basisI)) *
              (star (q : ℍ) * (q : ℍ)) := by simp only [mul_assoc]
        _ = star x * ((q : ℍ) * basisI) := by
          rw [q.property.1, mul_one]
        _ = (star x * (q : ℍ)) * basisI := by rw [mul_assoc]

end
end QuaternionicSymmetry.FourDimensionalHalfSpinCliffordActual
