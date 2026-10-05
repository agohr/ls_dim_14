import QuaternionicSymmetry.FourDimensionalHalfSpinCliffordCovariance

/-! The checked complex matrices also satisfy the norm-square relation
of Euclidean Clifford multiplication. The opposite-chirality map carries
the conventional minus sign, so their composite is `-‖x‖²`. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinCliffordRelation

open scoped Quaternion Matrix
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinQuaternionCoordinates
  FourDimensionalHalfSpinCliffordActual

noncomputable section

theorem clifford_normSquare (x : ℍ) (v : Spinor) :
    cliffordMultiply (star x) (cliffordMultiply x v) =
      Quaternion.normSq x • v := by
  apply fromSpinor_injective
  rw [fromSpinor_cliffordMultiply, fromSpinor_cliffordMultiply]
  rw [star_star]
  change x * (star x * fromSpinor v) =
    spinorQuaternionEquiv (Quaternion.normSq x • v)
  rw [map_smul]
  change x * (star x * fromSpinor v) =
    Quaternion.normSq x • fromSpinor v
  rw [← mul_assoc, Quaternion.self_mul_star]
  rw [Algebra.smul_def]
  rw [Quaternion.algebraMap_def]

def oppositeCliffordMultiply (x : ℍ) (v : Spinor) : Spinor :=
  -cliffordMultiply (star x) v

theorem opposite_clifford_relation (x : ℍ) (v : Spinor) :
    oppositeCliffordMultiply x (cliffordMultiply x v) =
      -(Quaternion.normSq x • v) := by
  exact congrArg Neg.neg (clifford_normSquare x v)

end
end QuaternionicSymmetry.FourDimensionalHalfSpinCliffordRelation
