import QuaternionicSymmetry.FourDimensionalHalfSpinHopfScalar

/-! The normalized quaternionic Hopf expression lands in the genuine
coefficient two-sphere.  The selected `i` axis and the order `q i q*` make
the local source convention explicit. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfSphere

open scoped Quaternion
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinQuaternionCoordinates
open QuaternionicUnitQuaternionTransport
open QuaternionicUnitScalarIsometries
open ManifoldTwistorSphereBundle

noncomputable section

private theorem fromSpinor_zero :
    fromSpinor (0 : Spinor) = 0 := by
  ext <;> simp [fromSpinor]

private theorem fromSpinor_ne_zero (v : Spinor) (hv : v ≠ 0) :
    fromSpinor v ≠ 0 := by
  intro h
  apply hv
  apply fromSpinor_injective
  simpa [fromSpinor_zero] using h

/-- The unit-quaternion representative of a nonzero complex spinor. -/
def spinorUnit (v : Spinor) (hv : v ≠ 0) : unitary ℍ :=
  normalize (fromSpinor v) (fromSpinor_ne_zero v hv)

/-- The normalized Hopf quaternion in the chosen axis convention. -/
def hopfQuaternion (v : Spinor) (hv : v ≠ 0) : ℍ :=
  (spinorUnit v hv : ℍ) * basisI * star (spinorUnit v hv : ℍ)

theorem hopfQuaternion_re (v : Spinor) (hv : v ≠ 0) :
    (hopfQuaternion v hv).re = 0 :=
  conjugate_imaginary (spinorUnit v hv : ℍ) basisI basisI_unit.1

theorem hopfQuaternion_normSq (v : Spinor) (hv : v ≠ 0) :
    Quaternion.normSq (hopfQuaternion v hv) = 1 := by
  simp [hopfQuaternion, map_mul, Quaternion.normSq_star,
    normSq_one_of_unitary, basisI_unit.2]

/-- The normalized Hopf map has its actual codomain the same unit
coefficient sphere as the quaternionic twistor atlas. -/
def hopfSphere (v : Spinor) (hv : v ≠ 0) : coefficientSphere :=
  let p := hopfQuaternion v hv
  ⟨![p.imI,p.imJ,p.imK], by
    have hp := hopfQuaternion_normSq v hv
    simpa [p, squareNorm, Fin.sum_univ_succ,
      Quaternion.normSq_def', hopfQuaternion_re v hv,
      pow_two, add_assoc] using hp⟩

theorem pureScalar_hopfSphere (v : Spinor) (hv : v ≠ 0) :
    pureScalar (hopfSphere v hv).1 = hopfQuaternion v hv := by
  ext <;> simp [pureScalar, hopfSphere, hopfQuaternion_re]

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfSphere
