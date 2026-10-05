import QuaternionicSymmetry.FourDimensionalHalfSpinHopfLocalInverseRaw

/-! The non-antipodal local projective section based at the chosen `i`
axis is a literal right inverse of the projective Hopf map. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfNorthSection

open scoped Quaternion
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinQuaternionCoordinates
  FourDimensionalHalfSpinHopfProjectiveDescent
  FourDimensionalHalfSpinHopfUnitSection
  FourDimensionalHalfSpinHopfLocalInverseRaw
open QuaternionicUnitQuaternionTransport
  QuaternionicUnitQuaternionLocalSections
  QuaternionicUnitQuaternionSmoothTransport
  QuaternionicUnitScalarIsometries
open ManifoldTwistorSphereBundle
  ComplexProjectiveTopology

noncomputable section

theorem normSq_pureScalar (a : coefficientSphere) :
    Quaternion.normSq (pureScalar a.1) = 1 := by
  simpa [pureScalar, Quaternion.normSq_def', squareNorm,
    Fin.sum_univ_succ, pow_two, add_assoc] using a.2

theorem pureScalar_sq (a : coefficientSphere) :
    pureScalar a.1 * pureScalar a.1 = -1 :=
  imaginaryUnit_sq _ (pureScalar_re _) (normSq_pureScalar a)

theorem projectiveHopf_localNorth (a : coefficientSphere)
    (ha : pureScalar a.1 ≠ -basisI) :
    projectiveHopf (localProjective basisI (pureScalar a.1)) = a := by
  let q : unitary ℍ := localTransport basisI
    (imaginaryUnit_sq basisI basisI_unit.1 basisI_unit.2)
      ⟨pureScalar a.1, ha⟩
  have hq : (q : ℍ) * basisI = pureScalar a.1 * q :=
    localTransport_intertwines basisI
      (imaginaryUnit_sq basisI basisI_unit.1 basisI_unit.2)
      ⟨pureScalar a.1, ha⟩ (pureScalar_sq a)
  have hlocal : normalizedRaw basisI (pureScalar a.1) = (q : ℍ) := rfl
  have hspin : localSpinor basisI (pureScalar a.1) =
      spinorQuaternionEquiv.symm (q : ℍ) := by
    simp [localSpinor, hlocal]
  rw [localProjective, projectivize_of_ne_zero 1 _
    (localSpinor_ne_zero basisI (pureScalar a.1)
      (imaginaryUnit_sq basisI basisI_unit.1 basisI_unit.2) ha)]
  simpa only [hspin] using projectiveHopf_of_unitIntertwiner a q hq

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfNorthSection
