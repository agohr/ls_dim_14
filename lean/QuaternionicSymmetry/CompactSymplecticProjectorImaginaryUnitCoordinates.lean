import QuaternionicSymmetry.CompactSymplecticProjectorStrongBaseTwistorInjective

/-! A pure-imaginary quaternion squaring to minus one has unique
unit-sphere coordinates, with no independent twistor-model premise. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorImaginaryUnitCoordinates

open QuaternionicUnitScalarIsometries
open ManifoldTwistorSphereBundle
open scoped Quaternion

noncomputable section

theorem exists_unit_coordinates (r : ℍ) (hr : r.re = 0)
    (hrsq : r * r = -1) :
    ∃ z : coefficientSphere, pureScalar z.1 = r := by
  let b : Fin 3 → ℝ := ![r.imI, r.imJ, r.imK]
  have hnorm : Quaternion.normSq r = 1 := by
    have h := (Quaternion.sq_eq_neg_normSq).mpr hr
    rw [pow_two, hrsq] at h
    have hre := congrArg (fun s : ℍ => s.re) h
    simpa using hre.symm
  have hb : squareNorm b = 1 := by
    simpa [b, squareNorm, Quaternion.normSq_def', Fin.sum_univ_succ, hr,
      pow_two, add_assoc] using hnorm
  refine ⟨⟨b, hb⟩, ?_⟩
  ext <;> simp [pureScalar, b, hr]

end
end QuaternionicSymmetry.CompactSymplecticProjectorImaginaryUnitCoordinates
