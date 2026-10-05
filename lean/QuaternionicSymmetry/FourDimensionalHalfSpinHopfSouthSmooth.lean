import QuaternionicSymmetry.FourDimensionalHalfSpinHopfSouthSection

/-! The second explicit local inverse section is C∞ on its actual
non-antipodal ambient domain, completing a smooth two-chart inverse cover
once the sphere inclusion is composed. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfSouthSmooth

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinQuaternionCoordinates
  FourDimensionalHalfSpinHopfSouthSection
open QuaternionicUnitQuaternionTransport
  QuaternionicUnitQuaternionSmoothTransport
  ComplexProjectiveTopology

noncomputable section

theorem southProjective_contMDiffOn :
    ContMDiffOn 𝓘(ℝ,ℍ) 𝓘(ℝ,Fin 1 → ℂ) ∞
      southProjective {v : ℍ | v ≠ basisI} := by
  have hsq : (-basisI : ℍ) * (-basisI) = -1 := by
    rw [neg_mul_neg]
    exact imaginaryUnit_sq basisI basisI_unit.1 basisI_unit.2
  have hraw : ContDiffOn ℝ ∞
      (fun v : ℍ => normalizedRaw (-basisI) v * basisJ)
      {v : ℍ | v ≠ basisI} := by
    convert (contDiffOn_normalizedRaw (-basisI) hsq).mul contDiffOn_const using 1
    ext v
    simp
  have hspin : ContMDiffOn 𝓘(ℝ,ℍ) 𝓘(ℝ,Spinor) ∞
      southSpinor {v : ℍ | v ≠ basisI} :=
    (spinorQuaternionEquiv.symm.toLinearMap.toContinuousLinearMap.contDiff.contMDiff).comp_contMDiffOn
      hraw.contMDiffOn
  have hproj : ContMDiffOn 𝓘(ℝ,Spinor) 𝓘(ℝ,Fin 1 → ℂ) ∞
      (projectivize 1) {v : Spinor | v ≠ 0} := by
    obtain ⟨hcont, hcharts⟩ :=
      contMDiffOn_iff.mp (contMDiffOn_projectivize_nonzero 1)
    apply contMDiffOn_iff.mpr
    exact ⟨hcont, fun x y => (hcharts x y).restrict_scalars ℝ⟩
  exact hproj.comp hspin (fun v hv => southSpinor_ne_zero v hv)

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfSouthSmooth
