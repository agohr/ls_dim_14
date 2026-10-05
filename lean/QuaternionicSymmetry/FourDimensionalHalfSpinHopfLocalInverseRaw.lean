import QuaternionicSymmetry.FourDimensionalHalfSpinHopfUnitSection
import QuaternionicSymmetry.QuaternionicUnitQuaternionSmoothTransport
import QuaternionicSymmetry.ComplexProjectiveQuotientHolomorphic

/-! Projectivizing the explicit normalized quaternion transporter is real
C∞ on its genuine non-antipodal domain. It is a local candidate inverse to
the Hopf map; the unit-axis identity is certified separately. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfLocalInverseRaw

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinQuaternionCoordinates
open QuaternionicUnitQuaternionTransport
  QuaternionicUnitScalarIsometries
  QuaternionicUnitQuaternionLocalSections
  QuaternionicUnitQuaternionSmoothTransport
  ComplexProjectiveTopology

noncomputable section

def localSpinor (u v : ℍ) : Spinor :=
  spinorQuaternionEquiv.symm (normalizedRaw u v)

def localProjective (u v : ℍ) : ProjectiveSpinor :=
  projectivize 1 (localSpinor u v)

theorem localSpinor_ne_zero (u v : ℍ) (hu : u * u = -1)
    (hv : v ≠ -u) : localSpinor u v ≠ 0 := by
  intro hz
  have hqz : normalizedRaw u v = 0 := by
    have h := congrArg (spinorQuaternionEquiv : Spinor →ₗ[ℝ] ℍ) hz
    simpa [localSpinor] using h
  have hunit : normalizedRaw u v =
      (localTransport u hu ⟨v, hv⟩ : ℍ) := rfl
  rw [hunit] at hqz
  have hn := normSq_one_of_unitary (localTransport u hu ⟨v,hv⟩)
  rw [hqz, map_zero] at hn
  norm_num at hn

theorem localProjective_contMDiffOn (u : ℍ) (hu : u * u = -1) :
    ContMDiffOn 𝓘(ℝ,ℍ) 𝓘(ℝ,Fin 1 → ℂ) ∞
      (localProjective u) {v : ℍ | v ≠ -u} := by
  have hraw := contDiffOn_normalizedRaw u hu
  have hspin : ContMDiffOn 𝓘(ℝ,ℍ) 𝓘(ℝ,Spinor) ∞
      (localSpinor u) {v : ℍ | v ≠ -u} :=
    (spinorQuaternionEquiv.symm.toLinearMap.toContinuousLinearMap.contDiff.contMDiff).comp_contMDiffOn
      hraw.contMDiffOn
  have hproj : ContMDiffOn 𝓘(ℝ,Spinor) 𝓘(ℝ,Fin 1 → ℂ) ∞
      (projectivize 1) {v : Spinor | v ≠ 0} := by
    obtain ⟨hcont, hcharts⟩ :=
      contMDiffOn_iff.mp (contMDiffOn_projectivize_nonzero 1)
    apply contMDiffOn_iff.mpr
    exact ⟨hcont, fun x y => (hcharts x y).restrict_scalars ℝ⟩
  exact hproj.comp hspin (fun v hv => localSpinor_ne_zero u v hu hv)

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfLocalInverseRaw
