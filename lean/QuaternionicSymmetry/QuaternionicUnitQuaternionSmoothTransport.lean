import QuaternionicSymmetry.QuaternionicUnitQuaternionLocalSections

/-! Smoothness of the explicit normalized quaternion transporter away from
the antipodal locus, stated in ambient quaternion coordinates. -/

namespace QuaternionicSymmetry.QuaternionicUnitQuaternionSmoothTransport

open scoped Quaternion ContDiff
open QuaternionicUnitQuaternionTransport
  QuaternionicUnitQuaternionLocalSections

noncomputable section

def normalizedRaw (u v : ℍ) : ℍ :=
  (‖1 - v * u‖⁻¹ : ℝ) • (1 - v * u)

theorem contDiffAt_normalizedRaw (u v : ℍ)
    (hu : u * u = -1) (hv : v ≠ -u) :
    ContDiffAt ℝ ∞ (normalizedRaw u) v := by
  let r : ℍ → ℍ := fun w => 1 - w * u
  have hr : ContDiffAt ℝ ∞ r v :=
    contDiffAt_const.sub (contDiffAt_id.mul contDiffAt_const)
  have hrne : r v ≠ 0 := rawTransport_ne_zero u v hu hv
  have hn : ContDiffAt ℝ ∞ (fun w : ℍ => ‖r w‖) v :=
    (contDiffAt_norm ℝ hrne).comp v hr
  have hi : ContDiffAt ℝ ∞ (fun w : ℍ => (‖r w‖ : ℝ)⁻¹) v :=
    hn.inv (norm_ne_zero_iff.mpr hrne)
  exact hi.smul hr

theorem contDiffOn_normalizedRaw (u : ℍ) (hu : u * u = -1) :
    ContDiffOn ℝ ∞ (normalizedRaw u) {v : ℍ | v ≠ -u} := by
  intro v hv
  exact (contDiffAt_normalizedRaw u v hu hv).contDiffWithinAt

end
end QuaternionicSymmetry.QuaternionicUnitQuaternionSmoothTransport
