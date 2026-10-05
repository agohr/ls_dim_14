import QuaternionicSymmetry.QuaternionicManifoldPointwiseLifts
import QuaternionicSymmetry.QuaternionicUnitQuaternionTransport

/-! The normalized quaternion transporter is continuous on the open set
where its two imaginary directions are non-antipodal. -/

namespace QuaternionicSymmetry.QuaternionicUnitQuaternionLocalSections

open scoped Quaternion
open QuaternionicUnitQuaternionTransport

noncomputable section

abbrev NonAntipodal (u : ℍ) := {v : ℍ // v ≠ -u}

theorem isOpen_nonAntipodal (u : ℍ) : IsOpen {v : ℍ | v ≠ -u} := by
  exact isOpen_ne

def localTransport (u : ℍ) (hu : u * u = -1)
    (v : NonAntipodal u) : unitary ℍ :=
  normalize (1 - (v : ℍ) * u)
    (rawTransport_ne_zero u v hu v.property)

@[simp] theorem localTransport_coe (u : ℍ) (hu : u * u = -1)
    (v : NonAntipodal u) :
    ((localTransport u hu v : unitary ℍ) : ℍ) =
      (‖1 - (v : ℍ) * u‖⁻¹ : ℝ) • (1 - (v : ℍ) * u) := rfl

theorem continuous_localTransport (u : ℍ) (hu : u * u = -1) :
    Continuous (localTransport u hu) := by
  let r : NonAntipodal u → ℍ := fun v => 1 - (v : ℍ) * u
  have hr : Continuous r :=
    continuous_const.sub (continuous_subtype_val.mul continuous_const)
  have hn : Continuous (fun v : NonAntipodal u => ‖r v‖) := hr.norm
  have hne (v : NonAntipodal u) : ‖r v‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (rawTransport_ne_zero u v hu v.property)
  have hi : Continuous (fun v : NonAntipodal u => (‖r v‖ : ℝ)⁻¹) :=
    hn.inv₀ hne
  have hs : Continuous (fun v : NonAntipodal u =>
      (‖r v‖⁻¹ : ℝ) • r v) := hi.smul hr
  have hsub := hs.subtype_mk (fun v =>
    (localTransport u hu v).property)
  convert hsub using 1

theorem localTransport_intertwines (u : ℍ) (hu : u * u = -1)
    (v : NonAntipodal u) (hv : (v : ℍ) * v = -1) :
    ((localTransport u hu v : unitary ℍ) : ℍ) * u =
      (v : ℍ) * localTransport u hu v :=
  normalize_intertwines _ u v _ (rawTransport_intertwines u v hu hv)

end
end QuaternionicSymmetry.QuaternionicUnitQuaternionLocalSections
