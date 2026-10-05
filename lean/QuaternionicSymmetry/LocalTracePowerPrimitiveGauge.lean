import QuaternionicSymmetry.LocalTracePowerGauge
import QuaternionicSymmetry.LocalChernWeilPowerTransgressionForm

/-!
# Gauge invariance of higher local Chern--Simons integrands

The path direction transforms by the homogeneous adjoint law. Together with
the curvature-power gauge law, this makes the normalized traced wedge
independent of the choice of local projective gauge lift.
-/

namespace QuaternionicSymmetry.LocalTracePowerPrimitiveGauge

open QuaternionicSymmetry.LocalConnection
  QuaternionicSymmetry.LocalConnectionForms
  QuaternionicSymmetry.LocalConnectionGauge
  QuaternionicSymmetry.LocalChernWeilQuadratic
  QuaternionicSymmetry.LocalChernWeilTracePowers
  QuaternionicSymmetry.LocalChernWeilPowerTransgressionForm
  QuaternionicSymmetry.LocalContinuousWedgeGauge
  QuaternionicSymmetry.LocalTracePowerGauge

open scoped Topology

noncomputable section

variable {E R B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R

/-- The normalized `T(θ ∧ F^(k+1))` integrand is unchanged across a local
inverse-pair gauge overlap when `θ` obeys the homogeneous adjoint law. -/
theorem traceConnectionCurvaturePower_transition
    (T : R →L[ℝ] B) (hT : ∀ a b : R, T (a * b) = T (b * a))
    (Γi Γj θi θj : Form (E := E) (A := R)) (g h : E → R) (x : E)
    (hΓpatch : Γj =ᶠ[𝓝 x] transform Γi g h)
    (hθpatch : θj =ᶠ[𝓝 x] adjointForm θi g h)
    (hΓ : DifferentiableAt ℝ Γi x) (hg : ContDiffAt ℝ 2 g x)
    (hh : DifferentiableAt ℝ h x)
    (hleft : (fun y => h y * g y) =ᶠ[𝓝 x] fun _ => 1)
    (hright : g x * h x = 1) (k : ℕ) :
    traceConnectionCurvaturePower T Γj θj k x =
      traceConnectionCurvaturePower T Γi θi k x := by
  have hθ : connectionForm θj x =
      conjugateForm (g x) (h x) (connectionForm θi x) := by
    ext v
    have hp := hθpatch.eq_of_nhds
    have hv := congrArg (fun f : E →L[ℝ] R => f (v 0)) hp
    simpa only [connectionForm, oneFormMap_apply, adjointForm_apply,
      conjugateForm_apply] using hv
  have hF := curvaturePowerForm_transition Γi Γj g h x hΓpatch
    hΓ hg hh hleft hright k
  change ContinuousWedge.wedge (traceProduct T) (connectionForm θj x)
      (curvaturePowerForm Γj k x) =
    ContinuousWedge.wedge (traceProduct T) (connectionForm θi x)
      (curvaturePowerForm Γi k x)
  rw [hθ, hF]
  simpa only [mapForm_wedge_mul] using
    (trace_wedge_mul_conjugate T hT (g x) (h x) hright
      (connectionForm θi x) (curvaturePowerForm Γi k x))

end
end QuaternionicSymmetry.LocalTracePowerPrimitiveGauge
