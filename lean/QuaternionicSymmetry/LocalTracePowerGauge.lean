import QuaternionicSymmetry.LocalChernWeilTracePowers
import QuaternionicSymmetry.LocalContinuousWedgeGauge
import QuaternionicSymmetry.LocalProjectiveGauge

/-! Gauge invariance of every normalized local curvature trace power. -/

namespace QuaternionicSymmetry.LocalTracePowerGauge

open QuaternionicSymmetry.LocalConnection
  QuaternionicSymmetry.LocalConnectionGauge
  QuaternionicSymmetry.LocalConnectionForms
  QuaternionicSymmetry.LocalProjectiveGauge
  QuaternionicSymmetry.LocalChernWeilTracePowers
  QuaternionicSymmetry.LocalContinuousWedgeGauge
  QuaternionicSymmetry.ContinuousWedge

open scoped Topology

noncomputable section

variable {E R B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R

/-- An inverse-pair gauge change conjugates each ordered curvature wedge
power. The inverse identity `g x * h x = 1` is used to multiply conjugated
coefficients; the local inverse identity supplies the curvature change. -/
theorem curvaturePowerForm_transition
    (Γi Γj : Form (E := E) (A := R)) (g h : E → R) (x : E)
    (hpatch : Γj =ᶠ[𝓝 x] transform Γi g h)
    (hΓ : DifferentiableAt ℝ Γi x) (hg : ContDiffAt ℝ 2 g x)
    (hh : DifferentiableAt ℝ h x)
    (hleft : (fun y => h y * g y) =ᶠ[𝓝 x] fun _ => 1)
    (hright : g x * h x = 1) (k : ℕ) :
    curvaturePowerForm Γj k x =
      conjugateForm (g x) (h x) (curvaturePowerForm Γi k x) := by
  have hF : curvatureForm Γj x =
      conjugateForm (g x) (h x) (curvatureForm Γi x) := by
    ext v
    rw [curvatureForm_transition Γi Γj g h x hpatch hΓ hg hh hleft hright v]
    simp only [conjugateForm_apply]
    noncomm_ring
  induction k with
  | zero => exact hF
  | succ k ih =>
      change wedge (ContinuousLinearMap.mul ℝ R)
        (curvatureForm Γj x) (curvaturePowerForm Γj k x) = _
      rw [hF, ih]
      exact (conjugateForm_wedge_mul (g x) (h x) hright
        (curvatureForm Γi x) (curvaturePowerForm Γi k x)).symm

/-- Every positive normalized curvature trace power agrees on overlapping
charts of a supplied inverse-pair gauge atlas. This is equality of local
forms, with no assertion yet about a global characteristic class. -/
theorem tracePowerForm_transition
    (T : R →L[ℝ] B) (hT : ∀ a b : R, T (a * b) = T (b * a))
    (Γi Γj : Form (E := E) (A := R)) (g h : E → R) (x : E)
    (hpatch : Γj =ᶠ[𝓝 x] transform Γi g h)
    (hΓ : DifferentiableAt ℝ Γi x) (hg : ContDiffAt ℝ 2 g x)
    (hh : DifferentiableAt ℝ h x)
    (hleft : (fun y => h y * g y) =ᶠ[𝓝 x] fun _ => 1)
    (hright : g x * h x = 1) (k : ℕ) :
    tracePowerForm T Γj k x = tracePowerForm T Γi k x := by
  change T.compContinuousAlternatingMap (curvaturePowerForm Γj k x) = _
  rw [curvaturePowerForm_transition Γi Γj g h x hpatch hΓ hg hh hleft hright k]
  exact cyclic_conjugateForm T hT (g x) (h x) hright _

end
end QuaternionicSymmetry.LocalTracePowerGauge
