import QuaternionicSymmetry.QuaternionicProjectiveAdjointGaugeDerivative
import QuaternionicSymmetry.LocalConnectionGauge

/-! An ordinary gauge transformation of a matrix-valued connection induces
the affine gauge transformation of its adjoint connection.  The derivative
of the conjugation gauge is calculated, not supplied. -/

namespace QuaternionicSymmetry.QuaternionicProjectiveAdjointGaugeDescent

open QuaternionicProjectiveAdjointGaugeDerivative
  QuaternionicProjectiveAdjointGaugeAlgebra
  LocalConnectionGauge
open scoped Topology
noncomputable section

variable {E R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R]

local instance : NormedSpace ℝ R := inferInstance

def ad : R →L[ℝ] (R →L[ℝ] R) :=
  (ContinuousLinearMap.mul ℝ R) - (ContinuousLinearMap.mul ℝ R).flip

@[simp] theorem ad_apply (A B : R) : ad A B = A * B - B * A := rfl

def adjointForm (Γ : LocalConnection.Form (E := E) (A := R)) :
    LocalConnection.Form (E := E) (A := R →L[ℝ] R) :=
  fun y => (ad (R := R)).comp (Γ y)

theorem adjointForm_apply (Γ : LocalConnection.Form (E := E) (A := R))
    (x u : E) (B : R) :
    adjointForm Γ x u B = Γ x u * B - B * Γ x u := rfl

theorem adjoint_transform (Γ : LocalConnection.Form (E := E) (A := R))
    (g h : E → R) (x u : E)
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h x)
    (hleft : (fun y => h y * g y) =ᶠ[𝓝 x] fun _ => 1)
    (hleftx : h x * g x = 1) (hrightx : g x * h x = 1) :
    adjointForm (LocalConnectionGauge.transform Γ g h) x u =
      LocalConnectionGauge.transform (adjointForm Γ)
        (conjugationGauge g h) (conjugationGauge h g) x u := by
  apply ContinuousLinearMap.ext
  intro B
  have hdh := fderiv_inverse_pair g h x hg hh hleft hrightx u
  have hder : fderiv ℝ h x u * g x = -(h x * fderiv ℝ g x u) := by
    rw [hdh]
    simp only [neg_mul, mul_assoc, hleftx, mul_one]
  have halg := commutator_affine (g x) (h x) (Γ x u)
    (fderiv ℝ g x u) (fderiv ℝ h x u) B hleftx hder
  change
    (h x * (Γ x u * g x + fderiv ℝ g x u)) * B -
      B * (h x * (Γ x u * g x + fderiv ℝ g x u)) =
    (conjugationGauge h g x)
      (adjointForm Γ x u (conjugationGauge g h x B) +
        fderiv ℝ (conjugationGauge g h) x u B)
  rw [fderiv_conjugationGauge_apply g h x u B hg hh]
  simpa only [adjointForm_apply, conjugationGauge_apply, mul_add, add_mul] using halg

end
end QuaternionicSymmetry.QuaternionicProjectiveAdjointGaugeDescent
