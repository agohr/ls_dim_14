import QuaternionicSymmetry.LocalConnectionGauge
import QuaternionicSymmetry.LocalConnectionCoordinatePullback

/-! Transport of an affine connection overlap through two constant frame
identifications. -/

namespace QuaternionicSymmetry.LocalConnectionConstantConjugation

open LocalConnectionGauge LocalConnection
noncomputable section

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]

def transportedGauge (Qinv P : A) (g : E → A) (y : E) : A :=
  Qinv * g y * P

def transportedForm (Qinv Q : A) (Γ : Form (E := E) (A := A)) :
    Form (E := E) (A := A) :=
  fun y => ((ContinuousLinearMap.mul ℝ A) Qinv).comp
    (((ContinuousLinearMap.mul ℝ A).flip Q).comp (Γ y))

theorem transportedForm_pullback (Qinv Q : A)
    (Γ : Form (E := E) (A := A)) (φ : E → E) :
    transportedForm Qinv Q (LocalConnectionCoordinatePullback.pullback Γ φ) =
      LocalConnectionCoordinatePullback.pullback
        (transportedForm Qinv Q Γ) φ := by
  funext y
  apply ContinuousLinearMap.ext
  intro u
  rfl

theorem fderiv_transportedGauge (Qinv P : A) (g : E → A) (y u : E)
    (hg : DifferentiableAt ℝ g y) :
    fderiv ℝ (transportedGauge Qinv P g) y u =
      Qinv * fderiv ℝ g y u * P := by
  have hd : fderiv ℝ (fun z => Qinv * g z * P) y =
      MulOpposite.op P • (Qinv • fderiv ℝ g y) := by
    rw [fderiv_mul_const' (hg.const_mul Qinv) P, fderiv_const_mul hg Qinv]
  have he := congrArg (fun F : E →L[ℝ] A => F u) hd
  simpa only [transportedGauge, ContinuousLinearMap.smul_apply,
    smul_eq_mul, op_smul_eq_mul] using he

theorem transform_constant_conjugation
    (Γ : Form (E := E) (A := A)) (g h : E → A)
    (P Pinv Q Qinv : A)
    (hQ₂ : Q * Qinv = 1)
    (y u : E) (hg : DifferentiableAt ℝ g y) :
    Pinv * (transform Γ g h y u) * P =
      transform (transportedForm Qinv Q Γ)
        (transportedGauge Qinv P g)
        (transportedGauge Pinv Q h) y u := by
  rw [transform_apply, transform_apply,
    fderiv_transportedGauge Qinv P g y u hg]
  change Pinv * (h y * (Γ y u * g y + fderiv ℝ g y u)) * P =
    (Pinv * h y * Q) *
      ((Qinv * (Γ y u * Q)) * (Qinv * g y * P) +
        Qinv * fderiv ℝ g y u * P)
  simp only [mul_add, add_mul]
  calc
    _ = Pinv * h y * Γ y u * g y * P +
        Pinv * h y * fderiv ℝ g y u * P := by noncomm_ring
    _ = _ := by
      simp only [mul_assoc, ← mul_assoc Q Qinv, hQ₂, one_mul]

end
end QuaternionicSymmetry.LocalConnectionConstantConjugation
