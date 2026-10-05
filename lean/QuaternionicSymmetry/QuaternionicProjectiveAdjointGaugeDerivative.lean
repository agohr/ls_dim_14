import QuaternionicSymmetry.QuaternionicProjectiveAdjointGaugeAlgebra

/-! The derivative of conjugation by a variable operator gauge. -/

namespace QuaternionicSymmetry.QuaternionicProjectiveAdjointGaugeDerivative

open LocalConnectionBianchi
open scoped Topology
noncomputable section

variable {E R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R]

def conjugationGauge (g h : E → R) (y : E) : R →L[ℝ] R :=
  (((ContinuousLinearMap.mul ℝ R).flip) (h y)).comp
    ((ContinuousLinearMap.mul ℝ R) (g y))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp] theorem conjugationGauge_apply (g h : E → R) (y : E) (B : R) :
    conjugationGauge g h y B = g y * B * h y := rfl

theorem differentiableAt_conjugationGauge (g h : E → R) (x : E)
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h x) :
    DifferentiableAt ℝ (conjugationGauge g h) x := by
  exact (((ContinuousLinearMap.mul ℝ R).flip).differentiableAt.comp x hh).clm_comp
    ((ContinuousLinearMap.mul ℝ R).differentiableAt.comp x hg)

theorem fderiv_conjugationGauge_apply (g h : E → R) (x u : E) (B : R)
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h x) :
    fderiv ℝ (conjugationGauge g h) x u B =
      fderiv ℝ g x u * B * h x +
        g x * B * fderiv ℝ h x u := by
  have hgb : DifferentiableAt ℝ (fun y => g y * B) x :=
    hg.mul_const B
  have hderiv := (hgb.hasFDerivAt.mul' hh.hasFDerivAt).fderiv
  have he := congrArg (fun L : E →L[ℝ] R => L u) hderiv
  rw [← fderiv_eval_const (differentiableAt_conjugationGauge g h x hg hh) B u]
  change fderiv ℝ (fun y => g y * B * h y) x u = _
  have he' : fderiv ℝ (fun y => g y * B * h y) x u =
      ((g x * B) • fderiv ℝ h x +
        MulOpposite.op (h x) • fderiv ℝ (fun y => g y * B) x) u := by
    simpa only [Pi.mul_apply] using he
  rw [he']
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, op_smul_eq_mul]
  rw [fderiv_mul_const' hg B]
  simp only [ContinuousLinearMap.smul_apply, op_smul_eq_mul]
  abel

end
end QuaternionicSymmetry.QuaternionicProjectiveAdjointGaugeDerivative
