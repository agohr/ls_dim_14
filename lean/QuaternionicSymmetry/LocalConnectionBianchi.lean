import QuaternionicSymmetry.LocalConnectionForms
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! The local Bianchi identity, derived from actual second derivatives and
their symmetry for a twice continuously differentiable connection form. -/

namespace QuaternionicSymmetry.LocalConnectionBianchi

open LocalConnection

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_eval_const {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → F →L[ℝ] G} {x : E}
    (hf : DifferentiableAt ℝ f x) (v : F) (u : E) :
    fderiv ℝ (fun y => f y v) x u = fderiv ℝ f x u v := by
  rw [fderiv_clm_apply hf (differentiableAt_const _)]
  simp

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

theorem fderiv_curvature_apply (Γ : Form (E := E) (A := A)) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) (hD : DifferentiableAt ℝ (fderiv ℝ Γ) x) (u v w : E) :
    fderiv ℝ (fun y => curvature Γ y v w) x u =
      fderiv ℝ (fderiv ℝ Γ) x u v w - fderiv ℝ (fderiv ℝ Γ) x u w v +
        Γ x v * fderiv ℝ Γ x u w + fderiv ℝ Γ x u v * Γ x w -
        (Γ x w * fderiv ℝ Γ x u v + fderiv ℝ Γ x u w * Γ x v) := by
  have hv : DifferentiableAt ℝ (fun y => Γ y v) x := hΓ.clm_apply (differentiableAt_const _)
  have hw : DifferentiableAt ℝ (fun y => Γ y w) x := hΓ.clm_apply (differentiableAt_const _)
  have hvw : DifferentiableAt ℝ (fun y => fderiv ℝ Γ y v w) x :=
    (hD.clm_apply (differentiableAt_const _)).clm_apply (differentiableAt_const _)
  have hwv : DifferentiableAt ℝ (fun y => fderiv ℝ Γ y w v) x :=
    (hD.clm_apply (differentiableAt_const _)).clm_apply (differentiableAt_const _)
  simp_rw [curvature_apply]
  have hd := (((hvw.hasFDerivAt.sub hwv.hasFDerivAt).add
    (hv.hasFDerivAt.mul' hw.hasFDerivAt)).sub (hw.hasFDerivAt.mul' hv.hasFDerivAt)).fderiv
  change fderiv ℝ (fun y => fderiv ℝ Γ y v w - fderiv ℝ Γ y w v +
    Γ y v * Γ y w - Γ y w * Γ y v) x = _ at hd
  rw [hd]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, op_smul_eq_mul,
    fderiv_eval_const (hD.clm_apply (differentiableAt_const _)),
    fderiv_eval_const hD, fderiv_eval_const hΓ]
  abel

def covariantCurvatureDerivative (Γ : Form (E := E) (A := A)) (x u v w : E) : A :=
  fderiv ℝ (fun y => curvature Γ y v w) x u +
    Γ x u * curvature Γ x v w - curvature Γ x v w * Γ x u

theorem bianchi (Γ : Form (E := E) (A := A)) (x : E) (hΓ : ContDiffAt ℝ 2 Γ x)
    (u v w : E) :
    covariantCurvatureDerivative Γ x u v w + covariantCurvatureDerivative Γ x v w u +
      covariantCurvatureDerivative Γ x w u v = 0 := by
  have h₁ : DifferentiableAt ℝ Γ x := hΓ.differentiableAt (by norm_num)
  have h₂ : DifferentiableAt ℝ (fderiv ℝ Γ) x :=
    (hΓ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hs := hΓ.isSymmSndFDerivAt (by norm_num)
  simp only [covariantCurvatureDerivative]
  simp_rw [fderiv_curvature_apply Γ x h₁ h₂]
  simp only [curvature_apply]
  rw [hs.eq v u, hs.eq w u, hs.eq w v]
  noncomm_ring

end
end QuaternionicSymmetry.LocalConnectionBianchi
