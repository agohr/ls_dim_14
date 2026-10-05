import QuaternionicSymmetry.LocalConnectionBianchi

/-! Regularity of local curvature and the Bianchi identity for the actual
exterior derivative of its continuous alternating two-form. -/

namespace QuaternionicSymmetry.LocalConnectionExterior

open LocalConnection LocalConnectionForms LocalConnectionBianchi ContinuousAlternatingMap

noncomputable section

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]

local instance : NormedSpace ℝ A := NormedAlgebra.toNormedSpace A
local instance : NormedAddCommGroup (E →L[ℝ] A) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] A) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] A) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] A) := ContinuousLinearMap.toNormedSpace

def alternatingPartCLM : Bilinear (E := E) (A := A) →L[ℝ] E [⋀^Fin 2]→L[ℝ] A :=
  (alternatizeUncurryFinCLM ℝ E A).comp
    ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] A) (E [⋀^Fin 1]→L[ℝ] A)) oneFormMap)

theorem alternatingPartCLM_apply (B : Bilinear (E := E) (A := A)) :
    alternatingPartCLM B = alternatingPart B := rfl

def productCLM : (E →L[ℝ] A) →L[ℝ] (E →L[ℝ] A) →L[ℝ] E →L[ℝ] E →L[ℝ] A :=
  ContinuousLinearMap.precompL E
    (ContinuousLinearMap.precompR E (ContinuousLinearMap.mul ℝ A))

theorem productCLM_apply (Γ θ : Form (E := E) (A := A)) (x : E) :
    productCLM (Γ x) (θ x) = product Γ θ x := by
  ext v w
  rfl

theorem differentiableAt_product (Γ θ : Form (E := E) (A := A)) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) (hθ : DifferentiableAt ℝ θ x) :
    DifferentiableAt ℝ (product Γ θ) x := by
  have h := (((productCLM (E := E) (A := A)).differentiableAt.comp x hΓ).clm_apply hθ)
  simpa only [productCLM_apply] using h

theorem differentiableAt_curvatureForm (Γ : Form (E := E) (A := A)) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) (hD : DifferentiableAt ℝ (fderiv ℝ Γ) x) :
    DifferentiableAt ℝ (curvatureForm Γ) x := by
  exact (alternatingPartCLM (E := E) (A := A)).differentiableAt.comp x
    (hD.add (differentiableAt_product Γ Γ x hΓ hΓ))

theorem extDeriv_curvatureForm_apply (Γ : Form (E := E) (A := A)) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) (hD : DifferentiableAt ℝ (fderiv ℝ Γ) x)
    (v : Fin 3 → E) :
    extDeriv (curvatureForm Γ) x v =
      fderiv ℝ (fun y => curvature Γ y (v 1) (v 2)) x (v 0) -
      fderiv ℝ (fun y => curvature Γ y (v 0) (v 2)) x (v 1) +
      fderiv ℝ (fun y => curvature Γ y (v 0) (v 1)) x (v 2) := by
  rw [extDeriv_apply (differentiableAt_curvatureForm Γ x hΓ hD)]
  simp [Fin.sum_univ_succ, curvatureForm_apply, Fin.removeNth, sub_eq_add_neg, add_assoc]

def commutatorForm (Γ : Form (E := E) (A := A)) (F : E [⋀^Fin 2]→L[ℝ] A)
    (x : E) : E [⋀^Fin 3]→L[ℝ] A :=
  alternatizeUncurryFin
    (((ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ E A A).flip F).comp
      (((ContinuousLinearMap.mul ℝ A) - (ContinuousLinearMap.mul ℝ A).flip).comp (Γ x)))

theorem commutatorForm_apply (Γ : Form (E := E) (A := A))
    (F : E [⋀^Fin 2]→L[ℝ] A) (x : E) (v : Fin 3 → E) :
    commutatorForm Γ F x v =
      (Γ x (v 0) * F ![v 1, v 2] - F ![v 1, v 2] * Γ x (v 0)) -
      (Γ x (v 1) * F ![v 0, v 2] - F ![v 0, v 2] * Γ x (v 1)) +
      (Γ x (v 2) * F ![v 0, v 1] - F ![v 0, v 1] * Γ x (v 2)) := by
  have h₀ : Fin.tail v = ![v 1, v 2] := by ext i; fin_cases i <;> rfl
  have h₁ : Fin.removeNth (1 : Fin 3) v = ![v 0, v 2] := by ext i; fin_cases i <;> rfl
  have h₂ : Fin.removeNth (2 : Fin 3) v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  simp [commutatorForm, alternatizeUncurryFin_apply, Fin.sum_univ_succ, h₀, h₁, h₂,
    sub_eq_add_neg]
  abel

theorem bianchi_form (Γ : Form (E := E) (A := A)) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) :
    extDeriv (curvatureForm Γ) x + commutatorForm Γ (curvatureForm Γ x) x = 0 := by
  have h₁ : DifferentiableAt ℝ Γ x := hΓ.differentiableAt (by norm_num)
  have h₂ : DifferentiableAt ℝ (fderiv ℝ Γ) x :=
    (hΓ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hs := hΓ.isSymmSndFDerivAt (by norm_num)
  ext v
  change extDeriv (curvatureForm Γ) x v + commutatorForm Γ (curvatureForm Γ x) x v = 0
  rw [extDeriv_curvatureForm_apply Γ x h₁ h₂, commutatorForm_apply]
  simp_rw [fderiv_curvature_apply Γ x h₁ h₂]
  simp only [curvatureForm_apply, Matrix.cons_val_zero, Matrix.cons_val_one, curvature_apply]
  rw [hs.eq (v 1) (v 0), hs.eq (v 2) (v 0), hs.eq (v 2) (v 1)]
  noncomm_ring

end
end QuaternionicSymmetry.LocalConnectionExterior
