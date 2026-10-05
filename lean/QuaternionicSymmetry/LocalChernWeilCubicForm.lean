import QuaternionicSymmetry.LocalChernWeilQuadratic

/-!
# An iterated normalized cubic curvature form

The normalized `2∧4` pairing below extends the existing normalized `2∧2`
product.  It constructs a genuine scalar six-form from three copies of the
local curvature.  Its closedness is not asserted: proving that requires a
graded exterior Leibniz rule for these normalized products, followed by
Bianchi and cyclic trace cancellation.
-/

namespace QuaternionicSymmetry.LocalChernWeilCubicForm

open QuaternionicSymmetry.ContinuousAlternation
  QuaternionicSymmetry.ContinuousMultilinearProduct
  QuaternionicSymmetry.LocalConnection
  QuaternionicSymmetry.LocalConnectionForms
  QuaternionicSymmetry.LocalConnectionExterior
  QuaternionicSymmetry.LocalChernWeilQuadratic

noncomputable section

variable {E A B C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup C] [NormedSpace ℝ C]

local instance : NormedAddCommGroup (E [⋀^Fin 2]→L[ℝ] A) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 2]→L[ℝ] A) := inferInstance
local instance : NormedAddCommGroup (E [⋀^Fin 4]→L[ℝ] B) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 4]→L[ℝ] B) := inferInstance

/-- The normalized exterior product of a two-form and a four-form through a
continuous coefficient pairing.  The factor is `1/(2!4!) = 1/48`. -/
def wedge24 (P : A →L[ℝ] B →L[ℝ] C)
    (α : E [⋀^Fin 2]→L[ℝ] A) (β : E [⋀^Fin 4]→L[ℝ] B) :
    E [⋀^Fin 6]→L[ℝ] C :=
  (48⁻¹ : ℝ) • alternationCLM
    ((concatenate P α.toContinuousMultilinearMap β.toContinuousMultilinearMap).domDomCongr
      (finSumFinEquiv (m := 2) (n := 4)))

theorem wedge24_add_left (P : A →L[ℝ] B →L[ℝ] C)
    (α₁ α₂ : E [⋀^Fin 2]→L[ℝ] A) (β : E [⋀^Fin 4]→L[ℝ] B) :
    wedge24 P (α₁ + α₂) β = wedge24 P α₁ β + wedge24 P α₂ β := by
  ext v
  simp [wedge24, alternationCLM_apply, concatenate_apply,
    Finset.sum_add_distrib, smul_add]

theorem wedge24_smul_left (P : A →L[ℝ] B →L[ℝ] C)
    (r : ℝ) (α : E [⋀^Fin 2]→L[ℝ] A) (β : E [⋀^Fin 4]→L[ℝ] B) :
    wedge24 P (r • α) β = r • wedge24 P α β := by
  ext v
  simp [wedge24, alternationCLM_apply, concatenate_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [smul_comm (Equiv.Perm.sign σ) r]
  simp only [smul_smul]
  rw [mul_comm (48⁻¹ : ℝ) r]

theorem wedge24_add_right (P : A →L[ℝ] B →L[ℝ] C)
    (α : E [⋀^Fin 2]→L[ℝ] A) (β₁ β₂ : E [⋀^Fin 4]→L[ℝ] B) :
    wedge24 P α (β₁ + β₂) = wedge24 P α β₁ + wedge24 P α β₂ := by
  ext v
  simp [wedge24, alternationCLM_apply, concatenate_apply,
    Finset.sum_add_distrib, smul_add]

theorem wedge24_smul_right (P : A →L[ℝ] B →L[ℝ] C)
    (r : ℝ) (α : E [⋀^Fin 2]→L[ℝ] A) (β : E [⋀^Fin 4]→L[ℝ] B) :
    wedge24 P α (r • β) = r • wedge24 P α β := by
  ext v
  simp [wedge24, alternationCLM_apply, concatenate_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [smul_comm (Equiv.Perm.sign σ) r]
  simp only [smul_smul]
  rw [mul_comm (48⁻¹ : ℝ) r]

def wedge24Linear (P : A →L[ℝ] B →L[ℝ] C) :
    (E [⋀^Fin 2]→L[ℝ] A) →ₗ[ℝ]
      (E [⋀^Fin 4]→L[ℝ] B) →ₗ[ℝ] (E [⋀^Fin 6]→L[ℝ] C) :=
  LinearMap.mk₂ ℝ (wedge24 P)
    (wedge24_add_left P) (wedge24_smul_left P)
    (wedge24_add_right P) (wedge24_smul_right P)

theorem norm_wedge24_le (P : A →L[ℝ] B →L[ℝ] C)
    (α : E [⋀^Fin 2]→L[ℝ] A) (β : E [⋀^Fin 4]→L[ℝ] B) :
    ‖wedge24 P α β‖ ≤ 15 * ‖P‖ * ‖α‖ * ‖β‖ := by
  let f := concatenate P α.toContinuousMultilinearMap β.toContinuousMultilinearMap
  let g := f.domDomCongr (finSumFinEquiv (m := 2) (n := 4))
  have h₁ : ‖alternationCLM g‖ ≤ 720 * ‖g‖ := by
    simpa using norm_alternation_le g
  have h₂ : ‖f‖ ≤ ‖P‖ * ‖α‖ * ‖β‖ := by
    simpa only [ContinuousAlternatingMap.norm_toContinuousMultilinearMap] using
      norm_concatenate_le P α.toContinuousMultilinearMap β.toContinuousMultilinearMap
  calc
    ‖wedge24 P α β‖ = (48⁻¹ : ℝ) * ‖alternationCLM g‖ := by
      simp [wedge24, g, f, norm_smul]
    _ ≤ (48⁻¹ : ℝ) * (720 * ‖g‖) := by gcongr
    _ = 15 * ‖f‖ := by
      rw [ContinuousMultilinearMap.norm_domDomCongr]
      ring
    _ ≤ 15 * (‖P‖ * ‖α‖ * ‖β‖) := by gcongr
    _ = 15 * ‖P‖ * ‖α‖ * ‖β‖ := by ring

def wedge24CLM (P : A →L[ℝ] B →L[ℝ] C) :
    (E [⋀^Fin 2]→L[ℝ] A) →L[ℝ]
      (E [⋀^Fin 4]→L[ℝ] B) →L[ℝ] (E [⋀^Fin 6]→L[ℝ] C) :=
  (wedge24Linear P).mkContinuous₂ (15 * ‖P‖)
    (fun α β => norm_wedge24_le P α β)

theorem wedge24CLM_apply (P : A →L[ℝ] B →L[ℝ] C)
    (α : E [⋀^Fin 2]→L[ℝ] A) (β : E [⋀^Fin 4]→L[ℝ] B) :
    wedge24CLM P α β = wedge24 P α β := rfl

set_option maxHeartbeats 1000000 in
theorem differentiableAt_wedge24 (P : A →L[ℝ] B →L[ℝ] C)
    (α : E → E [⋀^Fin 2]→L[ℝ] A)
    (β : E → E [⋀^Fin 4]→L[ℝ] B) (x : E)
    (hα : DifferentiableAt ℝ α x) (hβ : DifferentiableAt ℝ β x) :
    DifferentiableAt ℝ (fun y => wedge24 P (α y) (β y)) x := by
  have hconst : DifferentiableAt ℝ (fun _ : E =>
      wedge24CLM (E := E) (A := A) (B := B) (C := C) P) x :=
    differentiableAt_const _
  have hf : DifferentiableAt ℝ (fun y =>
      wedge24CLM (E := E) (A := A) (B := B) (C := C) P (α y)) x :=
    DifferentiableAt.clm_apply
      (G := E [⋀^Fin 2]→L[ℝ] A)
      (H := (E [⋀^Fin 4]→L[ℝ] B) →L[ℝ] E [⋀^Fin 6]→L[ℝ] C)
      hconst hα
  simpa only [wedge24CLM_apply] using hf.clm_apply hβ

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R

/-- The scalar six-form obtained by iterating the normalized exterior
products on three copies of local curvature. -/
def traceCubeForm (T : R →L[ℝ] C) (Γ : Form (E := E) (A := R)) :
    E → E [⋀^Fin 6]→L[ℝ] C := fun x =>
  wedge24 (traceProduct T) (curvatureForm Γ x)
    (wedge22 (ContinuousLinearMap.mul ℝ R)
      (curvatureForm Γ x) (curvatureForm Γ x))

theorem differentiableAt_traceCubeForm (T : R →L[ℝ] C)
    (Γ : Form (E := E) (A := R)) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) :
    DifferentiableAt ℝ (traceCubeForm T Γ) x := by
  have h₁ : DifferentiableAt ℝ Γ x := hΓ.differentiableAt (by norm_num)
  have h₂ : DifferentiableAt ℝ (fderiv ℝ Γ) x :=
    (hΓ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hF : DifferentiableAt ℝ (curvatureForm Γ) x :=
    differentiableAt_curvatureForm Γ x h₁ h₂
  exact differentiableAt_wedge24 (traceProduct T) (curvatureForm Γ)
    (fun y => wedge22 (ContinuousLinearMap.mul ℝ R)
      (curvatureForm Γ y) (curvatureForm Γ y)) x hF
    (differentiableAt_wedge22 (ContinuousLinearMap.mul ℝ R)
      (curvatureForm Γ) (curvatureForm Γ) x hF hF)

end
end QuaternionicSymmetry.LocalChernWeilCubicForm
