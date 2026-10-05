import QuaternionicSymmetry.LocalChernWeilCubicForm

/-! Differential calculus for the normalized `2∧4` pairing. -/

namespace QuaternionicSymmetry.LocalWedge24Leibniz

open QuaternionicSymmetry.LocalChernWeilCubicForm

noncomputable section

variable {E A B C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup C] [NormedSpace ℝ C]

local instance : NormedAddCommGroup (E [⋀^Fin 2]→L[ℝ] A) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 2]→L[ℝ] A) := inferInstance
local instance : NormedAddCommGroup (E [⋀^Fin 4]→L[ℝ] B) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 4]→L[ℝ] B) := inferInstance

/-- Spatial Fréchet product rule for the normalized `2∧4` pairing. -/
theorem fderiv_wedge24 (P : A →L[ℝ] B →L[ℝ] C)
    (α : E → E [⋀^Fin 2]→L[ℝ] A)
    (β : E → E [⋀^Fin 4]→L[ℝ] B) (x u : E)
    (hα : DifferentiableAt ℝ α x) (hβ : DifferentiableAt ℝ β x) :
    fderiv ℝ (fun y => wedge24 P (α y) (β y)) x u =
      wedge24 P (fderiv ℝ α x u) (β x) +
        wedge24 P (α x) (fderiv ℝ β x u) := by
  let W := wedge24CLM (E := E) (A := A) (B := B) (C := C) P
  have hc : DifferentiableAt ℝ (fun _ : E => W) x := differentiableAt_const _
  have h₁ : DifferentiableAt ℝ (fun y => W (α y)) x :=
    DifferentiableAt.clm_apply
      (G := E [⋀^Fin 2]→L[ℝ] A)
      (H := (E [⋀^Fin 4]→L[ℝ] B) →L[ℝ] E [⋀^Fin 6]→L[ℝ] C)
      hc hα
  have hD₁ := fderiv_clm_apply
    (G := E [⋀^Fin 2]→L[ℝ] A)
    (H := (E [⋀^Fin 4]→L[ℝ] B) →L[ℝ] E [⋀^Fin 6]→L[ℝ] C)
    hc hα
  have hD₂ := fderiv_clm_apply
    (G := E [⋀^Fin 4]→L[ℝ] B)
    (H := E [⋀^Fin 6]→L[ℝ] C)
    h₁ hβ
  have hzero : fderiv ℝ (fun _ : E => W) x = 0 := by simp
  change fderiv ℝ (fun y => W (α y) (β y)) x u = _
  rw [hD₂, hD₁, hzero]
  simp [W, wedge24CLM_apply, add_comm]

/-- The exterior derivative of a normalized `2∧4` product, expressed as its
seven-term alternating sum of the two Fréchet slot derivatives.  A graded
Leibniz theorem would identify the two sums separately with normalized
`3∧4` and `2∧5` products of the exterior derivatives. -/
theorem extDeriv_wedge24_apply (P : A →L[ℝ] B →L[ℝ] C)
    (α : E → E [⋀^Fin 2]→L[ℝ] A)
    (β : E → E [⋀^Fin 4]→L[ℝ] B) (x : E)
    (hα : DifferentiableAt ℝ α x) (hβ : DifferentiableAt ℝ β x)
    (v : Fin 7 → E) :
    extDeriv (fun y => wedge24 P (α y) (β y)) x v =
      ∑ i : Fin 7, (-1 : ℤ) ^ i.val •
        (wedge24 P (fderiv ℝ α x (v i)) (β x) (i.removeNth v) +
          wedge24 P (α x) (fderiv ℝ β x (v i)) (i.removeNth v)) := by
  have hω := differentiableAt_wedge24 P α β x hα hβ
  rw [extDeriv_apply hω]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_continuousAlternatingMap_apply_const_apply hω (i.removeNth v) (v i),
    fderiv_wedge24 P α β x (v i) hα hβ]
  rfl

end
end QuaternionicSymmetry.LocalWedge24Leibniz
