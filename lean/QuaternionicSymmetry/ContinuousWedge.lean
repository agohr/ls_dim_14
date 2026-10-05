import QuaternionicSymmetry.ContinuousMultilinearProduct
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# Normalized wedge products of continuous alternating forms

For every pair of degrees this file constructs the actual alternating wedge
through a continuous bilinear pairing of coefficients.  The normalization is
`1/(p!q!)`, matching the `2∧2` and `2∧4` Chern--Weil forms elsewhere in this
library.  The bundled pairing supports Fréchet differentiation of form fields.
-/

namespace QuaternionicSymmetry.ContinuousWedge

open QuaternionicSymmetry.ContinuousAlternation
  QuaternionicSymmetry.ContinuousMultilinearProduct

noncomputable section

variable {E A B C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup C] [NormedSpace ℝ C]
  {p q : ℕ}

local instance : NormedAddCommGroup (E [⋀^Fin p]→L[ℝ] A) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin p]→L[ℝ] A) := inferInstance
local instance : NormedAddCommGroup (E [⋀^Fin q]→L[ℝ] B) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin q]→L[ℝ] B) := inferInstance

/-- The normalized `p∧q` product through a bounded bilinear coefficient
pairing.  No commutativity of the coefficient pairing is needed. -/
def wedge (P : A →L[ℝ] B →L[ℝ] C)
    (α : E [⋀^Fin p]→L[ℝ] A) (β : E [⋀^Fin q]→L[ℝ] B) :
    E [⋀^Fin (p + q)]→L[ℝ] C :=
  (((p.factorial * q.factorial : ℕ) : ℝ)⁻¹) • alternationCLM
    ((concatenate P α.toContinuousMultilinearMap β.toContinuousMultilinearMap).domDomCongr
      (finSumFinEquiv (m := p) (n := q)))

theorem wedge_apply (P : A →L[ℝ] B →L[ℝ] C)
    (α : E [⋀^Fin p]→L[ℝ] A) (β : E [⋀^Fin q]→L[ℝ] B)
    (v : Fin (p + q) → E) :
    wedge P α β v = (((p.factorial * q.factorial : ℕ) : ℝ)⁻¹) •
      ∑ σ : Equiv.Perm (Fin (p + q)), Equiv.Perm.sign σ •
        P (α (v ∘ σ ∘ (finSumFinEquiv (m := p) (n := q)) ∘ Sum.inl))
          (β (v ∘ σ ∘ (finSumFinEquiv (m := p) (n := q)) ∘ Sum.inr)) := by
  simp [wedge, alternationCLM_apply, concatenate_apply,
    ContinuousMultilinearMap.domDomCongr_apply, Function.comp_def]

theorem wedge_add_left (P : A →L[ℝ] B →L[ℝ] C)
    (α₁ α₂ : E [⋀^Fin p]→L[ℝ] A) (β : E [⋀^Fin q]→L[ℝ] B) :
    wedge P (α₁ + α₂) β = wedge P α₁ β + wedge P α₂ β := by
  ext v
  simp [wedge, alternationCLM_apply, concatenate_apply,
    Finset.sum_add_distrib, smul_add]

theorem wedge_smul_left (P : A →L[ℝ] B →L[ℝ] C)
    (r : ℝ) (α : E [⋀^Fin p]→L[ℝ] A) (β : E [⋀^Fin q]→L[ℝ] B) :
    wedge P (r • α) β = r • wedge P α β := by
  ext v
  simp [wedge, alternationCLM_apply, concatenate_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [smul_comm (Equiv.Perm.sign σ) r]
  simp only [smul_smul]
  congr 1
  ring

theorem wedge_add_right (P : A →L[ℝ] B →L[ℝ] C)
    (α : E [⋀^Fin p]→L[ℝ] A) (β₁ β₂ : E [⋀^Fin q]→L[ℝ] B) :
    wedge P α (β₁ + β₂) = wedge P α β₁ + wedge P α β₂ := by
  ext v
  simp [wedge, alternationCLM_apply, concatenate_apply,
    Finset.sum_add_distrib, smul_add]

theorem wedge_smul_right (P : A →L[ℝ] B →L[ℝ] C)
    (r : ℝ) (α : E [⋀^Fin p]→L[ℝ] A) (β : E [⋀^Fin q]→L[ℝ] B) :
    wedge P α (r • β) = r • wedge P α β := by
  ext v
  simp [wedge, alternationCLM_apply, concatenate_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [smul_comm (Equiv.Perm.sign σ) r]
  simp only [smul_smul]
  congr 1
  ring

def wedgeLinear (P : A →L[ℝ] B →L[ℝ] C) :
    (E [⋀^Fin p]→L[ℝ] A) →ₗ[ℝ]
      (E [⋀^Fin q]→L[ℝ] B) →ₗ[ℝ] (E [⋀^Fin (p + q)]→L[ℝ] C) :=
  LinearMap.mk₂ ℝ (wedge P)
    (wedge_add_left P) (wedge_smul_left P)
    (wedge_add_right P) (wedge_smul_right P)

theorem norm_wedge_le (P : A →L[ℝ] B →L[ℝ] C)
    (α : E [⋀^Fin p]→L[ℝ] A) (β : E [⋀^Fin q]→L[ℝ] B) :
    ‖wedge P α β‖ ≤ ((p + q).factorial : ℝ) * ‖P‖ * ‖α‖ * ‖β‖ := by
  let f := concatenate P α.toContinuousMultilinearMap β.toContinuousMultilinearMap
  let g := f.domDomCongr (finSumFinEquiv (m := p) (n := q))
  have h₁ : ‖alternationCLM g‖ ≤ ((p + q).factorial : ℝ) * ‖g‖ := by
    simpa using norm_alternation_le g
  have h₂ : ‖f‖ ≤ ‖P‖ * ‖α‖ * ‖β‖ := by
    simpa only [ContinuousAlternatingMap.norm_toContinuousMultilinearMap] using
      norm_concatenate_le P α.toContinuousMultilinearMap β.toContinuousMultilinearMap
  have hfac : 1 ≤ ((p.factorial * q.factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
  have hinv : ((p.factorial * q.factorial : ℕ) : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hfac
  calc
    ‖wedge P α β‖ = ((p.factorial * q.factorial : ℕ) : ℝ)⁻¹ * ‖alternationCLM g‖ := by
      simp [wedge, g, f, norm_smul]
    _ ≤ 1 * (((p + q).factorial : ℝ) * ‖g‖) := by gcongr
    _ = ((p + q).factorial : ℝ) * ‖f‖ := by
      rw [ContinuousMultilinearMap.norm_domDomCongr]
      ring
    _ ≤ ((p + q).factorial : ℝ) * (‖P‖ * ‖α‖ * ‖β‖) := by gcongr
    _ = ((p + q).factorial : ℝ) * ‖P‖ * ‖α‖ * ‖β‖ := by ring

def wedgeCLM (P : A →L[ℝ] B →L[ℝ] C) :
    (E [⋀^Fin p]→L[ℝ] A) →L[ℝ]
      (E [⋀^Fin q]→L[ℝ] B) →L[ℝ] (E [⋀^Fin (p + q)]→L[ℝ] C) :=
  (wedgeLinear P).mkContinuous₂ (((p + q).factorial : ℝ) * ‖P‖)
    (fun α β => norm_wedge_le P α β)

theorem wedgeCLM_apply (P : A →L[ℝ] B →L[ℝ] C)
    (α : E [⋀^Fin p]→L[ℝ] A) (β : E [⋀^Fin q]→L[ℝ] B) :
    wedgeCLM P α β = wedge P α β := rfl

theorem differentiableAt_wedge (P : A →L[ℝ] B →L[ℝ] C)
    (α : E → E [⋀^Fin p]→L[ℝ] A)
    (β : E → E [⋀^Fin q]→L[ℝ] B) (x : E)
    (hα : DifferentiableAt ℝ α x) (hβ : DifferentiableAt ℝ β x) :
    DifferentiableAt ℝ (fun y => wedge P (α y) (β y)) x := by
  have hconst : DifferentiableAt ℝ (fun _ : E =>
      wedgeCLM (E := E) (A := A) (B := B) (C := C) (p := p) (q := q) P) x :=
    differentiableAt_const _
  have hf : DifferentiableAt ℝ (fun y =>
      wedgeCLM (E := E) (A := A) (B := B) (C := C) (p := p) (q := q) P (α y)) x :=
    DifferentiableAt.clm_apply
      (G := E [⋀^Fin p]→L[ℝ] A)
      (H := (E [⋀^Fin q]→L[ℝ] B) →L[ℝ] E [⋀^Fin (p + q)]→L[ℝ] C)
      hconst hα
  simpa only [wedgeCLM_apply] using hf.clm_apply hβ

theorem fderiv_wedge (P : A →L[ℝ] B →L[ℝ] C)
    (α : E → E [⋀^Fin p]→L[ℝ] A)
    (β : E → E [⋀^Fin q]→L[ℝ] B) (x u : E)
    (hα : DifferentiableAt ℝ α x) (hβ : DifferentiableAt ℝ β x) :
    fderiv ℝ (fun y => wedge P (α y) (β y)) x u =
      wedge P (fderiv ℝ α x u) (β x) +
        wedge P (α x) (fderiv ℝ β x u) := by
  let W := wedgeCLM (E := E) (A := A) (B := B) (C := C) (p := p) (q := q) P
  have hc : DifferentiableAt ℝ (fun _ : E => W) x := differentiableAt_const _
  have h₁ : DifferentiableAt ℝ (fun y => W (α y)) x :=
    DifferentiableAt.clm_apply
      (G := E [⋀^Fin p]→L[ℝ] A)
      (H := (E [⋀^Fin q]→L[ℝ] B) →L[ℝ] E [⋀^Fin (p + q)]→L[ℝ] C)
      hc hα
  have hD₁ := fderiv_clm_apply
    (G := E [⋀^Fin p]→L[ℝ] A)
    (H := (E [⋀^Fin q]→L[ℝ] B) →L[ℝ] E [⋀^Fin (p + q)]→L[ℝ] C)
    hc hα
  have hD₂ := fderiv_clm_apply
    (G := E [⋀^Fin q]→L[ℝ] B)
    (H := E [⋀^Fin (p + q)]→L[ℝ] C)
    h₁ hβ
  have hzero : fderiv ℝ (fun _ : E => W) x = 0 := by simp
  change fderiv ℝ (fun y => W (α y) (β y)) x u = _
  rw [hD₂, hD₁, hzero]
  simp [W, wedgeCLM_apply, add_comm]

/-- The exterior derivative of a normalized product as a sum of its actual
Fréchet derivatives in each coefficient slot.  Identifying these sums with
wedges of the exterior derivatives is the graded shuffle identity. -/
theorem extDeriv_wedge_apply (P : A →L[ℝ] B →L[ℝ] C)
    (α : E → E [⋀^Fin p]→L[ℝ] A)
    (β : E → E [⋀^Fin q]→L[ℝ] B) (x : E)
    (hα : DifferentiableAt ℝ α x) (hβ : DifferentiableAt ℝ β x)
    (v : Fin (p + q + 1) → E) :
    extDeriv (fun y => wedge P (α y) (β y)) x v =
      ∑ i : Fin (p + q + 1), (-1 : ℤ) ^ i.val •
        (wedge P (fderiv ℝ α x (v i)) (β x) (i.removeNth v) +
          wedge P (α x) (fderiv ℝ β x (v i)) (i.removeNth v)) := by
  have hω := differentiableAt_wedge P α β x hα hβ
  rw [extDeriv_apply hω]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_continuousAlternatingMap_apply_const_apply hω (i.removeNth v) (v i),
    fderiv_wedge P α β x (v i) hα hβ]
  rfl

end
end QuaternionicSymmetry.ContinuousWedge
