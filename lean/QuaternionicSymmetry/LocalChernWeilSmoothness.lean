import QuaternionicSymmetry.LocalChernWeilTracePowers

/-!
Smoothness of local Chern--Weil curvature trace powers on an open chart
target follows from smoothness of the connection one-form. This discharges
the analytic regularity field used by manifold chart descent.
-/

namespace QuaternionicSymmetry.LocalChernWeilSmoothness

open QuaternionicSymmetry.LocalConnection
  QuaternionicSymmetry.LocalConnectionForms
  QuaternionicSymmetry.LocalConnectionExterior
  QuaternionicSymmetry.LocalChernWeilTracePowers
  QuaternionicSymmetry.ContinuousWedge
open scoped ContDiff Topology

variable {E R B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

noncomputable section

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R
local instance : NormedAddCommGroup (E →L[ℝ] R) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] R) :=
  ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] R) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] R) :=
  ContinuousLinearMap.toNormedSpace

theorem curvatureForm_contDiffOn (Γ : Form (E := E) (A := R))
    {s : Set E} (hs : IsOpen s) (hΓ : ContDiffOn ℝ ∞ Γ s) :
    ContDiffOn ℝ ∞ (curvatureForm Γ) s := by
  have hfd : ContDiffOn ℝ ∞ (fderiv ℝ Γ) s := by
    simpa using hΓ.fderiv_of_isOpen hs (by simp)
  have hleft : ContDiffOn ℝ ∞
      (fun x => productCLM (E := E) (A := R) (Γ x)) s :=
    hΓ.continuousLinearMap_comp _
  have hprod : ContDiffOn ℝ ∞ (product Γ Γ) s := by
    simpa only [productCLM_apply] using hleft.clm_apply hΓ
  have hsum : ContDiffOn ℝ ∞
      (fun x => fderiv ℝ Γ x + product Γ Γ x) s := hfd.add hprod
  simpa only [curvatureForm, alternatingPartCLM_apply] using
    hsum.continuousLinearMap_comp (alternatingPartCLM (E := E) (A := R))

theorem curvaturePowerForm_contDiffOn (Γ : Form (E := E) (A := R))
    {s : Set E} (hs : IsOpen s) (hΓ : ContDiffOn ℝ ∞ Γ s)
    (k : ℕ) : ContDiffOn ℝ ∞ (curvaturePowerForm Γ k) s := by
  have hF := curvatureForm_contDiffOn Γ hs hΓ
  induction k with
  | zero => exact hF
  | succ k ih =>
      have hleft : ContDiffOn ℝ ∞
          (fun x => (wedgeCLM (E := E) (p := 2)
            (q := powerDegree k) (ContinuousLinearMap.mul ℝ R))
              (curvatureForm Γ x)) s :=
        hF.continuousLinearMap_comp _
      simpa only [curvaturePowerForm, wedgeCLM_apply] using
        hleft.clm_apply ih

theorem tracePowerForm_contDiffOn (T : R →L[ℝ] B)
    (Γ : Form (E := E) (A := R))
    {s : Set E} (hs : IsOpen s) (hΓ : ContDiffOn ℝ ∞ Γ s)
    (k : ℕ) : ContDiffOn ℝ ∞ (tracePowerForm T Γ k) s := by
  have hpow := curvaturePowerForm_contDiffOn Γ hs hΓ k
  simpa only [tracePowerForm, QuaternionicSymmetry.DifferentialFormCoefficient.mapForm] using
    hpow.continuousLinearMap_comp
      (ContinuousLinearMap.compContinuousAlternatingMapCLM
        (ι := Fin (powerDegree k)) ℝ E R B T)

end
end QuaternionicSymmetry.LocalChernWeilSmoothness
