import QuaternionicSymmetry.LocalConnectionGauge

/-! Regularity of the gauge-transformed connection needed for differential
Bianchi identities. -/
namespace QuaternionicSymmetry.LocalConnectionGaugeSmooth
open QuaternionicSymmetry.LocalConnectionGauge
open QuaternionicSymmetry.LocalConnection
open scoped Topology ContDiff
noncomputable section
variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]

theorem contDiffAt_transform (Γ : Form (E := E) (A := A)) (g h : E → A)
    (x : E) (hΓ : ContDiffAt ℝ 2 Γ x) (hg : ContDiffAt ℝ 3 g x)
    (hh : ContDiffAt ℝ 2 h x) :
    ContDiffAt ℝ 2 (transform Γ g h) x := by
  have hD : ContDiffAt ℝ 2 (fderiv ℝ g) x := by
    simpa using hg.fderiv_right (m := 2) (by norm_num)
  have hL : ContDiffAt ℝ 2
      (fun z => (ContinuousLinearMap.mul ℝ A) (h z)) x :=
    (show ContDiffAt ℝ 2
      (fun _ : E => ContinuousLinearMap.mul ℝ A) x from contDiffAt_const).clm_apply hh
  have hR : ContDiffAt ℝ 2
      (fun z => (ContinuousLinearMap.mul ℝ A).flip (g z)) x :=
    (show ContDiffAt ℝ 2
      (fun _ : E => (ContinuousLinearMap.mul ℝ A).flip) x from contDiffAt_const).clm_apply
      (hg.of_le (show (2 : WithTop ℕ∞) ≤ 3 by norm_num))
  exact hL.clm_comp ((hR.clm_comp hΓ).add hD)

end
end QuaternionicSymmetry.LocalConnectionGaugeSmooth
