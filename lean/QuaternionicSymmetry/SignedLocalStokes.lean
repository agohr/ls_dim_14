import QuaternionicSymmetry.CompactSupportDomainStokes

/-! The locally constant orientation sign of a nowhere-zero real density
may be inserted in compact-support Stokes, even on disconnected charts. -/
namespace QuaternionicSymmetry.SignedLocalStokes

open Filter Set MeasureTheory Measure
open scoped ContDiff Topology
set_option maxHeartbeats 800000
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def orientationSign (a : ℝ) : ℝ := |a| / a

omit [NormedSpace ℝ E] in
theorem orientationSign_eventually_constant {g : E → ℝ} {x : E}
    (hg : ContinuousAt g x) (hne : g x ≠ 0) :
    (fun y => orientationSign (g y)) =ᶠ[𝓝 x] fun _ => orientationSign (g x) := by
  rcases lt_or_gt_of_ne hne with hn | hp
  · filter_upwards [hg.eventually_lt_const hn] with y hy
    simp [orientationSign, abs_of_neg hn, abs_of_neg hy, hn.ne, hy.ne]
  · filter_upwards [hg.eventually_const_lt hp] with y hy
    simp [orientationSign, abs_of_pos hp, abs_of_pos hy, hp.ne', hy.ne']

theorem contDiffOn_signed_form {n : ℕ} {s : Set E} (hs : IsOpen s)
    {g : E → ℝ} (hg : ContinuousOn g s) (hne : ∀ x ∈ s, g x ≠ 0)
    {α : E → E [⋀^Fin n]→L[ℝ] ℝ} (hα : ContDiffOn ℝ ∞ α s) :
    ContDiffOn ℝ ∞ (fun x => orientationSign (g x) • α x) s := by
  intro x hx
  have he := orientationSign_eventually_constant
    ((hg x hx).continuousAt (hs.mem_nhds hx)) (hne x hx)
  have hc := ((hα x hx).contDiffAt (hs.mem_nhds hx)).const_smul (orientationSign (g x))
  apply (hc.congr_of_eventuallyEq _).contDiffWithinAt
  filter_upwards [he] with y hy
  simp only [hy]

theorem extDeriv_signed_form {n : ℕ} {g : E → ℝ} {x : E}
    (hg : ContinuousAt g x) (hne : g x ≠ 0)
    (α : E → E [⋀^Fin n]→L[ℝ] ℝ) :
    extDeriv (fun y => orientationSign (g y) • α y) x =
      orientationSign (g x) • extDeriv α x := by
  have he := orientationSign_eventually_constant hg hne
  have hev : (fun y => orientationSign (g y) • α y) =ᶠ[𝓝 x]
      fun y => orientationSign (g x) • α y := by
    filter_upwards [he] with y hy
    simp only [hy]
  rw [hev.extDeriv_eq]
  exact extDeriv_smul (orientationSign (g x)) α

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsAddHaarMeasure μ]

theorem setIntegral_signed_extDeriv_eq_zero {n : ℕ} {s : Set E} (hs : IsOpen s)
    {g : E → ℝ} (hg : ContinuousOn g s) (hne : ∀ x ∈ s, g x ≠ 0)
    {α : E → E [⋀^Fin n]→L[ℝ] ℝ}
    (hα : ContDiffOn ℝ ∞ α s) (hc : HasCompactSupport α)
    (hsub : tsupport α ⊆ s) (v : Fin (n + 1) → E) :
    (∫ x in s, orientationSign (g x) * extDeriv α x v ∂μ) = 0 := by
  let β : E → E [⋀^Fin n]→L[ℝ] ℝ := fun x => orientationSign (g x) • α x
  have hb := contDiffOn_signed_form hs hg hne hα
  have hbc : HasCompactSupport β := hc.smul_left (f := fun x => orientationSign (g x))
  have hbs : tsupport β ⊆ s := (tsupport_smul_subset_right (fun x => orientationSign (g x)) α).trans hsub
  have hzero := CompactSupportDomainStokes.setIntegral_extDeriv_eq_zero
    (μ := μ) hs hb hbc hbs v
  apply Eq.trans _ hzero
  apply setIntegral_congr_fun hs.measurableSet
  intro x hx
  dsimp only
  rw [extDeriv_signed_form ((hg x hx).continuousAt (hs.mem_nhds hx)) (hne x hx)]
  rfl

end QuaternionicSymmetry.SignedLocalStokes
