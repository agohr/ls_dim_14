import QuaternionicSymmetry.ComplexParametricIntegralC1
import Mathlib.Analysis.Complex.RemovableSingularity

/-! The Cauchy integral formula upgrades the derivative of a complex C1 map
to C1 on finite-dimensional domains. This avoids any smooth-flow premise. -/
namespace QuaternionicSymmetry.ComplexC1DerivativeRegularity
open Set Filter Metric MeasureTheory Complex
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 800000
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Each fixed-direction derivative is continuously complex differentiable. -/
theorem derivative_apply_contDiffAt {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℂ 1 f U) (x₀ : E) (hx₀ : x₀ ∈ U) (v : E) :
    ContDiffAt ℂ 1 (fun x => fderiv ℂ f x v) x₀ := by
  have hdf : ContinuousOn (fderiv ℂ f) U := by
    have hh : ContDiffOn ℂ (0+1) f U := by simpa using hf
    exact contDiffOn_zero.mp ((contDiffOn_succ_iff_fderiv_of_isOpen hU).mp hh).2.2
  have heval : Continuous (fun p : E × ℂ => p.1 + p.2 • v) :=
    continuous_fst.add (continuous_snd.smul continuous_const)
  have hn : (fun p : E × ℂ => p.1+p.2 • v) ⁻¹' U ∈ 𝓝 (x₀,(0 : ℂ)) :=
    heval.continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds hx₀)
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp hn
  let r := δ/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hTube (x : E) (hx : x ∈ ball x₀ r) (z : ℂ) (hz : z ∈ closedBall 0 r) :
      x + z • v ∈ U := by
    apply hsub (a := (x,z))
    rw [mem_ball,Prod.dist_eq,max_lt_iff]
    exact ⟨lt_trans hx (by dsimp [r]; linarith),lt_of_le_of_lt hz (by dsimp [r]; linarith)⟩
  let z : ℝ → ℂ := circleMap 0 r
  let k : ℝ → ℂ := fun t => deriv (circleMap 0 r) t * ((z t)^2)⁻¹
  have hz (t : ℝ) : z t ∈ closedBall 0 r := by
    rw [mem_closedBall,dist_zero_right]
    exact le_of_eq ((norm_circleMap_zero r t).trans (abs_of_pos hr))
  have hzne (t : ℝ) : z t ≠ 0 := circleMap_ne_center hr.ne'
  have hk : Continuous k := by
    dsimp only [k]
    simp only [deriv_circleMap]
    exact ((continuous_circleMap 0 r).mul continuous_const).mul
      (((continuous_circleMap 0 r).pow 2).inv₀ (fun t => pow_ne_zero _ (hzne t)))
  let g : E → ℝ → F := fun x t => k t • f (x+z t • v)
  let d : E → ℝ → E →L[ℂ] F := fun x t => k t • fderiv ℂ f (x+z t • v)
  have harg : Continuous (fun p : E × ℝ => p.1+z p.2 • v) :=
    continuous_fst.add (((continuous_circleMap 0 r).comp continuous_snd).smul continuous_const)
  have hg : ContinuousOn (Function.uncurry g) (ball x₀ r ×ˢ Set.univ) :=
    (hk.comp continuous_snd).continuousOn.smul (hf.continuousOn.comp harg.continuousOn
      (fun p hp => hTube p.1 hp.1 _ (hz p.2)))
  have hd : ContinuousOn (Function.uncurry d) (ball x₀ r ×ˢ Set.univ) :=
    (hk.comp continuous_snd).continuousOn.smul (hdf.comp harg.continuousOn
      (fun p hp => hTube p.1 hp.1 _ (hz p.2)))
  have hgd (x : E) (hx : x ∈ ball x₀ r) (t : ℝ) : HasFDerivAt (fun y => g y t) (d x t) x := by
    have hp := hTube x hx _ (hz t)
    have hh := ((hf.differentiableOn_one _ hp).differentiableAt (hU.mem_nhds hp)).hasFDerivAt
    simpa only [ContinuousLinearMap.comp_id] using
      (hh.comp x ((hasFDerivAt_id x).add_const (z t • v))).const_smul (k t)
  have hI := ComplexParametricIntegralC1.integral_contDiffOn_one isOpen_ball g d hg hd hgd 0 (2*Real.pi)
  have hformula (x : E) (hx : x ∈ ball x₀ r) :
      fderiv ℂ f x v = (2 * Real.pi * I : ℂ)⁻¹ • ∫ t in 0..2*Real.pi, g x t := by
    let A : Set ℂ := (fun z : ℂ => x+z • v) ⁻¹' U
    have hA : IsOpen A := hU.preimage (continuous_const.add (continuous_id.smul continuous_const))
    have hDA : DifferentiableOn ℂ (fun z : ℂ => f (x+z • v)) A :=
      hf.differentiableOn_one.comp
        ((differentiable_const x).add (differentiable_id.smul_const v)).differentiableOn (fun _ h => h)
    have hc := two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable hA
      (hTube x hx) hDA (mem_ball_self hr)
    have hpx : x ∈ U := by simpa using hTube x hx 0 (mem_closedBall_self hr.le)
    have hder := (((hf.differentiableOn_one x hpx).differentiableAt (hU.mem_nhds hpx)).hasFDerivAt).comp_hasDerivAt_of_eq 0 (((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x) (by simp)
    have hder' : deriv (fun z : ℂ => f (x+z • v)) 0 = fderiv ℂ f x v := by
      simpa using hder.deriv
    rw [hder'] at hc
    simpa only [circleIntegral,sub_zero,smul_smul,g,k,z] using hc.symm
  have hSc : ContDiffOn ℂ 1 (fun x => (2 * Real.pi * I : ℂ)⁻¹ •
      ∫ t in 0..2*Real.pi, g x t) (ball x₀ r) := contDiffOn_const.smul hI
  apply (hSc.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hr))).congr_of_eventuallyEq
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with x hx
  exact hformula x hx

/-- The full derivative field is complex C1. -/
theorem fderiv_contDiffOn_one {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℂ 1 f U) : ContDiffOn ℂ 1 (fderiv ℂ f) U := by
  apply contDiffOn_clm_apply.mpr
  intro v x hx
  exact (derivative_apply_contDiffAt hU hf x hx v).contDiffWithinAt

end
end QuaternionicSymmetry.ComplexC1DerivativeRegularity
