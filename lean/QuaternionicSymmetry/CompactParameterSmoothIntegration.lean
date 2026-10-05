import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Smooth integration over a compact parameter manifold. This is the
analytic ingredient for averaging a local chart under a compact action. -/
namespace QuaternionicSymmetry.CompactParameterSmoothIntegration
open MeasureTheory Filter Set
open scoped Manifold ContDiff Topology
noncomputable section
set_option maxHeartbeats 800000

variable {A E F K : Type}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace K] [ChartedSpace A K] [IsManifold 𝓘(ℝ,A) ∞ K]

lemma partial_fderiv_smooth {f : K × E → F} {U : Set E}
    (hU : IsOpen U)
    (hf : ContMDiffOn (𝓘(ℝ,A).prod 𝓘(ℝ,E)) 𝓘(ℝ,F) ∞ f (univ ×ˢ U)) :
    ContMDiffOn (𝓘(ℝ,A).prod 𝓘(ℝ,E)) 𝓘(ℝ,E →L[ℝ] F) ∞
      (fun p => fderiv ℝ (fun x => f (p.1,x)) p.2) (univ ×ˢ U) := by
  intro p hp
  have hs : ContMDiffAt ((𝓘(ℝ,A).prod 𝓘(ℝ,E)).prod 𝓘(ℝ,E))
      𝓘(ℝ,F) ∞ (fun q : (K × E) × E => f (q.1.1,q.2)) (p,p.2) := by
    apply (hf.contMDiffAt ((isOpen_univ.prod hU).mem_nhds hp)).comp _
    exact (contMDiffAt_fst.fst).prodMk contMDiffAt_snd
  have hd := hs.mfderiv (fun p : K × E => fun x => f (p.1,x))
    Prod.snd contMDiffAt_snd (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)
  simpa only [inTangentCoordinates_model_space, mfderiv_eq_fderiv] using hd.contMDiffWithinAt (s := univ ×ˢ U)

variable [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (μ : Measure K) [IsFiniteMeasure μ]

lemma integral_continuousOn {f : K × E → F} {U : Set E}
    (hf : ContinuousOn f (univ ×ˢ U)) :
    ContinuousOn (fun x => ∫ k, f (k,x) ∂μ) U := by
  apply continuousOn_integral_of_compact_support isCompact_univ
  · exact hf.comp continuous_swap.continuousOn (fun p hp => ⟨hp.2,hp.1⟩)
  · intro x k hx hk
    exact False.elim (hk (mem_univ k))

lemma integral_hasFDerivAt {f : K × E → F} {U : Set E}
    (hU : IsOpen U)
    (hf : ContMDiffOn (𝓘(ℝ,A).prod 𝓘(ℝ,E)) 𝓘(ℝ,F) ∞ f (univ ×ˢ U))
    {x : E} (hx : x ∈ U) :
    HasFDerivAt (fun y => ∫ k, f (k,y) ∂μ)
      (∫ k, fderiv ℝ (fun y => f (k,y)) x ∂μ) x := by
  let D : K × E → E →L[ℝ] F := fun p => fderiv ℝ (fun y => f (p.1,y)) p.2
  have hD := (partial_fderiv_smooth hU hf).continuousOn
  obtain ⟨r,hr,hrU⟩ := Metric.isOpen_iff.mp hU x hx
  have hball : Metric.closedBall x (r/2) ⊆ U := by
    intro y hy
    exact hrU (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hy) (by linarith)))
  have hcompact := (isCompact_univ : IsCompact (univ : Set K)).prod (isCompact_closedBall x (r/2))
  obtain ⟨C,hC⟩ := hcompact.bddAbove_image (hD.norm.mono (Set.prod_mono Subset.rfl hball))
  have hcont (y : E) (hy : y ∈ U) : Continuous (fun k => f (k,y)) :=
    (hf.continuousOn.comp_continuous (continuous_id.prodMk continuous_const)
      (fun _ => ⟨mem_univ _,hy⟩))
  have hdcont (y : E) (hy : y ∈ U) : Continuous (fun k => D (k,y)) :=
    (hD.comp_continuous (continuous_id.prodMk continuous_const)
      (fun _ => ⟨mem_univ _,hy⟩))
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.closedBall x (r/2)) (bound := fun _ => C)
    (F' := fun y k => D (k,y))
    (Metric.closedBall_mem_nhds x (by linarith))
  · filter_upwards [hU.mem_nhds hx] with y hy
    exact (hcont y hy).aestronglyMeasurable
  · exact (hcont x hx).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact (hdcont x hx).aestronglyMeasurable
  · filter_upwards with k y hy
    exact hC (mem_image_of_mem _ ⟨mem_univ k,hy⟩)
  · exact integrable_const C
  · filter_upwards with k y hy
    have hsm : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ (fun y => f (k,y)) y :=
      (hf.contMDiffAt ((isOpen_univ.prod hU).mem_nhds ⟨mem_univ k,hball hy⟩)).comp y
        (contMDiffAt_const.prodMk contMDiffAt_id)
    exact (hsm.contDiffAt.differentiableAt (by simp)).hasFDerivAt

lemma integral_contDiffOn_nat (n : ℕ) {f : K × E → F} {U : Set E}
    (hU : IsOpen U)
    (hf : ContMDiffOn (𝓘(ℝ,A).prod 𝓘(ℝ,E)) 𝓘(ℝ,F) ∞ f (univ ×ˢ U)) :
    ContDiffOn ℝ n (fun x => ∫ k, f (k,x) ∂μ) U := by
  induction n generalizing F with
  | zero => exact contDiffOn_zero.mpr (integral_continuousOn μ hf.continuousOn)
  | succ n ih =>
    have hd (x : E) (hx : x ∈ U) := integral_hasFDerivAt μ hU hf hx
    have hsm := ih (F := E →L[ℝ] F) (partial_fderiv_smooth hU hf)
    rw [show ((n+1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by simp]
    apply (contDiffOn_succ_iff_hasFDerivWithinAt (by simp)).mpr
    intro x hx
    refine ⟨U,?_,by simp, (fun y => ∫ k, fderiv ℝ (fun z => f (k,z)) y ∂μ),?_,hsm⟩
    · rw [insert_eq_of_mem hx]
      exact self_mem_nhdsWithin
    · intro y hy
      exact (hd y hy).hasFDerivWithinAt

lemma integral_contDiffOn {f : K × E → F} {U : Set E}
    (hU : IsOpen U)
    (hf : ContMDiffOn (𝓘(ℝ,A).prod 𝓘(ℝ,E)) 𝓘(ℝ,F) ∞ f (univ ×ˢ U)) :
    ContDiffOn ℝ ∞ (fun x => ∫ k, f (k,x) ∂μ) U :=
  contDiffOn_infty.mpr (fun n => integral_contDiffOn_nat μ n hU hf)

end
end QuaternionicSymmetry.CompactParameterSmoothIntegration
