import QuaternionicSymmetry.HolomorphicVectorFieldRealSmooth
import QuaternionicSymmetry.HolomorphicPicardFlow
import QuaternionicSymmetry.CompactVectorFieldCompleteness

/-! Local real integral curves of holomorphic vector fields have jointly
continuous flows and genuine smooth holomorphic time maps on manifold charts. -/
namespace QuaternionicSymmetry.HolomorphicVectorFieldLocalFlow
open HolomorphicTangentSectionCoordinates ComplexRealTangentTopology Set Filter
open scoped Manifold ContDiff Topology
noncomputable section
set_option maxHeartbeats 800000
variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ,E) ∞ M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

theorem local_flow
    (X : ContMDiffSection 𝓘(ℂ,E) E ∞ (TangentSpace 𝓘(ℂ,E) : M → Type _)) (x₀ : M) :
    ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧ ∃ ε > (0 : ℝ), ∃ β : M × ℝ → M,
      ContinuousOn β (U ×ˢ Ioo (-ε) ε) ∧
      (∀ t ∈ Ioo (-ε) ε, ContMDiffOn 𝓘(ℂ,E) 𝓘(ℂ,E) ∞ (fun x => β (x,t)) U) ∧
      ∀ x ∈ U, β (x,0) = x ∧ IsMIntegralCurveOn (I := 𝓘(ℝ,E)) (fun t => β (x,t)) X (Ioo (-ε) ε) := by
  let I := 𝓘(ℝ,E)
  let i := achart E x₀
  let e := extChartAt 𝓘(ℂ,E) x₀
  let F := coordinateField X i
  have hF : ContDiffOn ℂ ∞ F e.target := by
    intro y hy
    have hy' : y ∈ i.1.target := by simpa [e,i,extChartAt,mfld_simps] using hy
    have hh := coordinateField_contDiffAt X i (i.1.symm y) (i.1.map_target hy')
    rw [i.1.right_inv hy'] at hh
    exact hh.contDiffWithinAt
  obtain ⟨r,hr,ε,hε,α,hαcont,hαhol,hflow⟩ := HolomorphicPicardFlow.local_flow_smooth
    (isOpen_extChartAt_target (I := 𝓘(ℂ,E)) x₀) (mem_extChartAt_target x₀) hF
  let U := e.source ∩ e ⁻¹' Metric.ball (e x₀) r
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have hs := (isOpen_extChartAt_source (I := 𝓘(ℂ,E)) x₀).mem_nhds hx.1
    have hc : ContinuousAt e x := (continuousOn_extChartAt x₀ x hx.1).continuousAt hs
    exact inter_mem hs (hc.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hx.2))
  let β : M × ℝ → M := fun p => e.symm (α (e p.1,p.2))
  refine ⟨U,hU,⟨mem_extChartAt_source x₀,Metric.mem_ball_self hr⟩,ε,hε,β,?_,?_,?_⟩
  · have hg : ContinuousOn (fun p : M × ℝ => (e p.1,p.2)) (U ×ˢ Ioo (-ε) ε) :=
      ((continuousOn_extChartAt x₀).comp continuousOn_fst (fun p hp => hp.1.1)).prodMk continuousOn_snd
    apply (continuousOn_extChartAt_symm (I := 𝓘(ℂ,E)) x₀).comp
      (hαcont.comp hg (fun p hp => ⟨hp.1.2,hp.2⟩))
    exact fun p hp => ((hflow (e p.1) hp.1.2).2 p.2 hp.2).2
  · intro t ht
    have he : ContMDiffOn 𝓘(ℂ,E) 𝓘(ℂ,E) ∞ e U :=
      (contMDiffOn_extChartAt (I := 𝓘(ℂ,E)) (x := x₀)).mono (fun _ h => by simpa only [e,extChartAt_source] using h.1)
    have hcomp := ((hαhol t ht).contMDiffOn).comp he (fun _ h => h.2)
    exact (contMDiffOn_extChartAt_symm x₀).comp hcomp
      (fun x hx => ((hflow (e x) hx.2).2 t ht).2)
  · intro x hx
    let f : ℝ → E := fun t => α (e x,t)
    have hα₀ : f 0 = e x := (hflow (e x) hx.2).1
    have hα := (hflow (e x) hx.2).2
    refine ⟨?_,?_⟩
    · change e.symm (f 0) = x
      rw [hα₀]
      exact e.left_inv hx.1
    intro t ht
    let xₜ : M := e.symm (f t)
    have hf3 : f t ∈ e.target := (hα t ht).2
    have hft1 : xₜ ∈ e.source := e.map_target hf3
    have hft2 := mem_extChartAt_source (I := I) xₜ
    have h : HasDerivAt f (tangentCoordChange I xₜ x₀ xₜ (X xₜ)) t := by
      have hh := (hα t ht).1
      change HasDerivAt f (tangentCoordChange 𝓘(ℂ,E) xₜ x₀ xₜ (X xₜ)) t at hh
      rw [coordChange_real_complex xₜ x₀ xₜ (mem_extChartAt_source xₜ) hft1]
      exact hh
    apply HasMFDerivAt.hasMFDerivWithinAt
    refine ⟨(continuousAt_extChartAt_symm'' hf3).comp h.continuousAt,
      HasDerivWithinAt.hasFDerivWithinAt ?_⟩
    simp only [mfld_simps,hasDerivWithinAt_univ]
    change HasDerivAt ((extChartAt I xₜ ∘ e.symm) ∘ f) (X xₜ) t
    rw [← tangentCoordChange_self (I := I) (x := xₜ) (z := xₜ) (v := X xₜ) hft2,
      ← tangentCoordChange_comp (x := x₀) ⟨⟨hft2,hft1⟩,hft2⟩]
    apply HasFDerivAt.comp_hasDerivAt _ _ h
    have hh := hasFDerivWithinAt_tangentCoordChange (I := I) ⟨hft1,hft2⟩
    have hh' : HasFDerivAt ((extChartAt I xₜ) ∘ (extChartAt I x₀).symm)
        (tangentCoordChange I x₀ xₜ xₜ) ((extChartAt I x₀) xₜ) := by
      simpa only [I,modelWithCornersSelf_coe,Set.range_id,hasFDerivWithinAt_univ] using hh
    convert hh' using 1
    exact (e.right_inv hf3).symm

end
end QuaternionicSymmetry.HolomorphicVectorFieldLocalFlow
