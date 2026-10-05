import QuaternionicSymmetry.HolomorphicRealPartLevi

/-! Curvature invariance of the actual gauge-pulled Hermitian line metric.
The only analytic ingredient is the internally proved zero Levi Hessian of
the logarithm of a nonvanishing holomorphic scalar. -/

namespace QuaternionicSymmetry.HolomorphicLineHermitianGaugeCurvature

open QuaternionicSymmetry.HolomorphicLineCoreClasses
open QuaternionicSymmetry.HolomorphicLineGauge
open QuaternionicSymmetry.HolomorphicLineHermitianMetric
open QuaternionicSymmetry.HolomorphicLineHermitianGauge
open QuaternionicSymmetry.HolomorphicRealPartLevi
open QuaternionicSymmetry.HolomorphicLinePowers
open scoped Manifold ContDiff Topology
noncomputable section
universe uB uF

variable {B : Type uB} {F : Type uF}
  [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [ChartedSpace F B]

/-- A holomorphic scalar map on a neighborhood of `x`, read in the actual
complex chart at `x`, is complex C² at its chart coordinate. -/
theorem holomorphicOn_chartContDiffAt {f : B → ℂ} {s : Set B}
    (hf : ContMDiffOn 𝓘(ℂ,F) 𝓘(ℂ,ℂ) ∞ f s)
    (hs : IsOpen s) {x : B} (hx : x ∈ s) :
    ContDiffAt ℂ 2 (fun z : F => f ((chartAt F x).symm z))
      ((chartAt F x) x) := by
  have hAt := hf.contMDiffAt (hs.mem_nhds hx)
  have hchart := (contMDiffAt_iff.mp hAt).2
  simpa only [mfld_simps, Function.comp_apply, contDiffWithinAt_univ] using
    hchart.of_le (show (2 : WithTop ℕ∞) ≤ ∞ from ENat.LEInfty.out)

/-- The analogous chart C² bridge for a real-smooth local frame norm. -/
theorem realSmoothOn_chartContDiffAt {f : B → ℝ} {s : Set B}
    (hf : ContMDiffOn 𝓘(ℝ,F) 𝓘(ℝ,ℝ) ∞ f s)
    (hs : IsOpen s) {x : B} (hx : x ∈ s) :
    ContDiffAt ℝ 2 (fun z : F => f ((chartAt F x).symm z))
      ((chartAt F x) x) := by
  have hAt := hf.contMDiffAt (hs.mem_nhds hx)
  have hchart := (contMDiffAt_iff.mp hAt).2
  simpa only [mfld_simps, Function.comp_apply, contDiffWithinAt_univ] using
    hchart.of_le (show (2 : WithTop ℕ∞) ≤ ∞ from ENat.LEInfty.out)

/-- A local equality `p=f-g` gives the corresponding equality of real
Hessians, provided the two components are genuinely C². -/
theorem hessian_eq_sub_of_eventuallyEq
    {p f g : F → ℝ} {z : F}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z)
    (heq : p =ᶠ[𝓝 z] (fun w => f w - g w)) :
    fderiv ℝ (fderiv ℝ p) z =
      fderiv ℝ (fderiv ℝ f) z - fderiv ℝ (fderiv ℝ g) z := by
  have hfNear : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ f y :=
    (hf.eventually (by decide : (2 : WithTop ℕ∞) ≠ ∞)).mono
      (fun _ h => h.differentiableAt (by decide : (2 : WithTop ℕ∞) ≠ 0))
  have hgNear : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ g y :=
    (hg.eventually (by decide : (2 : WithTop ℕ∞) ≠ ∞)).mono
      (fun _ h => h.differentiableAt (by decide : (2 : WithTop ℕ∞) ≠ 0))
  have heqFirst : fderiv ℝ p =ᶠ[𝓝 z]
      (fun w => fderiv ℝ f w - fderiv ℝ g w) := by
    filter_upwards [heq.fderiv (𝕜 := ℝ), hfNear, hgNear] with y hy hfY hgY
    rw [hy, fderiv_fun_sub hfY hgY]
  have hSecond := heqFirst.fderiv_eq (𝕜 := ℝ)
  rw [hSecond]
  have hfDiff : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1)
      (by decide : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt_one
  have hgDiff : DifferentiableAt ℝ (fderiv ℝ g) z :=
    (hg.fderiv_right (m := 1)
      (by decide : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt_one
  exact fderiv_fun_sub hfDiff hgDiff

universe uI

/-- The local potential of a gauge-pulled line metric differs from the
target potential by precisely minus the logarithmic squared modulus of
the gauge scalar, on a neighborhood inside any common pair of charts. -/
theorem gaugePotential_eventuallyEq
    (L M : LineCore.{uI} (B := B) 𝓘(ℂ,F))
    (h : Isomorphic 𝓘(ℂ,F) L M) (m : HermitianLineMetric M)
    (i : L.Index) (a : M.Index) (x : B)
    (hx : x ∈ L.core.baseSet i ∩ M.core.baseSet a) :
    HermitianLineMetric.localChernPotential L
      (gaugePullbackMetric L M h m) i x =ᶠ[𝓝 ((chartAt F x) x)]
    (fun z => HermitianLineMetric.localChernPotential M m a x z -
      Real.log (Complex.normSq
        (gaugeForward L M h i a ((chartAt F x).symm z)))) := by
  letI := L.holomorphic
  letI := M.holomorphic
  let e := Classical.choice h
  let z := (chartAt F x) x
  have hz : z ∈ (chartAt F x).target := mem_chart_target F x
  have hzsymm : (chartAt F x).symm z = x :=
    (chartAt F x).left_inv (mem_chart_source F x)
  have hNear : ∀ᶠ w in 𝓝 z,
      (chartAt F x).symm w ∈ L.core.baseSet i ∩ M.core.baseSet a := by
    apply ((chartAt F x).continuousAt_symm hz).preimage_mem_nhds
    rw [hzsymm]
    exact (L.core.isOpen_baseSet i |>.inter (M.core.isOpen_baseSet a)).mem_nhds hx
  filter_upwards [hNear] with w hw
  let y := (chartAt F x).symm w
  have he := gaugePullbackWeight_eq_chart L M h m i a y hw
  change gaugePullbackWeight L M h m i y =
    Complex.normSq (e.forward i a y) * m.frameNormSq a y at he
  have hf : e.forward i a y ≠ 0 := e.forward_ne_zero i a y hw
  have hnf : Complex.normSq (e.forward i a y) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr hf)
  have hm : m.frameNormSq a y ≠ 0 := ne_of_gt (m.positive a y hw.2)
  change -Real.log (gaugePullbackWeight L M h m i y) =
    -Real.log (m.frameNormSq a y) -
      Real.log (Complex.normSq (e.forward i a y))
  rw [he, Real.log_mul hnf hm]
  ring

/-- Pulling a positive Hermitian metric back across any holomorphic
isomorphism of represented line cores preserves strict Chern curvature.
The gauge contribution cancels by the internally proved pluriharmonic
logarithmic norm identity. -/
theorem gaugePullbackMetric_positive
    (L M : LineCore.{uI} (B := B) 𝓘(ℂ,F))
    (h : Isomorphic 𝓘(ℂ,F) L M) (m : HermitianLineMetric M)
    (hm : m.PositiveChernCurvature M) :
    (gaugePullbackMetric L M h m).PositiveChernCurvature L := by
  letI := L.holomorphic
  letI := M.holomorphic
  let e := Classical.choice h
  intro i x hx v hv
  let a := M.core.indexAt x
  have ha : x ∈ M.core.baseSet a := M.core.mem_baseSet_at x
  let z := (chartAt F x) x
  let g : F → ℂ := fun w => gaugeForward L M h i a ((chartAt F x).symm w)
  let φM := HermitianLineMetric.localChernPotential M m a x
  let φL := HermitianLineMetric.localChernPotential L
    (gaugePullbackMetric L M h m) i x
  let χ : F → ℝ := fun w => Real.log (Complex.normSq (g w))
  have hOpen : IsOpen (L.core.baseSet i ∩ M.core.baseSet a) :=
    (L.core.isOpen_baseSet i).inter (M.core.isOpen_baseSet a)
  have hGauge : ContDiffAt ℂ 2 g z := by
    change ContDiffAt ℂ 2
      (fun w => e.forward i a ((chartAt F x).symm w)) z
    exact holomorphicOn_chartContDiffAt
      (e.forward_holomorphic i a) hOpen ⟨hx, ha⟩
  have hAt : g z = e.forward i a x := by
    dsimp [g, z, gaugeForward]
    rw [(chartAt F x).left_inv (mem_chart_source F x)]
  have hne : g z ≠ 0 := by
    rw [hAt]
    exact e.forward_ne_zero i a x ⟨hx, ha⟩
  have hChi : ContDiffAt ℝ 2 χ z := by
    have hn := (hGauge.restrict_scalars ℝ).norm_sq ℝ
    have hnn : ‖g z‖ ^ 2 ≠ 0 := by
      rw [← Complex.normSq_eq_norm_sq]
      exact ne_of_gt (Complex.normSq_pos.mpr hne)
    simpa only [χ, Complex.normSq_eq_norm_sq] using hn.log hnn
  have hFrame := realSmoothOn_chartContDiffAt (m.smooth a)
    (M.core.isOpen_baseSet a) ha
  have hFrameAt : m.frameNormSq a ((chartAt F x).symm z) ≠ 0 := by
    rw [show (chartAt F x).symm z = x from
      (chartAt F x).left_inv (mem_chart_source F x)]
    exact ne_of_gt (m.positive a x ha)
  have hPhiM : ContDiffAt ℝ 2 φM z := by
    change ContDiffAt ℝ 2
      (fun w => -Real.log (m.frameNormSq a ((chartAt F x).symm w))) z
    exact (hFrame.log hFrameAt).neg
  have heq : φL =ᶠ[𝓝 z] (fun w => φM w - χ w) :=
    gaugePotential_eventuallyEq L M h m i a x ⟨hx, ha⟩
  have hHess := hessian_eq_sub_of_eventuallyEq hPhiM hChi heq
  have hZero := logNormSq_levi_zero g z v hGauge hne
  have hPos := hm a x ha v hv
  dsimp [HermitianLineMetric.PositiveChernCurvature, φL, φM, χ] at hPos ⊢
  rw [hHess]
  simp only [ContinuousLinearMap.sub_apply]
  nlinarith

end
end QuaternionicSymmetry.HolomorphicLineHermitianGaugeCurvature
