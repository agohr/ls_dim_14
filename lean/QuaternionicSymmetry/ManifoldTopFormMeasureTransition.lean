import QuaternionicSymmetry.ManifoldTopFormLocalMeasure
import QuaternionicSymmetry.ManifoldQuaternionicConnection

/-! Change of variables on overlaps of the preferred manifold charts. -/
namespace QuaternionicSymmetry.ManifoldTopFormMeasureTransition

open Module MeasureTheory ManifoldDifferentialForms
  ManifoldQuaternionicConnection ManifoldTopFormJacobian
  ManifoldTopFormLocalMeasure
open scoped Manifold Topology ContDiff ENNReal
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem chartTransition_mem_overlap (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ, E)) p q) :
    chartTransition (I := 𝓘(ℝ, E)) p q y ∈
      chartOverlap (I := 𝓘(ℝ, E)) q p := by
  let x := (extChartAt 𝓘(ℝ, E) p).symm y
  have hxq : x ∈ (extChartAt 𝓘(ℝ, E) q).source := hy.2
  have hxp : x ∈ (extChartAt 𝓘(ℝ, E) p).source := by
    exact (extChartAt 𝓘(ℝ, E) p).map_target hy.1
  constructor
  · exact (extChartAt 𝓘(ℝ, E) q).map_source hxq
  · change (extChartAt 𝓘(ℝ, E) q).symm
      ((extChartAt 𝓘(ℝ, E) q) x) ∈ _
    simpa only [(extChartAt 𝓘(ℝ, E) q).left_inv hxq] using hxp

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem chartTransition_injOn (p q : M) :
    Set.InjOn (chartTransition (I := 𝓘(ℝ, E)) p q)
      (chartOverlap (I := 𝓘(ℝ, E)) p q) := by
  intro y hy z hz he
  have hxy := (extChartAt 𝓘(ℝ, E) q).left_inv hy.2
  have hxz := (extChartAt 𝓘(ℝ, E) q).left_inv hz.2
  have hx : (extChartAt 𝓘(ℝ, E) p).symm y =
      (extChartAt 𝓘(ℝ, E) p).symm z := by
    calc
      _ = (extChartAt 𝓘(ℝ, E) q).symm
        (chartTransition (I := 𝓘(ℝ, E)) p q y) := hxy.symm
      _ = (extChartAt 𝓘(ℝ, E) q).symm
        (chartTransition (I := 𝓘(ℝ, E)) p q z) := by rw [he]
      _ = _ := hxz
  calc
    y = (extChartAt 𝓘(ℝ, E) p)
        ((extChartAt 𝓘(ℝ, E) p).symm y) :=
      ((extChartAt 𝓘(ℝ, E) p).right_inv hy.1).symm
    _ = (extChartAt 𝓘(ℝ, E) p)
        ((extChartAt 𝓘(ℝ, E) p).symm z) := by rw [hx]
    _ = z := (extChartAt 𝓘(ℝ, E) p).right_inv hz.1

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem chartTransition_image_overlap (p q : M) :
    chartTransition (I := 𝓘(ℝ, E)) p q ''
      chartOverlap (I := 𝓘(ℝ, E)) p q =
    chartOverlap (I := 𝓘(ℝ, E)) q p := by
  apply Set.Subset.antisymm
  · rintro z ⟨y, hy, rfl⟩
    exact chartTransition_mem_overlap p q y hy
  · intro z hz
    refine ⟨chartTransition (I := 𝓘(ℝ, E)) q p z,
      chartTransition_mem_overlap q p z hz, ?_⟩
    unfold chartTransition
    rw [(extChartAt 𝓘(ℝ, E) p).left_inv hz.2]
    exact (extChartAt 𝓘(ℝ, E) q).right_inv hz.1

omit [FiniteDimensional ℝ E] in
theorem chartTransition_hasFDerivWithinAt (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ, E)) p q) :
    HasFDerivWithinAt (chartTransition (I := 𝓘(ℝ, E)) p q)
      (fderiv ℝ (chartTransition (I := 𝓘(ℝ, E)) p q) y)
      (chartOverlap (I := 𝓘(ℝ, E)) p q) y := by
  exact ((chartTransition_contDiffAt (I := 𝓘(ℝ, E)) p q y hy).differentiableAt
    (by norm_num)).hasFDerivAt.hasFDerivWithinAt

variable [MeasurableSpace E] [BorelSpace E]

theorem chartTransition_lintegral (p q : M) (g : E → ℝ≥0∞) :
    (∫⁻ z in chartOverlap (I := 𝓘(ℝ, E)) q p,
      g z ∂((Module.finBasis ℝ E).addHaar : Measure E)) =
    ∫⁻ y in chartOverlap (I := 𝓘(ℝ, E)) p q,
      ENNReal.ofReal |(fderiv ℝ (chartTransition (I := 𝓘(ℝ, E)) p q) y).toLinearMap.det| *
        g (chartTransition (I := 𝓘(ℝ, E)) p q y)
        ∂((Module.finBasis ℝ E).addHaar : Measure E) := by
  have h := MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
    ((Module.finBasis ℝ E).addHaar : Measure E)
    ((chartOverlap_isOpen (I := 𝓘(ℝ, E)) p q).measurableSet)
    (chartTransition_hasFDerivWithinAt p q)
    (chartTransition_injOn p q) g
  rw [chartTransition_image_overlap] at h
  exact h

theorem chartTransition_density_lintegral
    (ν : Form 𝓘(ℝ, E) M (Module.finrank ℝ E))
    (p q : M) (g : E → ℝ≥0∞) :
    (∫⁻ y in chartOverlap (I := 𝓘(ℝ, E)) p q,
      ENNReal.ofReal (chartDensity ν p y) *
        g (chartTransition (I := 𝓘(ℝ, E)) p q y)
      ∂((Module.finBasis ℝ E).addHaar : Measure E)) =
    ∫⁻ z in chartOverlap (I := 𝓘(ℝ, E)) q p,
      ENNReal.ofReal (chartDensity ν q z) * g z
      ∂((Module.finBasis ℝ E).addHaar : Measure E) := by
  calc
    (∫⁻ y in chartOverlap (I := 𝓘(ℝ, E)) p q,
      ENNReal.ofReal (chartDensity ν p y) *
        g (chartTransition (I := 𝓘(ℝ, E)) p q y)
      ∂((Module.finBasis ℝ E).addHaar : Measure E)) =
      ∫⁻ y in chartOverlap (I := 𝓘(ℝ, E)) p q,
        ENNReal.ofReal |(fderiv ℝ (chartTransition (I := 𝓘(ℝ, E)) p q) y).toLinearMap.det| *
        (ENNReal.ofReal
          (chartDensity ν q (chartTransition (I := 𝓘(ℝ, E)) p q y)) *
          g (chartTransition (I := 𝓘(ℝ, E)) p q y))
        ∂((Module.finBasis ℝ E).addHaar : Measure E) := by
          apply setLIntegral_congr_fun
            ((chartOverlap_isOpen (I := 𝓘(ℝ, E)) p q).measurableSet)
          intro y hy
          change ENNReal.ofReal (chartDensity ν p y) * g (chartTransition p q y) = _
          rw [chartDensity_transition ν p q hy.1 hy.2]
          rw [ENNReal.ofReal_mul (abs_nonneg _)]
          ac_rfl
    _ = _ := (chartTransition_lintegral p q
      (fun z => ENNReal.ofReal (chartDensity ν q z) * g z)).symm

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem coordinateMeasure_overlap_lintegral
    (ν : Form 𝓘(ℝ, E) M (Module.finrank ℝ E))
    (hν : ChartSmooth ν) (p q : M) (g : E → ℝ≥0∞) :
    (∫⁻ y in chartOverlap (I := 𝓘(ℝ, E)) p q,
      g y ∂coordinateMeasure ν p) =
    ∫⁻ y in chartOverlap (I := 𝓘(ℝ, E)) p q,
      ENNReal.ofReal (chartDensity ν p y) * g y
      ∂((Module.finBasis ℝ E).addHaar : Measure E) := by
  let μ : Measure E := (Module.finBasis ℝ E).addHaar
  let s : Set E := chartOverlap (I := 𝓘(ℝ, E)) p q
  let t : Set E := (extChartAt 𝓘(ℝ, E) p).target
  have hs : MeasurableSet s :=
    (chartOverlap_isOpen (I := 𝓘(ℝ, E)) p q).measurableSet
  have hst : s ⊆ t := fun y hy => hy.1
  have hcont : ContinuousOn (chartDensity ν p) s :=
    (chartDensity_continuousOn ν hν p).mono hst
  have hmeas : AEMeasurable (fun y => ENNReal.ofReal (chartDensity ν p y))
      ((μ.restrict t).restrict s) :=
    (hcont.aemeasurable₀ hs.nullMeasurableSet).ennreal_ofReal
  have hfinite : ∀ᵐ y ∂(μ.restrict t).restrict s,
      ENNReal.ofReal (chartDensity ν p y) < (⊤ : ℝ≥0∞) :=
    Filter.Eventually.of_forall (fun y => ENNReal.ofReal_lt_top)
  have h := setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀
    (μ.restrict t) hmeas g hs hfinite
  change (∫⁻ y in s, g y ∂(μ.restrict t).withDensity
      (fun y => ENNReal.ofReal (chartDensity ν p y))) =
    ∫⁻ y in s, ENNReal.ofReal (chartDensity ν p y) * g y ∂μ
  rw [h]
  change (∫⁻ y, ENNReal.ofReal (chartDensity ν p y) * g y
    ∂(μ.restrict t).restrict s) = _
  rw [Measure.restrict_restrict_of_subset hst]

theorem chartTransition_coordinateMeasure_lintegral
    (ν : Form 𝓘(ℝ, E) M (Module.finrank ℝ E))
    (hν : ChartSmooth ν) (p q : M) (g : E → ℝ≥0∞) :
    (∫⁻ y in chartOverlap (I := 𝓘(ℝ, E)) p q,
      g (chartTransition (I := 𝓘(ℝ, E)) p q y)
      ∂coordinateMeasure ν p) =
    ∫⁻ z in chartOverlap (I := 𝓘(ℝ, E)) q p,
      g z ∂coordinateMeasure ν q := by
  rw [coordinateMeasure_overlap_lintegral ν hν p q,
    chartTransition_density_lintegral ν p q g,
    coordinateMeasure_overlap_lintegral ν hν q p]

theorem chartTransition_map_coordinateMeasure_overlap
    (ν : Form 𝓘(ℝ, E) M (Module.finrank ℝ E))
    (hν : ChartSmooth ν) (p q : M) :
    Measure.map (chartTransition (I := 𝓘(ℝ, E)) p q)
      ((coordinateMeasure ν p).restrict
        (chartOverlap (I := 𝓘(ℝ, E)) p q)) =
    (coordinateMeasure ν q).restrict
      (chartOverlap (I := 𝓘(ℝ, E)) q p) := by
  let s : Set E := chartOverlap (I := 𝓘(ℝ, E)) p q
  have hs : MeasurableSet s :=
    (chartOverlap_isOpen (I := 𝓘(ℝ, E)) p q).measurableSet
  have hcont : ContinuousOn (chartTransition (I := 𝓘(ℝ, E)) p q) s := by
    intro y hy
    exact ((chartTransition_contDiffAt (I := 𝓘(ℝ, E)) p q y hy).continuousAt).continuousWithinAt
  have hF : AEMeasurable (chartTransition (I := 𝓘(ℝ, E)) p q)
      ((coordinateMeasure ν p).restrict s) :=
    hcont.aemeasurable₀ hs.nullMeasurableSet
  apply Measure.ext_of_lintegral _
  intro g hg
  rw [lintegral_map' hg.aemeasurable hF]
  exact chartTransition_coordinateMeasure_lintegral ν hν p q g

variable [MeasurableSpace M] [BorelSpace M] [Nontrivial E] [Nonempty M]

omit [IsManifold 𝓘(ℝ, E) ∞ M] [Nontrivial E] [Nonempty M] in
theorem chartMeasure_restrict_source
    (ν : Form 𝓘(ℝ, E) M (Module.finrank ℝ E)) (p q : M) :
    (chartMeasure ν p).restrict (extChartAt 𝓘(ℝ, E) q).source =
      Measure.map (extChartAt 𝓘(ℝ, E) p).symm
        ((coordinateMeasure ν p).restrict
          (chartOverlap (I := 𝓘(ℝ, E)) p q)) := by
  rw [chartMeasure, Measure.restrict_map_of_aemeasurable
    (chartSymm_aeMeasurable ν p)
      ((isOpen_extChartAt_source (I := 𝓘(ℝ, E)) q).measurableSet)]
  have heq :
      ((extChartAt 𝓘(ℝ, E) p).symm ⁻¹'
          (extChartAt 𝓘(ℝ, E) q).source) =ᵐ[coordinateMeasure ν p]
        chartOverlap (I := 𝓘(ℝ, E)) p q := by
    filter_upwards [coordinateMeasure_ae_mem_target ν p] with y hy
    apply propext
    exact ⟨fun h => ⟨hy, h⟩, fun h => h.2⟩
  rw [Measure.restrict_congr_set heq]

omit [Nontrivial E] [Nonempty M] in
theorem chartMeasure_overlap_eq
    (ν : Form 𝓘(ℝ, E) M (Module.finrank ℝ E))
    (hν : ChartSmooth ν) (p q : M) :
    (chartMeasure ν p).restrict (extChartAt 𝓘(ℝ, E) q).source =
      (chartMeasure ν q).restrict (extChartAt 𝓘(ℝ, E) p).source := by
  let s : Set E := chartOverlap (I := 𝓘(ℝ, E)) p q
  have hs : MeasurableSet s :=
    (chartOverlap_isOpen (I := 𝓘(ℝ, E)) p q).measurableSet
  let μ : Measure E := (coordinateMeasure ν p).restrict s
  let f : E → E := chartTransition (I := 𝓘(ℝ, E)) p q
  have hf : AEMeasurable f μ := by
    have hcont : ContinuousOn f s := by
      intro y hy
      exact ((chartTransition_contDiffAt (I := 𝓘(ℝ, E)) p q y hy).continuousAt).continuousWithinAt
    exact hcont.aemeasurable₀ hs.nullMeasurableSet
  have hmap : Measure.map f μ =
      (coordinateMeasure ν q).restrict
        (chartOverlap (I := 𝓘(ℝ, E)) q p) :=
    chartTransition_map_coordinateMeasure_overlap ν hν p q
  have hq : AEMeasurable (extChartAt 𝓘(ℝ, E) q).symm (Measure.map f μ) := by
    rw [hmap]
    exact (chartSymm_aeMeasurable ν q).restrict
  calc
    (chartMeasure ν p).restrict (extChartAt 𝓘(ℝ, E) q).source =
        Measure.map (extChartAt 𝓘(ℝ, E) p).symm μ :=
      chartMeasure_restrict_source ν p q
    _ = Measure.map ((extChartAt 𝓘(ℝ, E) q).symm ∘ f) μ := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem hs] with y hy
      exact ((extChartAt 𝓘(ℝ, E) q).left_inv hy.2).symm
    _ = Measure.map (extChartAt 𝓘(ℝ, E) q).symm (Measure.map f μ) :=
      (AEMeasurable.map_map_of_aemeasurable hq hf).symm
    _ = Measure.map (extChartAt 𝓘(ℝ, E) q).symm
          ((coordinateMeasure ν q).restrict
            (chartOverlap (I := 𝓘(ℝ, E)) q p)) := by rw [hmap]
    _ = (chartMeasure ν q).restrict (extChartAt 𝓘(ℝ, E) p).source :=
      (chartMeasure_restrict_source ν q p).symm

end
end QuaternionicSymmetry.ManifoldTopFormMeasureTransition
