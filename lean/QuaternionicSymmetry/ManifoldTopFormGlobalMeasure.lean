import QuaternionicSymmetry.ManifoldTopFormMeasureTransition
import QuaternionicSymmetry.ManifoldFiniteFormPartition

/-! Gluing the chart measures of a smooth top form by a finite smooth partition. -/
namespace QuaternionicSymmetry.ManifoldTopFormGlobalMeasure

open Module MeasureTheory ManifoldDifferentialForms
  ManifoldTopFormLocalMeasure ManifoldTopFormMeasureTransition
open scoped Manifold Topology ContDiff ENNReal
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [Nontrivial E] [Nonempty M]

/-- Any finite smooth chart partition yields a measure from the top form. -/
def partitionMeasure {ι : Type*} [Fintype ι]
    (ν : Form 𝓘(ℝ, E) M (Module.finrank ℝ E))
    (centers : ι → M)
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, E) M Set.univ) : Measure M :=
  ∑ i : ι, (chartMeasure ν (centers i)).withDensity
    (fun x => ENNReal.ofReal (ρ i x))

omit [Nontrivial E] [Nonempty M] in
theorem weighted_chart_restrict
    {ι : Type*} [Fintype ι]
    (ν : Form 𝓘(ℝ, E) M (Module.finrank ℝ E))
    (hν : ChartSmooth ν) (centers : ι → M)
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, E) M Set.univ)
    (hsub : ρ.IsSubordinate (fun i => (extChartAt 𝓘(ℝ, E) (centers i)).source))
    (i : ι) (q : M) :
    ((chartMeasure ν (centers i)).withDensity
      (fun x => ENNReal.ofReal (ρ i x))).restrict
        (extChartAt 𝓘(ℝ, E) q).source =
      (chartMeasure ν q).withDensity (fun x => ENNReal.ofReal (ρ i x)) := by
  let Ui : Set M := (extChartAt 𝓘(ℝ, E) (centers i)).source
  let Uq : Set M := (extChartAt 𝓘(ℝ, E) q).source
  let fi : M → ℝ≥0∞ := fun x => ENNReal.ofReal (ρ i x)
  have hUi : MeasurableSet Ui :=
    (isOpen_extChartAt_source (I := 𝓘(ℝ, E)) (centers i)).measurableSet
  have hUq : MeasurableSet Uq :=
    (isOpen_extChartAt_source (I := 𝓘(ℝ, E)) q).measurableSet
  have hfi : Ui.indicator fi = fi := by
    funext x
    by_cases hx : x ∈ Ui
    · simp [Set.indicator_of_mem hx]
    · have hxzero : ρ i x = 0 := by
        by_contra h
        have hsupport : x ∈ Function.support (ρ i) := by simpa using h
        exact hx ((hsub i) ((subset_tsupport (ρ i)) hsupport))
      simp [Set.indicator_of_notMem hx, fi, hxzero]
  calc
    ((chartMeasure ν (centers i)).withDensity fi).restrict Uq =
        ((chartMeasure ν (centers i)).restrict Uq).withDensity fi :=
      restrict_withDensity hUq fi
    _ = ((chartMeasure ν q).restrict Ui).withDensity fi := by
      rw [chartMeasure_overlap_eq ν hν (centers i) q]
    _ = (chartMeasure ν q).withDensity (Ui.indicator fi) :=
      (withDensity_indicator hUi fi).symm
    _ = (chartMeasure ν q).withDensity fi := by rw [hfi]

omit [Nontrivial E] [Nonempty M] in
theorem partitionMeasure_restrict_chart
    {ι : Type*} [Fintype ι]
    (ν : Form 𝓘(ℝ, E) M (Module.finrank ℝ E))
    (hν : ChartSmooth ν) (centers : ι → M)
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, E) M Set.univ)
    (hsub : ρ.IsSubordinate (fun i => (extChartAt 𝓘(ℝ, E) (centers i)).source))
    (q : M) :
    (partitionMeasure ν centers ρ).restrict
      (extChartAt 𝓘(ℝ, E) q).source = chartMeasure ν q := by
  classical
  let Uq : Set M := (extChartAt 𝓘(ℝ, E) q).source
  let fi (i : ι) : M → ℝ≥0∞ := fun x => ENNReal.ofReal (ρ i x)
  let μi (i : ι) : Measure M := (chartMeasure ν (centers i)).withDensity (fi i)
  have hdist (s : Finset ι) :
      (∑ i ∈ s, μi i).restrict Uq = ∑ i ∈ s, (μi i).restrict Uq := by
    classical
    induction s using Finset.induction_on with
    | empty => simp [Measure.restrict_zero]
    | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        rw [Measure.restrict_add, ih]
  have hmeas (i : ι) : Measurable (fi i) := by
    dsimp [fi]
    fun_prop
  have hsum (s : Finset ι) :
      (∑ i ∈ s, (chartMeasure ν q).withDensity (fi i)) =
        (chartMeasure ν q).withDensity (∑ i ∈ s, fi i) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp [withDensity_zero]
    | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        rw [ih]
        exact (withDensity_add_left (hmeas i) _).symm
  have hfi_one : (∑ i : ι, fi i) = (1 : M → ℝ≥0∞) := by
    funext x
    have hreal : (∑ i : ι, ρ i x) = 1 := by
      simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (Set.mem_univ x)
    simp only [Finset.sum_apply, Pi.one_apply, fi]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => ρ.nonneg i x), hreal]
    norm_num
  change (∑ i : ι, μi i).restrict Uq = chartMeasure ν q
  rw [hdist]
  simp_rw [show ∀ i : ι, (μi i).restrict Uq =
      (chartMeasure ν q).withDensity (fi i) from
    fun i => weighted_chart_restrict ν hν centers ρ hsub i q]
  rw [hsum, hfi_one, withDensity_one]

variable [T2Space M] [CompactSpace M]

private def chosenChartPartition :
    Σ s : Finset M, {ρ : SmoothPartitionOfUnity s 𝓘(ℝ, E) M Set.univ //
      ρ.IsSubordinate (fun i => (extChartAt 𝓘(ℝ, E) (i : M)).source)} := by
  classical
  let h := ManifoldFiniteFormPartition.exists_finite_chart_partition (E := E) (M := M)
  let s := Classical.choose h
  let ρ := Classical.choose (Classical.choose_spec h)
  have hρ := Classical.choose_spec (Classical.choose_spec h)
  refine ⟨s, ρ, ?_⟩
  simpa only [extChartAt_source] using hρ

/-- The canonical measure determined by a smooth tangent top form. The
definition uses one finite chart partition; the local restriction theorem
below makes the result independent of that choice. -/
def canonicalTopFormMeasure
    (ν : Form 𝓘(ℝ, E) M (Module.finrank ℝ E)) : Measure M :=
  let c := chosenChartPartition (E := E) (M := M)
  partitionMeasure ν (fun i : c.1 => (i : M)) c.2.1

omit [Nontrivial E] [Nonempty M] in
theorem canonicalTopFormMeasure_restrict_chart
    (ν : Form 𝓘(ℝ, E) M (Module.finrank ℝ E))
    (hν : ChartSmooth ν) (q : M) :
    (canonicalTopFormMeasure ν).restrict (extChartAt 𝓘(ℝ, E) q).source =
      chartMeasure ν q := by
  unfold canonicalTopFormMeasure
  let c := chosenChartPartition (E := E) (M := M)
  exact partitionMeasure_restrict_chart ν hν (fun i : c.1 => (i : M))
    c.2.1 c.2.2 q

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsManifold 𝓘(ℝ, E) ∞ M] [BorelSpace M] [Nontrivial E] [Nonempty M]
  [T2Space M] in
theorem measure_eq_of_chart_restrict (μ ν : Measure M)
    (h : ∀ q : M, μ.restrict (extChartAt 𝓘(ℝ, E) q).source =
      ν.restrict (extChartAt 𝓘(ℝ, E) q).source) : μ = ν := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun p : M => (extChartAt 𝓘(ℝ, E) p).source)
    (fun p => isOpen_extChartAt_source (I := 𝓘(ℝ, E)) p)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, mem_extChartAt_source x⟩)
  have hcover : (⋃ p ∈ s, (extChartAt 𝓘(ℝ, E) p).source) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact hs (Set.mem_univ x)
  have he := (Measure.restrict_biUnion_finset_congr
    (μ := μ) (ν := ν) (s := s)
    (t := fun p : M => (extChartAt 𝓘(ℝ, E) p).source)).mpr
      (fun p hp => h p)
  rw [hcover, Measure.restrict_univ, Measure.restrict_univ] at he
  exact he

omit [Nontrivial E] [Nonempty M] in
/-- Smoothness makes the canonical top-form measure locally finite; compactness
then makes it finite. -/
theorem canonicalTopFormMeasure_finite
    (ν : Form 𝓘(ℝ, E) M (Module.finrank ℝ E))
    (hν : ChartSmooth ν) :
    IsFiniteMeasure (canonicalTopFormMeasure ν) := by
  let μ := canonicalTopFormMeasure ν
  have hloc : IsLocallyFiniteMeasure μ := by
    refine ⟨fun x => ?_⟩
    let c := extChartAt 𝓘(ℝ, E) x
    let y := c x
    have hy : y ∈ c.target := c.map_source (mem_extChartAt_source x)
    obtain ⟨K, hK, hyK, hKT⟩ := exists_compact_subset
      (isOpen_extChartAt_target (I := 𝓘(ℝ, E)) x) hy
    let W : Set M := c.source ∩ c ⁻¹' K
    have hWmem : W ∈ 𝓝 x := by
      apply Filter.inter_mem
      · exact (isOpen_extChartAt_source (I := 𝓘(ℝ, E)) x).mem_nhds
          (mem_extChartAt_source x)
      · exact (continuousAt_extChartAt x).preimage_mem_nhds
          (mem_interior_iff_mem_nhds.mp hyK)
    have hWmeas : MeasurableSet W := by
      have hcont : ContinuousOn c c.source := continuousOn_extChartAt x
      have hopen : IsOpen (c.source ∩ c ⁻¹' Kᶜ) :=
        hcont.isOpen_inter_preimage
          (isOpen_extChartAt_source (I := 𝓘(ℝ, E)) x) hK.isClosed.isOpen_compl
      have hset : W = c.source \ (c.source ∩ c ⁻¹' Kᶜ) := by
        ext z
        simp [W]
      rw [hset]
      exact (isOpen_extChartAt_source (I := 𝓘(ℝ, E)) x).measurableSet.diff
        hopen.measurableSet
    have hWle : (chartMeasure ν x) W ≤ coordinateMeasure ν x K := by
      rw [chartMeasure, Measure.map_apply_of_aemeasurable
        (chartSymm_aeMeasurable ν x) hWmeas]
      apply measure_mono_ae
      filter_upwards [coordinateMeasure_ae_mem_target ν x] with z hz hzw
      exact (c.right_inv hz ▸ hzw.2)
    have hμW : μ W < (⊤ : ENNReal) := by
      have hres := canonicalTopFormMeasure_restrict_chart ν hν x
      have hsub : W ⊆ c.source := Set.inter_subset_left
      have heq : μ W = (chartMeasure ν x) W := by
        calc
          μ W = (μ.restrict c.source) W := by
            rw [Measure.restrict_apply hWmeas, Set.inter_eq_left.mpr hsub]
          _ = _ := congrArg (fun m : Measure M => m W) hres
      rw [heq]
      exact lt_of_le_of_lt hWle (coordinateMeasure_compact_lt_top ν hν x hK hKT)
    exact ⟨W, hWmem, hμW⟩
  letI := hloc
  -- A finite subcover by finite-measure neighborhoods bounds the total mass.
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : M => Classical.choose (μ.exists_isOpen_measure_lt_top x))
    (fun x => (Classical.choose_spec (μ.exists_isOpen_measure_lt_top x)).2.1)
    (fun x _ => Set.mem_iUnion.mpr
      ⟨x, (Classical.choose_spec (μ.exists_isOpen_measure_lt_top x)).1⟩)
  have hcover : (Set.univ : Set M) ⊆ ⋃ x ∈ s,
      Classical.choose (μ.exists_isOpen_measure_lt_top x) := hs
  have hbound : μ Set.univ ≤ ∑ x ∈ s,
      μ (Classical.choose (μ.exists_isOpen_measure_lt_top x)) := by
    exact (measure_mono hcover).trans (measure_biUnion_finset_le s _)
  refine ⟨lt_of_le_of_lt hbound ?_⟩
  exact ENNReal.sum_lt_top.mpr (fun x hx =>
    (Classical.choose_spec (μ.exists_isOpen_measure_lt_top x)).2.2)

end
end QuaternionicSymmetry.ManifoldTopFormGlobalMeasure
