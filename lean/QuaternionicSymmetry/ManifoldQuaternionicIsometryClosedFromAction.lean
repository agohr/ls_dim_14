import QuaternionicSymmetry.ManifoldQuaternionicIsometryClosedSubgroup

/-! Closedness of quaternionic isometries from the smooth joint action alone. -/
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryClosedSubgroup
open QuaternionicSymmetry Manifold
open ManifoldQuaternionicRiemannianDistance MetricIsometryCompactness
open ManifoldRiemannianIsometryLieInput ManifoldQuaternionicJointAdaptedDerivative
open ProdTangentCoordChange
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicChartProjection
open VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction

section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {G : Type*} [TopologicalSpace G] [ChartedSpace V G]
  [IsManifold 𝓘(ℝ,V) ∞ G]
variable (act : G × M → M)
variable (hAction : ContMDiff (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
  act)

omit hAction in
/-- Metric preservation is closed in a jointly smooth family. This uses
the genuine derivative and the metric in a fixed target chart. -/
theorem isClosed_preservesMetric_family
    (f : G → Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞)
    (ha : ContMDiff (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
      (fun p : G × M => f p.1 p.2)) :
    IsClosed {g : G | ManifoldQuaternionicFundamentalSymmetry.PreservesMetric Q (f g)} := by
  rw [isClosed_iff_frequently]
  intro g₀ hfreq x v w
  let a : G × M → M := fun p => f p.1 p.2
  let D : G → E →L[ℝ] E := partialMatrix (E := E) (V := V) a g₀ x
  let j := achart E (f g₀ x)
  let B : G → ℝ := fun g => Q.chartMetricForm j (f g x) (D g v) (D g w)
  have hD : ContinuousAt D g₀ := continuousAt_partialMatrix a ha g₀ x
  have heval : ContinuousAt (fun g : G => f g x) g₀ :=
    ha.continuous.continuousAt.comp (f := fun g : G => (g,x))
      (continuousAt_id.prodMk continuousAt_const)
  have hmetric : ContinuousAt (Q.chartMetricForm j) (f g₀ x) :=
    (Q.smooth_chartMetricForm j).continuousOn.continuousAt
      ((chartAt E (f g₀ x)).open_source.mem_nhds (mem_chart_source E (f g₀ x)))
  have hB : ContinuousAt B g₀ :=
    ((hmetric.comp (f := fun g : G => f g x) heval).clm_apply
      (hD.clm_apply continuousAt_const)).clm_apply
      (hD.clm_apply continuousAt_const)
  have hGG : ∀ᶠ g : G in 𝓝 g₀, g ∈ (chartAt V g₀).source :=
    (chartAt V g₀).open_source.mem_nhds (mem_chart_source V g₀)
  have hYX : ∀ᶠ g : G in 𝓝 g₀, f g x ∈ (chartAt E (f g₀ x)).source :=
    heval.eventually ((chartAt E (f g₀ x)).open_source.mem_nhds
      (mem_chart_source E (f g₀ x)))
  have hBeq (g : G) (hg : g ∈ (chartAt V g₀).source)
      (hy : f g x ∈ (chartAt E (f g₀ x)).source) :
      B g = Q.tangentMetricForm (f g x)
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f g : M → M) x v)
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f g : M → M) x w) := by
    rw [Q.tangentMetric_chart_eq j (f g x) hy]
    dsimp only [B, D]
    rw [partialMatrix_eq_actual a ha g₀ g x hg hy]
    rfl
  have hBF : ∃ᶠ g : G in 𝓝 g₀, B g = Q.tangentMetricForm x v w := by
    apply (hfreq.and_eventually (hGG.and hYX)).mono
    rintro g ⟨hf,hg,hy⟩
    exact (hBeq g hg hy).trans (hf x v w)
  have hEq : B g₀ = Q.tangentMetricForm x v w :=
    (isClosed_eq continuous_fst continuous_snd).mem_of_frequently_of_tendsto
      hBF (hB.prodMk continuousAt_const)
  rw [hBeq g₀ (mem_chart_source V g₀) (mem_chart_source E (f g₀ x))] at hEq
  exact hEq


end
open ManifoldQuaternionicFullIsometryEmbedding ManifoldQuaternionicIsometryTopology

/-- Both metric and quaternionic preservation are closed conditions on the
smooth action. No regularity theorem for distance isometries is required. -/
theorem isClosed_range_toFullMetricIsometry_of_isometryLie
    (hR3 : IsometryLieConclusion Q) :
    letI : MetricSpace M := riemannianMetricSpace Q
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    IsClosed (Set.range (toFullMetricIsometry Q)) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  obtain ⟨V,hNorm,hSpace,hFinite,hChart,hManifold,hLie,hAction⟩ := hR3
  letI : NormedAddCommGroup V := hNorm
  letI : NormedSpace ℝ V := hSpace
  letI : FiniteDimensional ℝ V := hFinite
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  letI : IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hManifold
  let f : (M ≃ᵢ M) → Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞ := fun g => {
    toEquiv := g.toEquiv
    contMDiff_toFun := hAction.comp (contMDiff_const.prodMk contMDiff_id)
    contMDiff_invFun := hAction.comp
      (contMDiff_const (c := g.symm).prodMk contMDiff_id) }
  have heval (g : M ≃ᵢ M) (x : M) : f g x = g x := rfl
  have ha : ContMDiff (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
      (fun p : (M ≃ᵢ M) × M => f p.1 p.2) := by
    simpa only [heval] using hAction
  have hForward := isClosed_preservesSpanForward_family Q f ha
  have hBoth : IsClosed {g : M ≃ᵢ M | PreservesSpan Q (f g)} := by
    have hi := hForward.preimage (isometryEquiv_inv_continuous (X := M))
    exact hForward.inter hi
  have hMetric := isClosed_preservesMetric_family Q f ha
  have hrange : Set.range (toFullMetricIsometry Q) =
      {g : M ≃ᵢ M | ManifoldQuaternionicFundamentalSymmetry.PreservesMetric Q (f g) ∧
        PreservesSpan Q (f g)} := by
    ext g
    constructor
    · rintro ⟨q,rfl⟩
      have hfq : f (toFullMetricIsometry Q q) = q.1 := by
        apply Diffeomorph.ext
        intro x
        exact heval _ x
      simpa only [Set.mem_setOf_eq,hfq] using q.2
    · intro hg
      refine ⟨⟨f g,hg⟩,?_⟩
      apply IsometryEquiv.ext
      intro x
      exact heval g x
  rw [hrange]
  exact hMetric.inter hBoth

/-- Compactness of the quaternionic isometries from the existing smooth
isometry-group action, without Myers--Steenrod. -/
theorem quaternionicIsometries_compactSpace_of_isometryLie
    (hR3 : IsometryLieConclusion Q) :
    CompactSpace (QuaternionicIsometries Q) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : CompactSpace (M ≃ᵢ M) := isometryEquiv_compactSpace (X := M)
  have hc : Topology.IsClosedEmbedding (toFullMetricIsometry Q) :=
    ⟨toFullMetricIsometry_isEmbedding Q,isClosed_range_toFullMetricIsometry_of_isometryLie Q hR3⟩
  exact hc.compactSpace



/-- The Lee closed-subgroup boundary now supplies a genuine Lie
atlas and smooth actual action, without BG-Q1. The Killing-dimension comparison is separate; the production rank route
uses the contact-section dimension comparison. -/
theorem exists_quaternionic_lie_atlas_of_isometryLie
    (hR3 : IsometryLieConclusion Q)
    (hLee : GeneralClosedSubgroupLieSource.LeeClosedEmbeddingTheorem) :
    ∃ (d : ℕ) (hChart : ChartedSpace (Fin d → ℝ) (QuaternionicIsometries Q)),
      letI := hChart
      IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (QuaternionicIsometries Q) ∧
      LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (QuaternionicIsometries Q) ∧
      ContMDiff ((𝓘(ℝ,Fin d → ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
        (fun p : QuaternionicIsometries Q × M => p.1 • p.2) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : CompactSpace (M ≃ᵢ M) := isometryEquiv_compactSpace (X := M)
  obtain ⟨V,hNorm,hSpace,hFinite,hChart,hManifold,hLie,hAction⟩ := hR3
  letI : NormedAddCommGroup V := hNorm
  letI : NormedSpace ℝ V := hSpace
  letI : FiniteDimensional ℝ V := hFinite
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  letI : IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hManifold
  letI : LieGroup 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hLie
  have hpairs : Topology.IsEmbedding (isometryEquivPairsEquiv (X := M)) :=
    ⟨⟨rfl⟩,(isometryEquivPairsEquiv (X := M)).injective⟩
  letI : T2Space (M ≃ᵢ M) := hpairs.t2Space
  letI : SecondCountableTopology (M ≃ᵢ M) :=
    ChartedSpace.secondCountable_of_sigmaCompact V (M ≃ᵢ M)
  have hR3' : IsometryLieConclusion Q :=
    ⟨V,hNorm,hSpace,hFinite,hChart,hManifold,hLie,hAction⟩
  have hclosed : Topology.IsClosedEmbedding (toFullMetricIsometry Q) :=
    ⟨toFullMetricIsometry_isEmbedding Q,isClosed_range_toFullMetricIsometry_of_isometryLie Q hR3'⟩
  obtain ⟨d,⟨a⟩⟩ := hLee (E := V) (toFullMetricIsometry Q) hclosed
  letI : ChartedSpace (Fin d → ℝ) (QuaternionicIsometries Q) := a.charts
  letI : IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (QuaternionicIsometries Q) := a.manifold
  letI : LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (QuaternionicIsometries Q) := a.lieGroup
  refine ⟨d,a.charts,a.manifold,a.lieGroup,?_⟩
  have hi := ManifoldImmersionSmooth.smoothEmbedding_contMDiff a.smoothEmbedding
  have hp : ContMDiff ((𝓘(ℝ,Fin d → ℝ)).prod 𝓘(ℝ,E))
      ((𝓘(ℝ,V)).prod 𝓘(ℝ,E)) ∞
      (fun p : QuaternionicIsometries Q × M => (toFullMetricIsometry Q p.1,p.2)) :=
    (hi.comp contMDiff_fst).prodMk contMDiff_snd
  exact hAction.comp hp


end
end QuaternionicSymmetry.ManifoldQuaternionicIsometryClosedSubgroup
