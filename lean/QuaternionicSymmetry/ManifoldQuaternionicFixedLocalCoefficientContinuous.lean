import QuaternionicSymmetry.ManifoldQuaternionicJointAdaptedDerivative
import QuaternionicSymmetry.ManifoldQuaternionicFullIsometryEmbedding

/-! Joint continuity of actual local adapted derivatives on a genuine fixed
component, using BG-R3 smooth full-isometry evaluation. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicFixedLocalCoefficientContinuous
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicFullIsometryEmbedding
open ManifoldQuaternionicJointAdaptedDerivative
open ManifoldQuaternionicFixedCoefficientRepresentation
open ManifoldQuaternionicRiemannianDistance
open MetricIsometryCompactness
open ManifoldRiemannianFixedComponentInput
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff Topology
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- The actual fixed component points lying in the chosen source adapted
chart. This open local domain uses no preferred `indexAt` outside the chart. -/
def fixedChartDomain (S : Subgroup (QuaternionicIsometries Q)) (x c : M) :
    Set (FixedComponent Q S x) :=
  {y | y.1 ∈ (chartAt E c).source}

theorem isOpen_fixedChartDomain
    (S : Subgroup (QuaternionicIsometries Q)) (x c : M) :
    IsOpen (fixedChartDomain Q S x c) := by
  exact (chartAt E c).open_source.preimage continuous_subtype_val

/-- The actual BG-R3 joint adapted derivative in the chart centered at
`x₀`, with BG-R3 source tangent coordinates centered at `(f₀,x₁)`. -/
def jointFixedFrameDerivative
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hChart :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      ChartedSpace V (M ≃ᵢ M))
    (hManifold :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M))
    (f₀ : QuaternionicIsometries Q) (x₀ x₁ : M)
    (f : QuaternionicIsometries Q) (y : M) : E →L[ℝ] E := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  letI : IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hManifold
  exact (Q.frames.toFrame (achart E x₀) y).comp
    (((tangentBundleCore 𝓘(ℝ,E) M).coordChange
      (achart E x₁) (achart E x₀) y).comp
      (((inTangentCoordinates
        (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) id
        (fun p : (M ≃ᵢ M) × M => p.1 p.2)
        (mfderiv (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E)
          (fun p : (M ≃ᵢ M) × M => p.1 p.2))
        (toFullMetricIsometry Q f₀,x₁) (toFullMetricIsometry Q f,y)).comp
          (ContinuousLinearMap.inr ℝ V E)).comp
        (((tangentBundleCore 𝓘(ℝ,E) M).coordChange
          (achart E x₀) (achart E x₁) y).comp
          (Q.frames.fromFrame (achart E x₀) y))))

theorem jointFixedFrameDerivative_eq_localAdaptedDerivative
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hChart :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      ChartedSpace V (M ≃ᵢ M))
    (hManifold :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M))
    (hAction :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      ContMDiff (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
        (fun p : (M ≃ᵢ M) × M => p.1 p.2))
    (f₀ f : QuaternionicIsometries Q) (x₀ x₁ y : M)
    (hgg :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      toFullMetricIsometry Q f ∈
        (chartAt V (toFullMetricIsometry Q f₀)).source)
    (hy₀ : y ∈ (chartAt E x₀).source)
    (hy₁ : y ∈ (chartAt E x₁).source)
    (hfixf₀ : f₀ • x₁ = x₁)
    (hfixx₀ : f • x₀ = x₀)
    (hfixx₁ : f • x₁ = x₁)
    (hfixy : f • y = y) :
    jointFixedFrameDerivative Q hChart hManifold f₀ x₀ x₁ f y =
      ManifoldQuaternionicIsometryLocalDerivative.localAdaptedDerivative Q f x₀ y := by
  have hJ := jointFixedFrame_eq_individualAdapted Q hChart hManifold hAction
    (toFullMetricIsometry Q f₀) (toFullMetricIsometry Q f)
    x₀ x₁ y hgg hy₀ hy₁ hfixf₀ hfixx₀ hfixx₁ hfixy
  simpa only [jointFixedFrameDerivative,
    ManifoldQuaternionicIsometryLocalDerivative.localAdaptedDerivative,
    hfixx₀,hfixy] using hJ

/-- The actual adapted derivative is jointly continuous in a quaternionic
isometry and a point of an actual fixed-component chart domain. This is
derived internally from BG-R3 joint smooth evaluation, not postulated. -/
theorem continuousAt_localAdaptedDerivative_onFixedChart
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hChart :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      ChartedSpace V (M ≃ᵢ M))
    (hManifold :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M))
    (hAction :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      ContMDiff (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
        (fun p : (M ≃ᵢ M) × M => p.1 p.2))
    (S : Subgroup (QuaternionicIsometries Q)) (x c : M)
    (hc : c ∈ fixedPoints Q S)
    (f₀ : S) (y₀ : fixedChartDomain Q S x c) :
    ContinuousAt
      (fun p : S × fixedChartDomain Q S x c =>
        ManifoldQuaternionicIsometryLocalDerivative.localAdaptedDerivative
          Q p.1.1 c p.2.1.1)
      (f₀,y₀) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  letI : IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hManifold
  let U := fixedChartDomain Q S x c
  let j : S → M ≃ᵢ M := fun f => toFullMetricIsometry Q f.1
  let s : U → M := fun y => y.1.1
  have hj : Continuous j := subgroup_toFullMetricIsometry_continuous Q S
  have hs : Continuous s := continuous_subtype_val.comp continuous_subtype_val
  have hi : s y₀ ∈ Q.frames.adaptedCore.baseSet (achart E c) := y₀.2
  have hF := continuousAt_jointAdaptedPartial_fixedFrame Q hChart hManifold
    hAction j hj s hs f₀ y₀ (achart E c) hi
  change ContinuousAt
    (fun p : S × U => jointFixedFrameDerivative Q hChart hManifold
      f₀.1 c (s y₀) p.1.1 (s p.2)) (f₀,y₀) at hF
  have hGAt : ContinuousAt (fun p : S × U => j p.1) (f₀,y₀) :=
    hj.continuousAt.comp continuousAt_fst
  have hYAt : ContinuousAt (fun p : S × U => s p.2) (f₀,y₀) :=
    hs.continuousAt.comp continuousAt_snd
  have hGe : ∀ᶠ p : S × U in 𝓝 (f₀,y₀),
      j p.1 ∈ (chartAt V (j f₀)).source :=
    hGAt.eventually ((chartAt V (j f₀)).open_source.mem_nhds
      (mem_chart_source V (j f₀)))
  have hYe : ∀ᶠ p : S × U in 𝓝 (f₀,y₀),
      s p.2 ∈ (chartAt E (s y₀)).source :=
    hYAt.eventually ((chartAt E (s y₀)).open_source.mem_nhds
      (mem_chart_source E (s y₀)))
  have heq : (fun p : S × U => jointFixedFrameDerivative Q hChart hManifold
        f₀.1 c (s y₀) p.1.1 (s p.2)) =ᶠ[𝓝 (f₀,y₀)]
      (fun p : S × U =>
        ManifoldQuaternionicIsometryLocalDerivative.localAdaptedDerivative
          Q p.1.1 c (s p.2)) := by
    filter_upwards [hGe,hYe] with p hpG hpY
    have hy₀ : s p.2 ∈ (chartAt E c).source := p.2.2
    have hf₀ : f₀.1 • s y₀ = s y₀ :=
      (fixedComponent_mem_fixedPoints Q S x y₀.1) f₀.1 f₀.2
    have hfc : p.1.1 • c = c := hc p.1.1 p.1.2
    have hfy₀ : p.1.1 • s y₀ = s y₀ :=
      (fixedComponent_mem_fixedPoints Q S x y₀.1) p.1.1 p.1.2
    have hfy : p.1.1 • s p.2 = s p.2 :=
      (fixedComponent_mem_fixedPoints Q S x p.2.1) p.1.1 p.1.2
    exact jointFixedFrameDerivative_eq_localAdaptedDerivative Q hChart
      hManifold hAction f₀.1 p.1.1 c (s y₀) (s p.2)
      hpG hy₀ hpY hf₀ hfc hfy₀ hfy
  exact hF.congr_of_eventuallyEq heq.symm

/-- Each actual rank-three coefficient of the fixed-chart isotropy action
is jointly continuous in `(f,y)`. The inverse derivative varies continuously
because inversion in the actual quaternionic-isometry topological group does. -/
theorem continuousAt_localCoefficientRotation_onFixedChart
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hChart :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      ChartedSpace V (M ≃ᵢ M))
    (hManifold :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M))
    (hAction :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      ContMDiff (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
        (fun p : (M ≃ᵢ M) × M => p.1 p.2))
    (S : Subgroup (QuaternionicIsometries Q)) (x c : M)
    (hc : c ∈ fixedPoints Q S)
    (a : Fin 3 → ℝ) (f₀ : S) (y₀ : fixedChartDomain Q S x c) :
    ContinuousAt
      (fun p : S × fixedChartDomain Q S x c =>
        ManifoldQuaternionicIsometryLocalDerivative.localCoefficientRotation
          Q p.1.1 c p.2.1.1 a) (f₀,y₀) := by
  let U := fixedChartDomain Q S x c
  let D : S × U → E →L[ℝ] E := fun p =>
    ManifoldQuaternionicIsometryLocalDerivative.localAdaptedDerivative
      Q p.1.1 c p.2.1.1
  let I : S × U → E →L[ℝ] E := fun p =>
    ManifoldQuaternionicIsometryLocalDerivative.localAdaptedDerivative
      Q (p.1⁻¹).1 c p.2.1.1
  have hD : ContinuousAt D (f₀,y₀) :=
    continuousAt_localAdaptedDerivative_onFixedChart Q hChart hManifold
      hAction S x c hc f₀ y₀
  have hI0 : ContinuousAt D (f₀⁻¹,y₀) :=
    continuousAt_localAdaptedDerivative_onFixedChart Q hChart hManifold
      hAction S x c hc f₀⁻¹ y₀
  have hInv : ContinuousAt
      (fun p : S × U => (p.1⁻¹,p.2)) (f₀,y₀) :=
    ((continuous_inv.comp continuous_fst).prodMk continuous_snd).continuousAt
  have hI : ContinuousAt I (f₀,y₀) := by
    simpa only [D,I] using
      (ContinuousAt.comp (f := fun p : S × U => (p.1⁻¹,p.2))
        (x := (f₀,y₀)) hI0 hInv)
  have hS : ContinuousAt
      (fun _ : S × U => synth (Q.reduction.Q (achart E c)) a)
      (f₀,y₀) := continuousAt_const
  have hC : ContinuousAt (fun p : S × U =>
      coeff (Q.reduction.Q (achart E c))
        ((D p).comp ((synth (Q.reduction.Q (achart E c)) a).comp (I p))))
      (f₀,y₀) :=
    (coeff (Q.reduction.Q (achart E c))).continuous.continuousAt.comp
      (f := fun p : S × U =>
        (D p).comp ((synth (Q.reduction.Q (achart E c)) a).comp (I p)))
      (x := (f₀,y₀)) (hD.clm_comp (hS.clm_comp hI))
  have heq : (fun p : S × U =>
      coeff (Q.reduction.Q (achart E c))
        ((D p).comp ((synth (Q.reduction.Q (achart E c)) a).comp (I p)))) =
      (fun p : S × U =>
        ManifoldQuaternionicIsometryLocalDerivative.localCoefficientRotation
          Q p.1.1 c p.2.1.1 a) := by
    funext p
    have hfc : p.1.1 • c = c := hc p.1.1 p.1.2
    have hfy : p.1.1 • p.2.1.1 = p.2.1.1 :=
      (fixedComponent_mem_fixedPoints Q S x p.2.1) p.1.1 p.1.2
    simp only [D,I,
      ManifoldQuaternionicIsometryLocalDerivative.localCoefficientRotation,
      ManifoldQuaternionicIsometryLocalDerivative.localAdaptedInverseDerivative,
      hfc,hfy,Subgroup.coe_inv]
  simpa only [heq] using hC

end
end QuaternionicSymmetry.ManifoldQuaternionicFixedLocalCoefficientContinuous
