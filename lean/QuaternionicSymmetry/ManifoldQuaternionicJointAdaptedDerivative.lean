import QuaternionicSymmetry.ManifoldRiemannianIsometryLieInput
import QuaternionicSymmetry.ManifoldQuaternionicFixedCoefficientRepresentation
import QuaternionicSymmetry.ProdTangentCoordChange
import QuaternionicSymmetry.ManifoldFixedChartDerivativeTransport
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The spatial partial derivative of the actual full-isometry action remains
jointly continuous after conversion into one fixed local adapted quaternionic
frame. This is the analytic input for local rank-three isotropy matrices. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicJointAdaptedDerivative
open ManifoldQuaternionicRiemannianDistance
open MetricIsometryCompactness
open ManifoldRiemannianIsometryLieInput
open ProdTangentCoordChange
open ManifoldFixedChartDerivativeTransport
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff InnerProduct
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- Actual adapted gauges preserve joint derivative continuity on a fixed
chart. The proof uses their smoothness, not a global choice of frames. -/
theorem continuousAt_adaptedConjugate
    {K N : Type*} [TopologicalSpace K] [TopologicalSpace N]
    (k₀ : K) (n₀ : N)
    (F : K × N → E →L[ℝ] E) (hF : ContinuousAt F (k₀,n₀))
    (s : N → M) (hs : Continuous s)
    (i : atlas E M)
    (hi : s n₀ ∈ Q.frames.adaptedCore.baseSet i) :
    ContinuousAt
      (fun p : K × N =>
        (Q.frames.toFrame i (s p.2)).comp
          ((F p).comp (Q.frames.fromFrame i (s p.2))))
      (k₀,n₀) := by
  have hsAt : ContinuousAt (fun p : K × N => s p.2) (k₀,n₀) :=
    hs.continuousAt.comp continuousAt_snd
  have hto : ContinuousAt (Q.frames.toFrame i) (s n₀) :=
    (Q.frames.smooth_to i).continuousOn.continuousAt
      ((Q.frames.adaptedCore.isOpen_baseSet i).mem_nhds hi)
  have hfrom : ContinuousAt (Q.frames.fromFrame i) (s n₀) :=
    (Q.frames.smooth_from i).continuousOn.continuousAt
      ((Q.frames.adaptedCore.isOpen_baseSet i).mem_nhds hi)
  have hto' : ContinuousAt (fun p : K × N => Q.frames.toFrame i (s p.2))
      (k₀,n₀) := ContinuousAt.comp (f := fun p : K × N => s p.2)
        (x := (k₀,n₀)) hto hsAt
  have hfrom' : ContinuousAt (fun p : K × N => Q.frames.fromFrame i (s p.2))
      (k₀,n₀) := ContinuousAt.comp (f := fun p : K × N => s p.2)
        (x := (k₀,n₀)) hfrom hsAt
  exact hto'.clm_comp (hF.clm_comp hfrom')

/-- Finite-dimensional quaternionic coefficient extraction is continuous
under the adjoint-conjugation of a jointly continuous adapted derivative.
For actual isometries, this adjoint is the inverse derivative. -/
theorem continuousAt_coefficientOfAdjointConjugation
    {Z : Type*} [TopologicalSpace Z] (i : atlas E M)
    (D : Z → E →L[ℝ] E) (z₀ : Z) (hD : ContinuousAt D z₀)
    (a : Fin 3 → ℝ) :
    ContinuousAt (fun z =>
      coeff (Q.reduction.Q i)
        ((D z).comp ((synth (Q.reduction.Q i) a).comp ((D z)†)))) z₀ := by
  have hAdj : ContinuousAt (fun z => (D z)†) z₀ :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := E)).continuous.continuousAt.comp
      (f := D) (x := z₀) hD
  have hSynth : ContinuousAt (fun _ : Z => synth (Q.reduction.Q i) a) z₀ :=
    continuousAt_const
  have hComp : ContinuousAt (fun z =>
      (D z).comp ((synth (Q.reduction.Q i) a).comp ((D z)†))) z₀ :=
    hD.clm_comp (hSynth.clm_comp hAdj)
  exact (coeff (Q.reduction.Q i)).continuous.continuousAt.comp
    (f := fun z => (D z).comp ((synth (Q.reduction.Q i) a).comp ((D z)†)))
    (x := z₀) hComp

/-- Apply the preceding gauge lemma to the actual spatial partial of the
BG-R3 smooth joint evaluation. `j` can be the continuous inclusion of a
compact subgroup and `s` the actual fixed-component inclusion. -/
theorem continuousAt_jointAdaptedPartial
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
    {K N : Type*} [TopologicalSpace K] [TopologicalSpace N]
    (j : K → (letI : MetricSpace M := riemannianMetricSpace Q; M ≃ᵢ M))
    (hj :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      Continuous j)
    (s : N → M) (hs : Continuous s) (k₀ : K) (n₀ : N)
    (i : atlas E M)
    (hi : s n₀ ∈ Q.frames.adaptedCore.baseSet i) :
    letI : MetricSpace M := riemannianMetricSpace Q
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : ChartedSpace V (M ≃ᵢ M) := hChart
    ContinuousAt
      (fun p : K × N =>
        (Q.frames.toFrame i (s p.2)).comp
          (((inTangentCoordinates
            (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) id
            (fun q : (M ≃ᵢ M) × M => q.1 q.2)
            (mfderiv (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E)
              (fun q : (M ≃ᵢ M) × M => q.1 q.2))
            (j k₀,s n₀) (j p.1,s p.2)).comp
              (ContinuousLinearMap.inr ℝ V E)).comp
            (Q.frames.fromFrame i (s p.2))))
      (k₀,n₀) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  let F : K × N → E →L[ℝ] E := fun p =>
    (inTangentCoordinates (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) id
      (fun q : (M ≃ᵢ M) × M => q.1 q.2)
      (mfderiv (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E)
        (fun q : (M ≃ᵢ M) × M => q.1 q.2))
      (j k₀,s n₀) (j p.1,s p.2)).comp
        (ContinuousLinearMap.inr ℝ V E)
  have hF : ContinuousAt F (k₀,n₀) :=
    continuousAt_actionPartialX_along_families Q hChart hManifold
      hAction j hj s hs k₀ n₀
  exact continuousAt_adaptedConjugate Q k₀ n₀ F hF s hs i hi

/-- The correctly transported derivative in a fixed adapted chart. The
BG-R3 tangent coordinates are centered at `s n₀`; the two actual tangent-core
coordinate changes move them into the fixed chart `i` before applying its
smooth frame gauges. -/
theorem continuousAt_jointAdaptedPartial_fixedFrame
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
    {K N : Type*} [TopologicalSpace K] [TopologicalSpace N]
    (j : K → (letI : MetricSpace M := riemannianMetricSpace Q; M ≃ᵢ M))
    (hj :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      Continuous j)
    (s : N → M) (hs : Continuous s) (k₀ : K) (n₀ : N)
    (i : atlas E M)
    (hi : s n₀ ∈ Q.frames.adaptedCore.baseSet i) :
    letI : MetricSpace M := riemannianMetricSpace Q
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : ChartedSpace V (M ≃ᵢ M) := hChart
    ContinuousAt
      (fun p : K × N =>
        (Q.frames.toFrame i (s p.2)).comp
          (((tangentBundleCore 𝓘(ℝ,E) M).coordChange
            (achart E (s n₀)) i (s p.2)).comp
            (((inTangentCoordinates
              (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) id
              (fun q : (M ≃ᵢ M) × M => q.1 q.2)
              (mfderiv (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E)
                (fun q : (M ≃ᵢ M) × M => q.1 q.2))
              (j k₀,s n₀) (j p.1,s p.2)).comp
                (ContinuousLinearMap.inr ℝ V E)).comp
              (((tangentBundleCore 𝓘(ℝ,E) M).coordChange
                i (achart E (s n₀)) (s p.2)).comp
                (Q.frames.fromFrame i (s p.2))))))
      (k₀,n₀) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  let k := achart E (s n₀)
  have hk : s n₀ ∈ Q.frames.adaptedCore.baseSet k :=
    Q.frames.adaptedCore.mem_baseSet_at (s n₀)
  have hsAt : ContinuousAt (fun p : K × N => s p.2) (k₀,n₀) :=
    hs.continuousAt.comp continuousAt_snd
  have hopen : IsOpen (Q.frames.adaptedCore.baseSet i ∩
      Q.frames.adaptedCore.baseSet k) :=
    (Q.frames.adaptedCore.isOpen_baseSet i).inter
      (Q.frames.adaptedCore.isOpen_baseSet k)
  have hki : ContinuousAt
      ((tangentBundleCore 𝓘(ℝ,E) M).coordChange k i) (s n₀) :=
    ((tangentBundleCore 𝓘(ℝ,E) M).continuousOn_coordChange k i).continuousAt
      (((Q.frames.adaptedCore.isOpen_baseSet k).inter
        (Q.frames.adaptedCore.isOpen_baseSet i)).mem_nhds ⟨hk,hi⟩)
  have hik : ContinuousAt
      ((tangentBundleCore 𝓘(ℝ,E) M).coordChange i k) (s n₀) :=
    ((tangentBundleCore 𝓘(ℝ,E) M).continuousOn_coordChange i k).continuousAt
      (hopen.mem_nhds ⟨hi,hk⟩)
  have hki' : ContinuousAt
      (fun p : K × N => (tangentBundleCore 𝓘(ℝ,E) M).coordChange k i (s p.2))
      (k₀,n₀) := ContinuousAt.comp (f := fun p : K × N => s p.2)
        (x := (k₀,n₀)) hki hsAt
  have hik' : ContinuousAt
      (fun p : K × N => (tangentBundleCore 𝓘(ℝ,E) M).coordChange i k (s p.2))
      (k₀,n₀) := ContinuousAt.comp (f := fun p : K × N => s p.2)
        (x := (k₀,n₀)) hik hsAt
  let F : K × N → E →L[ℝ] E := fun p =>
    ((tangentBundleCore 𝓘(ℝ,E) M).coordChange k i (s p.2)).comp
      (((inTangentCoordinates (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) id
        (fun q : (M ≃ᵢ M) × M => q.1 q.2)
        (mfderiv (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E)
          (fun q : (M ≃ᵢ M) × M => q.1 q.2))
        (j k₀,s n₀) (j p.1,s p.2)).comp
          (ContinuousLinearMap.inr ℝ V E)).comp
        ((tangentBundleCore 𝓘(ℝ,E) M).coordChange i k (s p.2)))
  have hpartial := continuousAt_actionPartialX_along_families Q hChart
    hManifold hAction j hj s hs k₀ n₀
  have hF : ContinuousAt F (k₀,n₀) :=
    hki'.clm_comp (hpartial.clm_comp hik')
  exact continuousAt_adaptedConjugate Q k₀ n₀ F hF s hs i hi

/-- The `(0,v)` spatial partial derivative of the smooth full-isometry
action is exactly the derivative of the individual isometry at that point.
This is the algebraic identity needed to compare the joint derivative above
with the existing fixed-chart quaternionic coefficient formula. -/
theorem actionPartial_eq_isometryDerivative
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
    (g : letI : MetricSpace M := riemannianMetricSpace Q; M ≃ᵢ M)
    (y : M) (v : E) :
    letI : MetricSpace M := riemannianMetricSpace Q
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : ChartedSpace V (M ≃ᵢ M) := hChart
    mfderiv (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E)
      (fun p : (M ≃ᵢ M) × M => p.1 p.2) (g,y) (0,v) =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (g : M → M) y v := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  letI : IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hManifold
  have hf : MDifferentiableAt (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E)
      (fun p : (M ≃ᵢ M) × M => p.1 p.2) (g,y) :=
    hAction.mdifferentiableAt (by simp)
  have h := mfderiv_prod_eq_add_apply hf (v := (0,v))
  simpa using h

/-- At an actual common fixed locus, the vertical block of BG-R3's joint
evaluation derivative in fixed product charts is the fixed-chart derivative
of the individual isometry. The `g`-chart overlap is local in the group;
the `y`-chart overlap is local in the fixed component. -/
theorem jointPartial_eq_individualFixedChart
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
    (g₀ g : letI : MetricSpace M := riemannianMetricSpace Q; M ≃ᵢ M)
    (x₀ y : M)
    (hgg :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      g ∈ (chartAt V g₀).source)
    (hxy : y ∈ (chartAt E x₀).source)
    (hfix₀ : g₀ x₀ = x₀) (hfixg₀ : g x₀ = x₀)
    (hfixgy : g y = y) :
    letI : MetricSpace M := riemannianMetricSpace Q
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : ChartedSpace V (M ≃ᵢ M) := hChart
    (inTangentCoordinates (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) id
      (fun p : (M ≃ᵢ M) × M => p.1 p.2)
      (mfderiv (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E)
        (fun p : (M ≃ᵢ M) × M => p.1 p.2))
      (g₀,x₀) (g,y)).comp (ContinuousLinearMap.inr ℝ V E) =
      inTangentCoordinates 𝓘(ℝ,E) 𝓘(ℝ,E) id (g : M → M)
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (g : M → M)) x₀ y := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  letI : IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hManifold
  apply ContinuousLinearMap.ext
  intro v
  have hprod : (g,y) ∈ (chartAt (ModelProd V E) (g₀,x₀)).source := by
    simpa only [prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_source,
      Set.mem_prod] using And.intro hgg hxy
  rw [inTangentCoordinates_eq id
    (fun p : (M ≃ᵢ M) × M => p.1 p.2)
    (mfderiv (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E)
      (fun p : (M ≃ᵢ M) × M => p.1 p.2))
    hprod (by simpa only [hfix₀,hfixgy] using hxy)]
  rw [inTangentCoordinates_eq id (g : M → M)
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (g : M → M))
    hxy (by simpa only [hfixg₀,hfixgy] using hxy)]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    id_eq]
  rw [coordChange_prod_inr g₀ g x₀ y v hgg hxy]
  have hpart := actionPartial_eq_isometryDerivative Q hChart hManifold
    hAction g y
      ((tangentBundleCore 𝓘(ℝ,E) M).coordChange
        (achart E x₀) (achart E y) y v)
  have htarget := congrArg
    (fun w : E => (tangentBundleCore 𝓘(ℝ,E) M).coordChange
      (achart E (g y)) (achart E (g₀ x₀)) (g y) w) hpart
  simpa only [hfix₀,hfixg₀,hfixgy] using htarget

/-- The correctly transported BG-R3 derivative in a fixed adapted chart
is precisely the individual isometry derivative expressed in that chart.
No arbitrary equality of analytic and geometric actions is assumed. -/
theorem jointFixedFrame_eq_individualAdapted
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
    (g₀ g : letI : MetricSpace M := riemannianMetricSpace Q; M ≃ᵢ M)
    (x₀ x₁ y : M)
    (hgg :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      g ∈ (chartAt V g₀).source)
    (hy₀ : y ∈ (chartAt E x₀).source)
    (hy₁ : y ∈ (chartAt E x₁).source)
    (hfixg₀ : g₀ x₁ = x₁) (hfixx₀ : g x₀ = x₀)
    (hfixx₁ : g x₁ = x₁) (hfixy : g y = y) :
    letI : MetricSpace M := riemannianMetricSpace Q
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : ChartedSpace V (M ≃ᵢ M) := hChart
    (Q.frames.toFrame (achart E x₀) y).comp
      (((tangentBundleCore 𝓘(ℝ,E) M).coordChange
        (achart E x₁) (achart E x₀) y).comp
        (((inTangentCoordinates
          (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) id
          (fun p : (M ≃ᵢ M) × M => p.1 p.2)
          (mfderiv (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E)
            (fun p : (M ≃ᵢ M) × M => p.1 p.2))
          (g₀,x₁) (g,y)).comp
            (ContinuousLinearMap.inr ℝ V E)).comp
          (((tangentBundleCore 𝓘(ℝ,E) M).coordChange
            (achart E x₀) (achart E x₁) y).comp
            (Q.frames.fromFrame (achart E x₀) y)))) =
      (Q.frames.toFrame (achart E x₀) y).comp
        ((inTangentCoordinates 𝓘(ℝ,E) 𝓘(ℝ,E) id (g : M → M)
          (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (g : M → M)) x₀ y).comp
          (Q.frames.fromFrame (achart E x₀) y)) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  letI : IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hManifold
  have hpartial := jointPartial_eq_individualFixedChart Q hChart hManifold
    hAction g₀ g x₁ y hgg hy₁ hfixg₀ hfixx₁ hfixy
  have htrans := fixedChartDerivative_transport (g : M → M)
    x₀ x₁ y hfixx₀ hfixx₁ hfixy hy₀ hy₁
  have hcore : ((tangentBundleCore 𝓘(ℝ,E) M).coordChange
      (achart E x₁) (achart E x₀) y).comp
      (((inTangentCoordinates
        (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) id
        (fun p : (M ≃ᵢ M) × M => p.1 p.2)
        (mfderiv (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E)
          (fun p : (M ≃ᵢ M) × M => p.1 p.2))
        (g₀,x₁) (g,y)).comp
          (ContinuousLinearMap.inr ℝ V E)).comp
        ((tangentBundleCore 𝓘(ℝ,E) M).coordChange
          (achart E x₀) (achart E x₁) y)) =
        inTangentCoordinates 𝓘(ℝ,E) 𝓘(ℝ,E) id (g : M → M)
          (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (g : M → M)) x₀ y := by
    rw [hpartial]
    exact htrans
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg
    (fun T : E →L[ℝ] E => T (Q.frames.fromFrame (achart E x₀) y v)) hcore
  have hv' := congrArg (Q.frames.toFrame (achart E x₀) y) hv
  simpa only [ContinuousLinearMap.comp_apply] using hv'

end
end QuaternionicSymmetry.ManifoldQuaternionicJointAdaptedDerivative
