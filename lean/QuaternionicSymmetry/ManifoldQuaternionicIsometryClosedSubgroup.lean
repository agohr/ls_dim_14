import QuaternionicSymmetry.ManifoldQuaternionicJointAdaptedDerivative
import QuaternionicSymmetry.GeneralClosedSubgroupLieSource
import QuaternionicSymmetry.ManifoldImmersionSmooth
import QuaternionicSymmetry.ManifoldQuaternionicFullIsometryEmbedding
import QuaternionicSymmetry.ManifoldQuaternionicChartProjection
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Quaternionic isometries form a closed subgroup of the metric isometry
 group. Compactness and a Lie atlas follow from Myers--Steenrod, the smooth
 metric-isometry action, and the closed-subgroup theorem. No assertion about
 preservation of Q by disconnected metric isometries is used. -/
set_option maxHeartbeats 2000000
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

/-- Coordinate change between two genuine tangent charts, as an equivalence. -/
def chartCoordEquiv (i j : atlas E M) (y : M)
    (hi : y ∈ (tangentBundleCore 𝓘(ℝ,E) M).baseSet i)
    (hj : y ∈ (tangentBundleCore 𝓘(ℝ,E) M).baseSet j) : E ≃L[ℝ] E where
  toFun := (tangentBundleCore 𝓘(ℝ,E) M).coordChange i j y
  invFun := (tangentBundleCore 𝓘(ℝ,E) M).coordChange j i y
  map_add' := by intros; simp
  map_smul' := by intros; simp
  left_inv v := by
    rw [(tangentBundleCore 𝓘(ℝ,E) M).coordChange_comp i j i y ⟨⟨hi,hj⟩,hi⟩,
      (tangentBundleCore 𝓘(ℝ,E) M).coordChange_self i y hi]
  right_inv v := by
    rw [(tangentBundleCore 𝓘(ℝ,E) M).coordChange_comp j i j y ⟨⟨hj,hi⟩,hj⟩,
      (tangentBundleCore 𝓘(ℝ,E) M).coordChange_self j y hj]
  continuous_toFun := ((tangentBundleCore 𝓘(ℝ,E) M).coordChange i j y).continuous
  continuous_invFun := ((tangentBundleCore 𝓘(ℝ,E) M).coordChange j i y).continuous

theorem chart_conjugation_mem_iff (i j : atlas E M) (y : M)
    (hi : y ∈ (tangentBundleCore 𝓘(ℝ,E) M).baseSet i)
    (hj : y ∈ (tangentBundleCore 𝓘(ℝ,E) M).baseSet j) (A : E →L[ℝ] E) :
    (chartCoordEquiv i j y hi hj).conjContinuousAlgEquiv A ∈ Q.chartSpan j y ↔
      A ∈ Q.chartSpan i y := by
  let P := transitionAtlas (tangentBundleCore 𝓘(ℝ,E) M)
  change P.adjointCoordChange i j y A ∈ Q.chartSpan j y ↔ A ∈ Q.chartSpan i y
  constructor
  · intro h
    have h' : P.adjointCoordChange j i y (P.adjointCoordChange i j y A) ∈
        Q.chartSpan i y := Q.tangent_map_chartSpan_le j i y hj hi ⟨_,h,rfl⟩
    rw [P.adjointCoordChange_comp i j i y hi hj hi,
      P.adjointCoordChange_self i y hi] at h'
    exact h'
  · intro h
    exact Q.tangent_map_chartSpan_le i j y hi hj ⟨_,h,rfl⟩

theorem preservesSpanForward_iff_conjugation
    (f : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞) :
    PreservesSpanForward Q f ↔ ∀ x A, A ∈ tangentSpan Q x →
      (f.mfderivToContinuousLinearEquiv (by simp) x).conjContinuousAlgEquiv A ∈
        tangentSpan Q (f x) := by
  constructor
  · intro h x A hA
    obtain ⟨B,hB,hAB⟩ := h x A hA
    have heq : (f.mfderivToContinuousLinearEquiv (by simp) x).conjContinuousAlgEquiv A = B := by
      ext w
      let D := f.mfderivToContinuousLinearEquiv (by simp) x
      obtain ⟨v,rfl⟩ := D.surjective w
      change D (A (D.symm (D v))) = B (D v)
      rw [D.symm_apply_apply]
      exact hAB v
    rw [heq]
    exact hB
  · intro h x A hA
    refine ⟨_,h x A hA,?_⟩
    intro v
    let D := f.mfderivToContinuousLinearEquiv (by simp) x
    change D (A v) = D (A (D.symm (D v)))
    rw [D.symm_apply_apply]

theorem continuousAt_chartProjection (y : M) :
    ContinuousAt (chartProjection Q (achart E y)) y := by
  let i := achart E y
  have hi := (tangentBundleCore 𝓘(ℝ,E) M).mem_baseSet_at y
  have ht : ContinuousAt (Q.frames.toFrame i) y :=
    (Q.frames.smooth_to i).continuousOn.continuousAt
      ((tangentBundleCore 𝓘(ℝ,E) M).isOpen_baseSet i |>.mem_nhds hi)
  have hf : ContinuousAt (Q.frames.fromFrame i) y :=
    (Q.frames.smooth_from i).continuousOn.continuousAt
      ((tangentBundleCore 𝓘(ℝ,E) M).isOpen_baseSet i |>.mem_nhds hi)
  let mul := ContinuousLinearMap.mul ℝ (E →L[ℝ] E)
  have hL : ContinuousAt (fun z => Q.chartConjugation i z) y :=
    (mul.continuous.continuousAt.comp hf).clm_comp
      (mul.flip.continuous.continuousAt.comp ht)
  have hR : ContinuousAt (inverseChartConjugation Q i) y :=
    (mul.continuous.continuousAt.comp ht).clm_comp
      (mul.flip.continuous.continuousAt.comp hf)
  exact hL.clm_comp (continuousAt_const.clm_comp (continuousAt_const.clm_comp hR))

section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {G : Type*} [TopologicalSpace G] [ChartedSpace V G]
  [IsManifold 𝓘(ℝ,V) ∞ G]
variable (act : G × M → M)
variable (hAction : ContMDiff (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
  act)

/-- Fixed coordinates centered at `(g₀,x)` before adapting both tangent frames. -/
def partialMatrix (g₀ : G) (x : M) (g : G) : E →L[ℝ] E :=
  (inTangentCoordinates (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) id
    act
    (mfderiv (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E)
      act) (g₀,x) (g,x)).comp
    (ContinuousLinearMap.inr ℝ V E)

def adaptedMatrix (g₀ : G) (x : M) (g : G) : E →L[ℝ] E :=
  (Q.frames.toFrame (achart E (act (g₀,x))) (act (g,x))).comp
    ((partialMatrix (E := E) (V := V) act g₀ x g).comp
      (Q.frames.fromFrame (achart E x) x))

include hAction

theorem continuousAt_partialMatrix (g₀ : G) (x : M) :
    ContinuousAt (partialMatrix (E := E) (V := V) act g₀ x) g₀ := by
  have h : ContinuousAt
      (inTangentCoordinates (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) id
        act
        (mfderiv (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E)
          act) (g₀,x)) (g₀,x) :=
    ((hAction.contMDiffAt (x := (g₀,x))).mfderiv_const (m := 0) (by simp)).continuousAt
  have hc : ContinuousAt
      (fun g : G => inTangentCoordinates (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) id act
        (mfderiv (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) act) (g₀,x) (g,x)) g₀ :=
    ContinuousAt.comp (f := fun g : G => (g,x)) (x := g₀) h
      (continuousAt_id.prodMk continuousAt_const)
  exact continuousAt_comp_inr (E := E) _ g₀ hc

theorem continuousAt_adaptedMatrix (g₀ : G) (x : M) :
    ContinuousAt (adaptedMatrix Q (V := V) act g₀ x) g₀ := by
  have heval : ContinuousAt (fun g : G => act (g,x)) g₀ :=
    hAction.continuous.continuousAt.comp (continuousAt_id.prodMk continuousAt_const)
  have hframe : ContinuousAt (Q.frames.toFrame (achart E (act (g₀,x)))) (act (g₀,x)) :=
    (Q.frames.smooth_to _).continuousOn.continuousAt
      ((Q.frames.adaptedCore.isOpen_baseSet _).mem_nhds
        (Q.frames.adaptedCore.mem_baseSet_at (act (g₀,x))))
  exact (hframe.comp (f := fun g : G => act (g,x)) heval).clm_comp
    ((continuousAt_partialMatrix (E := E) (V := V) act hAction g₀ x).clm_comp continuousAt_const)

/-- This coordinate comparison permits `g x` to move. The target chart remains centered at `g₀ x`. -/
theorem partialMatrix_eq_actual (g₀ g : G) (x : M)
    (hg : g ∈ (chartAt V g₀).source)
    (hx : act (g,x) ∈ (chartAt E (act (g₀,x))).source) :
    partialMatrix (E := E) (V := V) act g₀ x g =
      ((tangentBundleCore 𝓘(ℝ,E) M).coordChange
        (achart E (act (g,x))) (achart E (act (g₀,x))) (act (g,x))).comp
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun y => act (g,y)) x) := by
  apply ContinuousLinearMap.ext
  intro v
  have hprod : (g,x) ∈ (chartAt (ModelProd V E) (g₀,x)).source := by
    simpa only [prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_source,
      Set.mem_prod] using And.intro hg (mem_chart_source E x)
  unfold partialMatrix
  rw [inTangentCoordinates_eq id
    act
    (mfderiv (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E)
      act) hprod hx]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, id_eq]
  rw [coordChange_prod_inr g₀ g x x v hg (mem_chart_source E x),
    (tangentBundleCore 𝓘(ℝ,E) M).coordChange_self (achart E x) x
      (mem_chart_source E x)]
  have hf : MDifferentiableAt (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E)
      act (g,x) :=
    hAction.mdifferentiableAt (by simp)
  have hp := mfderiv_prod_eq_add_apply hf (v := (0,v))
  congr 1
  simpa using hp

omit hAction in
/-- Global closedness of forward quaternionic preservation in any jointly
smooth family of actual diffeomorphisms. No curvature or metric premise. -/
theorem isClosed_preservesSpanForward_family
    (f : G → Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞)
    (ha : ContMDiff (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
      (fun p : G × M => f p.1 p.2)) :
    IsClosed {g : G | PreservesSpanForward Q (f g)} := by
  rw [isClosed_iff_frequently]
  intro g₀ hfreq
  change PreservesSpanForward Q (f g₀)
  rw [preservesSpanForward_iff_conjugation]
  intro x A hA
  let a : G × M → M := fun p => f p.1 p.2
  let D : G → E →L[ℝ] E := partialMatrix (E := E) (V := V) a g₀ x
  let j := achart E (f g₀ x)
  let e₀ : E ≃L[ℝ] E := (f g₀).mfderivToContinuousLinearEquiv (by simp) x
  have hD : ContinuousAt D g₀ := continuousAt_partialMatrix a ha g₀ x
  have hD₀ : D g₀ = e₀.toContinuousLinearMap := by
    rw [show D g₀ = partialMatrix (E := E) (V := V) a g₀ x g₀ from rfl,
      partialMatrix_eq_actual a ha g₀ g₀ x (mem_chart_source V g₀)
        (mem_chart_source E (f g₀ x))]
    ext v
    exact (tangentBundleCore 𝓘(ℝ,E) M).coordChange_self
      (achart E (f g₀ x)) (f g₀ x) (mem_chart_source E (f g₀ x)) _
  have hInv : ContinuousAt (fun g => (D g).inverse) g₀ := by
    have hi : ContinuousAt ContinuousLinearMap.inverse (D g₀) := by
      rw [hD₀]
      exact (contDiffAt_map_inverse (n := 0) e₀).continuousAt
    exact hi.comp (f := D) hD
  let A₀ : E →L[ℝ] E := A
  let C : G → E →L[ℝ] E := fun g => (D g).comp (A₀.comp (D g).inverse)
  have hC : ContinuousAt C g₀ := hD.clm_comp (continuousAt_const.clm_comp hInv)
  have heval : ContinuousAt (fun g : G => f g x) g₀ :=
    ha.continuous.continuousAt.comp (f := fun g : G => (g,x))
      (continuousAt_id.prodMk continuousAt_const)
  have hP : ContinuousAt (fun g : G => chartProjection Q j (f g x)) g₀ :=
    (continuousAt_chartProjection Q (f g₀ x)).comp (f := fun g : G => f g x) heval
  have hPC : ContinuousAt (fun g : G => chartProjection Q j (f g x) (C g)) g₀ :=
    hP.clm_apply hC
  have hGG : ∀ᶠ g : G in 𝓝 g₀, g ∈ (chartAt V g₀).source :=
    (chartAt V g₀).open_source.mem_nhds (mem_chart_source V g₀)
  have hYX : ∀ᶠ g : G in 𝓝 g₀, f g x ∈ (chartAt E (f g₀ x)).source :=
    heval.eventually ((chartAt E (f g₀ x)).open_source.mem_nhds
      (mem_chart_source E (f g₀ x)))
  have hCF : ∃ᶠ g : G in 𝓝 g₀,
      chartProjection Q j (f g x) (C g) = C g := by
    apply (hfreq.and_eventually (hGG.and hYX)).mono
    rintro g ⟨hf,hg,hy⟩
    let k := achart E (f g x)
    have hk : f g x ∈ (tangentBundleCore 𝓘(ℝ,E) M).baseSet k :=
      mem_chart_source E (f g x)
    let e : E ≃L[ℝ] E := (f g).mfderivToContinuousLinearEquiv (by simp) x
    let c := chartCoordEquiv k j (f g x) hk hy
    have hDe : D g = (e.trans c).toContinuousLinearMap := by
      exact partialMatrix_eq_actual a ha g₀ g x hg hy
    have hCe : C g = c.conjContinuousAlgEquiv (e.conjContinuousAlgEquiv A) := by
      dsimp only [C]
      rw [hDe, ContinuousLinearMap.inverse_equiv]
      rfl
    have hAm : e.conjContinuousAlgEquiv A ∈ Q.chartSpan k (f g x) :=
      (preservesSpanForward_iff_conjugation Q (f g)).mp hf x A hA
    have hCm : C g ∈ Q.chartSpan j (f g x) := by
      rw [hCe]
      exact (chart_conjugation_mem_iff Q k j (f g x) hk hy _).mpr hAm
    exact chartProjection_fixed Q j (f g x) hy (C g) hCm
  have hEq : chartProjection Q j (f g₀ x) (C g₀) = C g₀ :=
    (isClosed_eq continuous_fst continuous_snd).mem_of_frequently_of_tendsto
      hCF (hPC.prodMk hC)
  have hMem : C g₀ ∈ Q.chartSpan j (f g₀ x) := by
    rw [← hEq]
    exact chartProjection_mem Q j (f g₀ x) (C g₀)
  have hC₀ : C g₀ = e₀.conjContinuousAlgEquiv A := by
    dsimp only [C]
    rw [hD₀,ContinuousLinearMap.inverse_equiv]
    rfl
  rw [hC₀] at hMem
  exact hMem


end

open ManifoldQuaternionicFullIsometryEmbedding ManifoldQuaternionicIsometryTopology
open ManifoldRiemannianMyersSteenrodInput

/-- The full-isometry image of the actual quaternionic-preserving group is
closed. The only geometric source conclusions used are Myers--Steenrod
and BG-R3's smooth full-isometry action. BG-Q1 is absent. -/
theorem isClosed_range_toFullMetricIsometry
    (hMS : MyersSteenrodConclusion Q) (hR3 : IsometryLieConclusion Q) :
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
  let f : (M ≃ᵢ M) → Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞ :=
    fun g => Classical.choose (hMS g)
  have hmetric (g : M ≃ᵢ M) :
      ManifoldQuaternionicFundamentalSymmetry.PreservesMetric Q (f g) :=
    (Classical.choose_spec (hMS g)).1
  have heval (g : M ≃ᵢ M) (x : M) : f g x = g x :=
    congrFun (Classical.choose_spec (hMS g)).2 x
  have hinv (g : M ≃ᵢ M) : f g⁻¹ = (f g).symm := by
    apply Diffeomorph.ext
    intro x
    apply (f g).injective
    change f g (f g⁻¹ x) = f g ((f g).symm x)
    rw [(f g).apply_symm_apply, heval,heval]
    exact g.apply_symm_apply x
  have ha : ContMDiff (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
      (fun p : (M ≃ᵢ M) × M => f p.1 p.2) := by
    simpa only [heval] using hAction
  have hForward := isClosed_preservesSpanForward_family Q f ha
  have hBoth : IsClosed {g : M ≃ᵢ M | PreservesSpan Q (f g)} := by
    have hi := hForward.preimage (isometryEquiv_inv_continuous (X := M))
    convert hForward.inter hi using 1
    ext g
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, PreservesSpan,hinv]
  have hrange : Set.range (toFullMetricIsometry Q) =
      {g : M ≃ᵢ M | PreservesSpan Q (f g)} := by
    ext g
    constructor
    · rintro ⟨q,rfl⟩
      have hfq : f (toFullMetricIsometry Q q) = q.1 := by
        apply Diffeomorph.ext
        intro x
        exact heval _ x
      simpa only [Set.mem_setOf_eq,hfq] using q.2.2
    · intro hg
      refine ⟨⟨f g,hmetric g,hg⟩,?_⟩
      apply IsometryEquiv.ext
      intro x
      exact heval g x
  rw [hrange]
  exact hBoth

/-- The production compact-open topology on quaternionic isometries is
exactly the induced full metric-isometry topology. -/
theorem toFullMetricIsometry_isEmbedding :
    letI : MetricSpace M := riemannianMetricSpace Q
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    Topology.IsEmbedding (toFullMetricIsometry Q) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  have hp : Topology.IsInducing (isometryEquivToContinuousPairs (X := M)) := by
    constructor
    exact isometryEquivTopology_eq_compactOpen (X := M)
  have hc : Topology.IsInducing
      (isometryEquivToContinuousPairs (X := M) ∘ toFullMetricIsometry Q) := by
    simpa only [Function.comp_def,toFullMetricIsometry_pair] using
      (mapPair_isEmbedding Q).isInducing
  exact ⟨hp.of_comp_iff.mp hc,toFullMetricIsometry_injective Q⟩

/-- The actual quaternionic-preserving group is compact without the false
unrestricted full-isometry preservation boundary. This does not construct
its Lie atlas or identify its Killing algebra. -/
theorem quaternionicIsometries_compactSpace
    (hMS : MyersSteenrodConclusion Q) (hR3 : IsometryLieConclusion Q) :
    CompactSpace (QuaternionicIsometries Q) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : CompactSpace (M ≃ᵢ M) := isometryEquiv_compactSpace (X := M)
  have hc : Topology.IsClosedEmbedding (toFullMetricIsometry Q) :=
    ⟨toFullMetricIsometry_isEmbedding Q,isClosed_range_toFullMetricIsometry Q hMS hR3⟩
  exact hc.compactSpace



/-- The Lee closed-subgroup boundary now supplies a genuine Lie
atlas and smooth actual action, without BG-Q1. The Killing-dimension comparison is separate; the production rank route
uses the contact-section dimension comparison. -/
theorem exists_quaternionic_lie_atlas_without_full_preservation
    (hMS : MyersSteenrodConclusion Q) (hR3 : IsometryLieConclusion Q)
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
    ⟨toFullMetricIsometry_isEmbedding Q,isClosed_range_toFullMetricIsometry Q hMS hR3'⟩
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
