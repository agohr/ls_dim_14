import QuaternionicSymmetry.ManifoldRiemannianMyersSteenrodInput
import QuaternionicSymmetry.ManifoldQuaternionicKillingFields
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-! BG-R3/R4 on the full isometry group of the constructed Riemannian
metric. These source boundaries contain only general Riemannian geometry;
no quaternionic-preserving subgroup or classification conclusion occurs. -/
namespace QuaternionicSymmetry.ManifoldRiemannianIsometryLieInput
open Manifold
open ManifoldQuaternionicRiemannianDistance
open MetricIsometryCompactness
open ManifoldQuaternionicKillingFields
open scoped Manifold ContDiff
noncomputable section
universe uIso vIso

variable {E : Type uIso} {M : Type vIso}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- BG-R3's Lie-structure conclusion for the genuine compact-open full
isometry group. The atlas is on `M ≃ᵢ M` itself and shares the already
constructed group topology. -/
def IsometryLieConclusion : Prop :=
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  ∃ (V : Type) (hNorm : NormedAddCommGroup V),
    letI : NormedAddCommGroup V := hNorm
    ∃ (hSpace : NormedSpace ℝ V),
      letI : NormedSpace ℝ V := hSpace
      ∃ (hFinite : FiniteDimensional ℝ V)
        (hChart : ChartedSpace V (M ≃ᵢ M)),
        letI : FiniteDimensional ℝ V := hFinite
        letI : ChartedSpace V (M ≃ᵢ M) := hChart
        IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M) ∧
        LieGroup 𝓘(ℝ,V) ∞ (M ≃ᵢ M) ∧
        ContMDiff (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
          (fun p : (M ≃ᵢ M) × M => p.1 p.2)

/-- BG-R4 identifies the tangent at the actual group identity with the
actual metric Killing fields. The pointwise orbit-derivative equation pins
down the comparison map rather than postulating an arbitrary equivalence. -/
def KillingLieConclusion
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hChart :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      ChartedSpace V (M ≃ᵢ M)) : Prop :=
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  ∃ L : TangentSpace 𝓘(ℝ,V) (1 : M ≃ᵢ M) ≃ₗ[ℝ] KillingFields Q,
    ∀ (v : TangentSpace 𝓘(ℝ,V) (1 : M ≃ᵢ M)) (x : M),
      (L v).1 x =
        mfderiv 𝓘(ℝ,V) 𝓘(ℝ,E) (fun g : M ≃ᵢ M => g x) 1 v

/-- Joint continuity of the differential action is an internal consequence
of BG-R3's smooth joint evaluation, in bundled tangent coordinates. -/
theorem continuous_tangentAction
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
        (fun p : (M ≃ᵢ M) × M => p.1 p.2)) :
    letI : MetricSpace M := riemannianMetricSpace Q
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : ChartedSpace V (M ≃ᵢ M) := hChart
    Continuous (tangentMap (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E)
      (fun p : (M ≃ᵢ M) × M => p.1 p.2)) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  letI : IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hManifold
  exact hAction.continuous_tangentMap (by simp)

/-- In the fixed source/target tangent charts centered at `p₀`, the full
derivative of joint evaluation varies continuously near `p₀`. This is a
coordinate-level consequence of smooth joint evaluation, complementary to
the bundled-tangent statement above. -/
theorem continuousAt_actionDerivative_inTangentCoordinates
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
    (p₀ :
      letI : MetricSpace M := riemannianMetricSpace Q
      (M ≃ᵢ M) × M) :
    letI : MetricSpace M := riemannianMetricSpace Q
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : ChartedSpace V (M ≃ᵢ M) := hChart
    ContinuousAt
      (inTangentCoordinates (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) id
        (fun p : (M ≃ᵢ M) × M => p.1 p.2)
        (mfderiv (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E)
          (fun p : (M ≃ᵢ M) × M => p.1 p.2)) p₀) p₀ := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  letI : IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hManifold
  have h := (hAction.contMDiffAt (x := p₀)).mfderiv_const (m := 0) (by simp)
  exact h.continuousAt

/-- Restricting the full charted derivative to the `(0,v)` direction is
continuous as an operation on continuous linear maps. -/
theorem continuousAt_comp_inr
    {Z : Type*} [TopologicalSpace Z]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : Z → (V × E →L[ℝ] E)) (z : Z)
    (hF : ContinuousAt F z) :
    ContinuousAt
      (fun w => (F w).comp (ContinuousLinearMap.inr ℝ V E)) z := by
  have hpre : ContinuousAt
      (fun w => (ContinuousLinearMap.compL ℝ E (V × E) E) (F w)) z :=
    ((ContinuousLinearMap.compL ℝ E (V × E) E).continuous.continuousAt).comp
      (f := F) (x := z) hF
  exact hpre.clm_apply continuousAt_const

/-- Fixed-chart derivative continuity persists on every continuously
parametrized subgroup and base locus. In particular one may take `K` to be
a compact subgroup of full isometries and `N` a fixed-locus component. -/
theorem continuousAt_actionDerivative_along_families
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
    (s : N → M) (hs : Continuous s) (k₀ : K) (n₀ : N) :
    letI : MetricSpace M := riemannianMetricSpace Q
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : ChartedSpace V (M ≃ᵢ M) := hChart
    ContinuousAt
      (fun p : K × N =>
        inTangentCoordinates (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) id
          (fun q : (M ≃ᵢ M) × M => q.1 q.2)
          (mfderiv (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E)
            (fun q : (M ≃ᵢ M) × M => q.1 q.2))
          (j k₀, s n₀) (j p.1, s p.2)) (k₀, n₀) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  have hbase : Continuous (fun p : K × N => (j p.1, s p.2)) :=
    (hj.comp continuous_fst).prodMk (hs.comp continuous_snd)
  have hbaseAt : ContinuousAt (fun p : K × N => (j p.1, s p.2))
      (k₀, n₀) := hbase.continuousAt
  let F := inTangentCoordinates (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) id
    (fun q : (M ≃ᵢ M) × M => q.1 q.2)
    (mfderiv (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E)
      (fun q : (M ≃ᵢ M) × M => q.1 q.2)) (j k₀, s n₀)
  have hAt : ContinuousAt F (j k₀, s n₀) :=
    continuousAt_actionDerivative_inTangentCoordinates Q hChart
      hManifold hAction (j k₀, s n₀)
  have hcomp : ContinuousAt (F ∘ fun p : K × N => (j p.1, s p.2))
      (k₀, n₀) := ContinuousAt.comp
        (f := fun p : K × N => (j p.1, s p.2))
        (x := (k₀, n₀)) hAt hbaseAt
  simpa only [Function.comp_def] using hcomp

/-- For compact-subgroup and fixed-component families, the spatial
partial derivative `v ↦ D(action)(0,v)` is continuous in fixed charts.
The right injection is the literal `(0,v)` tangent direction. -/
theorem continuousAt_actionPartialX_along_families
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
    (s : N → M) (hs : Continuous s) (k₀ : K) (n₀ : N) :
    letI : MetricSpace M := riemannianMetricSpace Q
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : ChartedSpace V (M ≃ᵢ M) := hChart
    ContinuousAt
      (fun p : K × N =>
        (inTangentCoordinates (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) id
          (fun q : (M ≃ᵢ M) × M => q.1 q.2)
          (mfderiv (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E)
            (fun q : (M ≃ᵢ M) × M => q.1 q.2))
          (j k₀, s n₀) (j p.1, s p.2)).comp
          (ContinuousLinearMap.inr ℝ V E)) (k₀, n₀) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  let F : K × N → (V × E →L[ℝ] E) := fun p =>
    inTangentCoordinates (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) id
      (fun q : (M ≃ᵢ M) × M => q.1 q.2)
      (mfderiv (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E)
        (fun q : (M ≃ᵢ M) × M => q.1 q.2))
      (j k₀, s n₀) (j p.1, s p.2)
  have hF : ContinuousAt F (k₀, n₀) :=
    continuousAt_actionDerivative_along_families Q hChart hManifold
      hAction j hj s hs k₀ n₀
  exact continuousAt_comp_inr (E := E) F (k₀, n₀) hF

/-- The numerical Lie-algebra dimension consequence is obtained from the
orbit-derivative-characterized BG-R4 equivalence, not assumed separately. -/
theorem tangent_finrank_eq_killingDimension
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hChart :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      ChartedSpace V (M ≃ᵢ M))
    (hK : KillingLieConclusion Q hChart) :
    letI : MetricSpace M := riemannianMetricSpace Q
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : ChartedSpace V (M ≃ᵢ M) := hChart
    Module.finrank ℝ (TangentSpace 𝓘(ℝ,V) (1 : M ≃ᵢ M)) =
      killingDimension Q := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  obtain ⟨L, _⟩ := hK
  exact L.finrank_eq

/-- BG-R4, conditional only on the BG-R3 Lie structure and smooth actual
action. Compactness of `M` supplies completeness. -/
def KillingLieSourceOn : Prop :=
  ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (hChart :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      ChartedSpace V (M ≃ᵢ M)),
    letI : MetricSpace M := riemannianMetricSpace Q
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    letI : ChartedSpace V (M ≃ᵢ M) := hChart
    IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M) →
    LieGroup 𝓘(ℝ,V) ∞ (M ≃ᵢ M) →
    ContMDiff (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
      (fun p : (M ≃ᵢ M) × M => p.1 p.2) →
    KillingLieConclusion Q hChart

/-- Universal BG-R3 source boundary: Lie group and smooth evaluation on
the actual compact-open isometry group, for standard compact connected
finite-dimensional Riemannian manifolds. -/
def IsometryLieSource : Prop :=
  ∀ {E : Type uIso} {M : Type vIso}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    [CompactSpace M] [T3Space M] [SecondCountableTopology M]
    [PreconnectedSpace M] [Nonempty M],
    ∀ Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞),
      IsometryLieConclusion Q

/-- Universal BG-R4 source boundary; the orbit derivative determines the
Lie-algebra/Killing-field comparison. -/
def KillingLieSource : Prop :=
  ∀ {E : Type uIso} {M : Type vIso}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    [CompactSpace M] [T3Space M] [SecondCountableTopology M]
    [PreconnectedSpace M] [Nonempty M],
    ∀ Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞),
      KillingLieSourceOn Q

/-- The actual full metric-isometry group equipped with the sourced smooth
Lie structure and the orbit-derivative Killing-field identification. -/
def IsometryLieKillingConclusion : Prop :=
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  ∃ (V : Type) (hNorm : NormedAddCommGroup V),
    letI : NormedAddCommGroup V := hNorm
    ∃ (hSpace : NormedSpace ℝ V),
      letI : NormedSpace ℝ V := hSpace
      ∃ (hFinite : FiniteDimensional ℝ V)
        (hChart : ChartedSpace V (M ≃ᵢ M)),
        letI : FiniteDimensional ℝ V := hFinite
        letI : ChartedSpace V (M ≃ᵢ M) := hChart
        IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M) ∧
        LieGroup 𝓘(ℝ,V) ∞ (M ≃ᵢ M) ∧
        ContMDiff (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
          (fun p : (M ≃ᵢ M) × M => p.1 p.2) ∧
        KillingLieConclusion Q hChart

theorem isometryLieKilling_of_sources
    (hR3 : IsometryLieSource.{uIso,vIso})
    (hR4 : KillingLieSource.{uIso,vIso}) :
    IsometryLieKillingConclusion Q := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  obtain ⟨V, hNorm, hSpace, hFinite, hChart,
    hManifold, hLie, hAction⟩ := hR3 Q
  letI : NormedAddCommGroup V := hNorm
  letI : NormedSpace ℝ V := hSpace
  letI : FiniteDimensional ℝ V := hFinite
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  refine ⟨V, hNorm, hSpace, hFinite, hChart,
    hManifold, hLie, hAction, ?_⟩
  exact hR4 Q hChart hManifold hLie hAction

end
end QuaternionicSymmetry.ManifoldRiemannianIsometryLieInput
