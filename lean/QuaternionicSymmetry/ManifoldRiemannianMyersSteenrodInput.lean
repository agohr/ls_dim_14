import QuaternionicSymmetry.ManifoldQuaternionicMetricIsometryCompact

/-! Petersen's Myers–Steenrod theorem (BG-R3) is represented only by its
general geometric conclusion: a bijective distance isometry of the actual
Riemannian path metric is a smooth metric isometry. The source input does
not mention quaternionic preservation, Lie groups, or Killing fields. -/
namespace QuaternionicSymmetry.ManifoldRiemannianMyersSteenrodInput
open ManifoldQuaternionicRiemannianDistance
open ManifoldQuaternionicMetricIsometryDistance
open ManifoldQuaternionicFundamentalSymmetry
open scoped Manifold ContDiff
noncomputable section
universe uMS vMS

variable {E : Type uMS} {M : Type vMS} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- BG-R3 on this actual Riemannian manifold. The output is the smooth
metric isometry whose underlying map is the given distance isometry. -/
def MyersSteenrodConclusion : Prop :=
  letI : MetricSpace M := riemannianMetricSpace Q
  ∀ e : M ≃ᵢ M,
    ∃ f : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞,
      PreservesMetric Q f ∧ (f : M → M) = e

/-- The general BG-R3 source contract, with the standard finite-dimensional,
connected, Hausdorff and second-countable manifold hypotheses visible in
the source itself. Its only conclusion is smoothness/metric preservation of
distance isometries. -/
def MyersSteenrodSource : Prop :=
  ∀ {E : Type uMS} {M : Type vMS} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    [CompactSpace M] [T3Space M] [SecondCountableTopology M]
    [PreconnectedSpace M] [Nonempty M],
    ∀ Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞),
      MyersSteenrodConclusion Q

/-- The full smooth metric isometry type (without a quaternionic reduction
condition). -/
def SmoothMetricIsometries :=
  {f : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞ // PreservesMetric Q f}

def smoothToMetricIsometry (f : SmoothMetricIsometries Q) :
    letI : MetricSpace M := riemannianMetricSpace Q
    M ≃ᵢ M :=
  metricIsometryEquiv Q f.1 f.2

theorem smoothToMetricIsometry_injective :
    letI : MetricSpace M := riemannianMetricSpace Q
    Function.Injective (smoothToMetricIsometry Q) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  intro f g h
  apply Subtype.ext
  apply DFunLike.ext
  intro x
  exact congrFun (congrArg (fun e : M ≃ᵢ M => (e : M → M)) h) x

theorem smoothToMetricIsometry_surjective
    (hMS : MyersSteenrodConclusion Q) :
    letI : MetricSpace M := riemannianMetricSpace Q
    Function.Surjective (smoothToMetricIsometry Q) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  intro e
  obtain ⟨f, hf, he⟩ := hMS e
  refine ⟨⟨f, hf⟩, ?_⟩
  apply IsometryEquiv.ext
  intro x
  exact congrFun he x

/-- Internal identification after applying the general Myers–Steenrod
smoothness theorem. Its topology is transported from the already proved
compact-open topology on the full metric-isometry group. -/
def smoothMetricIsometriesEquiv
    (hMS : MyersSteenrodConclusion Q) :
    letI : MetricSpace M := riemannianMetricSpace Q
    SmoothMetricIsometries Q ≃ (M ≃ᵢ M) :=
  Equiv.ofBijective (smoothToMetricIsometry Q)
    ⟨smoothToMetricIsometry_injective Q,
      smoothToMetricIsometry_surjective Q hMS⟩

theorem myersSteenrod_on_actual_metric
    (hBG : MyersSteenrodSource.{uMS,vMS}) : MyersSteenrodConclusion Q :=
  hBG Q

/-- The universal BG-R3 input removes any per-manifold smoothness
assumption from the concrete smooth/metric isometry comparison. -/
def smoothMetricIsometriesEquiv_of_source
    (hBG : MyersSteenrodSource.{uMS,vMS}) :
    letI : MetricSpace M := riemannianMetricSpace Q
    SmoothMetricIsometries Q ≃ (M ≃ᵢ M) :=
  smoothMetricIsometriesEquiv Q (myersSteenrod_on_actual_metric Q hBG)

end
end QuaternionicSymmetry.ManifoldRiemannianMyersSteenrodInput
