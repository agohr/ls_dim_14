import QuaternionicSymmetry.ManifoldQuaternionicAdjointChernWeil
import QuaternionicSymmetry.ManifoldChernWeilGaugeHomotopy
import QuaternionicSymmetry.LocalOrderedPrimitiveSmoothness

/-! Independence of the induced rank-three trace-curvature class from the
choice of compatible tangent connection. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicAdjointChernWeilIndependence

open Filter QuaternionicSymmetry.ManifoldQuaternionicConnection
  QuaternionicSymmetry.ManifoldQuaternionicAdjointConnection
  QuaternionicSymmetry.ManifoldQuaternionicAdjointOverlap
  QuaternionicSymmetry.ManifoldQuaternionicAdjointChernWeil
  QuaternionicSymmetry.ManifoldDifferentialForms
  QuaternionicSymmetry.ManifoldChernWeilGaugeHomotopy
  QuaternionicSymmetry.LocalConnectionCoordinatePullback
  QuaternionicSymmetry.LocalChernWeilSmoothness
  QuaternionicSymmetry.LocalOrderedPrimitiveSmoothness
open scoped Manifold Topology ContDiff

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

noncomputable section

variable (Q : QuaternionicSymmetry.ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
variable (D₀ D₁ : CompatibleTangentConnection Q)

omit [Nontrivial E] [FiniteDimensional ℝ E] in
private theorem pullback_sub (Γ₁ Γ₀ : QuaternionicSymmetry.LocalConnection.Form
    (E := E) (A := R3 →L[ℝ] R3)) (φ : E → E) :
    pullback (Γ₁ - Γ₀) φ = pullback Γ₁ φ - pullback Γ₀ φ := by
  funext x
  ext v
  rfl

omit [Nontrivial E] [FiniteDimensional ℝ E] in
private theorem transform_sub (Γ₁ Γ₀ : QuaternionicSymmetry.LocalConnection.Form
    (E := E) (A := R3 →L[ℝ] R3))
    (g h : E → R3 →L[ℝ] R3) :
    QuaternionicSymmetry.LocalConnectionGauge.transform Γ₁ g h -
      QuaternionicSymmetry.LocalConnectionGauge.transform Γ₀ g h =
    QuaternionicSymmetry.LocalConnectionGauge.adjointForm (Γ₁ - Γ₀) g h := by
  funext x
  apply ContinuousLinearMap.ext
  intro v
  simp only [Pi.sub_apply, ContinuousLinearMap.sub_apply,
    QuaternionicSymmetry.LocalConnectionGauge.transform_apply,
    QuaternionicSymmetry.LocalConnectionGauge.adjointForm_apply]
  simp [mul_add, mul_sub, sub_mul]

theorem directionGaugeLaw (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ, E)) p q) :
    (fun r => inducedForm Q D₁ r - inducedForm Q D₀ r) p =ᶠ[𝓝 y]
      QuaternionicSymmetry.LocalConnectionGauge.adjointForm
        (pullback (inducedForm Q D₁ q - inducedForm Q D₀ q)
          (chartTransition (I := 𝓘(ℝ, E)) p q))
        (rankThreeGauge Q p q) (rankThreeGaugeInv Q p q) := by
  filter_upwards [(chartOverlap_isOpen (I := 𝓘(ℝ, E)) p q).mem_nhds hy]
    with z hz
  simp only [Pi.sub_apply]
  rw [inducedForm_affine_overlap Q D₁ p q z hz (by exact ENat.LEInfty.out),
    inducedForm_affine_overlap Q D₀ p q z hz (by exact ENat.LEInfty.out)]
  rw [pullback_sub]
  exact congrFun (transform_sub
    (pullback (inducedForm Q D₁ q) (chartTransition (I := 𝓘(ℝ, E)) p q))
    (pullback (inducedForm Q D₀ q) (chartTransition (I := 𝓘(ℝ, E)) p q))
    (rankThreeGauge Q p q) (rankThreeGaugeInv Q p q)) z

def gaugeHomotopy (k : ℕ) :
    GaugeCoordinateHomotopy (E := E) (M := M) (V := R3) k where
  start := gaugeAtlas Q D₀ k
  direction p := inducedForm Q D₁ p - inducedForm Q D₀ p
  directionC2 p y hy := by
    exact (((inducedForm_smooth Q D₁ p).sub (inducedForm_smooth Q D₀ p)).contDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).mem_nhds hy)).of_le (by exact ENat.LEInfty.out)
  directionGaugeLaw p q y hp hq :=
    directionGaugeLaw Q D₀ D₁ p q y ⟨hp, hq⟩
  endpointTraceRegular p := by
    exact tracePowerForm_contDiffOn
      QuaternionicSymmetry.LocalEndomorphismTrace.traceCLM
      (inducedForm Q D₀ p + (inducedForm Q D₁ p - inducedForm Q D₀ p))
      (isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p)
      ((inducedForm_smooth Q D₀ p).add
        ((inducedForm_smooth Q D₁ p).sub (inducedForm_smooth Q D₀ p))) k
  primitiveRegular p := by
    exact traceOrderedTransgressionForm_contDiffOn
      QuaternionicSymmetry.LocalEndomorphismTrace.traceCLM
      (inducedForm Q D₀ p) (inducedForm Q D₁ p - inducedForm Q D₀ p)
      (isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p)
      (inducedForm_smooth Q D₀ p)
      ((inducedForm_smooth Q D₁ p).sub (inducedForm_smooth Q D₀ p)) k

theorem finish_connection (k : ℕ) (p : M) :
    ((gaugeHomotopy Q D₀ D₁ k).finish).connection p = inducedForm Q D₁ p := by
  funext x
  change inducedForm Q D₀ p x +
    (inducedForm Q D₁ p x - inducedForm Q D₀ p x) = inducedForm Q D₁ p x
  abel

theorem traceCurvatureSquareClass_eq :
    traceCurvatureSquareClass Q D₁ = traceCurvatureSquareClass Q D₀ := by
  have hfinish :
      ((gaugeHomotopy Q D₀ D₁ 1).toTracePowerHomotopy.finish).closedGlobalForm =
        ((gaugeAtlas Q D₁ 1).toTracePowerAtlas).closedGlobalForm := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change
      (QuaternionicSymmetry.LocalChernWeilTracePowers.traceCurvaturePowerForm
        (((gaugeHomotopy Q D₀ D₁ 1).finish).connection x) 1
          (extChartAt 𝓘(ℝ, E) x x)).compContinuousLinearMap _ =
        (QuaternionicSymmetry.LocalChernWeilTracePowers.traceCurvaturePowerForm
          (inducedForm Q D₁ x) 1 (extChartAt 𝓘(ℝ, E) x x)).compContinuousLinearMap _
    rw [finish_connection]
  have h := (gaugeHomotopy Q D₀ D₁ 1).cohomologyClass_eq
  rw [hfinish] at h
  exact h

theorem quarterPontryaginCandidateClass_eq :
    quarterPontryaginCandidateClass Q D₁ =
      quarterPontryaginCandidateClass Q D₀ := by
  have hraw := traceCurvatureSquareClass_eq Q D₀ D₁
  rw [traceCurvatureSquareClass, traceCurvatureSquareClass,
    QuotientAddGroup.eq_iff_sub_mem] at hraw
  rw [quarterPontryaginCandidateClass, quarterPontryaginCandidateClass,
    QuotientAddGroup.eq_iff_sub_mem]
  change ((quarterPontryaginCandidateForm Q D₁ -
    quarterPontryaginCandidateForm Q D₀ :
      closedForms (E := E) (M₀ := M) 4) :
      smoothForms (I := 𝓘(ℝ, E)) (M := M) (n := 4)) ∈
      exactForms (E := E) (M₀ := M) 3
  change ((closedTraceCurvatureSquare Q D₁ -
    closedTraceCurvatureSquare Q D₀ :
      closedForms (E := E) (M₀ := M) 4) :
      smoothForms (I := 𝓘(ℝ, E)) (M := M) (n := 4)) ∈
      exactForms (E := E) (M₀ := M) 3 at hraw
  simpa only [quarterPontryaginCandidateForm, ← smul_sub,
    Submodule.coe_smul, Submodule.coe_sub] using
    (exactForms (E := E) (M₀ := M) 3).smul_mem
      (-(1 / (32 * Real.pi ^ 2)) : ℝ) hraw

end
end QuaternionicSymmetry.ManifoldQuaternionicAdjointChernWeilIndependence
