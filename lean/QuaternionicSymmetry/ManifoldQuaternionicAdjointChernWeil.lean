import QuaternionicSymmetry.ManifoldQuaternionicAdjointOverlap
import QuaternionicSymmetry.ManifoldQuaternionicInducedSkew
import QuaternionicSymmetry.ManifoldChernWeilGaugeDescent
import QuaternionicSymmetry.LocalChernWeilSmoothness

/-! Global Chern--Weil trace powers of the genuine quaternionic rank-three
bundle and its tangent-induced connection. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicAdjointChernWeil

open Filter QuaternionicSymmetry.ManifoldQuaternionicConnection
  QuaternionicSymmetry.ManifoldQuaternionicAdjointConnection
  QuaternionicSymmetry.ManifoldQuaternionicAdjointOverlap
  QuaternionicSymmetry.ManifoldDifferentialForms
  QuaternionicSymmetry.ManifoldChernWeilGaugeDescent
  QuaternionicSymmetry.ManifoldChernWeilGluing
  QuaternionicSymmetry.LocalChernWeilSmoothness
open scoped Manifold Topology ContDiff

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

noncomputable section

variable (Q : QuaternionicSymmetry.ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

/-- The rank-three connection produces an affine gauge atlas whose chart
law is a theorem of the tangent geometry. -/
def gaugeAtlas (k : ℕ) :
    GaugeCoordinateAtlas (E := E) (M := M) (V := R3) k where
  connection := inducedForm Q D
  connectionC2 p y hy := by
    exact ((inducedForm_smooth Q D p).contDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).mem_nhds hy)).of_le (by exact ENat.LEInfty.out)
  traceRegular p :=
    tracePowerForm_contDiffOn
      QuaternionicSymmetry.LocalEndomorphismTrace.traceCLM
      (inducedForm Q D p)
      (isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p)
      (inducedForm_smooth Q D p) k
  gauge := rankThreeGauge Q
  inverseGauge := rankThreeGaugeInv Q
  connectionGaugeLaw p q y hp hq := by
    have hy : y ∈ chartOverlap (I := 𝓘(ℝ, E)) p q := ⟨hp, hq⟩
    filter_upwards [(chartOverlap_isOpen (I := 𝓘(ℝ, E)) p q).mem_nhds hy]
      with z hz
    exact inducedForm_affine_overlap Q D p q z hz (by exact ENat.LEInfty.out)
  gaugeC2 p q y hp hq :=
    rankThreeGauge_contDiffAt Q p q y ⟨hp, hq⟩ (by exact ENat.LEInfty.out)
  inverseGaugeDifferentiable p q y hp hq :=
    (rankThreeGaugeInv_contDiffAt Q p q y ⟨hp, hq⟩ (by exact ENat.LEInfty.out)).differentiableAt
      (by norm_num)
  inverseLeft p q y hp hq :=
    rankThreeGauge_inverse_eventually Q p q y ⟨hp, hq⟩
  inverseRight p q y hp hq :=
    (rankThreeGauge_inverse Q p q y ⟨hp, hq⟩).2

theorem rankThreeConnection_metric (p : M) (y u : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) (a b : R3) :
    (∑ t : Fin 3, (inducedForm Q D p y u a) t * b t) +
      (∑ t : Fin 3, a t * (inducedForm Q D p y u b) t) = 0 :=
  QuaternionicSymmetry.ManifoldQuaternionicInducedSkew.inducedForm_dot_skew
    Q D p y u hy a b

/-- The closed global form whose local expression is the trace of the
square of rank-three curvature. -/
def traceCurvatureSquare : Form 𝓘(ℝ, E) M 4 :=
  ((gaugeAtlas Q D 1).toTracePowerAtlas).globalForm

theorem traceCurvatureSquare_chart (p : M) {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    inChartModel p (traceCurvatureSquare Q D) y =
      QuaternionicSymmetry.LocalChernWeilTracePowers.traceCurvaturePowerForm
        (inducedForm Q D p) 1 y :=
  ((gaugeAtlas Q D 1).toTracePowerAtlas).globalForm_chart p hy

theorem traceCurvatureSquare_smooth :
    ChartSmooth (traceCurvatureSquare Q D) :=
  ((gaugeAtlas Q D 1).toTracePowerAtlas).globalForm_smooth

theorem traceCurvatureSquare_closed :
    exteriorDerivative (traceCurvatureSquare Q D) = 0 :=
  ((gaugeAtlas Q D 1).toTracePowerAtlas).globalForm_closed

def closedTraceCurvatureSquare : closedForms (E := E) (M₀ := M) 4 :=
  ((gaugeAtlas Q D 1).toTracePowerAtlas).closedGlobalForm

def traceCurvatureSquareClass : positiveDegreeCohomology
    (E := E) (M₀ := M) 3 :=
  QuotientAddGroup.mk (closedTraceCurvatureSquare Q D)

/-- Chern--Weil candidate for one quarter of the first Pontryagin class of
the oriented rank-three bundle. This is an analytic normalization of the
curvature form; no comparison with a topological Pontryagin class is claimed. -/
def quarterPontryaginCandidateForm : closedForms (E := E) (M₀ := M) 4 :=
  (-(1 / (32 * Real.pi ^ 2)) : ℝ) • closedTraceCurvatureSquare Q D

def quarterPontryaginCandidateClass : positiveDegreeCohomology
    (E := E) (M₀ := M) 3 :=
  QuotientAddGroup.mk (quarterPontryaginCandidateForm Q D)

end
end QuaternionicSymmetry.ManifoldQuaternionicAdjointChernWeil
