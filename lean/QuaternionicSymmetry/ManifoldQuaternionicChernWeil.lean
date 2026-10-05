import QuaternionicSymmetry.ManifoldQuaternionicConnection
import QuaternionicSymmetry.ManifoldChernWeilGaugeDescent
import QuaternionicSymmetry.LocalChernWeilSmoothness

/-!
Chern--Weil trace powers of an actual compatible tangent connection on a
smooth quaternionic-Hermitian manifold. The tangent-frame affine connection
law and smoothness come from `ManifoldQuaternionicConnection`; the scalar
trace transition and closure are derived by gauge-coordinate descent.
-/

namespace QuaternionicSymmetry.ManifoldQuaternionicChernWeil

open QuaternionicSymmetry.ManifoldDifferentialForms
  QuaternionicSymmetry.ManifoldChernWeilGaugeDescent
  QuaternionicSymmetry.ManifoldChernWeilGluing
  QuaternionicSymmetry.ManifoldQuaternionicConnection
  QuaternionicSymmetry.LocalChernWeilSmoothness
open scoped Manifold Topology ContDiff

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

noncomputable section

variable (Q : QuaternionicSymmetry.ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

/-- Every positive trace power of the compatible tangent connection
possesses a genuine affine gauge atlas with derived trace transitions. -/
def gaugeAtlas (k : ℕ) :
    GaugeCoordinateAtlas (E := E) (M := M) (V := E) k where
  connection := D.form
  connectionC2 p y hy := by
    exact ((D.smooth_form p).contDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).mem_nhds hy)).of_le (by exact ENat.LEInfty.out)
  traceRegular p :=
    tracePowerForm_contDiffOn
      QuaternionicSymmetry.LocalEndomorphismTrace.traceCLM (D.form p)
      (isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p) (D.smooth_form p) k
  gauge := adaptedGauge Q
  inverseGauge := adaptedGaugeInv Q
  connectionGaugeLaw p q y hp hq := by
    have hy : y ∈ chartOverlap (I := 𝓘(ℝ, E)) p q := ⟨hp, hq⟩
    filter_upwards [(chartOverlap_isOpen (I := 𝓘(ℝ, E)) p q).mem_nhds hy]
      with z hz
    exact D.overlap p q z hz
  gaugeC2 p q y hp hq :=
    adaptedGauge_contDiffAt Q p q y ⟨hp, hq⟩ (by exact ENat.LEInfty.out)
  inverseGaugeDifferentiable p q y hp hq :=
    (adaptedGaugeInv_contDiffAt Q p q y ⟨hp, hq⟩ (by exact ENat.LEInfty.out)).differentiableAt
      (by norm_num)
  inverseLeft p q y hp hq :=
    adaptedGauge_inverse_eventually Q p q y ⟨hp, hq⟩
  inverseRight p q y hp hq :=
    (adaptedGauge_inverse Q p q y ⟨hp, hq⟩).2

/-- The closed global tangent form represented by `tr(F^(k+1))`. -/
def globalTracePower (k : ℕ) : Form 𝓘(ℝ, E) M (QuaternionicSymmetry.LocalChernWeilTracePowers.powerDegree k) :=
  ((gaugeAtlas (Q := Q) (D := D) k).toTracePowerAtlas).globalForm

theorem globalTracePower_smooth (k : ℕ) :
    ChartSmooth (globalTracePower (Q := Q) (D := D) k) :=
  ((gaugeAtlas (Q := Q) (D := D) k).toTracePowerAtlas).globalForm_smooth

theorem globalTracePower_closed (k : ℕ) :
    exteriorDerivative (globalTracePower (Q := Q) (D := D) k) = 0 :=
  ((gaugeAtlas (Q := Q) (D := D) k).toTracePowerAtlas).globalForm_closed

end
end QuaternionicSymmetry.ManifoldQuaternionicChernWeil
