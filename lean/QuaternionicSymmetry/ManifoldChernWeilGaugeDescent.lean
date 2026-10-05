import QuaternionicSymmetry.ManifoldChernWeilGluing
import QuaternionicSymmetry.LocalConnectionCoordinatePullback

/-!
Construct a global Chern--Weil trace-power atlas from local connections
that obey an affine gauge law across genuine manifold chart transitions.
The scalar trace coordinate law is proved, rather than included as a field.
-/

namespace QuaternionicSymmetry.ManifoldChernWeilGaugeDescent

open Filter QuaternionicSymmetry.ManifoldDifferentialForms
  QuaternionicSymmetry.ManifoldChernWeilGluing
  QuaternionicSymmetry.LocalChernWeilTracePowers
  QuaternionicSymmetry.LocalConnectionCoordinatePullback
  QuaternionicSymmetry.LocalConnection
open scoped Manifold Topology ContDiff

variable {E M V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

noncomputable section

local instance : NormedAddCommGroup (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

/-- Local matrix connections related by a genuine affine gauge transform
after the chart transition derivative has pulled back the second connection.
Inverse-pair gauge lifts may depend on the ordered pair of charts. -/
structure GaugeCoordinateAtlas (k : ℕ) where
  connection : M → QuaternionicSymmetry.LocalConnection.Form
    (E := E) (A := V →L[ℝ] V)
  connectionC2 : ∀ (p : M) (y : E),
    y ∈ (extChartAt 𝓘(ℝ, E) p).target →
      ContDiffAt ℝ 2 (connection p) y
  traceRegular : ∀ p : M,
    ContDiffOn ℝ ∞
      (traceCurvaturePowerForm (connection p) k)
      (extChartAt 𝓘(ℝ, E) p).target
  gauge : M → M → E → (V →L[ℝ] V)
  inverseGauge : M → M → E → (V →L[ℝ] V)
  connectionGaugeLaw : ∀ (p q : M) (y : E),
    y ∈ (extChartAt 𝓘(ℝ, E) p).target →
    (extChartAt 𝓘(ℝ, E) p).symm y ∈
      (extChartAt 𝓘(ℝ, E) q).source →
    connection p =ᶠ[𝓝 y]
      QuaternionicSymmetry.LocalConnectionGauge.transform
        (pullback (connection q)
          ((extChartAt 𝓘(ℝ, E) q) ∘
            (extChartAt 𝓘(ℝ, E) p).symm))
        (gauge p q) (inverseGauge p q)
  gaugeC2 : ∀ (p q : M) (y : E),
    y ∈ (extChartAt 𝓘(ℝ, E) p).target →
    (extChartAt 𝓘(ℝ, E) p).symm y ∈
      (extChartAt 𝓘(ℝ, E) q).source →
      ContDiffAt ℝ 2 (gauge p q) y
  inverseGaugeDifferentiable : ∀ (p q : M) (y : E),
    y ∈ (extChartAt 𝓘(ℝ, E) p).target →
    (extChartAt 𝓘(ℝ, E) p).symm y ∈
      (extChartAt 𝓘(ℝ, E) q).source →
      DifferentiableAt ℝ (inverseGauge p q) y
  inverseLeft : ∀ (p q : M) (y : E),
    y ∈ (extChartAt 𝓘(ℝ, E) p).target →
    (extChartAt 𝓘(ℝ, E) p).symm y ∈
      (extChartAt 𝓘(ℝ, E) q).source →
    (fun z => inverseGauge p q z * gauge p q z) =ᶠ[𝓝 y]
      fun _ => 1
  inverseRight : ∀ (p q : M) (y : E),
    y ∈ (extChartAt 𝓘(ℝ, E) p).target →
    (extChartAt 𝓘(ℝ, E) p).symm y ∈
      (extChartAt 𝓘(ℝ, E) q).source →
      gauge p q y * inverseGauge p q y = 1

namespace GaugeCoordinateAtlas

variable {k : ℕ} (A : GaugeCoordinateAtlas (E := E) (M := M) (V := V) k)

theorem traceCoordinateLaw (p q : M) (y : E)
    (hp : y ∈ (extChartAt 𝓘(ℝ, E) p).target)
    (hq : (extChartAt 𝓘(ℝ, E) p).symm y ∈
      (extChartAt 𝓘(ℝ, E) q).source) :
    traceCurvaturePowerForm (A.connection p) k y =
      ContinuousAlternatingMap.compContinuousLinearMap
        (traceCurvaturePowerForm (A.connection q) k
          ((extChartAt 𝓘(ℝ, E) q)
            ((extChartAt 𝓘(ℝ, E) p).symm y)))
        (fderiv ℝ
          ((extChartAt 𝓘(ℝ, E) q) ∘
            (extChartAt 𝓘(ℝ, E) p).symm) y) := by
  let Cp := extChartAt 𝓘(ℝ, E) p
  let Cq := extChartAt 𝓘(ℝ, E) q
  let φ : E → E := Cq ∘ Cp.symm
  have hmem : y ∈ (Cp.symm ≫ Cq).source := by
    change y ∈ Cp.target ∩ Cp.symm ⁻¹' Cq.source
    exact ⟨hp, hq⟩
  have hφ : ContDiffAt ℝ 2 φ y := by
    simpa [φ, Cp, Cq] using
      (contDiffWithinAt_ext_coord_change (I := 𝓘(ℝ, E)) q p hmem)
  have hqtarget : φ y ∈ Cq.target := Cq.map_source hq
  have hΓq : DifferentiableAt ℝ (A.connection q) (φ y) :=
    (A.connectionC2 q (φ y) hqtarget).differentiableAt (by norm_num)
  exact tracePowerForm_gauge_coordinate
    QuaternionicSymmetry.LocalEndomorphismTrace.traceCLM
    QuaternionicSymmetry.LocalEndomorphismTrace.traceCLM_cyclic
    (A.connection p) (A.connection q) φ (A.gauge p q)
    (A.inverseGauge p q) y
    (A.connectionGaugeLaw p q y hp hq) hΓq hφ
    (A.gaugeC2 p q y hp hq)
    (A.inverseGaugeDifferentiable p q y hp hq)
    (A.inverseLeft p q y hp hq)
    (A.inverseRight p q y hp hq) k

/-- The supplied affine connection law derives every scalar trace transition
law, so the existing gluing theorem produces a closed global form. -/
def toTracePowerAtlas : TracePowerAtlas (E := E) (M := M) (V := V) k where
  connection := A.connection
  connectionC2 := A.connectionC2
  traceRegular := A.traceRegular
  traceCoordinateLaw := A.traceCoordinateLaw

end GaugeCoordinateAtlas
end
end QuaternionicSymmetry.ManifoldChernWeilGaugeDescent
