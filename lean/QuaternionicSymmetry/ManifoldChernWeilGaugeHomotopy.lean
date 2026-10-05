import QuaternionicSymmetry.ManifoldChernWeilGaugeDescent
import QuaternionicSymmetry.ManifoldChernWeilTransgression
import QuaternionicSymmetry.LocalOrderedPrimitiveGaugeCoordinate

/-!
Global Chern--Weil homotopy from a single affine gauge atlas and a
homogeneously transforming connection variation. Both the endpoint trace
and ordered Chern--Simons primitive chart laws are derived from these laws.
-/

namespace QuaternionicSymmetry.ManifoldChernWeilGaugeHomotopy

open Filter QuaternionicSymmetry.ManifoldDifferentialForms
  QuaternionicSymmetry.ManifoldChernWeilGaugeDescent
  QuaternionicSymmetry.ManifoldChernWeilGluing
  QuaternionicSymmetry.ManifoldChernWeilTransgression
  QuaternionicSymmetry.LocalChernWeilTracePowers
  QuaternionicSymmetry.LocalChernWeilOrderedTransgression
  QuaternionicSymmetry.LocalChernWeilOrderedExact
  QuaternionicSymmetry.LocalConnectionCoordinatePullback
  QuaternionicSymmetry.LocalOrderedPrimitiveGaugeCoordinate
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

/-- A path direction transforming by the homogeneous adjoint law for an
existing affine gauge atlas. Smoothness of its trace powers and primitive
is still an explicit analytic input, independent of the chart law. -/
structure GaugeCoordinateHomotopy (k : ℕ) where
  start : GaugeCoordinateAtlas (E := E) (M := M) (V := V) k
  direction : M → QuaternionicSymmetry.LocalConnection.Form
    (E := E) (A := V →L[ℝ] V)
  directionC2 : ∀ (p : M) (y : E),
    y ∈ (extChartAt 𝓘(ℝ, E) p).target →
      ContDiffAt ℝ 2 (direction p) y
  directionGaugeLaw : ∀ (p q : M) (y : E),
    y ∈ (extChartAt 𝓘(ℝ, E) p).target →
    (extChartAt 𝓘(ℝ, E) p).symm y ∈
      (extChartAt 𝓘(ℝ, E) q).source →
    direction p =ᶠ[𝓝 y]
      QuaternionicSymmetry.LocalConnectionGauge.adjointForm
        (pullback (direction q)
          ((extChartAt 𝓘(ℝ, E) q) ∘
            (extChartAt 𝓘(ℝ, E) p).symm))
        (start.gauge p q) (start.inverseGauge p q)
  endpointTraceRegular : ∀ p : M,
    ContDiffOn ℝ ∞
      (traceCurvaturePowerForm
        (start.connection p + direction p) k)
      (extChartAt 𝓘(ℝ, E) p).target
  primitiveRegular : ∀ p : M,
    ContDiffOn ℝ ∞
      (traceOrderedTransgressionForm
        QuaternionicSymmetry.LocalEndomorphismTrace.traceCLM
        (start.connection p) (direction p) k)
      (extChartAt 𝓘(ℝ, E) p).target

namespace GaugeCoordinateHomotopy

variable {k : ℕ} (H : GaugeCoordinateHomotopy (E := E) (M := M) (V := V) k)

/-- The endpoint connection inherits the same affine gauge law. -/
def finish : GaugeCoordinateAtlas (E := E) (M := M) (V := V) k where
  connection p := H.start.connection p + H.direction p
  connectionC2 p y hy :=
    (H.start.connectionC2 p y hy).add (H.directionC2 p y hy)
  traceRegular := H.endpointTraceRegular
  gauge := H.start.gauge
  inverseGauge := H.start.inverseGauge
  connectionGaugeLaw p q y hp hq := by
    have hΓ := H.start.connectionGaugeLaw p q y hp hq
    have hθ := H.directionGaugeLaw p q y hp hq
    filter_upwards [hΓ, hθ] with z hΓz hθz
    simp only [Pi.add_apply, hΓz, hθz]
    have hpath : pullback
        (H.start.connection q + H.direction q)
        ((extChartAt 𝓘(ℝ, E) q) ∘
          (extChartAt 𝓘(ℝ, E) p).symm) =
      pullback (H.start.connection q)
        ((extChartAt 𝓘(ℝ, E) q) ∘
          (extChartAt 𝓘(ℝ, E) p).symm) +
      pullback (H.direction q)
        ((extChartAt 𝓘(ℝ, E) q) ∘
          (extChartAt 𝓘(ℝ, E) p).symm) := by
      simpa using pullback_path (H.start.connection q) (H.direction q)
        ((extChartAt 𝓘(ℝ, E) q) ∘
          (extChartAt 𝓘(ℝ, E) p).symm) 1
    rw [hpath]
    have ht := congrFun
      (QuaternionicSymmetry.LocalConnectionGauge.transform_path
        (pullback (H.start.connection q)
          ((extChartAt 𝓘(ℝ, E) q) ∘
            (extChartAt 𝓘(ℝ, E) p).symm))
        (pullback (H.direction q)
          ((extChartAt 𝓘(ℝ, E) q) ∘
            (extChartAt 𝓘(ℝ, E) p).symm))
        (H.start.gauge p q) (H.start.inverseGauge p q) 1) z
    simpa using ht.symm
  gaugeC2 := H.start.gaugeC2
  inverseGaugeDifferentiable := H.start.inverseGaugeDifferentiable
  inverseLeft := H.start.inverseLeft
  inverseRight := H.start.inverseRight

theorem primitiveCoordinateLaw (p q : M) (y : E)
    (hp : y ∈ (extChartAt 𝓘(ℝ, E) p).target)
    (hq : (extChartAt 𝓘(ℝ, E) p).symm y ∈
      (extChartAt 𝓘(ℝ, E) q).source) :
    traceOrderedTransgressionForm
        QuaternionicSymmetry.LocalEndomorphismTrace.traceCLM
        (H.start.connection p) (H.direction p) k y =
      ContinuousAlternatingMap.compContinuousLinearMap
        (traceOrderedTransgressionForm
          QuaternionicSymmetry.LocalEndomorphismTrace.traceCLM
          (H.start.connection q) (H.direction q) k
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
  have hΓq : DifferentiableAt ℝ (H.start.connection q) (φ y) :=
    (H.start.connectionC2 q (φ y) hqtarget).differentiableAt (by norm_num)
  have hθq : DifferentiableAt ℝ (H.direction q) (φ y) :=
    (H.directionC2 q (φ y) hqtarget).differentiableAt (by norm_num)
  exact traceOrderedTransgressionForm_gauge_coordinate
    QuaternionicSymmetry.LocalEndomorphismTrace.traceCLM
    QuaternionicSymmetry.LocalEndomorphismTrace.traceCLM_cyclic
    (H.start.connection p) (H.start.connection q)
    (H.direction p) (H.direction q) φ
    (H.start.gauge p q) (H.start.inverseGauge p q) y
    (H.start.connectionGaugeLaw p q y hp hq)
    (H.directionGaugeLaw p q y hp hq)
    hΓq hθq hφ
    (H.start.gaugeC2 p q y hp hq)
    (H.start.inverseGaugeDifferentiable p q y hp hq)
    (H.start.inverseLeft p q y hp hq)
    (H.start.inverseRight p q y hp hq) k

def toTracePowerHomotopy :
    TracePowerHomotopy (E := E) (M := M) (V := V) k where
  start := H.start.toTracePowerAtlas
  finish := H.finish.toTracePowerAtlas
  direction := H.direction
  endpoint _ := rfl
  directionC2 := H.directionC2
  primitiveRegular := H.primitiveRegular
  primitiveCoordinateLaw := H.primitiveCoordinateLaw

theorem cohomologyClass_eq :
    QuotientAddGroup.mk
      ((primitiveDegree_add_one k).symm ▸
        H.toTracePowerHomotopy.finish.closedGlobalForm) =
    (QuotientAddGroup.mk
      ((primitiveDegree_add_one k).symm ▸
        H.toTracePowerHomotopy.start.closedGlobalForm) :
          positiveDegreeCohomology (E := E) (M₀ := M) (primitiveDegree k)) :=
  H.toTracePowerHomotopy.cohomologyClass_eq

end GaugeCoordinateHomotopy
end
end QuaternionicSymmetry.ManifoldChernWeilGaugeHomotopy
