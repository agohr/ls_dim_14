import QuaternionicSymmetry.QuaternionicManifoldCorrectedGaugeGerm
import QuaternionicSymmetry.LocalConnectionGaugeDifference
import QuaternionicSymmetry.ManifoldChernWeilTransgression
import QuaternionicSymmetry.LocalOrderedPrimitiveGaugeCoordinate
import QuaternionicSymmetry.LocalOrderedPrimitiveSmoothness

/-! Actual global transgression between any two members of the standard
solder-corrected connection path. -/
namespace QuaternionicSymmetry.QuaternionicManifoldCorrectedTransgression
open QuaternionicManifoldCorrectedConnection QuaternionicManifoldCorrectedTracePowers
open QuaternionicManifoldCorrectedGaugeGerm QuaternionicProjectiveStandardL2
open ManifoldQuaternionicConnection ManifoldChernWeilTransgression
open LocalChernWeilTracePowers LocalChernWeilOrderedTransgression LocalChernWeilOrderedExact
open LocalConnectionCoordinatePullback LocalOrderedPrimitiveGaugeCoordinate
open LocalConnectionGaugeDifference ManifoldDifferentialForms
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (StandardSpace (E := E)) := inferInstance
local instance : NormedSpace ℝ
    (StandardSpace (E := E) →L[ℝ] StandardSpace (E := E)) := inferInstance
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞)) (D : CompatibleTangentConnection Q)

def direction (s t : ℝ) (p : M) :=
  correctedConnection S Q D t p - correctedConnection S Q D s p

theorem direction_smooth (s t : ℝ) (p : M) :
    ContDiffOn ℝ ∞ (direction S Q D s t p) (extChartAt 𝓘(ℝ,E) p).target :=
  (correctedConnection_smooth S Q D t p).sub (correctedConnection_smooth S Q D s p)

set_option maxHeartbeats 800000 in
theorem primitive_coordinate (s t : ℝ) (k : ℕ) (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q) :
    traceOrderedTransgressionForm LocalEndomorphismTrace.traceCLM
        (correctedConnection S Q D s p) (direction S Q D s t p) k y =
      (traceOrderedTransgressionForm LocalEndomorphismTrace.traceCLM
        (correctedConnection S Q D s q) (direction S Q D s t q) k
        (chartTransition (I := 𝓘(ℝ,E)) p q y)).compContinuousLinearMap
          (fderiv ℝ (chartTransition (I := 𝓘(ℝ,E)) p q) y) := by
  obtain ⟨G, K, hG, hK, hleft, hright, hAffine⟩ := exists_gauge S Q D p q y hy
  let φ := chartTransition (I := 𝓘(ℝ,E)) p q
  have hθ : direction S Q D s t p =ᶠ[𝓝 y]
      LocalConnectionGauge.adjointForm (pullback (direction S Q D s t q) φ) G K := by
    filter_upwards [hAffine t, hAffine s] with z ht hs
    change correctedConnection S Q D t p z - correctedConnection S Q D s p z = _
    rw [ht, hs]
    have hd := congrFun (transform_sub
      (pullback (correctedConnection S Q D t q) φ)
      (pullback (correctedConnection S Q D s q) φ) G K) z
    rw [← pullback_sub] at hd
    exact hd
  have hφ : ContDiffAt ℝ 2 φ y := by
    simpa [φ, chartTransition] using
      (contDiffWithinAt_ext_coord_change (I := 𝓘(ℝ,E)) (n := 2) q p hy)
  have hmem := (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) q).mem_nhds
    ((extChartAt 𝓘(ℝ,E) q).map_source hy.2)
  have hΓq := ((correctedConnection_smooth S Q D s q).differentiableOn
    (by norm_num)).differentiableAt hmem
  have hθq := ((direction_smooth S Q D s t q).differentiableOn
    (by norm_num)).differentiableAt hmem
  exact traceOrderedTransgressionForm_gauge_coordinate LocalEndomorphismTrace.traceCLM
    LocalEndomorphismTrace.traceCLM_cyclic
    (correctedConnection S Q D s p) (correctedConnection S Q D s q)
    (direction S Q D s t p) (direction S Q D s t q) φ G K y
    (hAffine s) hθ hΓq hθq hφ hG hK hleft hright k

def traceHomotopy (s t : ℝ) (k : ℕ) :
    TracePowerHomotopy (E := E) (M := M) (V := StandardSpace (E := E)) k where
  start := traceAtlas S Q D s k
  finish := traceAtlas S Q D t k
  direction := direction S Q D s t
  endpoint p := by
    change correctedConnection S Q D t p = correctedConnection S Q D s p +
      (correctedConnection S Q D t p - correctedConnection S Q D s p)
    abel
  directionC2 p _ hy := ((direction_smooth S Q D s t p).contDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy)).of_le ENat.LEInfty.out
  primitiveRegular p := LocalOrderedPrimitiveSmoothness.traceOrderedTransgressionForm_contDiffOn
    LocalEndomorphismTrace.traceCLM _ _ (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p)
    (correctedConnection_smooth S Q D s p) (direction_smooth S Q D s t p) k
  primitiveCoordinateLaw p q y hp hq := primitive_coordinate S Q D s t k p q y ⟨hp, hq⟩

theorem closedTracePower_class_eq (s t : ℝ) (k : ℕ) :
    QuotientAddGroup.mk ((primitiveDegree_add_one k).symm ▸ closedTracePower S Q D t k) =
      (QuotientAddGroup.mk ((primitiveDegree_add_one k).symm ▸ closedTracePower S Q D s k) :
        positiveDegreeCohomology (E := E) (M₀ := M) (primitiveDegree k)) :=
  (traceHomotopy S Q D s t k).cohomologyClass_eq

end
end QuaternionicSymmetry.QuaternionicManifoldCorrectedTransgression
