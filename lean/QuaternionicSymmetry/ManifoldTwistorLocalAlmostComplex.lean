import QuaternionicSymmetry.ManifoldTwistorSphereDerivative
import QuaternionicSymmetry.ManifoldTwistorTautologicalEndomorphism
/-! A local almost complex structure in raw base chart directions and
vertical sphere tangent vectors. The base rotation is conjugated by the
actual adapted tangent frame, while the induced connection supplies the
horizontal graph. Global overlap covariance and integrability are separate. -/

namespace QuaternionicSymmetry.ManifoldTwistorLocalAlmostComplex
open QuaternionicSymmetry.ManifoldTwistorHorizontalConnection
open QuaternionicSymmetry.ManifoldTwistorVerticalComplex
open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open QuaternionicSymmetry.ManifoldTwistorTautologicalEndomorphism
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicRankThreeOrthogonal
open QuaternionicSymmetry.VectorBundleFrameTransitions.QuaternionicFrameReduction
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped Manifold ContDiff Quaternion
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nontrivial E]

def baseComplex (S : QuaternionicStructure E) (a : coefficientSphere) : E →L[ℝ] E :=
 synth S a.1

private theorem synth_eq_action (S : QuaternionicStructure E)
    (a : Fin 3 → ℝ) (v : E) :
    synth S a v = S.action (imaginaryQuaternion a) v := by
  rw [synth_eval, S.action_apply]
  simp [imaginaryQuaternion, Fin.sum_univ_three,
    QuaternionicStructure.frame, QuaternionicStructure.K_apply]

theorem baseComplex_sq (S : QuaternionicStructure E) (a : coefficientSphere) (v : E) :
    baseComplex S a (baseComplex S a v) = -v := by
  change synth S a.1 (synth S a.1 v) = -v
  rw [synth_eq_action, synth_eq_action]
  change ((S.action (imaginaryQuaternion a.1) *
    S.action (imaginaryQuaternion a.1)) : Module.End ℝ E) v = -v
  rw [← map_mul, imaginaryQuaternion_sq]
  simp

def splitComplex (S : QuaternionicStructure E) (a : coefficientSphere) :
    (E × verticalSubmodule a) →ₗ[ℝ] (E × verticalSubmodule a) where
  toFun uv := (baseComplex S a uv.1, verticalComplex a uv.2)
  map_add' u v := by
    apply Prod.ext
    · exact (baseComplex S a).map_add u.1 v.1
    · exact (verticalComplex a).map_add u.2 v.2
  map_smul' r u := by
    apply Prod.ext
    · exact (baseComplex S a).map_smul r u.1
    · exact (verticalComplex a).map_smul r u.2

theorem splitComplex_sq (S : QuaternionicStructure E) (a : coefficientSphere)
    (uv : E × verticalSubmodule a) :
    splitComplex S a (splitComplex S a uv) = -uv := by
  apply Prod.ext
  · exact baseComplex_sq S a uv.1
  · exact verticalComplex_sq a uv.2

variable {M : Type*} [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

/-- The base complex structure in raw p-chart tangent coordinates, obtained
by conjugating the quaternionic rotation through the actual adapted frame. -/
def chartBaseComplex (p : M) (y : E) (a : coefficientSphere) : E →L[ℝ] E :=
  let x := (extChartAt 𝓘(ℝ,E) p).symm y
  (Q.frames.fromFrame (achart E p) x).comp
    ((baseComplex (Q.reduction.Q (achart E p)) a).comp
      (Q.frames.toFrame (achart E p) x))

omit [FiniteDimensional ℝ E] in
theorem chartBaseComplex_sq (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (a : coefficientSphere) (u : E) :
    chartBaseComplex Q p y a (chartBaseComplex Q p y a u) = -u := by
  let x := (extChartAt 𝓘(ℝ,E) p).symm y
  have hi : x ∈ Q.frames.adaptedCore.baseSet (achart E p) := by
    simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using
      (extChartAt 𝓘(ℝ,E) p).map_target hy
  change Q.frames.fromFrame (achart E p) x
    (baseComplex (Q.reduction.Q (achart E p)) a
      (Q.frames.toFrame (achart E p) x
        (Q.frames.fromFrame (achart E p) x
          (baseComplex (Q.reduction.Q (achart E p)) a
            (Q.frames.toFrame (achart E p) x u))))) = -u
  rw [Q.frames.to_from (achart E p) x hi]
  rw [baseComplex_sq]
  rw [map_neg, Q.frames.from_to (achart E p) x hi]

def chartSplitComplex (p : M) (y : E) (a : coefficientSphere) :
    (E × verticalSubmodule a) →ₗ[ℝ] (E × verticalSubmodule a) where
  toFun uv := (chartBaseComplex Q p y a uv.1, verticalComplex a uv.2)
  map_add' u v := by
    apply Prod.ext
    · exact (chartBaseComplex Q p y a).map_add u.1 v.1
    · exact (verticalComplex a).map_add u.2 v.2
  map_smul' r u := by
    apply Prod.ext
    · exact (chartBaseComplex Q p y a).map_smul r u.1
    · exact (verticalComplex a).map_smul r u.2

omit [FiniteDimensional ℝ E] in
theorem chartSplitComplex_sq (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (a : coefficientSphere) (uv : E × verticalSubmodule a) :
    chartSplitComplex Q p y a (chartSplitComplex Q p y a uv) = -uv := by
  apply Prod.ext
  · exact chartBaseComplex_sq Q p y hy a uv.1
  · exact verticalComplex_sq a uv.2

/-- Local almost complex structure on the genuine chart tangent model. -/
def localTwistorComplex (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (a : coefficientSphere) :
    (E × verticalSubmodule a) →ₗ[ℝ] (E × verticalSubmodule a) :=
  (connectionSplit Q D p y hy a).symm.toLinearMap.comp
    ((chartSplitComplex Q p y a).comp
      (connectionSplit Q D p y hy a).toLinearMap)

theorem localTwistorComplex_sq (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (a : coefficientSphere) (uv : E × verticalSubmodule a) :
    localTwistorComplex Q D p y hy a
      (localTwistorComplex Q D p y hy a uv) = -uv := by
  simp [localTwistorComplex, chartSplitComplex_sq Q p y hy a]

end
end QuaternionicSymmetry.ManifoldTwistorLocalAlmostComplex
