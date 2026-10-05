import QuaternionicSymmetry.ManifoldQuaternionicMetric
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Topology.Connected.Clopen

/-! The actual path-length distance of the quaternionic tangent metric.
Mathlib's construction retains the original manifold topology; this is not
an arbitrary auxiliary metrization. The norm used in each tangent fiber is
the one constructed from the genuine adapted-frame metric. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicRiemannianDistance

open Bundle Manifold ManifoldQuaternionicMetric
open scoped Manifold ContDiff Bundle ENNReal
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

def actualRiemannianBundle :
    RiemannianBundle (TangentSpace 𝓘(ℝ,E) : M → Type _) :=
  ⟨Q.riemannianMetric.toRiemannianMetric⟩

theorem actual_inner_eq (x : M) (v w : TangentSpace 𝓘(ℝ,E) x) :
    letI := actualRiemannianBundle Q
    inner ℝ v w = Q.tangentMetricForm x v w := rfl

/-- The metric distance allowing infinity between distinct connected
components. Its topology is definitionally the given manifold topology. -/
def riemannianEMetricSpace [T3Space M] : EMetricSpace M := by
  letI := actualRiemannianBundle Q
  exact EMetricSpace.ofRiemannianMetric 𝓘(ℝ,E) M

/-- The distance is defined by infima of genuine C¹ path lengths. -/
def riemannianEDistance (x y : M) : ℝ≥0∞ :=
  letI := actualRiemannianBundle Q
  riemannianEDist 𝓘(ℝ,E) x y

theorem riemannianEDistance_self (x : M) : riemannianEDistance Q x x = 0 := by
  letI := actualRiemannianBundle Q
  exact riemannianEDist_self

theorem riemannianEDistance_comm (x y : M) :
    riemannianEDistance Q x y = riemannianEDistance Q y x := by
  letI := actualRiemannianBundle Q
  exact riemannianEDist_comm

theorem riemannianEDistance_triangle (x y z : M) :
    riemannianEDistance Q x z ≤ riemannianEDistance Q x y +
      riemannianEDistance Q y z := by
  letI := actualRiemannianBundle Q
  exact riemannianEDist_triangle

theorem riemannianEDistance_ne_top [T3Space M] [PreconnectedSpace M]
    (x y : M) : riemannianEDistance Q x y ≠ ⊤ := by
  letI : EMetricSpace M := riemannianEMetricSpace Q
  have hc : IsClopen (Metric.eball x ⊤) :=
    ⟨Metric.isClosed_eball_top, Metric.isOpen_eball⟩
  have hall : Metric.eball x ⊤ = Set.univ :=
    hc.eq_univ ⟨x, by simp⟩
  have hy : y ∈ Metric.eball x ⊤ := by rw [hall]; trivial
  have hfin : edist x y < ⊤ := by
    simpa only [Metric.mem_eball, edist_comm] using hy
  exact hfin.ne

/-- On a connected manifold the genuine Riemannian path distance is
finite and defines a metric, retaining the original topology. -/
def riemannianMetricSpace [T3Space M] [PreconnectedSpace M] : MetricSpace M :=
  letI : EMetricSpace M := riemannianEMetricSpace Q
  EMetricSpace.toMetricSpace (riemannianEDistance_ne_top Q)

end
end QuaternionicSymmetry.ManifoldQuaternionicRiemannianDistance
