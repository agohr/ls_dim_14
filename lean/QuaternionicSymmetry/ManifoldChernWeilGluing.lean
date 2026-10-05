import QuaternionicSymmetry.ManifoldChartFormGluing
import QuaternionicSymmetry.LocalChernWeilTracePowers

/-!
Local Chern--Weil trace powers become closed forms on an actual smooth
manifold when their chart expressions satisfy the ordinary differential-form
transition law. The chart law remains an explicit geometric obligation: a
choice of local connections alone does not imply gauge or coordinate
compatibility.
-/

namespace QuaternionicSymmetry.ManifoldChernWeilGluing

open QuaternionicSymmetry.ManifoldDifferentialForms
  QuaternionicSymmetry.ManifoldChartFormGluing
  QuaternionicSymmetry.LocalChernWeilTracePowers
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

/-- Chartwise connection one-forms whose actual curvature trace power has
the regularity and coordinate transformation law needed for gluing. -/
structure TracePowerAtlas (k : ℕ) where
  connection : M → QuaternionicSymmetry.LocalConnection.Form
    (E := E) (A := V →L[ℝ] V)
  connectionC2 : ∀ (p : M) (y : E),
    y ∈ (extChartAt 𝓘(ℝ, E) p).target →
      ContDiffAt ℝ 2 (connection p) y
  traceRegular : ∀ p : M,
    ContDiffOn ℝ ∞
      (traceCurvaturePowerForm (connection p) k)
      (extChartAt 𝓘(ℝ, E) p).target
  traceCoordinateLaw : ∀ (p q : M) (y : E),
    y ∈ (extChartAt 𝓘(ℝ, E) p).target →
    (extChartAt 𝓘(ℝ, E) p).symm y ∈
      (extChartAt 𝓘(ℝ, E) q).source →
    traceCurvaturePowerForm (connection p) k y =
      ContinuousAlternatingMap.compContinuousLinearMap
        (traceCurvaturePowerForm (connection q) k
          ((extChartAt 𝓘(ℝ, E) q)
            ((extChartAt 𝓘(ℝ, E) p).symm y)))
        (fderiv ℝ
          ((extChartAt 𝓘(ℝ, E) q) ∘
            (extChartAt 𝓘(ℝ, E) p).symm) y)

namespace TracePowerAtlas

variable {k : ℕ} (A : TracePowerAtlas (E := E) (M := M) (V := V) k)

/-- The chart trace powers as compatible scalar chart forms. -/
noncomputable def chartForms :
    ChartFormData (E := E) (M := M) (powerDegree k) where
  localForm p := traceCurvaturePowerForm (A.connection p) k
  regular := A.traceRegular
  coordinateLaw := A.traceCoordinateLaw

/-- The global tangent-bundle-valued Chern--Weil representative. -/
noncomputable def globalForm : Form 𝓘(ℝ, E) M (powerDegree k) :=
  A.chartForms.toForm

theorem globalForm_chart (p : M) {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    inChartModel p A.globalForm y =
      traceCurvaturePowerForm (A.connection p) k y :=
  A.chartForms.inChartModel_toForm p hy

theorem globalForm_smooth : ChartSmooth A.globalForm :=
  A.chartForms.toForm_smooth

theorem globalForm_closed : exteriorDerivative A.globalForm = 0 := by
  apply A.chartForms.toForm_closed
  intro p y hy
  exact traceCurvaturePowerForm_closed (A.connection p) y
    (A.connectionC2 p y hy) k

/-- A genuine closed smooth form in the positive degree `2(k+1)`. -/
def closedGlobalForm :
    closedForms (E := E) (M₀ := M) (powerDegree k) :=
  ⟨⟨A.globalForm, A.globalForm_smooth⟩, by
    change smoothExteriorDerivative (E := E) (M₀ := M) (powerDegree k)
      ⟨A.globalForm, A.globalForm_smooth⟩ = 0
    apply Subtype.ext
    exact A.globalForm_closed⟩

/-- The resulting class in positive-degree de Rham cohomology. -/
def cohomologyClass :
    positiveDegreeCohomology (E := E) (M₀ := M) (powerDegree k - 1) := by
  have hdegree : powerDegree k - 1 + 1 = powerDegree k := by
    rw [powerDegree_eq]
    omega
  exact QuotientAddGroup.mk (hdegree ▸ A.closedGlobalForm)

end TracePowerAtlas
end
end QuaternionicSymmetry.ManifoldChernWeilGluing
