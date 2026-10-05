import QuaternionicSymmetry.LocalConnectionCoordinatePullback
import QuaternionicSymmetry.LocalConnectionGauge
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-! General differential-geometric source boundary for Levi-Civita
existence. Petersen, *Riemannian Geometry* (author-hosted 2015 draft),
Theorem 2.2.2 and its preceding definition/proof, printed pp. 43–45,
constructs the unique smooth metric-compatible torsion-free connection by
the Koszul formula. The book's §1.1 assumptions are smooth Hausdorff,
second-countable, connected finite-dimensional manifolds. This schema
records only the existence of ordinary coordinate Christoffel forms,
with their genuine affine overlap law. It includes no quaternionic
preservation, curvature sign, or model-specific assertion. -/

namespace QuaternionicSymmetry.GeneralLeviCivitaSource

open Manifold Bundle
open scoped Manifold ContDiff Topology Bundle
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ConnectedSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

private abbrev EndE := E →L[ℝ] E
private abbrev FormE := LocalConnection.Form (E := E) (A := EndE (E := E))

def chartTransition (p q : M) (y : E) : E :=
  extChartAt 𝓘(ℝ,E) q ((extChartAt 𝓘(ℝ,E) p).symm y)

def chartOverlap (p q : M) : Set E :=
  {y | y ∈ (extChartAt 𝓘(ℝ,E) p).target ∧
    (extChartAt 𝓘(ℝ,E) p).symm y ∈ (extChartAt 𝓘(ℝ,E) q).source}

def chartDerivative (p q : M) (y : E) : EndE (E := E) :=
  fderiv ℝ (chartTransition p q) y

def chartInverseDerivative (p q : M) (y : E) : EndE (E := E) :=
  fderiv ℝ (chartTransition q p) (chartTransition p q y)

def chartMetric
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
      (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (p : M) (y u v : E) : ℝ :=
  let z := (extChartAt 𝓘(ℝ,E) p).symm y
  g.inner z
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) p).symm y u)
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) p).symm y v)

/-- Ordinary coordinate connection forms satisfying exactly the
Levi-Civita laws. The quaternionic reduction is deliberately absent. -/
structure CoordinateLeviCivitaConnection
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
      (TangentSpace 𝓘(ℝ,E) : M → Type _)) where
  form : M → FormE (E := E)
  smooth_form : ∀ p, ContDiffOn ℝ ∞ (form p) (extChartAt 𝓘(ℝ,E) p).target
  overlap : ∀ p q y, y ∈ chartOverlap p q →
    form p y = LocalConnectionGauge.transform
      (LocalConnectionCoordinatePullback.pullback (form q) (chartTransition p q))
      (chartDerivative p q) (chartInverseDerivative p q) y
  metric : ∀ p y u v w, y ∈ (extChartAt 𝓘(ℝ,E) p).target →
    fderiv ℝ (fun z => chartMetric g p z v w) y u =
      chartMetric g p y (form p y u v) w +
        chartMetric g p y v (form p y u w)
  torsion : ∀ p y u v, y ∈ (extChartAt 𝓘(ℝ,E) p).target →
    form p y u v = form p y v u

/-- Registered general background theorem BG-R5 (Petersen, Thm. 2.2.2).
No particular manifold, quaternionic structure, or curvature conclusion
appears in the premise. -/
def PetersenLeviCivitaExistenceTheorem : Prop :=
  ∀ (E M : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ConnectedSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
      (TangentSpace 𝓘(ℝ,E) : M → Type _)),
    Nonempty (CoordinateLeviCivitaConnection g)

end
end QuaternionicSymmetry.GeneralLeviCivitaSource
