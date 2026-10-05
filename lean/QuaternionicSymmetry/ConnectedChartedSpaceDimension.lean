import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.TotallyDisconnected

/-! A connected nontrivial manifold cannot have zero-dimensional Euclidean
charts. This is a statement about its genuine topology, not a dimension
convention imposed on a selected fixed component. -/
namespace QuaternionicSymmetry.ConnectedChartedSpaceDimension

theorem complex_dimension_pos {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] [Nontrivial X] (b : ℕ)
    [ChartedSpace (EuclideanSpace ℂ (Fin b)) X] : 0 < b := by
  by_contra h
  have hb : b = 0 := by omega
  subst b
  letI : DiscreteTopology X :=
    ChartedSpace.discreteTopology (EuclideanSpace ℂ (Fin 0)) X
  letI : Subsingleton X := ⟨fun x y =>
    isPreconnected_univ.subsingleton (Set.mem_univ x) (Set.mem_univ y)⟩
  exact not_nontrivial X inferInstance

end QuaternionicSymmetry.ConnectedChartedSpaceDimension
