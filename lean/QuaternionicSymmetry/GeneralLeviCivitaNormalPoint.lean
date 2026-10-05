import QuaternionicSymmetry.GeneralLeviCivitaCoordinateKoszul

/-! A vanishing first jet of the coordinate metric forces the ordinary
Levi-Civita Christoffel form to vanish at that point. This is an internal
consequence of the checked Koszul identity and positive definiteness. -/

namespace QuaternionicSymmetry.GeneralLeviCivitaNormalPoint

open Manifold Bundle GeneralLeviCivitaSource
open GeneralLeviCivitaCoordinateKoszul
open GeneralLeviCivitaCoordinatePositive
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem form_zero_of_metric_first_jet_zero
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
      (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (D : CoordinateLeviCivitaConnection g)
    (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (hjet : ∀ u v w : E,
      fderiv ℝ (fun z => chartMetric g p z v w) y u = 0) :
    D.form p y = 0 := by
  ext u v
  let z : E := D.form p y u v
  have hz : chartMetric g p y z z = 0 := by
    have h := coordinate_koszul g D p y u v z hy
    rw [hjet u v z, hjet v u z, hjet z u v] at h
    have h₂ : 2 * chartMetric g p y z z = 0 := by
      simpa only [z, zero_add, sub_zero] using h
    linarith only [h₂]
  by_contra hne
  have hp := chartMetric_pos g p y z hy hne
  linarith only [hz, hp]

end
end QuaternionicSymmetry.GeneralLeviCivitaNormalPoint
