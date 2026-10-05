import QuaternionicSymmetry.GeneralLeviCivitaAdaptedMetricBridge
import QuaternionicSymmetry.GeneralLeviCivitaCoordinateKoszul

/-! The ordinary Levi-Civita Koszul identity in the genuine adapted
coordinate metric, obtained from an equality of metric fields on the
valid chart domain. There is no quaternionic connection assumption. -/

namespace QuaternionicSymmetry.GeneralLeviCivitaAdaptedKoszul

open Filter Manifold Bundle GeneralLeviCivitaSource
open GeneralLeviCivitaAdaptedMetricBridge
open GeneralLeviCivitaCoordinateKoszul
open ManifoldQuaternionicCoordinateMetricity
open scoped Manifold ContDiff Topology
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem coordinate_koszul_adapted
    (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
      (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (hmetric : ∀ x (v w : TangentSpace 𝓘(ℝ,E) x),
      g.inner x v w = Q.tangentMetricForm x v w)
    (D : CoordinateLeviCivitaConnection g)
    (p : M) (y u v w : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    2 * coordinateMetric Q p y (D.form p y u v) w =
      fderiv ℝ (fun z => coordinateMetric Q p z v w) y u +
      fderiv ℝ (fun z => coordinateMetric Q p z u w) y v -
      fderiv ℝ (fun z => coordinateMetric Q p z u v) y w := by
  have hval (a b : E) := chartMetric_eq_coordinateMetric Q g hmetric p y hy a b
  have hder (a b c : E) :
      fderiv ℝ (fun z => chartMetric g p z b c) y a =
        fderiv ℝ (fun z => coordinateMetric Q p z b c) y a := by
    have hevent : (fun z => chartMetric g p z b c) =ᶠ[𝓝 y]
        fun z => coordinateMetric Q p z b c := by
      filter_upwards [(isOpen_extChartAt_target p).mem_nhds hy]
        with z hz
      exact chartMetric_eq_coordinateMetric Q g hmetric p z hz b c
    exact congrArg (fun L : E →L[ℝ] ℝ => L a) (hevent.fderiv_eq (𝕜 := ℝ))
  have h := coordinate_koszul g D p y u v w hy
  rw [hval, hder u v w, hder v u w, hder w u v] at h
  exact h

end
end QuaternionicSymmetry.GeneralLeviCivitaAdaptedKoszul
