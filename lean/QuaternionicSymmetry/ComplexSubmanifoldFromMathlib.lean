import QuaternionicSymmetry.ComplexSubmanifoldAtlas

/-! The complex-submanifold contract follows from the inverse function theorem
and the internally proved real-smooth Cauchy–Riemann criterion. -/
namespace QuaternionicSymmetry.ComplexSubmanifoldFromMathlib
open ComplexSubmanifoldInput ComplexSubmanifoldChart ComplexSubmanifoldAtlas
open scoped Manifold ContDiff
noncomputable section

theorem closedComplexTangentSubmanifold : ClosedComplexTangentSubmanifoldTheorem := by
  intro F B _ _ _ _ _ _ _ _ _ S _hClosed k A hI
  letI := A.charts
  letI := A.manifold
  have hcharts : ∀ x : S, ∃ e : AdaptedChart (E := EuclideanSpace ℝ (Fin k))
      (F := F) (Subtype.val : S → B) (k / 2), x ∈ e.chart.source := by
    intro x
    obtain ⟨m,e,hd,hx⟩ := exists_adapted_chart
      A.inclusion_smooth A.inclusion_injective_derivative hI x
    have hm : m = k / 2 := by
      have hk : k = 2 * m := by simpa using hd
      omega
    subst m
    exact ⟨e,hx⟩
  choose C hC using hcharts
  exact ⟨k / 2,⟨{
    charts := charts C hC
    manifold := complexManifold C hC
    realManifold := realManifold C hC
    smoothToReal := smoothToReal C hC
    smoothFromReal := smoothFromReal C hC
    inclusion_holomorphic := inclusion_holomorphic C hC }⟩⟩

end
end QuaternionicSymmetry.ComplexSubmanifoldFromMathlib
