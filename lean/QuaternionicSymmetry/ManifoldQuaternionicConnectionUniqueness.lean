import QuaternionicSymmetry.ManifoldQuaternionicScalarCurvature
import QuaternionicSymmetry.AlgebraicLeviCivitaUniqueness

/-! A metric torsion-free compatible tangent connection is unique on all
valid manifold chart coordinates. Hence the supplied connection data, when
present, is the Levi-Civita connection of the actual adapted metric. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicConnectionUniqueness
open ManifoldQuaternionicConnection
open ManifoldQuaternionicScalarCurvature
open QuaternionicSymmetry.AlgebraicLeviCivitaUniqueness
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance : NormedSpace ℝ E := inferInstance
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D₁ D₂ : CompatibleTangentConnection Q)

omit [FiniteDimensional ℝ E] in
theorem form_eq_on_chart (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    D₁.form p y = D₂.form p y := by
  let e := solderEquiv Q p y hy
  let B : E → E → E → ℝ := fun u v w =>
    inner ℝ ((D₁.form p y (e.symm u) - D₂.form p y (e.symm u)) v) w
  have hskew : ∀ u v w, B u v w = -B u w v := by
    intro u v w
    have h₁ := D₁.metric p y (e.symm u) v w hy
    have h₂ := D₂.metric p y (e.symm u) v w hy
    dsimp [B]
    simp only [inner_sub_left]
    rw [← real_inner_comm v (((D₁.form p y) (e.symm u)) w)] at h₁
    rw [← real_inner_comm v (((D₂.form p y) (e.symm u)) w)] at h₂
    linear_combination h₁ - h₂
  have hsym : ∀ u v w, B u v w = B v u w := by
    intro u v w
    have h₁ := D₁.torsion p y (e.symm u) (e.symm v) hy
    have h₂ := D₂.torsion p y (e.symm u) (e.symm v) hy
    have hu : solder Q p y (e.symm u) = u := e.apply_symm_apply u
    have hv : solder Q p y (e.symm v) = v := e.apply_symm_apply v
    rw [hu, hv] at h₁ h₂
    have hz :
        (D₁.form p y (e.symm u) - D₂.form p y (e.symm u)) v =
          (D₁.form p y (e.symm v) - D₂.form p y (e.symm v)) u := by
      simp only [ContinuousLinearMap.sub_apply]
      apply sub_eq_zero.mp
      calc
        ((D₁.form p y (e.symm u)) v - (D₂.form p y (e.symm u)) v) -
            ((D₁.form p y (e.symm v)) u - (D₂.form p y (e.symm v)) u) =
          (fderiv ℝ (solder Q p) y (e.symm u) (e.symm v) -
            fderiv ℝ (solder Q p) y (e.symm v) (e.symm u) +
            (D₁.form p y (e.symm u)) v - (D₁.form p y (e.symm v)) u) -
          (fderiv ℝ (solder Q p) y (e.symm u) (e.symm v) -
            fderiv ℝ (solder Q p) y (e.symm v) (e.symm u) +
            (D₂.form p y (e.symm u)) v - (D₂.form p y (e.symm v)) u) := by abel
        _ = 0 := by rw [h₁, h₂]; simp
    exact congrArg (fun z : E => inner ℝ z w) hz
  ext u v
  let z : E := (D₁.form p y u - D₂.form p y u) v
  have hz : inner ℝ z z = 0 := by
    have h := symmetric_skew_tensor_zero B hsym hskew (e u) v z
    simpa only [B, e.symm_apply_apply, z,
      ContinuousLinearMap.sub_apply] using h
  have hz0 : z = 0 := by
    by_contra hne
    have hp := real_inner_self_pos.mpr hne
    linarith
  exact sub_eq_zero.mp hz0

end
end QuaternionicSymmetry.ManifoldQuaternionicConnectionUniqueness
