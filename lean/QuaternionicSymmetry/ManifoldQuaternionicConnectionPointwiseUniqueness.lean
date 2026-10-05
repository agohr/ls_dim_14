import QuaternionicSymmetry.ManifoldQuaternionicConnectionUniqueness

/-! Pointwise Koszul uniqueness for a metric, torsion-free candidate
connection form. This avoids packaging a transformed form into a global
compatible connection before proving its equality with the given one. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicConnectionPointwiseUniqueness

open ManifoldQuaternionicConnection
open ManifoldQuaternionicScalarCurvature
open QuaternionicSymmetry.AlgebraicLeviCivitaUniqueness
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

omit [FiniteDimensional ℝ E] in
/-- Any single candidate form satisfying the metric and torsion laws at a
chart point agrees there with the unique actual Levi-Civita form. Neither
global smoothness nor quaternionic compatibility is needed for uniqueness. -/
theorem candidate_eq_on_chart (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (A : E →L[ℝ] (E →L[ℝ] E))
    (hmetric : ∀ (u v w : E),
      inner ℝ ((A u) v) w + inner ℝ v ((A u) w) = 0)
    (htorsion : ∀ (u v : E),
      fderiv ℝ (solder Q p) y u v - fderiv ℝ (solder Q p) y v u +
        A u (solder Q p y v) - A v (solder Q p y u) = 0) :
    A = D.form p y := by
  let e := solderEquiv Q p y hy
  let B : E → E → E → ℝ := fun u v w =>
    inner ℝ ((A (e.symm u) - D.form p y (e.symm u)) v) w
  have hskew : ∀ u v w, B u v w = -B u w v := by
    intro u v w
    have h₁ := hmetric (e.symm u) v w
    have h₂ := D.metric p y (e.symm u) v w hy
    dsimp [B]
    simp only [inner_sub_left]
    rw [← real_inner_comm v ((A (e.symm u)) w)] at h₁
    rw [← real_inner_comm v ((D.form p y) (e.symm u) w)] at h₂
    linear_combination h₁ - h₂
  have hsym : ∀ u v w, B u v w = B v u w := by
    intro u v w
    have h₁ := htorsion (e.symm u) (e.symm v)
    have h₂ := D.torsion p y (e.symm u) (e.symm v) hy
    have hu : solder Q p y (e.symm u) = u := e.apply_symm_apply u
    have hv : solder Q p y (e.symm v) = v := e.apply_symm_apply v
    rw [hu, hv] at h₁ h₂
    have hz :
        (A (e.symm u) - D.form p y (e.symm u)) v =
          (A (e.symm v) - D.form p y (e.symm v)) u := by
      simp only [ContinuousLinearMap.sub_apply]
      apply sub_eq_zero.mp
      calc
        (A (e.symm u) v - D.form p y (e.symm u) v) -
            (A (e.symm v) u - D.form p y (e.symm v) u) =
          (fderiv ℝ (solder Q p) y (e.symm u) (e.symm v) -
            fderiv ℝ (solder Q p) y (e.symm v) (e.symm u) +
            A (e.symm u) v - A (e.symm v) u) -
          (fderiv ℝ (solder Q p) y (e.symm u) (e.symm v) -
            fderiv ℝ (solder Q p) y (e.symm v) (e.symm u) +
            D.form p y (e.symm u) v - D.form p y (e.symm v) u) := by abel
        _ = 0 := by rw [h₁, h₂]; simp
    exact congrArg (fun z : E => inner ℝ z w) hz
  ext u v
  let z : E := (A u - D.form p y u) v
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
end QuaternionicSymmetry.ManifoldQuaternionicConnectionPointwiseUniqueness
