import QuaternionicSymmetry.ManifoldQuaternionicCanonicalIntegration

/-! A pointwise coefficient lower bound relative to the actual fundamental
top form gives the corresponding canonical integral lower bound. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicIntegralLowerBound
open ManifoldDifferentialForms ManifoldQuaternionicMetric
open ManifoldQuaternionicVolume ManifoldQuaternionicDensityIntegration
open ManifoldQuaternionicCanonicalIntegration
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

def volumeForm : SmoothTopForms (E := E) (M := M) :=
  ⟨fundamentalTopForm Q, fundamentalTopForm_smooth Q⟩

theorem integral_lower_bound (α : SmoothTopForms (E := E) (M := M)) (c : ℝ)
    (h : ∀ x : M, ∃ r : ℝ, c ≤ r ∧ α.val x = r • fundamentalTopForm Q x) :
    c * integral Q (volumeForm Q) ≤ integral Q α := by
  have hp : ∀ x : M, PositiveRay.Contains (fundamentalTopForm Q x)
      ((α - c • volumeForm Q).val x) := by
    intro x
    obtain ⟨r, hr, he⟩ := h x
    refine ⟨r-c, sub_nonneg.mpr hr, ?_⟩
    change α.val x - c • fundamentalTopForm Q x = _
    rw [he, sub_smul]
  have hi := integral_nonneg Q (α - c • volumeForm Q) hp
  rw [map_sub, map_smul, smul_eq_mul] at hi
  exact sub_nonneg.mp hi

theorem integral_positive (α : SmoothTopForms (E := E) (M := M)) (c : ℝ) (hc : 0 < c)
    (h : ∀ x : M, ∃ r : ℝ, c ≤ r ∧ α.val x = r • fundamentalTopForm Q x) :
    0 < integral Q α :=
  lt_of_lt_of_le (mul_pos hc (integral_topForm_pos Q)) (integral_lower_bound Q α c h)

end
end QuaternionicSymmetry.ManifoldQuaternionicIntegralLowerBound
