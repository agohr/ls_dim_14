import QuaternionicSymmetry.ManifoldQuaternionicLocalSynthSpan

/-! An explicit source-free projection onto the genuine chartwise
quaternionic three-plane, conjugated through the actual tangent gauge. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicChartProjection

open ManifoldQuaternionicReduction
open VectorBundleFrameTransitions
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private abbrev EndE := E →L[ℝ] E

def inverseChartConjugation (i : atlas E M) (x : M) :
    EndE (E := E) →L[ℝ] EndE (E := E) :=
  ((ContinuousLinearMap.mul ℝ (EndE (E := E))) (Q.frames.toFrame i x)).comp
    (((ContinuousLinearMap.mul ℝ (EndE (E := E))).flip)
      (Q.frames.fromFrame i x))

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem inverseChartConjugation_apply (i : atlas E M) (x : M)
    (T : EndE (E := E)) :
    inverseChartConjugation Q i x T =
      Q.frames.toFrame i x * T * Q.frames.fromFrame i x := by
  change Q.frames.toFrame i x * (T * Q.frames.fromFrame i x) = _
  rw [mul_assoc]

def chartProjection (i : atlas E M) (x : M) :
    EndE (E := E) →L[ℝ] EndE (E := E) :=
  (Q.chartConjugation i x).comp
    ((synth (Q.reduction.Q i)).comp
      ((coeff (Q.reduction.Q i)).comp
        (inverseChartConjugation Q i x)))

theorem chartProjection_mem (i : atlas E M) (x : M)
    (T : EndE (E := E)) :
    chartProjection Q i x T ∈ Q.chartSpan i x := by
  rw [Q.chartSpan_eq_map]
  exact ⟨synth (Q.reduction.Q i)
    (coeff (Q.reduction.Q i) (inverseChartConjugation Q i x T)),
    synth_mem _ _, rfl⟩

theorem chartProjection_fixed (i : atlas E M) (x : M)
    (hx : x ∈ (tangentBundleCore 𝓘(ℝ,E) M).baseSet i)
    (T : EndE (E := E)) (hT : T ∈ Q.chartSpan i x) :
    chartProjection Q i x T = T := by
  rw [Q.chartSpan_eq_map] at hT
  obtain ⟨U, hU, rfl⟩ := hT
  have hto : Q.frames.toFrame i x * Q.frames.fromFrame i x = 1 := by
    ext v
    exact Q.frames.to_from i x hx v
  have hfrom : Q.frames.fromFrame i x * Q.frames.toFrame i x = 1 := by
    ext v
    exact Q.frames.from_to i x hx v
  have hinv : inverseChartConjugation Q i x
      (Q.chartConjugation i x U) = U := by
    rw [inverseChartConjugation_apply, Q.chartConjugation_apply]
    calc
      Q.frames.toFrame i x *
          (Q.frames.fromFrame i x * U * Q.frames.toFrame i x) *
          Q.frames.fromFrame i x =
        (Q.frames.toFrame i x * Q.frames.fromFrame i x) * U *
          (Q.frames.toFrame i x * Q.frames.fromFrame i x) := by
            simp only [mul_assoc]
      _ = U := by simp [hto]
  change Q.chartConjugation i x
      (synth (Q.reduction.Q i)
        (coeff (Q.reduction.Q i)
          (inverseChartConjugation Q i x (Q.chartConjugation i x U)))) =
    Q.chartConjugation i x U
  rw [hinv, synth_coeff_of_mem _ _ hU]

end
end QuaternionicSymmetry.ManifoldQuaternionicChartProjection
