import QuaternionicSymmetry.ManifoldQuaternionicIntrinsicTwistorComparison

/-! Continuity of the actual twistor-sphere point represented by a varying
coefficient in one fixed fiber. This uses the genuine bundle topology. -/

namespace QuaternionicSymmetry.ManifoldTwistorFixedFiberPointContinuous

open ManifoldTwistorSphereBundle
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem continuous_pointOfLocal_fixed (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i) :
    Continuous (pointOfLocal Q i x hi) := by
  let h : coefficientSphere →
      {x : M // x ∈ Q.frames.adaptedCore.baseSet i} × coefficientSphere :=
    fun z => (⟨x, hi⟩, z)
  have hh : Continuous h := continuous_const.prodMk continuous_id
  have hcomp :=
    ((localTrivializationHomeomorph Q i).symm.continuous.comp hh)
  exact (continuous_subtype_val.comp hcomp).congr (by
    intro z
    rfl)

theorem continuous_preferredPoint_fixed (x : M) :
    Continuous (ManifoldQuaternionicIntrinsicTwistorComparison.preferredPoint Q x) := by
  exact continuous_pointOfLocal_fixed Q _ x
    (Q.frames.adaptedCore.mem_baseSet_at x)

end
end QuaternionicSymmetry.ManifoldTwistorFixedFiberPointContinuous
