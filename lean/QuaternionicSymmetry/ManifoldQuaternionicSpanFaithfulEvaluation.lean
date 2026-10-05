import QuaternionicSymmetry.ManifoldQuaternionicIntrinsicTwistorComparison
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-! A quaternionic endomorphism in the actual rank-three tangent plane is
determined by its value on any nonzero tangent vector. This permits unique
extension from a positive-dimensional quaternionic tangent subspace. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicSpanFaithfulEvaluation
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIntrinsicTwistorComparison
open ManifoldTwistorSphereBundle
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem tangentSpan_eq_zero_of_apply_eq_zero (x : M)
    (A : TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hA : A ∈ tangentSpan Q x) (v : TangentSpace 𝓘(ℝ,E) x)
    (hv : v ≠ 0) (hAv : A v = 0) : A = 0 := by
  obtain ⟨a, ha⟩ := exists_tangentSynth_of_mem Q x A hA
  have hs := tangentSynth_square Q x a v
  rw [ha, hAv, map_zero] at hs
  have hscalar : -(squareNorm a) = 0 :=
    (smul_eq_zero.mp hs.symm).resolve_right hv
  have ha0 : a = 0 := dotProduct_self_eq_zero.mp (neg_eq_zero.mp hscalar)
  rw [← ha, ha0, tangentSynth_zero]

theorem tangentSpan_eq_of_apply_eq (x : M)
    (A B : TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hA : A ∈ tangentSpan Q x) (hB : B ∈ tangentSpan Q x)
    (v : TangentSpace 𝓘(ℝ,E) x) (hv : v ≠ 0) (h : A v = B v) :
    A = B := by
  apply sub_eq_zero.mp
  exact tangentSpan_eq_zero_of_apply_eq_zero Q x (A-B)
    ((tangentSpan Q x).sub_mem hA hB) v hv (by simpa using sub_eq_zero.mpr h)

/-- Squaring to minus the identity on one nonzero vector is enough for a
quaternionic-span endomorphism to be a complex structure on the entire
tangent fiber. -/
theorem tangentSpan_sq_neg_of_one_vector (x : M)
    (A : TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hA : A ∈ tangentSpan Q x) (v : TangentSpace 𝓘(ℝ,E) x)
    (hv : v ≠ 0) (hAv : A (A v) = -v) :
    ∀ w : TangentSpace 𝓘(ℝ,E) x, A (A w) = -w := by
  obtain ⟨a, ha⟩ := exists_tangentSynth_of_mem Q x A hA
  have hs := tangentSynth_square Q x a v
  rw [ha, hAv] at hs
  have heq : (-(squareNorm a)) • v = (-1 : ℝ) • v := by
    simpa using hs.symm
  have hscalar : -(squareNorm a) = -1 := (smul_left_injective ℝ hv) heq
  intro w
  rw [← ha, tangentSynth_square, hscalar, neg_one_smul]

end
end QuaternionicSymmetry.ManifoldQuaternionicSpanFaithfulEvaluation
