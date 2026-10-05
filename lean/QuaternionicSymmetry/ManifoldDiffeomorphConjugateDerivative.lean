import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-! Source-free naturality of the actual manifold derivative across a
commuting square of smooth diffeomorphisms with distinct model spaces. -/

namespace QuaternionicSymmetry.ManifoldDiffeomorphConjugateDerivative

open Manifold
open scoped Manifold ContDiff
noncomputable section

variable {E V H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V K}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace K N]

theorem mfderiv_commuting_square
    (D : Diffeomorph I J M N ∞)
    (S : Diffeomorph I I M M ∞)
    (T : Diffeomorph J J N N ∞)
    (h : (D : M → N) ∘ (S : M → M) =
      (T : N → N) ∘ (D : M → N))
    (x : M) :
    (mfderiv I J (D : M → N) (S x)).comp
        (mfderiv I I (S : M → M) x) =
      (mfderiv J J (T : N → N) (D x)).comp
        (mfderiv I J (D : M → N) x) := by
  have hleft := mfderiv_comp x
    (D.contMDiff.mdifferentiable (by simp) (S x))
    (S.contMDiff.mdifferentiable (by simp) x)
  have hright := mfderiv_comp x
    (T.contMDiff.mdifferentiable (by simp) (D x))
    (D.contMDiff.mdifferentiable (by simp) x)
  rw [h] at hleft
  exact hleft.symm.trans hright

end
end QuaternionicSymmetry.ManifoldDiffeomorphConjugateDerivative
