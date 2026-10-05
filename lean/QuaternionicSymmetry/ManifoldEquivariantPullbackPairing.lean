import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! Differential equivariance and preservation of the literal pullback
pairing under a smooth map intertwined with a linear ambient isometry. -/

namespace QuaternionicSymmetry.ManifoldEquivariantPullbackPairing

open Manifold
open scoped Manifold ContDiff
noncomputable section

variable {E V M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (f : M → V) (a : M → M) (A : V →L[ℝ] V)
  (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,V) ∞ f)
  (ha : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ a)
  (heq : ∀ x, f (a x) = A (f x))

include hf ha heq

/-- Differentiate the actual equivariance identity; no independent
tangent-equivariance premise is needed. -/
theorem mfderiv_equivariance (x : M) (v : TangentSpace 𝓘(ℝ,E) x) :
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) f (a x)
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) a x v) =
      A (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) f x v) := by
  have hfun : f ∘ a = A ∘ f := funext heq
  have hl := mfderiv_comp x
    (hf.mdifferentiableAt (by simp)) (ha.mdifferentiableAt (by simp))
  have hr := mfderiv_comp x A.mdifferentiableAt
    (hf.mdifferentiableAt (by simp))
  rw [hfun, hr, A.mfderiv_eq] at hl
  exact congrArg (fun D : TangentSpace 𝓘(ℝ,E) x →L[ℝ] V => D v) hl.symm

/-- An invariant ambient bilinear form yields an invariant pullback form
on actual tangent vectors. Nondegeneracy and smoothness are separate
properties supplied by the immersion-metric construction. -/
theorem pullback_pairing_invariant
    (g : V →L[ℝ] V →L[ℝ] ℝ)
    (hA : ∀ v w, g (A v) (A w) = g v w)
    (x : M) (v w : TangentSpace 𝓘(ℝ,E) x) :
    g (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) f (a x)
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) a x v))
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) f (a x)
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) a x w)) =
    g (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) f x v)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) f x w) := by
  rw [mfderiv_equivariance f a A hf ha heq x v,
    mfderiv_equivariance f a A hf ha heq x w]
  exact hA _ _

end
end QuaternionicSymmetry.ManifoldEquivariantPullbackPairing
