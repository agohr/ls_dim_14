import QuaternionicSymmetry.ManifoldRelatedBracket
import Mathlib.Geometry.Manifold.GroupLieAlgebra

/-! The derivative of an actual smooth Lie-group homomorphism preserves
the genuine tangent Lie bracket. This is proved from naturality of vector
field brackets, not supplied as an additional source premise. -/

namespace QuaternionicSymmetry.SmoothLieHomDerivativeBracket

open ManifoldRelatedBracket
open scoped Manifold ContDiff
noncomputable section

variable {𝕜 E F G H : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [IsManifold 𝓘(𝕜,E) ∞ G] [LieGroup 𝓘(𝕜,E) ∞ G]
  [Group H] [TopologicalSpace H] [ChartedSpace F H]
  [IsManifold 𝓘(𝕜,F) ∞ H] [LieGroup 𝓘(𝕜,F) ∞ H]

theorem mfderiv_mulInvariantVectorField (f : G →* H)
    (hf : ContMDiff 𝓘(𝕜,E) 𝓘(𝕜,F) ∞ f)
    (v : GroupLieAlgebra 𝓘(𝕜,E) G) (g : G) :
    mfderiv 𝓘(𝕜,E) 𝓘(𝕜,F) f g (mulInvariantVectorField v g) =
      mulInvariantVectorField (mfderiv 𝓘(𝕜,E) 𝓘(𝕜,F) f 1 v) (f g) := by
  have hL : MDifferentiableAt 𝓘(𝕜,E) 𝓘(𝕜,E) (g * ·) (1 : G) :=
    (contMDiff_mul_left (I := 𝓘(𝕜,E)) (n := ∞)).mdifferentiableAt (by simp)
  have hR : MDifferentiableAt 𝓘(𝕜,F) 𝓘(𝕜,F) (f g * ·) (f 1) :=
    (contMDiff_mul_left (I := 𝓘(𝕜,F)) (n := ∞)).mdifferentiableAt (by simp)
  have hfun : f ∘ (g * ·) = (f g * ·) ∘ f := by
    funext h
    exact map_mul f g h
  have hleft := mfderiv_comp (1 : G) (hf.mdifferentiableAt (by simp)) hL
  have hright := mfderiv_comp (1 : G) hR (hf.mdifferentiableAt (by simp))
  rw [hfun, hright, mul_one, map_one] at hleft
  exact (congrArg (fun A : E →L[𝕜] F => A v) hleft).symm

variable [ENat.LEInfty (minSmoothness 𝕜 3)]

theorem mfderiv_map_lie (f : G →* H)
    (hf : ContMDiff 𝓘(𝕜,E) 𝓘(𝕜,F) ∞ f)
    (v w : GroupLieAlgebra 𝓘(𝕜,E) G) :
    mfderiv 𝓘(𝕜,E) 𝓘(𝕜,F) f 1 ⁅v,w⁆ =
      @Bracket.bracket (GroupLieAlgebra 𝓘(𝕜,F) H) (GroupLieAlgebra 𝓘(𝕜,F) H)
        inferInstance (mfderiv 𝓘(𝕜,E) 𝓘(𝕜,F) f 1 v)
          (mfderiv 𝓘(𝕜,E) 𝓘(𝕜,F) f 1 w) := by
  have h := mfderiv_mlieBracket_of_related f hf
    (mulInvariantVectorField v) (mulInvariantVectorField w)
    (mulInvariantVectorField (mfderiv 𝓘(𝕜,E) 𝓘(𝕜,F) f 1 v))
    (mulInvariantVectorField (mfderiv 𝓘(𝕜,E) 𝓘(𝕜,F) f 1 w))
    (mdifferentiable_mulInvariantVectorField v)
    (mdifferentiable_mulInvariantVectorField w)
    (mdifferentiable_mulInvariantVectorField _)
    (mdifferentiable_mulInvariantVectorField _)
    (mfderiv_mulInvariantVectorField f hf v)
    (mfderiv_mulInvariantVectorField f hf w) 1
    ((minSmoothness_monotone (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).trans
      (ENat.LEInfty.out : minSmoothness 𝕜 3 ≤ ∞))
  rw [map_one] at h
  exact h

end
end QuaternionicSymmetry.SmoothLieHomDerivativeBracket
