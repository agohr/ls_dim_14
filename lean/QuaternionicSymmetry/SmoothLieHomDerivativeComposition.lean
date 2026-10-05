import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-! Chain rule at the actual identity for smooth group homomorphisms.
The explicit source and target models prevent geometric applications
from unfolding their full manifold constructions during simplification. -/

namespace QuaternionicSymmetry.SmoothLieHomDerivativeComposition

open scoped Manifold ContDiff
noncomputable section

variable {𝕜 E F V G H K : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [Group H] [TopologicalSpace H] [ChartedSpace F H]
  [Group K] [TopologicalSpace K] [ChartedSpace V K]

theorem mfderiv_comp_hom_one (f : H →* K) (g : G →* H)
    (hf : ContMDiff 𝓘(𝕜,F) 𝓘(𝕜,V) ∞ f)
    (hg : ContMDiff 𝓘(𝕜,E) 𝓘(𝕜,F) ∞ g) :
    mfderiv 𝓘(𝕜,E) 𝓘(𝕜,V) (f.comp g) 1 =
      (mfderiv 𝓘(𝕜,F) 𝓘(𝕜,V) f 1).comp
        (mfderiv 𝓘(𝕜,E) 𝓘(𝕜,F) g 1) := by
  have h := mfderiv_comp (I := 𝓘(𝕜,E)) (I' := 𝓘(𝕜,F))
    (I'' := 𝓘(𝕜,V)) (x := (1 : G))
    (hf.mdifferentiableAt (by simp)) (hg.mdifferentiableAt (by simp))
  rw [map_one] at h
  exact h

end
end QuaternionicSymmetry.SmoothLieHomDerivativeComposition
