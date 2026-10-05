import QuaternionicSymmetry.HolomorphicLocalLogarithm
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! The actual holomorphic exponential is locally surjective as a
morphism of abelian sheaves on the genuine topology of opens. -/

namespace QuaternionicSymmetry.HolomorphicExponentialLocallySurjective

open CategoryTheory TopologicalSpace Manifold
open HolomorphicLineModuleSheaf HolomorphicUnitSheaf
open HolomorphicExponentialSheaf HolomorphicLocalLogarithm
open scoped Manifold ContDiff
noncomputable section

variable {B : Type} {H F : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)

instance exponential_locallySurjective :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (TopCat.of B))
      (exponential (B := B) IB).val where
  imageSieve_mem {U} s x hx := by
    obtain ⟨V, hVU, hxV, g, hg⟩ := exists_local_log IB U s.toMul ⟨x, hx⟩
    refine ⟨V, homOfLE hVU, ⟨g, ?_⟩, hxV⟩
    apply Units.ext
    apply Subtype.ext
    funext y
    exact hg y

end
end QuaternionicSymmetry.HolomorphicExponentialLocallySurjective
