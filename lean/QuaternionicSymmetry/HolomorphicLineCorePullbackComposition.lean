import QuaternionicSymmetry.HolomorphicLineCorePullback

/-! Literal composition and map-congruence of holomorphic line-core
pullbacks. The equalities hold at the represented core level, including
the transition functions; no extension of sections is asserted. -/

namespace QuaternionicSymmetry.HolomorphicLineCorePullbackComposition

open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open scoped Manifold ContDiff
noncomputable section

universe u
variable {B B' B'' H H' H'' F F' F'' : Type*}
  [TopologicalSpace B] [TopologicalSpace B'] [TopologicalSpace B'']
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup F'] [NormedSpace ℂ F']
  [NormedAddCommGroup F''] [NormedSpace ℂ F'']
  [ChartedSpace H B] [ChartedSpace H' B'] [ChartedSpace H'' B'']
  (IB : ModelWithCorners ℂ F H)
  (IB' : ModelWithCorners ℂ F' H')
  (IB'' : ModelWithCorners ℂ F'' H'')

/-- Pulling back a represented holomorphic line twice is literally the
pullback along the composite base map. -/
theorem pullbackLineCore_comp
    (L : LineCore.{u} (B := B) IB)
    (f : B' → B) (hf : ContMDiff IB' IB ∞ f)
    (g : B'' → B') (hg : ContMDiff IB'' IB' ∞ g) :
    pullbackLineCore IB' IB'' (pullbackLineCore IB IB' L f hf) g hg =
      pullbackLineCore IB IB'' L (f ∘ g) (hf.comp hg) := by
  rfl

/-- Equal holomorphic base maps yield equal represented pullback lines,
regardless of the chosen proofs of holomorphicity. -/
theorem pullbackLineCore_congr
    (L : LineCore.{u} (B := B) IB)
    (f g : B' → B)
    (hf : ContMDiff IB' IB ∞ f) (hg : ContMDiff IB' IB ∞ g)
    (hfg : f = g) :
    pullbackLineCore IB IB' L f hf = pullbackLineCore IB IB' L g hg := by
  subst g
  rfl

/-- Composition followed by equality of base maps identifies the actual
represented line cores, including their holomorphic transition data. -/
theorem pullbackLineCore_comp_congr
    (L : LineCore.{u} (B := B) IB)
    (f : B' → B) (hf : ContMDiff IB' IB ∞ f)
    (g : B'' → B') (hg : ContMDiff IB'' IB' ∞ g)
    (k : B'' → B) (hk : ContMDiff IB'' IB ∞ k)
    (hfg : f ∘ g = k) :
    pullbackLineCore IB' IB'' (pullbackLineCore IB IB' L f hf) g hg =
      pullbackLineCore IB IB'' L k hk := by
  rw [pullbackLineCore_comp]
  exact pullbackLineCore_congr IB IB'' L (f ∘ g) k
    (hf.comp hg) hk hfg

end
end QuaternionicSymmetry.HolomorphicLineCorePullbackComposition
