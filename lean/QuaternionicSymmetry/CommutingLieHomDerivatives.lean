import QuaternionicSymmetry.ProductGroupLieBracket
import Mathlib.GroupTheory.NoncommCoprod

/-! Smooth homomorphisms with pointwise commuting images have commuting
actual tangent images. The proof differentiates their genuine product
homomorphism and uses the genuine cross bracket in the product group. -/

namespace QuaternionicSymmetry.CommutingLieHomDerivatives

open SmoothLieHomDerivativeBracket ProductGroupLieBracket
open scoped Manifold ContDiff
noncomputable section

variable {𝕜 E F V G H K : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V]
  [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [IsManifold 𝓘(𝕜,E) ∞ G] [LieGroup 𝓘(𝕜,E) ∞ G]
  [Group H] [TopologicalSpace H] [ChartedSpace F H]
  [IsManifold 𝓘(𝕜,F) ∞ H] [LieGroup 𝓘(𝕜,F) ∞ H]
  [Group K] [TopologicalSpace K] [ChartedSpace V K]
  [IsManifold 𝓘(𝕜,V) ∞ K] [LieGroup 𝓘(𝕜,V) ∞ K]
  [ENat.LEInfty (minSmoothness 𝕜 3)]

local instance productCharts : ChartedSpace (E × F) (G × H) :=
  prodChartedSpace E G F H

theorem bracket_derivatives_eq_zero (f : G →* K) (g : H →* K)
    (hf : ContMDiff 𝓘(𝕜,E) 𝓘(𝕜,V) ∞ f)
    (hg : ContMDiff 𝓘(𝕜,F) 𝓘(𝕜,V) ∞ g)
    (hComm : ∀ a b, Commute (f a) (g b))
    (v : GroupLieAlgebra 𝓘(𝕜,E) G) (w : GroupLieAlgebra 𝓘(𝕜,F) H) :
    @Bracket.bracket (GroupLieAlgebra 𝓘(𝕜,V) K) (GroupLieAlgebra 𝓘(𝕜,V) K)
      inferInstance (mfderiv 𝓘(𝕜,E) 𝓘(𝕜,V) f 1 v)
        (mfderiv 𝓘(𝕜,F) 𝓘(𝕜,V) g 1 w) = 0 := by
  let p : G × H →* K := f.noncommCoprod g hComm
  have hp : ContMDiff 𝓘(𝕜,E × F) 𝓘(𝕜,V) ∞ p := by
    rw [modelWithCornersSelf_prod]
    exact (hf.comp contMDiff_fst).mul (hg.comp contMDiff_snd)
  let il : G → G × H := fun a => (a,1)
  let ir : H → G × H := fun b => (1,b)
  have hil : ContMDiff 𝓘(𝕜,E) 𝓘(𝕜,E × F) ∞ il := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_id.prodMk contMDiff_const
  have hir : ContMDiff 𝓘(𝕜,F) 𝓘(𝕜,E × F) ∞ ir := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_const.prodMk contMDiff_id
  have hilD : mfderiv 𝓘(𝕜,E) 𝓘(𝕜,E × F) il 1 v = (v,0) := by
    change mfderiv 𝓘(𝕜,E) 𝓘(𝕜,E × F) (fun a : G => (id a,(1 : H))) 1 v = _
    rw [modelWithCornersSelf_prod, mfderiv_prodMk mdifferentiableAt_id mdifferentiableAt_const,
      mfderiv_id, mfderiv_const]
    rfl
  have hirD : mfderiv 𝓘(𝕜,F) 𝓘(𝕜,E × F) ir 1 w = (0,w) := by
    change mfderiv 𝓘(𝕜,F) 𝓘(𝕜,E × F) (fun b : H => ((1 : G),id b)) 1 w = _
    rw [modelWithCornersSelf_prod, mfderiv_prodMk mdifferentiableAt_const mdifferentiableAt_id,
      mfderiv_const, mfderiv_id]
    rfl
  have hl : p ∘ il = f := by
    funext a
    simp [p, il]
  have hr : p ∘ ir = g := by
    funext b
    simp [p, ir]
  have hchainl := mfderiv_comp (1 : G)
    (hp.mdifferentiableAt (by simp)) (hil.mdifferentiableAt (by simp))
  have hchainr := mfderiv_comp (1 : H)
    (hp.mdifferentiableAt (by simp)) (hir.mdifferentiableAt (by simp))
  rw [hl] at hchainl
  rw [hr] at hchainr
  have hDl : mfderiv 𝓘(𝕜,E) 𝓘(𝕜,V) f 1 v =
      mfderiv 𝓘(𝕜,E × F) 𝓘(𝕜,V) p 1 (v,0) := by
    have h := congrArg (fun A : E →L[𝕜] V => A v) hchainl
    change mfderiv 𝓘(𝕜,E) 𝓘(𝕜,V) f 1 v =
      mfderiv 𝓘(𝕜,E × F) 𝓘(𝕜,V) p 1
        (mfderiv 𝓘(𝕜,E) 𝓘(𝕜,E × F) il 1 v) at h
    simpa only [hilD] using h
  have hDr : mfderiv 𝓘(𝕜,F) 𝓘(𝕜,V) g 1 w =
      mfderiv 𝓘(𝕜,E × F) 𝓘(𝕜,V) p 1 (0,w) := by
    have h := congrArg (fun A : F →L[𝕜] V => A w) hchainr
    change mfderiv 𝓘(𝕜,F) 𝓘(𝕜,V) g 1 w =
      mfderiv 𝓘(𝕜,E × F) 𝓘(𝕜,V) p 1
        (mfderiv 𝓘(𝕜,F) 𝓘(𝕜,E × F) ir 1 w) at h
    simpa only [hirD] using h
  have hbracket := mfderiv_map_lie p hp (v,0) (0,w)
  rw [bracket_cross_eq_zero (𝕜 := 𝕜) (E := E) (F := F) (G := G) (H := H),
    map_zero, ← hDl, ← hDr] at hbracket
  exact hbracket.symm

end
end QuaternionicSymmetry.CommutingLieHomDerivatives
