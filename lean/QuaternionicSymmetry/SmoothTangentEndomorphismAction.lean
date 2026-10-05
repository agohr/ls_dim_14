import QuaternionicSymmetry.SmoothSpatialTangentAction
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-! The actual derivative-conjugation action of a smooth family and its
smooth inverse on the genuine tangent endomorphism bundle. -/

namespace QuaternionicSymmetry.SmoothTangentEndomorphismAction

open Manifold Bundle ContinuousLinearMap
open scoped Manifold ContDiff Topology

noncomputable section

variable {V E G M : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace V G] [IsManifold 𝓘(ℝ, V) ∞ G]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Endomorphisms of the actual tangent fibers, with the usual hom-bundle
topology and smooth atlas, not the topology of a product with raw matrices. -/
abbrev TangentEndomorphismBundle (E M : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] :=
  Bundle.TotalSpace (E →L[ℝ] E)
    (fun x : M => TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E) x)

private theorem coordinates_conjugation
    (x₀ x y₀ y : M)
    (hx : x ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).baseSet)
    (hy : y ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) y₀).baseSet)
    (A B J : E →L[ℝ] E) :
    inCoordinates E (TangentSpace 𝓘(ℝ, E)) E (TangentSpace 𝓘(ℝ, E))
        y₀ y y₀ y (A.comp (J.comp B)) =
      (inCoordinates E (TangentSpace 𝓘(ℝ, E)) E (TangentSpace 𝓘(ℝ, E))
        x₀ x y₀ y A).comp
      ((inCoordinates E (TangentSpace 𝓘(ℝ, E)) E (TangentSpace 𝓘(ℝ, E))
        x₀ x x₀ x J).comp
      (inCoordinates E (TangentSpace 𝓘(ℝ, E)) E (TangentSpace 𝓘(ℝ, E))
        y₀ y x₀ x B)) := by
  rw [inCoordinates_eq hy hy, inCoordinates_eq hx hy,
    inCoordinates_eq hx hx, inCoordinates_eq hy hx]
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]
  rfl

/-- A jointly smooth family and a jointly smooth left inverse induce a
jointly smooth map on actual tangent endomorphisms by the literal spatial
derivative conjugation. In an action, `b (g,x) = a (g⁻¹,x)` supplies the
inverse family. No derivative smoothness is assumed separately. -/
theorem contMDiff_spatialEndomorphismAction
    (a b : G × M → M)
    (ha : ContMDiff (𝓘(ℝ, V).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ a)
    (hb : ContMDiff (𝓘(ℝ, V).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ b)
    (hInv : ∀ g x, b (g, a (g, x)) = x) :
    ContMDiff
      (𝓘(ℝ, V).prod (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] E)))
      (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : G × TangentEndomorphismBundle E M =>
        (⟨a (p.1, p.2.1),
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun x => a (p.1, x)) p.2.1).comp
            (p.2.2.comp
              (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun x => b (p.1, x))
                (a (p.1, p.2.1))))⟩ : TangentEndomorphismBundle E M)) := by
  intro p₀
  let N := G × TangentEndomorphismBundle E M
  let IN := 𝓘(ℝ, V).prod (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] E))
  let x : N → M := fun p => p.2.1
  let y : N → M := fun p => a (p.1, x p)
  let A : N → E →L[ℝ] E := fun p =>
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun t => a (p.1, t)) (x p)
  let B : N → E →L[ℝ] E := fun p =>
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun t => b (p.1, t)) (y p)
  have hx : ContMDiff IN 𝓘(ℝ, E) ∞ x :=
    (contMDiff_proj (IB := 𝓘(ℝ, E)) (n := ∞)
      (E := fun t : M => TangentSpace 𝓘(ℝ, E) t →L[ℝ]
        TangentSpace 𝓘(ℝ, E) t)).comp contMDiff_snd
  have hy : ContMDiff IN 𝓘(ℝ, E) ∞ y :=
    ha.comp (contMDiff_fst.prodMk hx)
  have hAf : ContMDiff (IN.prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : N × M => a (p.1.1, p.2)) :=
    ha.comp ((contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd)
  have hBf : ContMDiff (IN.prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : N × M => b (p.1.1, p.2)) :=
    hb.comp ((contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd)
  have hA := (hAf.contMDiffAt (x := (p₀, x p₀))).mfderiv (fun p t => a (p.1, t)) x
    hx.contMDiffAt (show (∞ : WithTop ℕ∞) + 1 ≤ ∞ by simp)
  have hB := (hBf.contMDiffAt (x := (p₀, y p₀))).mfderiv (fun p t => b (p.1, t)) y
    hy.contMDiffAt (show (∞ : WithTop ℕ∞) + 1 ≤ ∞ by simp)
  have htarget : (fun p : N => b (p.1, y p)) = x := by
    funext p
    exact hInv p.1 (x p)
  change ContMDiffAt IN 𝓘(ℝ, E →L[ℝ] E) ∞
    (inTangentCoordinates 𝓘(ℝ, E) 𝓘(ℝ, E) x y A p₀) p₀ at hA
  change ContMDiffAt IN 𝓘(ℝ, E →L[ℝ] E) ∞
    (inTangentCoordinates 𝓘(ℝ, E) 𝓘(ℝ, E) y
      (fun p : N => b (p.1, y p)) B p₀) p₀ at hB
  rw [htarget] at hB
  have hJ : ContMDiffAt IN (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : N => p.2) p₀ := contMDiffAt_snd
  have hJcoord := (contMDiffAt_hom_bundle (fun p : N => p.2)).mp hJ |>.2
  apply (contMDiffAt_hom_bundle _).mpr
  refine ⟨hy.contMDiffAt, ?_⟩
  have hsmooth := hA.clm_comp (hJcoord.clm_comp hB)
  apply hsmooth.congr_of_eventuallyEq
  have hxn : ∀ᶠ p : N in 𝓝 p₀,
      x p ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (x p₀)).baseSet :=
    hx.continuous.continuousAt.preimage_mem_nhds
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) (x p₀)).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' (x p₀)))
  have hyn : ∀ᶠ p : N in 𝓝 p₀,
      y p ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (y p₀)).baseSet :=
    hy.continuous.continuousAt.preimage_mem_nhds
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) (y p₀)).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' (y p₀)))
  filter_upwards [hxn, hyn] with p hxp hyp
  exact coordinates_conjugation (x p₀) (x p) (y p₀) (y p) hxp hyp
    (A p) (B p) p.2.2

end

end QuaternionicSymmetry.SmoothTangentEndomorphismAction
