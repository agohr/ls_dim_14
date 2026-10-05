import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import QuaternionicSymmetry.OpenMapDifferentialRank
import QuaternionicSymmetry.ManifoldFiniteFiberRank
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-! An open holomorphic map between finite-dimensional manifolds has a
surjective manifold derivative somewhere. -/
namespace QuaternionicSymmetry.ManifoldOpenMapRank
open ManifoldFiniteFiberRank OpenMapDifferentialRank
open scoped Manifold ContDiff Topology
open Filter Function Set Module
noncomputable section

section Charts
variable {E F M N : Type*}
  [TopologicalSpace E] [TopologicalSpace F]
  [TopologicalSpace M] [TopologicalSpace N]
  (e : OpenPartialHomeomorph M E) (e' : OpenPartialHomeomorph N F)
  {f : M → N}

lemma open_in_coordinates (hf : IsOpenMap f) {a : E}
    (ha : a ∈ coordinateDomain e e' (f := f))
    (s : Set E) (hs : s ∈ 𝓝 a) :
    (e' ∘ f ∘ e.symm) '' s ∈ 𝓝 ((e' ∘ f ∘ e.symm) a) := by
  rw [Set.image_comp, Set.image_comp]
  exact e'.image_mem_nhds ha.2 (hf.image_mem_nhds (e.symm.image_mem_nhds ha.1 hs))
end Charts

variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℂ,F) ∞ N]

theorem exists_surjective_mfderiv {f : M → N} (a : M)
    (hf : ContMDiff 𝓘(ℂ,E) 𝓘(ℂ,F) ∞ f) (ho : IsOpenMap f) :
    ∃ y, Function.Surjective (mfderiv 𝓘(ℂ,E) 𝓘(ℂ,F) f y) := by
  let e := chartAt E a
  let e' := chartAt F (f a)
  let U := coordinateDomain e e' (f := f)
  let g := e' ∘ f ∘ e.symm
  have hU : IsOpen U := isOpen_coordinateDomain e e' hf.continuous
  have hne : U.Nonempty := by
    refine ⟨e a, e.map_source (mem_chart_source E a), ?_⟩
    change f (e.symm (e a)) ∈ e'.source
    rw [e.left_inv (mem_chart_source E a)]
    exact mem_chart_source F (f a)
  have hg : ContDiffOn ℂ ∞ g U := by
    simpa [g, U, e, e', coordinateDomain] using (contMDiff_iff.mp hf).2 a (f a)
  obtain ⟨u, hu, hsurj⟩ := exists_surjective_fderiv_on hU hne (hg.restrict_scalars ℝ)
    (fun u hu => open_in_coordinates e e' ho hu)
  have hdc := (hg u hu |>.contDiffAt (hU.mem_nhds hu)).differentiableAt (by simp)
  rw [hdc.fderiv_restrictScalars (𝕜 := ℝ)] at hsurj
  have hsurjC : Surjective (fderiv ℂ g u) := hsurj
  let y := e.symm u
  have hs : MDifferentiableAt 𝓘(ℂ,E) 𝓘(ℂ,E) e.symm u :=
    (mdifferentiable_chart (I := 𝓘(ℂ,E)) a).mdifferentiableAt_symm hu.1
  have ht : MDifferentiableAt 𝓘(ℂ,F) 𝓘(ℂ,F) e' (f y) :=
    (mdifferentiable_chart (I := 𝓘(ℂ,F)) (f a)).mdifferentiableAt hu.2
  have hfy : MDifferentiableAt 𝓘(ℂ,E) 𝓘(ℂ,F) f y := hf.mdifferentiableAt (by simp)
  have hc : mfderiv 𝓘(ℂ,E) 𝓘(ℂ,F) (e' ∘ f ∘ e.symm) u =
      (mfderiv 𝓘(ℂ,F) 𝓘(ℂ,F) e' (f y)).comp
        ((mfderiv 𝓘(ℂ,E) 𝓘(ℂ,F) f y).comp
          (mfderiv 𝓘(ℂ,E) 𝓘(ℂ,E) e.symm u)) := by
    calc
      _ = (mfderiv 𝓘(ℂ,F) 𝓘(ℂ,F) e' (f y)).comp
          (mfderiv 𝓘(ℂ,E) 𝓘(ℂ,F) (f ∘ e.symm) u) := mfderiv_comp u ht (hfy.comp u hs)
      _ = _ := congrArg
        (fun D => (mfderiv 𝓘(ℂ,F) 𝓘(ℂ,F) e' (f y)).comp D)
        (mfderiv_comp u hfy hs)
  rw [← mfderiv_eq_fderiv] at hsurjC
  change Surjective (mfderiv 𝓘(ℂ,E) 𝓘(ℂ,F) (e' ∘ f ∘ e.symm) u) at hsurjC
  rw [hc] at hsurjC
  have hi := (mdifferentiable_chart (I := 𝓘(ℂ,F)) (f a)).mfderiv_injective hu.2
  refine ⟨y, ?_⟩
  intro v
  obtain ⟨w, hw⟩ := hsurjC (mfderiv 𝓘(ℂ,F) 𝓘(ℂ,F) e' (f y) v)
  exact ⟨mfderiv 𝓘(ℂ,E) 𝓘(ℂ,E) e.symm u w, hi hw⟩

end
end QuaternionicSymmetry.ManifoldOpenMapRank
