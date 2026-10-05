import QuaternionicSymmetry.FiniteFiberDifferentialRank
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! Finite-fiber rank arguments in actual manifold charts. -/

namespace QuaternionicSymmetry.ManifoldFiniteFiberRank

open FiniteFiberDifferentialRank
open scoped Manifold ContDiff Topology
open Filter Function Set Module
noncomputable section

section Charts
variable {E F M N : Type*}
  [TopologicalSpace E] [TopologicalSpace F]
  [TopologicalSpace M] [TopologicalSpace N]
  (e : OpenPartialHomeomorph M E) (e' : OpenPartialHomeomorph N F)
  {f : M → N}

def coordinateDomain : Set E := e.target ∩ e.symm ⁻¹' (f ⁻¹' e'.source)

theorem isOpen_coordinateDomain (hf : Continuous f) :
    IsOpen (coordinateDomain e e' (f := f)) :=
  e.symm.continuousOn.isOpen_inter_preimage e.open_target
    (e'.open_source.preimage hf)

theorem isolated_fiber_in_coordinates {a : E}
    (ha : a ∈ coordinateDomain e e' (f := f))
    (hIso : ∀ᶠ y in 𝓝 (e.symm a), f y = f (e.symm a) → y = e.symm a)
    (hf : Continuous f) :
    ∀ᶠ x in 𝓝 a, (e' ∘ f ∘ e.symm) x = (e' ∘ f ∘ e.symm) a → x = a := by
  have hc : ContinuousAt e.symm a := e.symm.continuousAt ha.1
  filter_upwards [(isOpen_coordinateDomain e e' hf).mem_nhds ha,
    hc.eventually hIso] with x hx hi heq
  apply e.symm.injOn hx.1 ha.1
  apply hi
  exact e'.injOn hx.2 ha.2 heq

end Charts

section RealManifolds
variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

/-- A smooth map with locally isolated fibers has a full-rank derivative
in some actual source chart. -/
theorem exists_injective_coordinate_derivative {f : M → N} (a : M)
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f)
    (hIso : ∀ y, ∀ᶠ x in 𝓝 y, f x = f y → x = y) :
    ∃ u ∈ coordinateDomain (chartAt E a) (chartAt F (f a)) (f := f),
      Function.Injective
        (fderiv ℝ (chartAt F (f a) ∘ f ∘ (chartAt E a).symm) u) := by
  have hU := isOpen_coordinateDomain (chartAt E a) (chartAt F (f a)) hf.continuous
  have hne : (coordinateDomain (chartAt E a) (chartAt F (f a)) (f := f)).Nonempty := by
    refine ⟨chartAt E a a, ?_, ?_⟩
    · exact (chartAt E a).map_source (mem_chart_source E a)
    · change f ((chartAt E a).symm (chartAt E a a)) ∈ (chartAt F (f a)).source
      rw [(chartAt E a).left_inv (mem_chart_source E a)]
      exact mem_chart_source F (f a)
  have hg : ContDiffOn ℝ ∞ (chartAt F (f a) ∘ f ∘ (chartAt E a).symm)
      (coordinateDomain (chartAt E a) (chartAt F (f a)) (f := f)) := by
    simpa [coordinateDomain] using (contMDiff_iff.mp hf).2 a (f a)
  exact exists_injective_fderiv_on hU hne hg
    (fun u hu => isolated_fiber_in_coordinates _ _ hu (hIso _) hf.continuous)

/-- Transfer the injective coordinate derivative to the actual manifold
derivative, using the invertible derivatives of the source chart. -/
theorem exists_injective_mfderiv {f : M → N} (a : M)
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f)
    (hIso : ∀ y, ∀ᶠ x in 𝓝 y, f x = f y → x = y) :
    ∃ y, Function.Injective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f y) := by
  obtain ⟨u, hu, hinj⟩ := exists_injective_coordinate_derivative a hf hIso
  let e := chartAt E a
  let e' := chartAt F (f a)
  let y := e.symm u
  have hs : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) e.symm u :=
    (mdifferentiable_chart (I := 𝓘(ℝ,E)) a).mdifferentiableAt_symm hu.1
  have ht : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,F) e' (f y) :=
    (mdifferentiable_chart (I := 𝓘(ℝ,F)) (f a)).mdifferentiableAt hu.2
  have hfy : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,F) f y :=
    hf.mdifferentiableAt (by simp)
  have hc : mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) (e' ∘ f ∘ e.symm) u =
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) e' (f y)).comp
        ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f y).comp
          (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) e.symm u)) := by
    calc
      _ = (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) e' (f y)).comp
          (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) (f ∘ e.symm) u) :=
        mfderiv_comp u ht (hfy.comp u hs)
      _ = _ := congrArg
        (fun D => (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) e' (f y)).comp D)
        (mfderiv_comp u hfy hs)
  rw [← mfderiv_eq_fderiv] at hinj
  change Function.Injective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) (e' ∘ f ∘ e.symm) u) at hinj
  rw [hc] at hinj
  have hinj' : Function.Injective
      ((mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) e' (f y)) ∘
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f y) ∘
          (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) e.symm u)) := hinj
  exact ⟨y, hinj'.of_comp.of_comp_right
    ((mdifferentiable_chart (I := 𝓘(ℝ,E)) a).symm.mfderiv_surjective hu.1)⟩

end RealManifolds

end
end QuaternionicSymmetry.ManifoldFiniteFiberRank
