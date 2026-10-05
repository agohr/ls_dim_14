import QuaternionicSymmetry.HolomorphicLineCoreFiniteSectionsContinuity
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! In finite dimension, continuity of the orbit of each basis section at
each point implies joint continuity of a linear section action. -/

namespace QuaternionicSymmetry.HolomorphicLineCoreBasisOrbitContinuity

open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineCoreFiniteSectionsContinuity
open scoped Manifold ContDiff
noncomputable section
universe u

variable {B H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)
  (L : LineCore.{u} (B := B) IB)

variable [TopologicalSpace (GlobalSections IB L)]
  [IsTopologicalAddGroup (GlobalSections IB L)]
  [ContinuousSMul ℂ (GlobalSections IB L)]
  [T2Space (GlobalSections IB L)]
  [FiniteDimensional ℂ (GlobalSections IB L)]

theorem continuous_action_of_basis_orbits
    {G : Type*} [TopologicalSpace G]
    (T : G → GlobalSections IB L →ₗ[ℂ] GlobalSections IB L)
    (hOrbit : ∀ (i : Fin (Module.finrank ℂ (GlobalSections IB L))) (z : B),
      Continuous (fun g : G => (T g
        ((Module.finBasis ℂ (GlobalSections IB L)) i)) z)) :
    Continuous (fun p : G × GlobalSections IB L => T p.1 p.2) := by
  let b := Module.finBasis ℂ (GlobalSections IB L)
  apply continuous_action_of_evaluation IB L T
  intro z
  have hformula : (fun p : G × GlobalSections IB L => (T p.1 p.2) z) =
      (fun p => ∑ i : Fin (Module.finrank ℂ (GlobalSections IB L)),
        (b.repr p.2 i) • (T p.1 (b i)) z) := by
    funext p
    let ev : GlobalSections IB L →ₗ[ℂ] ℂ := {
      toFun := fun s => s z
      map_add' := by intro s t; rfl
      map_smul' := by intro c s; rfl
    }
    conv_lhs => rw [← b.sum_repr p.2]
    simp only [map_sum, map_smul]
    change ev (∑ i, (b.repr p.2 i) • T p.1 (b i)) = _
    simp only [map_sum, map_smul]
    rfl
  rw [hformula]
  apply continuous_finset_sum
  intro i _
  let coord : GlobalSections IB L →ₗ[ℂ] ℂ := {
    toFun := fun s => b.repr s i
    map_add' := by intro s t; simp
    map_smul' := by intro c s; simp
  }
  have hc : Continuous (fun p : G × GlobalSections IB L => b.repr p.2 i) :=
    coord.continuous_of_finiteDimensional.comp continuous_snd
  have ho : Continuous (fun p : G × GlobalSections IB L => (T p.1 (b i)) z) :=
    (hOrbit i z).comp continuous_fst
  exact hc.smul ho

end
end QuaternionicSymmetry.HolomorphicLineCoreBasisOrbitContinuity
