import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The product of two genuine finite-dimensional real manifolds has the
actual product atlas, whose real model dimension is the sum. This is
internal Mathlib geometry, not a source premise about a chosen model. -/

namespace QuaternionicSymmetry.GeneralRealProductManifold

open Manifold
open scoped Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ

private instance productModelNormedAddCommGroup (d e : ℕ) :
    NormedAddCommGroup (ModelProd (RModel d) (RModel e)) :=
  inferInstanceAs (NormedAddCommGroup (RModel d × RModel e))

private instance productModelNormedSpace (d e : ℕ) :
    NormedSpace ℝ (ModelProd (RModel d) (RModel e)) :=
  inferInstanceAs (NormedSpace ℝ (RModel d × RModel e))

theorem exists_product_atlas {A B : Type} [TopologicalSpace A]
    [TopologicalSpace B] (d e : ℕ)
    (a : ChartedSpace (RModel d) A)
    (b : ChartedSpace (RModel e) B)
    (ha : letI := a; IsManifold 𝓘(ℝ, RModel d) ∞ A)
    (hb : letI := b; IsManifold 𝓘(ℝ, RModel e) ∞ B) :
    ∃ c : ChartedSpace (ModelProd (RModel d) (RModel e)) (A × B),
      letI := c
      IsManifold 𝓘(ℝ, ModelProd (RModel d) (RModel e)) ∞ (A × B) := by
  letI : ChartedSpace (RModel d) A := a
  letI : ChartedSpace (RModel e) B := b
  letI : IsManifold 𝓘(ℝ, RModel d) ∞ A := ha
  letI : IsManifold 𝓘(ℝ, RModel e) ∞ B := hb
  let c : ChartedSpace (ModelProd (RModel d) (RModel e)) (A × B) := inferInstance
  refine ⟨c, ?_⟩
  letI : ChartedSpace (ModelProd (RModel d) (RModel e)) (A × B) := c
  letI : ChartedSpace (RModel d × RModel e) (A × B) := c
  change IsManifold 𝓘(ℝ, RModel d × RModel e) ∞ (A × B)
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod A B

theorem finrank_product_model (d e : ℕ) :
    Module.finrank ℝ (ModelProd (RModel d) (RModel e)) = d + e := by
  simpa [ModelProd, Module.finrank_fin_fun] using
    (Module.finrank_prod (R := ℝ) (M := RModel d) (M' := RModel e))

end
end QuaternionicSymmetry.GeneralRealProductManifold
