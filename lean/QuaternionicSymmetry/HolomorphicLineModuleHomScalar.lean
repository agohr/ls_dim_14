import QuaternionicSymmetry.HolomorphicLineModuleHomLocalScalar

/-! A module-sheaf morphism gives a holomorphic scalar on every actual
intersection of a source and target line chart. Its local multiplication
formula holds on every smaller open subset, independently of the chosen
cover. Off the chart intersection the scalar's zero value is junk data. -/

namespace QuaternionicSymmetry.HolomorphicLineModuleHomScalar

open CategoryTheory TopologicalSpace Manifold Opposite
open HolomorphicLineModuleSheaf HolomorphicLineModuleLocalFree
open HolomorphicLineModuleHomLocalScalar
open scoped Manifold ContDiff
noncomputable section

variable {B : Type} {H F ι κ : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)
  (Z : VectorBundleCore ℂ B ℂ ι) (W : VectorBundleCore ℂ B ℂ κ)
  [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞]

def overlapOpen (i : ι) (a : κ) : Opens B :=
  ⟨Z.baseSet i ∩ W.baseSet a, (Z.isOpen_baseSet i).inter (W.isOpen_baseSet a)⟩

def overlapScalar (φ : moduleSheaf IB Z ⟶ moduleSheaf IB W)
    (i : ι) (a : κ) : Functions IB (overlapOpen Z W i a) :=
  localScalar IB Z W φ i a (overlapOpen Z W i a)
    (fun _ hx => hx.1) (fun _ hx => hx.2)

def scalar (φ : moduleSheaf IB Z ⟶ moduleSheaf IB W)
    (i : ι) (a : κ) (x : B) : ℂ := by
  classical
  exact if hx : x ∈ overlapOpen Z W i a then
    overlapScalar IB Z W φ i a ⟨x, hx⟩ else 0

theorem scalar_of_mem (φ : moduleSheaf IB Z ⟶ moduleSheaf IB W)
    (i : ι) (a : κ) (x : B) (hx : x ∈ Z.baseSet i ∩ W.baseSet a) :
    scalar IB Z W φ i a x = overlapScalar IB Z W φ i a ⟨x, hx⟩ := by
  exact dif_pos (show x ∈ overlapOpen Z W i a from hx)

theorem scalar_holomorphic (φ : moduleSheaf IB Z ⟶ moduleSheaf IB W)
    (i : ι) (a : κ) :
    ContMDiffOn IB 𝓘(ℂ,ℂ) ∞ (scalar IB Z W φ i a)
      (Z.baseSet i ∩ W.baseSet a) := by
  have h : ContMDiff IB 𝓘(ℂ,ℂ) ∞
      (fun x : overlapOpen Z W i a => scalar IB Z W φ i a x.1) := by
    convert (overlapScalar IB Z W φ i a).contMDiff using 1
    funext x
    exact scalar_of_mem IB Z W φ i a x.1 x.2
  intro x hx
  exact (contMDiffAt_subtype_iff.mp (h ⟨x, hx⟩)).contMDiffWithinAt

/-- Restricting the scalar computed on the full chart intersection gives
the scalar computed directly on the smaller open. -/
theorem scalar_eq_localScalar (φ : moduleSheaf IB Z ⟶ moduleSheaf IB W)
    (i : ι) (a : κ) (U : Opens B)
    (hZ : (U : Set B) ⊆ Z.baseSet i) (hW : (U : Set B) ⊆ W.baseSet a)
    (x : U) :
    scalar IB Z W φ i a x.1 = localScalar IB Z W φ i a U hZ hW x := by
  rw [scalar_of_mem IB Z W φ i a x.1 ⟨hZ x.2, hW x.2⟩]
  have hU : U ≤ overlapOpen Z W i a := fun _ hx => ⟨hZ hx, hW hx⟩
  have h := localScalar_restrict IB Z W φ i a (overlapOpen Z W i a) U hU
    (fun _ hx => hx.1) (fun _ hx => hx.2)
  exact (congrArg (fun f : Functions IB U => f x) h).symm

/-- The original module-sheaf morphism is pointwise multiplication by the
constructed scalar in any chosen pair of genuine local line charts. -/
theorem sectionMap_pointwise (φ : moduleSheaf IB Z ⟶ moduleSheaf IB W)
    (i : ι) (a : κ) (U : Opens B)
    (hZ : (U : Set B) ⊆ Z.baseSet i) (hW : (U : Set B) ⊆ W.baseSet a)
    (s : sectionSubmodule IB Z U) (x : U) :
    coordinateLinearEquiv IB W a U hW (sectionMap IB Z W φ U s) x =
      scalar IB Z W φ i a x.1 * coordinateLinearEquiv IB Z i U hZ s x := by
  rw [scalar_eq_localScalar IB Z W φ i a U hZ hW x]
  exact congrArg (fun f : Functions IB U => f x)
    (sectionMap_coordinates IB Z W φ i a U hZ hW s)

end
end QuaternionicSymmetry.HolomorphicLineModuleHomScalar
