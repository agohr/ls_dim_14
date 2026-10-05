import QuaternionicSymmetry.HolomorphicLineModuleHomScalar

/-! Actual overlap, composition and identity laws for the local scalars
extracted from module-sheaf morphisms. The proofs use the morphisms on
genuine smaller open sets and their linearity over holomorphic functions. -/

namespace QuaternionicSymmetry.HolomorphicLineModuleHomScalarLaws

open CategoryTheory TopologicalSpace Manifold Opposite
open HolomorphicLineModuleSheaf HolomorphicLineModuleLocalFree
open HolomorphicLineModuleHomLocalScalar HolomorphicLineModuleHomScalar
open HolomorphicLinePowers
open scoped Manifold ContDiff
noncomputable section

variable {B : Type} {H F ι κ τ : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)
  (Z : VectorBundleCore ℂ B ℂ ι) (W : VectorBundleCore ℂ B ℂ κ)
  [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞]

theorem scalar_compat (φ : moduleSheaf IB Z ⟶ moduleSheaf IB W)
    (i j : ι) (a b : κ) (x : B)
    (hx : x ∈ Z.baseSet i ∩ Z.baseSet j ∩ W.baseSet a ∩ W.baseSet b) :
    transitionScalar W a b x * scalar IB Z W φ i a x =
      scalar IB Z W φ j b x * transitionScalar Z i j x := by
  let U : Opens B := ⟨Z.baseSet i ∩ Z.baseSet j ∩ W.baseSet a ∩ W.baseSet b,
    (((Z.isOpen_baseSet i).inter (Z.isOpen_baseSet j)).inter
      (W.isOpen_baseSet a)).inter (W.isOpen_baseSet b)⟩
  have hi : (U : Set B) ⊆ Z.baseSet i := fun _ h => h.1.1.1
  have hj : (U : Set B) ⊆ Z.baseSet j := fun _ h => h.1.1.2
  have ha : (U : Set B) ⊆ W.baseSet a := fun _ h => h.1.2
  have hb : (U : Set B) ⊆ W.baseSet b := fun _ h => h.2
  let xx : U := ⟨x, hx⟩
  let s := (coordinateLinearEquiv IB Z i U hi).symm 1
  have hsi : coordinateLinearEquiv IB Z i U hi s xx = 1 := by
    change ((coordinateLinearEquiv IB Z i U hi)
      ((coordinateLinearEquiv IB Z i U hi).symm 1)) xx = 1
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hsj : coordinateLinearEquiv IB Z j U hj s xx = transitionScalar Z i j x := by
    rw [coordinate_transition IB Z i j U hi hj s xx, hsi, mul_one]
  have hφa := sectionMap_pointwise IB Z W φ i a U hi ha s xx
  rw [hsi, mul_one] at hφa
  have hφb := sectionMap_pointwise IB Z W φ j b U hj hb s xx
  rw [hsj] at hφb
  calc
    transitionScalar W a b x * scalar IB Z W φ i a x =
        transitionScalar W a b x *
          coordinateLinearEquiv IB W a U ha (sectionMap IB Z W φ U s) xx := by
      rw [hφa]
    _ = coordinateLinearEquiv IB W b U hb (sectionMap IB Z W φ U s) xx :=
      (coordinate_transition IB W a b U ha hb _ xx).symm
    _ = scalar IB Z W φ j b x * transitionScalar Z i j x := hφb

theorem scalar_id_self (i : ι) (x : B) (hx : x ∈ Z.baseSet i) :
    scalar IB Z Z (𝟙 (moduleSheaf IB Z)) i i x = 1 := by
  let U : Opens B := ⟨Z.baseSet i, Z.isOpen_baseSet i⟩
  have hU : (U : Set B) ⊆ Z.baseSet i := fun _ h => h
  rw [scalar_eq_localScalar IB Z Z (𝟙 (moduleSheaf IB Z)) i i U hU hU ⟨x, hx⟩]
  change ((coordinateLinearEquiv IB Z i U hU)
    ((coordinateLinearEquiv IB Z i U hU).symm 1)) ⟨x, hx⟩ = 1
  rw [LinearEquiv.apply_symm_apply]
  rfl

variable (V : VectorBundleCore ℂ B ℂ τ) [V.IsContMDiff IB ∞]

theorem scalar_comp (φ : moduleSheaf IB Z ⟶ moduleSheaf IB W)
    (ψ : moduleSheaf IB W ⟶ moduleSheaf IB V)
    (i : ι) (a : κ) (c : τ) (x : B)
    (hx : x ∈ Z.baseSet i ∩ W.baseSet a ∩ V.baseSet c) :
    scalar IB Z V (φ ≫ ψ) i c x =
      scalar IB W V ψ a c x * scalar IB Z W φ i a x := by
  let U : Opens B := ⟨Z.baseSet i ∩ W.baseSet a ∩ V.baseSet c,
    ((Z.isOpen_baseSet i).inter (W.isOpen_baseSet a)).inter (V.isOpen_baseSet c)⟩
  have hi : (U : Set B) ⊆ Z.baseSet i := fun _ h => h.1.1
  have ha : (U : Set B) ⊆ W.baseSet a := fun _ h => h.1.2
  have hc : (U : Set B) ⊆ V.baseSet c := fun _ h => h.2
  let xx : U := ⟨x, hx⟩
  let s := (coordinateLinearEquiv IB Z i U hi).symm 1
  have hsi : coordinateLinearEquiv IB Z i U hi s xx = 1 := by
    change ((coordinateLinearEquiv IB Z i U hi)
      ((coordinateLinearEquiv IB Z i U hi).symm 1)) xx = 1
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hφ := sectionMap_pointwise IB Z W φ i a U hi ha s xx
  rw [hsi, mul_one] at hφ
  have hψ := sectionMap_pointwise IB W V ψ a c U ha hc
    (sectionMap IB Z W φ U s) xx
  rw [hφ] at hψ
  have hcomp := sectionMap_pointwise IB Z V (φ ≫ ψ) i c U hi hc s xx
  rw [hsi, mul_one] at hcomp
  have heq : sectionMap IB Z V (φ ≫ ψ) U s =
      sectionMap IB W V ψ U (sectionMap IB Z W φ U s) := rfl
  rw [heq] at hcomp
  exact hcomp.symm.trans hψ

end
end QuaternionicSymmetry.HolomorphicLineModuleHomScalarLaws
