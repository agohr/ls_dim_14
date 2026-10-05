import QuaternionicSymmetry.HolomorphicLineUnitCocycle
import QuaternionicSymmetry.SheafCechCocycleComparison

/-! A genuine holomorphic bundle isomorphism induces an actual unit-sheaf
Čech coboundary comparison on the common refinement of its two covers. -/

namespace QuaternionicSymmetry.HolomorphicLineGaugeUnitComparison

open CategoryTheory TopologicalSpace Manifold Opposite
open HolomorphicLineModuleSheaf HolomorphicUnitSheaf
open HolomorphicLinePowers HolomorphicLineGauge HolomorphicLineUnitCocycle
open SheafCechOneCocycle SheafCechCocycleComparison
open scoped Manifold ContDiff
noncomputable section

variable {B : Type} {H F ι κ : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)
  {Z : VectorBundleCore ℂ B ℂ ι} {W : VectorBundleCore ℂ B ℂ κ}
  [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞]

def gaugeUnit (e : GaugeIso (IB := IB) Z W) (i : ι) (a : κ)
    (V : Opens B) (hi : V ≤ chartOpen Z i) (ha : V ≤ chartOpen W a) :
    (Functions IB V)ˣ where
  val := ⟨fun x => e.forward i a x.1, contMDiffOn_univ.mp
    ((e.forward_holomorphic i a).comp contMDiff_subtype_val.contMDiffOn
      (fun x _ => ⟨hi x.2, ha x.2⟩))⟩
  inv := ⟨fun x => e.backward a i x.1, contMDiffOn_univ.mp
    ((e.backward_holomorphic a i).comp contMDiff_subtype_val.contMDiffOn
      (fun x _ => ⟨ha x.2, hi x.2⟩))⟩
  val_inv := by
    apply Subtype.ext
    funext x
    exact e.right_inverse a i x.1 ⟨ha x.2, hi x.2⟩
  inv_val := by
    apply Subtype.ext
    funext x
    exact e.left_inverse i a x.1 ⟨hi x.2, ha x.2⟩

def gaugeComparison (e : GaugeIso (IB := IB) Z W) :
    Comparison (unitCocycle IB Z) (unitCocycle IB W) where
  value i a V hi ha := Additive.ofMul (gaugeUnit IB e i a V hi ha)
  naturality i a V T hTV hi ha := by
    apply Units.ext
    rfl
  compatibility i j a b V hi hj ha hb := by
    apply Units.ext
    apply Subtype.ext
    funext x
    change transitionScalar Z i j x.1 * e.forward j b x.1 =
      e.forward i a x.1 * transitionScalar W a b x.1
    simpa only [mul_comm] using
      (e.forward_compat i j a b x.1 ⟨⟨⟨hi x.2, hj x.2⟩, ha x.2⟩, hb x.2⟩).symm

end
end QuaternionicSymmetry.HolomorphicLineGaugeUnitComparison
