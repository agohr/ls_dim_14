import QuaternionicSymmetry.SheafCechOneCocycle
import QuaternionicSymmetry.HolomorphicUnitSheaf
import QuaternionicSymmetry.HolomorphicLineGauge

/-! A genuine holomorphic line bundle gives an actual Čech one-cocycle in
the sheaf of holomorphic units. Every section is a ring unit, with its
holomorphic inverse supplied by the reverse bundle coordinate change. -/

namespace QuaternionicSymmetry.HolomorphicLineUnitCocycle

open CategoryTheory TopologicalSpace Manifold Opposite
open HolomorphicLineModuleSheaf HolomorphicUnitSheaf
open HolomorphicLinePowers HolomorphicLineGauge SheafCechOneCocycle
open scoped Manifold ContDiff
noncomputable section

variable {B : Type} {H F ι : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H) (Z : VectorBundleCore ℂ B ℂ ι)
  [Z.IsContMDiff IB ∞]

def chartOpen (i : ι) : Opens B := ⟨Z.baseSet i, Z.isOpen_baseSet i⟩

theorem chartOpen_covers (x : B) : x ∈ chartOpen Z (Z.indexAt x) := Z.mem_baseSet_at x

def transitionFunction (i j : ι) (V : Opens B)
    (hi : V ≤ chartOpen Z i) (hj : V ≤ chartOpen Z j) : Functions IB V := by
  refine ⟨fun x => transitionScalar Z i j x.1, ?_⟩
  have h : ContMDiffOn IB 𝓘(ℂ,ℂ) ∞
      (fun x : V => transitionScalar Z i j x.1) Set.univ :=
    ((Z.contMDiffOn_coordChange IB i j).clm_apply contMDiffOn_const).comp
      contMDiff_subtype_val.contMDiffOn (fun x _ => ⟨hi x.2, hj x.2⟩)
  exact contMDiffOn_univ.mp h

def transitionUnit (i j : ι) (V : Opens B)
    (hi : V ≤ chartOpen Z i) (hj : V ≤ chartOpen Z j) : (Functions IB V)ˣ where
  val := transitionFunction IB Z i j V hi hj
  inv := transitionFunction IB Z j i V hj hi
  val_inv := by
    apply Subtype.ext
    funext x
    change transitionScalar Z i j x.1 * transitionScalar Z j i x.1 = 1
    exact (scalar_comp Z j i j x.1 ⟨⟨hj x.2, hi x.2⟩, hj x.2⟩).trans
      (Z.coordChange_self j x.1 (hj x.2) 1)
  inv_val := by
    apply Subtype.ext
    funext x
    change transitionScalar Z j i x.1 * transitionScalar Z i j x.1 = 1
    exact (scalar_comp Z i j i x.1 ⟨⟨hi x.2, hj x.2⟩, hi x.2⟩).trans
      (Z.coordChange_self i x.1 (hi x.2) 1)

theorem transitionUnit_restrict (i j : ι) (V W : Opens B) (hWV : W ≤ V)
    (hi : V ≤ chartOpen Z i) (hj : V ≤ chartOpen Z j) :
    restrict (unitSheaf IB) hWV (Additive.ofMul (transitionUnit IB Z i j V hi hj)) =
      Additive.ofMul (transitionUnit IB Z i j W (hWV.trans hi) (hWV.trans hj)) := by
  apply Units.ext
  rfl

theorem transitionUnit_cocycle (i j k : ι) (V : Opens B)
    (hi : V ≤ chartOpen Z i) (hj : V ≤ chartOpen Z j) (hk : V ≤ chartOpen Z k) :
    transitionUnit IB Z i j V hi hj * transitionUnit IB Z j k V hj hk =
      transitionUnit IB Z i k V hi hk := by
  apply Units.ext
  apply Subtype.ext
  funext x
  change transitionScalar Z i j x.1 * transitionScalar Z j k x.1 =
    transitionScalar Z i k x.1
  rw [mul_comm]
  exact scalar_comp Z i j k x.1 ⟨⟨hi x.2, hj x.2⟩, hk x.2⟩

def unitCocycle : OneCocycle (unitSheaf (B := B) IB) (chartOpen Z) where
  value i j V hi hj := Additive.ofMul (transitionUnit IB Z i j V hi hj)
  naturality := transitionUnit_restrict IB Z
  cocycle := transitionUnit_cocycle IB Z

end
end QuaternionicSymmetry.HolomorphicLineUnitCocycle
