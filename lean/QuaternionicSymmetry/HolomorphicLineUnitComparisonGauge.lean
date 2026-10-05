import QuaternionicSymmetry.HolomorphicLineGaugeUnitComparison
import QuaternionicSymmetry.SheafCechCocycleComparisonSymmetry

/-! Conversely, an actual unit-sheaf Čech coboundary comparison on the
common refinement recovers a genuine holomorphic bundle gauge. Thus this
cocycle equivalence is exactly bundle isomorphism, not just a necessary
condition on pointwise transition values. -/

namespace QuaternionicSymmetry.HolomorphicLineUnitComparisonGauge

open CategoryTheory TopologicalSpace Manifold Opposite
open HolomorphicLineModuleSheaf HolomorphicUnitSheaf
open HolomorphicLinePowers HolomorphicLineGauge HolomorphicLineUnitCocycle
open HolomorphicLineGaugeUnitComparison
open SheafCechOneCocycle SheafCechCocycleComparison
open scoped Manifold ContDiff
noncomputable section

variable {B : Type} {H F ι κ : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)
  {Z : VectorBundleCore ℂ B ℂ ι} {W : VectorBundleCore ℂ B ℂ κ}
  [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞]

abbrev comparisonUnit (e : Comparison (unitCocycle IB Z) (unitCocycle IB W))
    (i : ι) (a : κ) (V : Opens B)
    (hi : V ≤ chartOpen Z i) (ha : V ≤ chartOpen W a) : (Functions IB V)ˣ :=
  (e.value i a V hi ha).toMul

def comparisonScalar (e : Comparison (unitCocycle IB Z) (unitCocycle IB W))
    (i : ι) (a : κ) (x : B) : ℂ := by
  classical
  exact if hx : x ∈ chartOpen Z i ⊓ chartOpen W a then
    (comparisonUnit IB e i a (chartOpen Z i ⊓ chartOpen W a)
      inf_le_left inf_le_right).val ⟨x, hx⟩ else 0

theorem comparisonScalar_of_mem
    (e : Comparison (unitCocycle IB Z) (unitCocycle IB W))
    (i : ι) (a : κ) (x : B) (hx : x ∈ chartOpen Z i ⊓ chartOpen W a) :
    comparisonScalar IB e i a x =
      (comparisonUnit IB e i a (chartOpen Z i ⊓ chartOpen W a)
        inf_le_left inf_le_right).val ⟨x, hx⟩ := dif_pos hx

theorem comparisonScalar_holomorphic
    (e : Comparison (unitCocycle IB Z) (unitCocycle IB W)) (i : ι) (a : κ) :
    ContMDiffOn IB 𝓘(ℂ,ℂ) ∞ (comparisonScalar IB e i a)
      (Z.baseSet i ∩ W.baseSet a) := by
  have h : ContMDiff IB 𝓘(ℂ,ℂ) ∞
      (fun x : (chartOpen Z i ⊓ chartOpen W a : Opens B) =>
        comparisonScalar IB e i a x.1) := by
    convert (comparisonUnit IB e i a (chartOpen Z i ⊓ chartOpen W a)
      inf_le_left inf_le_right).val.contMDiff using 1
    funext x
    exact comparisonScalar_of_mem IB e i a x.1 x.2
  intro x hx
  exact (contMDiffAt_subtype_iff.mp (h ⟨x, hx⟩)).contMDiffWithinAt

theorem comparisonScalar_eq_value
    (e : Comparison (unitCocycle IB Z) (unitCocycle IB W))
    (i : ι) (a : κ) (V : Opens B)
    (hi : V ≤ chartOpen Z i) (ha : V ≤ chartOpen W a) (x : V) :
    comparisonScalar IB e i a x.1 = (comparisonUnit IB e i a V hi ha).val x := by
  rw [comparisonScalar_of_mem IB e i a x.1 ⟨hi x.2, ha x.2⟩]
  have h := e.naturality i a (chartOpen Z i ⊓ chartOpen W a) V
    (le_inf hi ha) inf_le_left inf_le_right
  exact congrArg (fun s : Additive (Functions IB V)ˣ => s.toMul.val x) h

theorem comparisonScalar_compat
    (e : Comparison (unitCocycle IB Z) (unitCocycle IB W))
    (i j : ι) (a b : κ) (x : B)
    (hx : x ∈ Z.baseSet i ∩ Z.baseSet j ∩ W.baseSet a ∩ W.baseSet b) :
    transitionScalar W a b x * comparisonScalar IB e i a x =
      comparisonScalar IB e j b x * transitionScalar Z i j x := by
  let V := ((chartOpen Z i ⊓ chartOpen Z j) ⊓ chartOpen W a) ⊓ chartOpen W b
  have hi : V ≤ chartOpen Z i := inf_le_left.trans (inf_le_left.trans inf_le_left)
  have hj : V ≤ chartOpen Z j := inf_le_left.trans (inf_le_left.trans inf_le_right)
  have ha : V ≤ chartOpen W a := inf_le_left.trans inf_le_right
  have hb : V ≤ chartOpen W b := inf_le_right
  let xx : V := ⟨x, hx⟩
  rw [comparisonScalar_eq_value IB e i a V hi ha xx,
    comparisonScalar_eq_value IB e j b V hj hb xx]
  have h := congrArg (fun s : Additive (Functions IB V)ˣ => s.toMul.val xx)
    (e.compatibility i j a b V hi hj ha hb)
  change transitionScalar Z i j x * (comparisonUnit IB e j b V hj hb).val xx =
    (comparisonUnit IB e i a V hi ha).val xx * transitionScalar W a b x at h
  simpa only [mul_comm] using h.symm

theorem comparisonScalar_inverse
    (e : Comparison (unitCocycle IB Z) (unitCocycle IB W))
    (i : ι) (a : κ) (x : B) (hx : x ∈ Z.baseSet i ∩ W.baseSet a) :
    comparisonScalar IB e.symm a i x * comparisonScalar IB e i a x = 1 := by
  let V := chartOpen Z i ⊓ chartOpen W a
  let xx : V := ⟨x, hx⟩
  rw [comparisonScalar_eq_value IB e.symm a i V inf_le_right inf_le_left xx,
    comparisonScalar_eq_value IB e i a V inf_le_left inf_le_right xx]
  exact congrArg (fun f : Functions IB V => f xx)
    (comparisonUnit IB e i a V inf_le_left inf_le_right).inv_val

def comparisonGauge (e : Comparison (unitCocycle IB Z) (unitCocycle IB W)) :
    GaugeIso (IB := IB) Z W where
  forward := comparisonScalar IB e
  backward := comparisonScalar IB e.symm
  forward_holomorphic := comparisonScalar_holomorphic IB e
  backward_holomorphic := comparisonScalar_holomorphic IB e.symm
  forward_compat := comparisonScalar_compat IB e
  backward_compat := comparisonScalar_compat IB e.symm
  left_inverse := comparisonScalar_inverse IB e
  right_inverse a i x hx := by
    rw [mul_comm]
    exact comparisonScalar_inverse IB e i a x ⟨hx.2, hx.1⟩

/-- Actual bundle gauge-isomorphism is precisely Čech coboundary
equivalence of its genuine unit-sheaf transition cocycle. -/
theorem nonempty_gauge_iff_cocycleComparison :
    Nonempty (GaugeIso (IB := IB) Z W) ↔
      Nonempty (Comparison (unitCocycle IB Z) (unitCocycle IB W)) :=
  ⟨fun ⟨e⟩ => ⟨gaugeComparison IB e⟩, fun ⟨e⟩ => ⟨comparisonGauge IB e⟩⟩

end
end QuaternionicSymmetry.HolomorphicLineUnitComparisonGauge
