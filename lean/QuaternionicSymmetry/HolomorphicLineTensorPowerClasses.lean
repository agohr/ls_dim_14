import QuaternionicSymmetry.HolomorphicLinePowerTensorGauge

/-! The existing scalar-cocycle power is identified with an actual
iteration of tensor products in represented holomorphic core classes. -/

namespace QuaternionicSymmetry.HolomorphicLineTensorPowerClasses

open QuaternionicSymmetry.HolomorphicLineCoreClasses
open QuaternionicSymmetry.HolomorphicLinePowers
open scoped Manifold ContDiff
noncomputable section

universe u

variable {B H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)

/-- The genuine scalar-cocycle `k`-th power as a represented
holomorphic line core. -/
def powerCoreRep (L : LineCore.{u} (B := B) IB) (k : ℕ) :
    LineCore.{u} (B := B) IB := by
  letI := L.holomorphic
  exact {
    Index := L.Index
    core := powerCore L.core k
    holomorphic := inferInstance }

/-- Iterated quotient-class tensor product of one represented line,
starting at its genuine zeroth-power trivial line. The iteration is
defined from `CoreClass.tensor`, not from the target scalar power. -/
def tensorIterate (L : LineCore.{u} (B := B) IB) : ℕ →
    CoreClass.{u} (B := B) IB
  | 0 => Quotient.mk _ (powerCoreRep IB L 0)
  | k + 1 => CoreClass.tensor IB (tensorIterate L k) (Quotient.mk _ L)

/-- Every tensor iteration is identified by an all-overlap holomorphic
gauge with the corresponding scalar-cocycle line power. -/
theorem tensorIterate_eq_power (L : LineCore.{u} (B := B) IB) (k : ℕ) :
    tensorIterate IB L k = Quotient.mk _ (powerCoreRep IB L k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [tensorIterate, ih]
      change Quotient.mk _ ((powerCoreRep IB L k).tensor IB L) =
        Quotient.mk _ (powerCoreRep IB L (k + 1))
      letI := L.holomorphic
      apply Quotient.sound
      exact ⟨HolomorphicLinePowerTensorGauge.powerTensorGauge
        (IB := IB) L.core k⟩

end
end QuaternionicSymmetry.HolomorphicLineTensorPowerClasses
