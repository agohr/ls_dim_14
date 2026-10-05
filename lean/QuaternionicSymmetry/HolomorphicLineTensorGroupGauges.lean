import QuaternionicSymmetry.HolomorphicLineGaugeRefinement

/-! Actual all-overlap holomorphic gauges for tensor associativity,
commutativity, the trivial line, and line/dual cancellation. No equality of
distinct local covers is stipulated. -/

namespace QuaternionicSymmetry.HolomorphicLineTensorGroupGauges

open HolomorphicLineGauge HolomorphicLinePowers HolomorphicLineTensor
open HolomorphicLineIntegerPowers HolomorphicLineGaugeRefinement
open scoped Manifold ContDiff
noncomputable section

universe u
variable {B H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [ChartedSpace H B] {IB : ModelWithCorners ℂ F H}
  {ι κ τ : Type*}

def trivialCore : VectorBundleCore ℂ B ℂ PUnit.{u+1} :=
  trivialVectorBundleCore ℂ B ℂ PUnit.{u+1}

instance trivialCore_isContMDiff : (trivialCore.{u} (B := B)).IsContMDiff IB ∞ where
  contMDiffOn_coordChange _ _ := contMDiffOn_const

def tensorCommGauge
    (Z : VectorBundleCore ℂ B ℂ ι) (W : VectorBundleCore ℂ B ℂ κ)
    [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞] :
    GaugeIso (IB := IB) (tensorCore Z W) (tensorCore W Z) :=
  refinementGauge _ _ Prod.swap
    (by intro a x hx; exact ⟨hx.2, hx.1⟩)
    (by intro a b x _; simp [tensorCore_transitionScalar, mul_comm])

def tensorAssocGauge
    (Z : VectorBundleCore ℂ B ℂ ι) (W : VectorBundleCore ℂ B ℂ κ)
    (V : VectorBundleCore ℂ B ℂ τ)
    [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞] [V.IsContMDiff IB ∞] :
    GaugeIso (IB := IB) (tensorCore (tensorCore Z W) V)
      (tensorCore Z (tensorCore W V)) :=
  refinementGauge _ _ (fun a => ((a.1, a.2.1), a.2.2))
    (by intro a x hx; exact ⟨⟨hx.1, hx.2.1⟩, hx.2.2⟩)
    (by intro a b x _; simp [tensorCore_transitionScalar, mul_assoc])

def tensorTrivialGauge
    (Z : VectorBundleCore ℂ B ℂ ι) [Z.IsContMDiff IB ∞] :
    GaugeIso (IB := IB) (tensorCore Z (trivialCore.{u} (B := B))) Z :=
  refinementGauge _ _ (fun i => (i, PUnit.unit))
    (by intro i x hx; exact ⟨hx, Set.mem_univ x⟩)
    (by
      intro i j x _
      rw [tensorCore_transitionScalar]
      simp [trivialCore, transitionScalar, trivialVectorBundleCore])

def zeroPowerTrivialGauge
    (Z : VectorBundleCore ℂ B ℂ ι) [Z.IsContMDiff IB ∞] :
    GaugeIso (IB := IB) (powerCore Z 0) (trivialCore.{u} (B := B)) where
  forward _ _ _ := 1
  backward _ _ _ := 1
  forward_holomorphic _ _ := contMDiffOn_const
  backward_holomorphic _ _ := contMDiffOn_const
  forward_compat _ _ _ _ _ _ := by
    simp [transitionScalar, powerCore, trivialCore, trivialVectorBundleCore]
  backward_compat _ _ _ _ _ _ := by
    simp [transitionScalar, powerCore, trivialCore, trivialVectorBundleCore]
  left_inverse _ _ _ _ := one_mul 1
  right_inverse _ _ _ _ := one_mul 1

def tensorDualZeroGauge
    (Z : VectorBundleCore ℂ B ℂ ι) [Z.IsContMDiff IB ∞] :
    GaugeIso (IB := IB) (tensorCore Z (dualCore Z)) (powerCore Z 0) :=
  refinementGauge _ _ (fun i => (i, i))
    (by intro i x hx; exact ⟨hx, hx⟩)
    (by
      intro i j x hx
      rw [tensorCore_dual_transitionScalar]
      have h := (scalar_comp Z i j i x ⟨hx, hx.1⟩).trans
        (Z.coordChange_self i x hx.1 1)
      simpa [transitionScalar, powerCore, mul_comm] using h.symm)

def tensorDualTrivialGauge
    (Z : VectorBundleCore ℂ B ℂ ι) [Z.IsContMDiff IB ∞] :
    GaugeIso (IB := IB) (tensorCore Z (dualCore Z)) (trivialCore.{u} (B := B)) :=
  (tensorDualZeroGauge Z).trans (zeroPowerTrivialGauge Z)

end
end QuaternionicSymmetry.HolomorphicLineTensorGroupGauges
