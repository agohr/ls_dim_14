import QuaternionicSymmetry.HolomorphicLineGauge

/-! A refinement of a holomorphic line's covering, with the same actual
transition cocycle on all overlaps, gives an all-overlap holomorphic gauge.
This includes tensor reassociation and permuted intersection covers. -/

namespace QuaternionicSymmetry.HolomorphicLineGaugeRefinement

open HolomorphicLineGauge HolomorphicLinePowers
open scoped Manifold ContDiff
noncomputable section

variable {B H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [ChartedSpace H B] {IB : ModelWithCorners ℂ F H}
  {ι κ : Type*}

def refinementGauge
    (Z : VectorBundleCore ℂ B ℂ ι) (W : VectorBundleCore ℂ B ℂ κ)
    [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞]
    (f : κ → ι)
    (hBase : ∀ a, W.baseSet a ⊆ Z.baseSet (f a))
    (hTransition : ∀ a b x, x ∈ W.baseSet a ∩ W.baseSet b →
      transitionScalar W a b x = transitionScalar Z (f a) (f b) x) :
    GaugeIso (IB := IB) Z W where
  forward i a x := transitionScalar Z i (f a) x
  backward a i x := transitionScalar Z (f a) i x
  forward_holomorphic i a :=
    ((Z.contMDiffOn_coordChange IB i (f a)).clm_apply contMDiffOn_const).mono
      (by intro x hx; exact ⟨hx.1, hBase a hx.2⟩)
  backward_holomorphic a i :=
    ((Z.contMDiffOn_coordChange IB (f a) i).clm_apply contMDiffOn_const).mono
      (by intro x hx; exact ⟨hBase a hx.1, hx.2⟩)
  forward_compat i j a b x hx := by
    rw [hTransition a b x ⟨hx.1.2, hx.2⟩]
    exact (scalar_comp Z i (f a) (f b) x
      ⟨⟨hx.1.1.1, hBase a hx.1.2⟩, hBase b hx.2⟩).trans
      (scalar_comp Z i j (f b) x
        ⟨⟨hx.1.1.1, hx.1.1.2⟩, hBase b hx.2⟩).symm
  backward_compat a b i j x hx := by
    rw [hTransition a b x ⟨hx.1.1.1, hx.1.1.2⟩]
    exact (scalar_comp Z (f a) i j x
      ⟨⟨hBase a hx.1.1.1, hx.1.2⟩, hx.2⟩).trans
      (scalar_comp Z (f a) (f b) j x
        ⟨⟨hBase a hx.1.1.1, hBase b hx.1.1.2⟩, hx.2⟩).symm
  left_inverse i a x hx := by
    exact (scalar_comp Z i (f a) i x
      ⟨⟨hx.1, hBase a hx.2⟩, hx.1⟩).trans
        (Z.coordChange_self i x hx.1 1)
  right_inverse a i x hx := by
    exact (scalar_comp Z (f a) i (f a) x
      ⟨⟨hBase a hx.1, hx.2⟩, hBase a hx.1⟩).trans
        (Z.coordChange_self (f a) x (hBase a hx.1) 1)

end
end QuaternionicSymmetry.HolomorphicLineGaugeRefinement
