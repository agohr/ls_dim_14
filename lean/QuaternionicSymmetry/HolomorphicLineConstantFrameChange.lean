import QuaternionicSymmetry.HolomorphicLineGauge

/-! Rescaling the local frames of a holomorphic line by fixed nonzero
complex constants gives an explicitly gauge-isomorphic holomorphic core. -/

namespace QuaternionicSymmetry.HolomorphicLineConstantFrameChange

open scoped Manifold ContDiff
open HolomorphicLinePowers HolomorphicLineGauge
noncomputable section

variable {B H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  {IB : ModelWithCorners ℂ F H} {ι : Type*}
  (Z : VectorBundleCore ℂ B ℂ ι) (s : ι → ℂˣ)

def changedCore : VectorBundleCore ℂ B ℂ ι where
  baseSet := Z.baseSet
  isOpen_baseSet := Z.isOpen_baseSet
  indexAt := Z.indexAt
  mem_baseSet_at := Z.mem_baseSet_at
  coordChange i j x := ((s j : ℂ) * transitionScalar Z i j x * (s i : ℂ)⁻¹) •
    ContinuousLinearMap.id ℂ ℂ
  coordChange_self i x hx v := by
    change ((s i : ℂ) * Z.coordChange i i x 1 * (s i : ℂ)⁻¹) * v = v
    rw [Z.coordChange_self i x hx]
    simp
  continuousOn_coordChange i j := by
    have ht : ContinuousOn (transitionScalar Z i j) (Z.baseSet i ∩ Z.baseSet j) :=
      (Z.continuousOn_coordChange i j).clm_apply continuousOn_const
    exact ((continuousOn_const.mul ht).mul continuousOn_const).smul continuousOn_const
  coordChange_comp i j k x hx v := by
    change ((s k : ℂ) * transitionScalar Z j k x * (s j : ℂ)⁻¹) *
      (((s j : ℂ) * transitionScalar Z i j x * (s i : ℂ)⁻¹) * v) =
      ((s k : ℂ) * transitionScalar Z i k x * (s i : ℂ)⁻¹) * v
    calc
      _ = (s k : ℂ) * (transitionScalar Z j k x * transitionScalar Z i j x) *
          (s i : ℂ)⁻¹ * v := by field_simp <;> ring
      _ = _ := by rw [scalar_comp Z i j k x hx]

@[simp] theorem transition_changedCore (i j : ι) (x : B) :
    transitionScalar (changedCore Z s) i j x =
      (s j : ℂ) * transitionScalar Z i j x * (s i : ℂ)⁻¹ := by
  change ((s j : ℂ) * transitionScalar Z i j x * (s i : ℂ)⁻¹) * 1 = _
  exact mul_one _

instance changedCore_holomorphic [Z.IsContMDiff IB ∞] :
    (changedCore Z s).IsContMDiff IB ∞ where
  contMDiffOn_coordChange i j := by
    have ht : ContMDiffOn IB 𝓘(ℂ,ℂ) ∞ (transitionScalar Z i j)
        (Z.baseSet i ∩ Z.baseSet j) :=
      (Z.contMDiffOn_coordChange IB i j).clm_apply contMDiffOn_const
    exact ((contMDiffOn_const.mul ht).mul contMDiffOn_const).smul contMDiffOn_const

def frameChangeGauge [Z.IsContMDiff IB ∞] :
    GaugeIso (IB := IB) Z (changedCore Z s) where
  forward i a x := (s a : ℂ) * transitionScalar Z i a x
  backward a i x := transitionScalar Z a i x * (s a : ℂ)⁻¹
  forward_holomorphic i a :=
    contMDiffOn_const.mul ((Z.contMDiffOn_coordChange IB i a).clm_apply contMDiffOn_const)
  backward_holomorphic a i :=
    ((Z.contMDiffOn_coordChange IB a i).clm_apply contMDiffOn_const).mul contMDiffOn_const
  forward_compat i j a b x hx := by
    rw [transition_changedCore]
    change ((s b : ℂ) * transitionScalar Z a b x * (s a : ℂ)⁻¹) *
      ((s a : ℂ) * transitionScalar Z i a x) =
      ((s b : ℂ) * transitionScalar Z j b x) * transitionScalar Z i j x
    calc
      _ = (s b : ℂ) * (transitionScalar Z a b x * transitionScalar Z i a x) := by
        field_simp <;> ring
      _ = (s b : ℂ) * transitionScalar Z i b x := by
        rw [scalar_comp Z i a b x ⟨⟨hx.1.1.1,hx.1.2⟩,hx.2⟩]
      _ = _ := by
        rw [← scalar_comp Z i j b x ⟨⟨hx.1.1.1,hx.1.1.2⟩,hx.2⟩]
        ring
  backward_compat a b i j x hx := by
    rw [transition_changedCore]
    change transitionScalar Z i j x * (transitionScalar Z a i x * (s a : ℂ)⁻¹) =
      (transitionScalar Z b j x * (s b : ℂ)⁻¹) *
      ((s b : ℂ) * transitionScalar Z a b x * (s a : ℂ)⁻¹)
    calc
      _ = (transitionScalar Z i j x * transitionScalar Z a i x) * (s a : ℂ)⁻¹ := by ring
      _ = transitionScalar Z a j x * (s a : ℂ)⁻¹ := by
        rw [scalar_comp Z a i j x ⟨⟨hx.1.1.1,hx.1.2⟩,hx.2⟩]
      _ = (transitionScalar Z b j x * transitionScalar Z a b x) * (s a : ℂ)⁻¹ := by
        rw [scalar_comp Z a b j x ⟨⟨hx.1.1.1,hx.1.1.2⟩,hx.2⟩]
      _ = _ := by field_simp <;> ring
  left_inverse i a x hx := by
    change (transitionScalar Z a i x * (s a : ℂ)⁻¹) *
      ((s a : ℂ) * transitionScalar Z i a x) = 1
    calc
      _ = transitionScalar Z a i x * transitionScalar Z i a x := by field_simp <;> ring
      _ = _ := (scalar_comp Z i a i x ⟨⟨hx.1,hx.2⟩,hx.1⟩).trans
        (Z.coordChange_self i x hx.1 1)
  right_inverse a i x hx := by
    change ((s a : ℂ) * transitionScalar Z i a x) *
      (transitionScalar Z a i x * (s a : ℂ)⁻¹) = 1
    calc
      _ = transitionScalar Z i a x * transitionScalar Z a i x := by field_simp <;> ring
      _ = _ := (scalar_comp Z a i a x ⟨⟨hx.1,hx.2⟩,hx.1⟩).trans
        (Z.coordChange_self a x hx.1 1)

end
end QuaternionicSymmetry.HolomorphicLineConstantFrameChange
