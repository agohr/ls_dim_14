import QuaternionicSymmetry.CompactSymplecticProjectorFirstColumn

/-! The explicit one-column projector parametrization is continuous in its
ambient finite-dimensional complex vector-space topology. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorColumnContinuity

open CompactSymplecticProjectorFirstColumn
noncomputable section

theorem continuous_firstColumn (n : ℕ) :
    Continuous (firstColumn n) := by
  apply continuous_pi
  intro i
  exact (continuous_apply (Sum.inl 0)).comp
    ((continuous_apply i).comp (continuous_subtype_val.comp continuous_subtype_val))

theorem continuous_pairedColumn (n : ℕ) :
    Continuous (pairedColumn n : (Fin (n + 1) ⊕ Fin (n + 1) → ℂ) →
      (Fin (n + 1) ⊕ Fin (n + 1) → ℂ)) := by
  apply continuous_pi
  intro i
  cases i with
  | inl k => exact (continuous_apply (Sum.inr k)).star.neg
  | inr k => exact (continuous_apply (Sum.inl k)).star

theorem continuous_columnProjector (n : ℕ) :
    Continuous (columnProjector n : (Fin (n + 1) ⊕ Fin (n + 1) → ℂ) →
      Matrix (Fin (n + 1) ⊕ Fin (n + 1))
        (Fin (n + 1) ⊕ Fin (n + 1)) ℂ) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact ((continuous_apply i).mul (continuous_apply j).star).add
    (((continuous_apply i).comp (continuous_pairedColumn n)).mul
      ((continuous_apply j).comp (continuous_pairedColumn n)).star)

end
end QuaternionicSymmetry.CompactSymplecticProjectorColumnContinuity
