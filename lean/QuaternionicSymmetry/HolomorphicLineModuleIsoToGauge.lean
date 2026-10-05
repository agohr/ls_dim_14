import QuaternionicSymmetry.HolomorphicLineModuleHomScalarLaws

/-! A genuine isomorphism of holomorphic section module sheaves recovers an
all-overlap holomorphic bundle gauge. Together with the forward construction,
this identifies bundle isomorphism classes with isomorphism classes of their
actual section sheaves. Reconstruction of arbitrary locally free rank-one
sheaves and computation of the Picard group are separate obligations. -/

namespace QuaternionicSymmetry.HolomorphicLineModuleIsoToGauge

open CategoryTheory TopologicalSpace Manifold
open HolomorphicLineModuleSheaf HolomorphicLineModuleGaugeIso
open HolomorphicLineModuleHomScalar HolomorphicLineModuleHomScalarLaws
open HolomorphicLineCoreClasses
open scoped Manifold ContDiff
noncomputable section

variable {B : Type} {H F ι κ : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)
  (Z : VectorBundleCore ℂ B ℂ ι) (W : VectorBundleCore ℂ B ℂ κ)
  [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞]

/-- Recover the bundle gauge from the original sheaf morphisms, by applying
them to the unit frame on each genuine overlap of the two covers. -/
def isoToGauge (e : moduleSheaf IB Z ≅ moduleSheaf IB W) :
    HolomorphicLineGauge.GaugeIso (IB := IB) Z W where
  forward := scalar IB Z W e.hom
  backward := scalar IB W Z e.inv
  forward_holomorphic := scalar_holomorphic IB Z W e.hom
  backward_holomorphic := scalar_holomorphic IB W Z e.inv
  forward_compat := scalar_compat IB Z W e.hom
  backward_compat := scalar_compat IB W Z e.inv
  left_inverse i a x hx := by
    have h := scalar_comp IB Z W Z e.hom e.inv i a i x ⟨hx, hx.1⟩
    rw [e.hom_inv_id, scalar_id_self IB Z i x hx.1] at h
    exact h.symm
  right_inverse a i x hx := by
    have h := scalar_comp IB W Z W e.inv e.hom a i a x ⟨hx, hx.1⟩
    rw [e.inv_hom_id, scalar_id_self IB W a x hx.1] at h
    exact h.symm

theorem nonempty_gauge_iff_moduleSheafIso :
    Nonempty (HolomorphicLineGauge.GaugeIso (IB := IB) Z W) ↔
      Nonempty (moduleSheaf IB Z ≅ moduleSheaf IB W) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨gaugeSheafIso IB Z W e⟩
  · rintro ⟨e⟩
    exact ⟨isoToGauge IB Z W e⟩

theorem nonempty_totalIso_iff_moduleSheafIso :
    Nonempty (HolomorphicLineGaugeFromBundleIso.TotalIso (IB := IB) Z W) ↔
      Nonempty (moduleSheaf IB Z ≅ moduleSheaf IB W) := by
  rw [← HolomorphicLineGaugeToBundleIso.nonempty_gauge_iff_totalIso]
  exact nonempty_gauge_iff_moduleSheafIso IB Z W

universe u
theorem class_eq_iff_moduleSheafIso (L M : LineCore.{u} (B := B) IB) :
    (Quotient.mk _ L : CoreClass IB) = Quotient.mk _ M ↔
      letI := L.holomorphic
      letI := M.holomorphic
      Nonempty (moduleSheaf IB L.core ≅ moduleSheaf IB M.core) := by
  letI := L.holomorphic
  letI := M.holomorphic
  rw [HolomorphicLineCoreClassGroup.class_eq_iff_isomorphic]
  exact nonempty_gauge_iff_moduleSheafIso IB L.core M.core

end
end QuaternionicSymmetry.HolomorphicLineModuleIsoToGauge
