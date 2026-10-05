import QuaternionicSymmetry.ComplexProjectiveAffineCharts

/-! Continuity of the standard affine projective coordinate maps. -/

namespace QuaternionicSymmetry.ComplexProjectiveTopology

open scoped Topology LinearAlgebra.Projectivization

private def nonzeroCoordinateVectors (d : ℕ) (i : Fin (d + 1)) :
    Set {v : Coord d // v ≠ 0} :=
  (Projectivization.mk' ℂ) ⁻¹' affineDomain d i

private def restrictedQuotient (d : ℕ) (i : Fin (d + 1)) :
    nonzeroCoordinateVectors d i → {p : Space d // p ∈ affineDomain d i} :=
  (affineDomain d i).restrictPreimage (Projectivization.mk' ℂ)

private theorem restrictedQuotient_isQuotientMap (d : ℕ) (i : Fin (d + 1)) :
    Topology.IsQuotientMap (restrictedQuotient d i) := by
  exact Topology.IsQuotientMap.restrictPreimage_isOpen
    (isQuotientMap_quotient_mk' : Topology.IsQuotientMap
      (Projectivization.mk' ℂ : {v : Coord d // v ≠ 0} → Space d))
    (isOpen_affineDomain d i)

theorem affineRatio_mk (d : ℕ) (i j : Fin (d + 1))
    (v : Coord d) (hv : v ≠ 0) (hvi : v i ≠ 0) :
    affineRatio d i ⟨Projectivization.mk ℂ v hv,
      (mem_affineDomain_mk d i v hv).2 hvi⟩ j = v j / v i := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  have hj := congrFun ha j
  have hi := congrFun ha i
  change (Projectivization.mk ℂ v hv).rep j /
    (Projectivization.mk ℂ v hv).rep i = v j / v i
  rw [← hj, ← hi]
  change ((a : ℂ) * v j) / ((a : ℂ) * v i) = v j / v i
  field_simp [a.ne_zero, hvi]

private theorem continuous_ratio_comp_restrictedQuotient (d : ℕ)
    (i : Fin (d + 1)) :
    Continuous (affineChart d i ∘ restrictedQuotient d i) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  have hi : ∀ v : nonzeroCoordinateVectors d i, v.1.1 i ≠ 0 := by
    intro v
    exact (mem_affineDomain_mk d i v.1.1 v.1.2).1 v.2
  have hc : Continuous (fun v : nonzeroCoordinateVectors d i => v.1.1) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hratio : Continuous (fun v : nonzeroCoordinateVectors d i => v.1.1 j / v.1.1 i) :=
    ((continuous_apply j).comp hc).div ((continuous_apply i).comp hc) hi
  convert hratio using 1
  funext v
  exact affineRatio_mk d i j v.1.1 v.1.2 (hi v)

/-- A standard affine ratio chart is continuous for the canonical quotient topology. -/
theorem continuous_affineChart (d : ℕ) (i : Fin (d + 1)) :
    Continuous (affineChart d i) := by
  exact (restrictedQuotient_isQuotientMap d i).continuous_iff.mpr
    (continuous_ratio_comp_restrictedQuotient d i)

/-- The inverse affine-to-projective coordinate map is continuous. -/
theorem continuous_affineChartInv (d : ℕ) (i : Fin (d + 1)) :
    Continuous (affineChartInv d i) := by
  apply Continuous.subtype_mk
  have hvector : Continuous
      (fun v : affineHyperplane d i =>
        (⟨v.1, by
          intro hv
          have hi : v.1 i = 1 := v.2
          simp [hv] at hi⟩ : {v : Coord d // v ≠ 0})) := by
    exact Continuous.subtype_mk continuous_subtype_val _
  exact (continuous_mk d).comp hvector

/-- The canonical quotient topology has the expected affine chart homeomorphisms. -/
noncomputable def affineChartHomeomorph (d : ℕ) (i : Fin (d + 1)) :
    {p : Space d // p ∈ affineDomain d i} ≃ₜ affineHyperplane d i where
  toEquiv := affineChartEquiv d i
  continuous_toFun := continuous_affineChart d i
  continuous_invFun := continuous_affineChartInv d i

end QuaternionicSymmetry.ComplexProjectiveTopology
