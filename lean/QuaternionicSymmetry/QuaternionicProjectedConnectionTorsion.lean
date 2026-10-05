import QuaternionicSymmetry.QuaternionicProjectedConnection

/-! Torsion of the projected connection is the orthogonal projection of
ambient torsion. This uses the exact product identity for the solder form. -/
namespace QuaternionicSymmetry.QuaternionicProjectedConnectionTorsion
open QuaternionicProjectedConnection QuaternionicRangeFrameCoordinates Filter
open scoped ContDiff Topology
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem derivative_product (B : F → F →L[ℝ] E) (T : F → F →L[ℝ] F)
    (A : F → F →L[ℝ] E) (y : F)
    (hB : DifferentiableAt ℝ B y) (hT : DifferentiableAt ℝ T y)
    (hA : A =ᶠ[𝓝 y] fun z => (B z).comp (T z)) (u v : F) :
    fderiv ℝ A y u v = B y (fderiv ℝ T y u v) + fderiv ℝ B y u (T y v) := by
  rw [hA.fderiv_eq,fderiv_clm_comp hB hT]
  rfl

theorem torsion (Γ : F → F →L[ℝ] E →L[ℝ] E) (B : F → F →L[ℝ] E)
    (T : F → F →L[ℝ] F) (A : F → F →L[ℝ] E) (y : F)
    (hB : DifferentiableAt ℝ B y) (hT : DifferentiableAt ℝ T y)
    (horth : ∀ v w, inner ℝ (B y v) (B y w) = inner ℝ v w)
    (hA : A =ᶠ[𝓝 y] fun z => (B z).comp (T z))
    (htorsion : ∀ u v, fderiv ℝ A y u v - fderiv ℝ A y v u +
      Γ y u (A y v) - Γ y v (A y u) = 0) (u v : F) :
    fderiv ℝ T y u v - fderiv ℝ T y v u +
      form Γ B y u (T y v) - form Γ B y v (T y u) = 0 := by
  have h := congrArg (B y).adjoint (htorsion u v)
  rw [derivative_product B T A y hB hT hA,derivative_product B T A y hB hT hA] at h
  simp only [map_sub,map_add,map_zero,adjoint_left_inverse (B y) horth] at h
  have ha : A y = (B y).comp (T y) := hA.eq_of_nhds
  rw [ha] at h
  simp only [form_apply,map_add]
  change (fderiv ℝ T y u v + (B y).adjoint (fderiv ℝ B y u (T y v))) -
    (fderiv ℝ T y v u + (B y).adjoint (fderiv ℝ B y v (T y u))) +
    (B y).adjoint (Γ y u (B y (T y v))) - (B y).adjoint (Γ y v (B y (T y u))) = 0 at h
  linear_combination (norm := module) h

end
end QuaternionicSymmetry.QuaternionicProjectedConnectionTorsion
