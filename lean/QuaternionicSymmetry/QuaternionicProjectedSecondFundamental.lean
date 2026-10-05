import QuaternionicSymmetry.QuaternionicProjectedConnectionTorsion
import QuaternionicSymmetry.QuaternionicSecondFundamentalAlgebra

/-! The normal component of the ambient covariant derivative vanishes for
the explicitly projected quaternionic connection. This argument constructs
total geodesy without assuming a positive geometry on the submanifold. -/
namespace QuaternionicSymmetry.QuaternionicProjectedSecondFundamental
open QuaternionicProjectedConnection QuaternionicProjectedConnectionTorsion
open QuaternionicFrameInjectionSpan QuaternionicSecondFundamentalAlgebra
open QuaternionicRangeFrameCoordinates VectorBundleFrameTransitions Filter
open scoped ContDiff Topology
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

def normalPart (Γ : F → F →L[ℝ] E →L[ℝ] E) (B : F → F →L[ℝ] E)
    (y u v : F) : E :=
  Γ y u (B y v) + fderiv ℝ B y u v - B y (form Γ B y u v)

theorem normalPart_orthogonal (Γ : F → F →L[ℝ] E →L[ℝ] E) (B : F → F →L[ℝ] E)
    (y : F) (horth : ∀ v w, inner ℝ (B y v) (B y w) = inner ℝ v w) (u v w : F) :
    inner ℝ (normalPart Γ B y u v) (B y w) = 0 := by
  rw [normalPart,inner_sub_left,horth,form_apply,ContinuousLinearMap.adjoint_inner_left]
  exact sub_self _

theorem normalPart_defect (S : QuaternionicStructure F) (Q : QuaternionicStructure E)
    (Γ : F → F →L[ℝ] E →L[ℝ] E) (B : F → F →L[ℝ] E) (y : F)
    (hB : DifferentiableAt ℝ B y)
    (hI : ∀ᶠ z in 𝓝 y, ∀ v, B z (S.I v) = Q.I (B z v))
    (hJ : ∀ᶠ z in 𝓝 y, ∀ v, B z (S.J v) = Q.J (B z v))
    (hΓ : ∀ u t, (Γ y u).comp (quaternionicGenerator Q t) -
      (quaternionicGenerator Q t).comp (Γ y u) ∈ quaternionicSpan Q)
    (u v : F) (t : Fin 3) :
    ∃ w, normalPart Γ B y u (quaternionicGenerator S t v) -
      quaternionicGenerator Q t (normalPart Γ B y u v) = B y w := by
  have hi := hI.self_of_nhds
  have hj := hJ.self_of_nhds
  obtain ⟨w,hw⟩ := span_preserves_image S Q (B y) hi hj _ (hΓ u t) v
  refine ⟨w - form Γ B y u (quaternionicGenerator S t v) +
    quaternionicGenerator S t (form Γ B y u v),?_⟩
  change Γ y u (quaternionicGenerator Q t (B y v)) -
    quaternionicGenerator Q t (Γ y u (B y v)) = B y w at hw
  simp only [normalPart,map_add,map_sub]
  rw [generator_intertwines S Q (B y) hi hj,
    derivative_generator S Q B y hB hI hJ,
    generator_intertwines S Q (B y) hi hj]
  linear_combination (norm := module) hw

theorem normalPart_zero_of_symmetric (S : QuaternionicStructure F) (Q : QuaternionicStructure E)
    (Γ : F → F →L[ℝ] E →L[ℝ] E) (B : F → F →L[ℝ] E) (y : F)
    (T : F ≃L[ℝ] F) (hB : DifferentiableAt ℝ B y)
    (horth : ∀ v w, inner ℝ (B y v) (B y w) = inner ℝ v w)
    (hI : ∀ᶠ z in 𝓝 y, ∀ v, B z (S.I v) = Q.I (B z v))
    (hJ : ∀ᶠ z in 𝓝 y, ∀ v, B z (S.J v) = Q.J (B z v))
    (hΓ : ∀ u t, (Γ y u).comp (quaternionicGenerator Q t) -
      (quaternionicGenerator Q t).comp (Γ y u) ∈ quaternionicSpan Q)
    (hsym : ∀ u v, normalPart Γ B y u (T v) = normalPart Γ B y v (T u))
    (u v : F) : normalPart Γ B y u v = 0 := by
  let H : F → F → E := fun a b => normalPart Γ B y (T.symm a) b
  have hHsym (a b : F) : H a b = H b a := by
    simpa only [T.apply_symm_apply] using hsym (T.symm a) (T.symm b)
  have h := secondFundamental_zero Q (B y) H S.I S.J hHsym
    (fun a b c => normalPart_orthogonal Γ B y horth (T.symm a) b c)
    (fun w => (hI.self_of_nhds w).symm) (fun w => (hJ.self_of_nhds w).symm)
    (fun a b => normalPart_defect S Q Γ B y hB hI hJ hΓ (T.symm a) b 0)
    (fun a b => normalPart_defect S Q Γ B y hB hI hJ hΓ (T.symm a) b 1)
    (T u) v
  simpa only [H,T.symm_apply_apply] using h

theorem normalPart_symmetric
    (Γ : F → F →L[ℝ] E →L[ℝ] E) (B : F → F →L[ℝ] E)
    (T : F → F →L[ℝ] F) (A : F → F →L[ℝ] E) (y : F)
    (hB : DifferentiableAt ℝ B y) (hT : DifferentiableAt ℝ T y)
    (horth : ∀ v w, inner ℝ (B y v) (B y w) = inner ℝ v w)
    (hA : A =ᶠ[𝓝 y] fun z => (B z).comp (T z))
    (htorsion : ∀ u v, fderiv ℝ A y u v - fderiv ℝ A y v u +
      Γ y u (A y v) - Γ y v (A y u) = 0) (u v : F) :
    normalPart Γ B y u (T y v) = normalPart Γ B y v (T y u) := by
  have h := htorsion u v
  rw [derivative_product B T A y hB hT hA,derivative_product B T A y hB hT hA,
    hA.eq_of_nhds] at h
  have h' := congrArg (B y) (torsion Γ B T A y hB hT horth hA htorsion u v)
  simp only [map_zero,map_sub,map_add] at h'
  simp only [normalPart]
  change (B y (fderiv ℝ T y u v) + fderiv ℝ B y u (T y v)) -
    (B y (fderiv ℝ T y v u) + fderiv ℝ B y v (T y u)) +
    Γ y u (B y (T y v)) - Γ y v (B y (T y u)) = 0 at h
  linear_combination (norm := module) h - h'

end
end QuaternionicSymmetry.QuaternionicProjectedSecondFundamental
