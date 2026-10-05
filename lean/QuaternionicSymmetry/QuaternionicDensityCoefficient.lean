import QuaternionicSymmetry.QuaternionicNormalizedDensityBounds
import QuaternionicSymmetry.PositiveRayLowerBound

/-! Pointwise functional density bounds give an actual real coefficient
bound relative to the unscaled quaternionic volume form. -/
namespace QuaternionicSymmetry.QuaternionicDensityCoefficient
open Module QuaternionicFundamental QuaternionicTracePositivity
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype ι]
local instance : CommRing (CE V) := inferInstance
local instance : Algebra ℝ (CE V) := inferInstance
local instance : IsScalarTower ℝ (CE V) (CE V) := inferInstance

theorem exists_coefficient_ge (S : QuaternionicStructure V) (b : Basis ι ℝ V)
    (x : E V) (a s : ℝ)
    (h : ∀ F : CE V →ₗ[ℝ] ℝ, 0 ≤ F (embed (V := V) (topForm S b)) →
      a * F ((s ^ 2 • embed (V := V) (form S b)) ^ S.quaternionicDimension) ≤
        F (embed (V := V) x)) :
    ∃ r : ℝ, a * s ^ (2*S.quaternionicDimension) ≤ r ∧
      x = r • (form S b ^ S.quaternionicDimension) := by
  have hpne : form S b ^ S.quaternionicDimension ≠ 0 := by
    intro hz
    apply QuaternionicSpectralSign.topForm_ne_zero S b
    simp only [topForm, hz, smul_zero]
  have hvne : embed (V := V) (form S b ^ S.quaternionicDimension) ≠ 0 := by
    intro hz
    apply hpne
    apply embed_injective
    simpa only [map_zero] using hz
  obtain ⟨r, hr, he⟩ := PositiveRayLowerBound.exists_coefficient_ge hvne
    (a * s ^ (2*S.quaternionicDimension)) (fun F hF => by
      have htop : 0 ≤ F (embed (V := V) (topForm S b)) :=
        (topForm_nonneg_iff S b (F.comp (embed (V := V)).toLinearMap)).mpr hF
      have hb := h F htop
      rw [smul_pow, F.map_smul] at hb
      simpa only [smul_eq_mul, ← pow_mul, map_pow, mul_assoc] using hb)
  refine ⟨r, hr, embed_injective ?_⟩
  exact he.trans ((embed (V := V)).toLinearMap.map_smul r _).symm

end
end QuaternionicSymmetry.QuaternionicDensityCoefficient
