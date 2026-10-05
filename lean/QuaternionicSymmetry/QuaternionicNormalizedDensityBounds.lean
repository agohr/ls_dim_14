import QuaternionicSymmetry.QuaternionicNormalizedDensityValues

/-! The complete dimension-eleven/twelve density bounds remain valid when
u is any positive square multiple of the quaternionic fundamental form. -/
namespace QuaternionicSymmetry.QuaternionicNormalizedDensityBounds
open Module MvPolynomial QuaternionicFundamental QuaternionicTracePositivity
open QuaternionicNormalizedDensityValues QuaternionicC12DensityBound
open PrintedProjectionCubicPositivity DimensionElevenTwelveDensity
noncomputable section
set_option synthInstance.maxHeartbeats 200000
variable {ι β V : Type*} [Fintype ι] [Fintype β] [DecidableEq β]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
local instance : CommRing (CE V) := inferInstance
local instance : Algebra ℝ (CE V) := inferInstance
local instance : IsScalarTower ℝ (CE V) (CE V) := inferInstance

theorem density11_lower_bound_normalized
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (Q : QuaternionicStructure V) (b : Basis ι ℝ V)
    (hn : Q.quaternionicDimension = 11) (s : ℝ) (hs : 0 < s)
    (B : β → Matrix (Fin 11 ⊕ Fin 11) (Fin 11 ⊕ Fin 11) ℂ)
    (hB : ∀ a, QuaternionicMatrixModel.HermitianAntiSelfDual (B a))
    (η : β → E V) (hη : ∀ a, η a ∈ HyperholomorphicExterior.formSpace Q b)
    (L : CE V →ₗ[ℝ] ℝ) (hL : 0 ≤ L (embed (V := V) (topForm Q b))) :
    288 * L ((s ^ 2 • embed (V := V) (form Q b)) ^ 11) ≤
      L (aeval (normalizedValues Q b s B η) density11) := by
  have hBs (a : β) : QuaternionicMatrixModel.HermitianAntiSelfDual (s⁻¹ • B a) :=
    (QuaternionicMatrixModel.hermitianAntiSelfDualSubmodule 11).smul_mem _ (hB a)
  have hp := density11_lower_bound hsource Q b hn (fun a => s⁻¹ • B a) hBs η hη L hL
  have hm := mul_le_mul_of_nonneg_left hp (pow_nonneg hs.le 22)
  rw [normalized_density11 Q b s hs.ne' B η, L.map_smul]
  simp only [smul_pow, L.map_smul, smul_eq_mul, ← pow_mul]
  convert hm using 1
  ring

theorem density12_lower_bound_normalized
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (Q : QuaternionicStructure V) (b : Basis ι ℝ V)
    (hn : Q.quaternionicDimension = 12) (s : ℝ) (hs : 0 < s)
    (B : β → Matrix (Fin 12 ⊕ Fin 12) (Fin 12 ⊕ Fin 12) ℂ)
    (hB : ∀ a, QuaternionicMatrixModel.HermitianAntiSelfDual (B a))
    (η : β → E V) (hη : ∀ a, η a ∈ HyperholomorphicExterior.formSpace Q b)
    (L : CE V →ₗ[ℝ] ℝ) (hL : 0 ≤ L (embed (V := V) (topForm Q b))) :
    336 * L ((s ^ 2 • embed (V := V) (form Q b)) ^ 12) ≤
      L (aeval (normalizedValues Q b s B η) density12) := by
  have hBs (a : β) : QuaternionicMatrixModel.HermitianAntiSelfDual (s⁻¹ • B a) :=
    (QuaternionicMatrixModel.hermitianAntiSelfDualSubmodule 12).smul_mem _ (hB a)
  have hp := density12_lower_bound hsource Q b hn (fun a => s⁻¹ • B a) hBs η hη L hL
  have hm := mul_le_mul_of_nonneg_left hp (pow_nonneg hs.le 24)
  rw [normalized_density12 Q b s hs.ne' B η, L.map_smul]
  simp only [smul_pow, L.map_smul, smul_eq_mul, ← pow_mul]
  convert hm using 1
  ring

end
end QuaternionicSymmetry.QuaternionicNormalizedDensityBounds
