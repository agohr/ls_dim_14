import QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereLocalCharts
import QuaternionicSymmetry.ManifoldQuaternionicFourNativeBilinearInclusion
import QuaternionicSymmetry.ExteriorDuality

/-! Native continuous alternating two-forms have an actual algebraic exterior
representative, obtained from the canonical bilinear exterior pairing. The
evaluation identity below makes the representation substantive. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeExteriorLiteral

open Module
open FourDimensionalExteriorHodge
open ManifoldQuaternionicFourNativeBilinearInclusion

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

local instance : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E [⋀^Fin 2]→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 2]→L[ℝ] ℝ) := inferInstance

def nativeBilinear (α : E [⋀^Fin 2]→L[ℝ] ℝ) :
    E →ₗ[ℝ] E →ₗ[ℝ] ℝ where
  toFun v := (nativeToBilinearCLM α v).toLinearMap
  map_add' v w := by
    ext u
    simp
  map_smul' c v := by
    ext u
    simp

theorem nativeBilinear_apply (α : E [⋀^Fin 2]→L[ℝ] ℝ)
    (v w : E) : nativeBilinear α v w = α ![v,w] :=
  nativeToBilinearCLM_apply α v w

theorem nativeBilinear_skew (α : E [⋀^Fin 2]→L[ℝ] ℝ)
    (v w : E) : nativeBilinear α v w = -nativeBilinear α w v := by
  rw [nativeBilinear_apply, nativeBilinear_apply]
  have h := α.toAlternatingMap.map_swap ![w,v]
    (i := 0) (j := 1) (by decide)
  have he : ![w,v] ∘ Equiv.swap (0 : Fin 2) 1 = ![v,w] := by
    funext t
    fin_cases t <;> rfl
  simpa only [he] using h

/-- Canonical exterior representative of the native form; the basis choice
is harmless because `ofBilinear_basis_independent` applies. -/
def nativeExterior (b : Basis (Fin 4) ℝ E)
    (α : E [⋀^Fin 2]→L[ℝ] ℝ) : TwoForm E :=
  BilinearExterior.ofBilinear b (nativeBilinear α)

theorem nativeExterior_basis_independent (b c : Basis (Fin 4) ℝ E)
    (α : E [⋀^Fin 2]→L[ℝ] ℝ) :
    nativeExterior b α = nativeExterior c α :=
  ExteriorDuality.ofBilinear_basis_independent b c _

theorem nativeExterior_evaluate (b : Basis (Fin 4) ℝ E)
    (α : E [⋀^Fin 2]→L[ℝ] ℝ) (v w : E) :
    BilinearExterior.evaluate v w (nativeExterior b α) = α ![v,w] := by
  rw [nativeExterior, BilinearExterior.evaluate_of_skew b
    (nativeBilinear α) (nativeBilinear_skew α) v w,
    nativeBilinear_apply]

theorem nativeExterior_injective (b : Basis (Fin 4) ℝ E) :
    Function.Injective (nativeExterior b) := by
  intro α β h
  apply ContinuousAlternatingMap.ext
  intro v
  have hv : v = ![v 0,v 1] := by
    funext t
    fin_cases t <;> rfl
  rw [hv]
  have he := congrArg (BilinearExterior.evaluate (v 0) (v 1)) h
  simpa only [nativeExterior_evaluate] using he

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeExteriorLiteral
