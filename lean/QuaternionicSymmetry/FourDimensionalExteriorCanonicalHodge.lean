import QuaternionicSymmetry.FourDimensionalExteriorEvaluationBilinear
import Mathlib.Analysis.Normed.Module.Normalize

/-! A candidate canonical real-four-dimensional Hodge operator, defined from
the quaternionic pullbacks of the genuine alternating bilinear evaluation.
The coefficient identity against the existing frame star is proved below. -/

namespace QuaternionicSymmetry.FourDimensionalExteriorCanonicalHodge

open Module
open FourDimensionalExteriorHodge
open FourDimensionalExteriorEvaluationBilinear
open FourDimensionalQuaternionicHodgeFrame
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Nontrivial V]

def bilinearPullback (T : V →ₗ[ℝ] V)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ where
  toFun v := (B (T v)).comp T
  map_add' v w := by ext z; simp
  map_smul' c v := by ext z; simp

@[simp] theorem bilinearPullback_apply (T : V →ₗ[ℝ] V)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (v w : V) :
    bilinearPullback T B v w = B (T v) (T w) := rfl

def quaternionicHodgeBilinear (Q : QuaternionicStructure V)
    (α : TwoForm V) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  (1 / 2 : ℝ) •
    (bilinearOfTwoForm α -
      bilinearPullback Q.I.toLinearEquiv.toLinearMap (bilinearOfTwoForm α) -
      bilinearPullback Q.J.toLinearEquiv.toLinearMap (bilinearOfTwoForm α) -
      bilinearPullback Q.K.toLinearEquiv.toLinearMap (bilinearOfTwoForm α))

theorem quaternionicHodgeBilinear_apply (Q : QuaternionicStructure V)
    (α : TwoForm V) (v w : V) :
    quaternionicHodgeBilinear Q α v w =
      (BilinearExterior.evaluate v w α -
        BilinearExterior.evaluate (Q.I v) (Q.I w) α -
        BilinearExterior.evaluate (Q.J v) (Q.J w) α -
        BilinearExterior.evaluate (Q.K v) (Q.K w) α) / 2 := by
  simp [quaternionicHodgeBilinear, bilinearOfTwoForm_apply,
    bilinearPullback_apply, smul_eq_mul]
  ring

private theorem evaluate_swap (α : TwoForm V) (v w : V) :
    BilinearExterior.evaluate w v α = -BilinearExterior.evaluate v w α := by
  have h := (exteriorPower.ιMulti ℝ 2 (M := V)).map_swap
    ![v,w] (i := 0) (j := 1) (by decide)
  have hp : (![v,w] : Fin 2 → V) ∘ Equiv.swap 0 1 = ![w,v] := by
    funext i
    fin_cases i <;> simp
  rw [hp] at h
  simp [BilinearExterior.evaluate, h]

theorem quaternionicHodgeBilinear_skew (Q : QuaternionicStructure V)
    (α : TwoForm V) (v w : V) :
    quaternionicHodgeBilinear Q α v w =
      -quaternionicHodgeBilinear Q α w v := by
  rw [quaternionicHodgeBilinear_apply,
    quaternionicHodgeBilinear_apply]
  simp only [evaluate_swap α w v,
    evaluate_swap α (Q.I w) (Q.I v),
    evaluate_swap α (Q.J w) (Q.J v),
    evaluate_swap α (Q.K w) (Q.K v)]
  ring

def quaternionicHodgeForm (Q : QuaternionicStructure V)
    (b : Basis (Fin 4) ℝ V) (α : TwoForm V) : TwoForm V :=
  BilinearExterior.ofBilinear b (quaternionicHodgeBilinear Q α)

theorem quaternionicHodgeForm_basis_independent (Q : QuaternionicStructure V)
    (b c : Basis (Fin 4) ℝ V) (α : TwoForm V) :
    quaternionicHodgeForm Q b α = quaternionicHodgeForm Q c α :=
  ExteriorDuality.ofBilinear_basis_independent b c _

theorem evaluate_quaternionicHodgeForm (Q : QuaternionicStructure V)
    (b : Basis (Fin 4) ℝ V) (α : TwoForm V) (v w : V) :
    BilinearExterior.evaluate v w (quaternionicHodgeForm Q b α) =
      quaternionicHodgeBilinear Q α v w :=
  BilinearExterior.evaluate_of_skew b _
    (quaternionicHodgeBilinear_skew Q α) v w

private theorem evaluate_neg_left (α : TwoForm V) (v w : V) :
    BilinearExterior.evaluate (-v) w α = -BilinearExterior.evaluate v w α := by
  rw [← bilinearOfTwoForm_apply, ← bilinearOfTwoForm_apply]
  simp

private theorem evaluate_neg_right (α : TwoForm V) (v w : V) :
    BilinearExterior.evaluate v (-w) α = -BilinearExterior.evaluate v w α := by
  rw [← bilinearOfTwoForm_apply, ← bilinearOfTwoForm_apply]
  simp

private theorem evaluate_self (α : TwoForm V) (v : V) :
    BilinearExterior.evaluate v v α = 0 := by
  have h := evaluate_swap α v v
  linarith

/-- The basis-independent quaternionic averaging formula is literally the
existing exterior Hodge star in every unit quaternionic frame. -/
theorem quaternionicHodgeForm_eq_frameStar (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v : V) (hv : ‖v‖ = 1)
    (α : TwoForm V) :
    quaternionicHodgeForm Q (frameBasis Q hdim v hv).toBasis α =
      frameStar (frameBasis Q hdim v hv) α := by
  let b := frameBasis Q hdim v hv
  apply (coordinateEquiv b.toBasis).injective
  change coordinates b.toBasis (quaternionicHodgeForm Q b.toBasis α) =
    coordinates b.toBasis (frameStar b α)
  rw [coordinates_frameStar]
  dsimp only [b]
  funext k
  fin_cases k <;>
    simp [coordinates, FourDimensionalCoordinateHodge.star,
      evaluate_quaternionicHodgeForm, quaternionicHodgeBilinear_apply,
      frameBasis_apply, Q.I_frame_zero, Q.I_frame_one,
      Q.I_frame_two, Q.I_frame_three,
      Q.J_frame_zero, Q.J_frame_one,
      Q.J_frame_two, Q.J_frame_three,
      Q.K_frame_zero, Q.K_frame_one,
      Q.K_frame_two, Q.K_frame_three,
      evaluate_neg_left, evaluate_neg_right,
      evaluate_swap α (Q.frame v 0) (Q.frame v 1),
      evaluate_swap α (Q.frame v 0) (Q.frame v 2),
      evaluate_swap α (Q.frame v 0) (Q.frame v 3),
      evaluate_swap α (Q.frame v 1) (Q.frame v 2),
      evaluate_swap α (Q.frame v 1) (Q.frame v 3),
      evaluate_swap α (Q.frame v 2) (Q.frame v 3),
      evaluate_self] <;> ring

/-- The genuine exterior Hodge operator is independent of the chosen unit
vector used to make a quaternionic orthonormal frame. -/
theorem frameStar_quaternionicFrame_independent (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v w : V)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    frameStar (frameBasis Q hdim v hv) =
      frameStar (frameBasis Q hdim w hw) := by
  apply LinearMap.ext
  intro α
  rw [← quaternionicHodgeForm_eq_frameStar Q hdim v hv α,
    ← quaternionicHodgeForm_eq_frameStar Q hdim w hw α]
  exact quaternionicHodgeForm_basis_independent Q _ _ α

private def chosenUnit : V := NormedSpace.normalize (Classical.choose (exists_ne (0 : V)))

private theorem chosenUnit_norm : ‖(chosenUnit : V)‖ = 1 :=
  NormedSpace.norm_normalize (Classical.choose_spec (exists_ne (0 : V)))

/-- Canonical pointwise exterior Hodge star in the quaternionic orientation.
The frame-independence theorem above makes the arbitrary normalized vector
used in this definition mathematically irrelevant. -/
def canonicalStar (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) : TwoForm V →ₗ[ℝ] TwoForm V :=
  frameStar (frameBasis Q hdim chosenUnit chosenUnit_norm)

theorem canonicalStar_eq_frameStar (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v : V) (hv : ‖v‖ = 1) :
    canonicalStar Q hdim = frameStar (frameBasis Q hdim v hv) :=
  frameStar_quaternionicFrame_independent Q hdim chosenUnit v chosenUnit_norm hv

end
end QuaternionicSymmetry.FourDimensionalExteriorCanonicalHodge
