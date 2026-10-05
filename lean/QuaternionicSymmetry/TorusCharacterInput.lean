import QuaternionicSymmetry.QuaternionicTorusWeightKernel
import Mathlib.Topology.Algebra.Group.CompactOpen
import Mathlib.Algebra.BigOperators.Pi

/-! The circle-character quantization interface was originally cited from
(Knapp, Lie Groups Beyond an Introduction, second edition, IV.2,
Example following Corollary 4.9, p.241). `TorusCharacterFromMathlib` now proves
this exact contract without a literature premise. Its finite-product extension
to the actual standard torus is proved here. -/
namespace QuaternionicSymmetry.TorusCharacterInput
open ManifoldQuaternionicTorusAction
noncomputable section

/-- BG-T1: every continuous circle character is an integer power.
No torus action, geometric weight or nonvanishing conclusion is included. -/
def CircleCharacterSource : Prop :=
  ∀ χ : Circle →ₜ* Circle, ∃ m : ℤ, ∀ z : Circle, χ z = z ^ m

/-- Coordinate inclusion of a circle in the genuine standard torus. -/
def coordinateCircle (r : ℕ) (i : Fin r) : Circle →ₜ* Torus r where
  toMonoidHom := MonoidHom.mulSingle (fun _ : Fin r => Circle) i
  continuous_toFun := by
    classical
    apply continuous_pi
    intro j
    change Continuous (fun z : Circle => (Pi.mulSingle i z : Torus r) j)
    simp only [Pi.mulSingle_apply]
    split_ifs <;> fun_prop

/-- All continuous characters of a finite standard torus have an integral
weight, by decomposing the torus into its coordinate circles. -/
theorem exists_weightCharacter (hCircle : CircleCharacterSource)
    {r : ℕ} (χ : Torus r →ₜ* Circle) :
    ∃ μ : Fin r → ℤ, ∀ t : Torus r, χ t = weightCharacter μ t := by
  classical
  have hcoord (i : Fin r) :
      ∃ m : ℤ, ∀ z : Circle, χ (Pi.mulSingle i z) = z ^ m :=
    hCircle (χ.comp (coordinateCircle r i))
  choose μ hμ using hcoord
  refine ⟨μ, fun t => ?_⟩
  have ht : (∏ i : Fin r, Pi.mulSingle i (t i)) = t := by
    funext j
    simp [Pi.mulSingle_apply]
  calc
    χ t = χ (∏ i : Fin r, Pi.mulSingle i (t i)) := congrArg χ ht.symm
    _ = ∏ i : Fin r, χ (Pi.mulSingle i (t i)) := map_prod χ _ _
    _ = ∏ i : Fin r, t i ^ μ i := Finset.prod_congr rfl (fun i _ => hμ i (t i))
    _ = weightCharacter μ t := rfl

end
end QuaternionicSymmetry.TorusCharacterInput
