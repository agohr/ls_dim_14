import QuaternionicSymmetry.ExteriorDuality
import QuaternionicSymmetry.ContinuousWedge
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix

/-! The canonical exterior dual pairing gives genuine continuous alternating
forms on a finite-dimensional normed space. The pairing is bijective and its
degree-two normalization agrees with the existing bilinear exterior model. -/
namespace QuaternionicSymmetry.ExteriorContinuousPairing

open Module
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

abbrev Power (V : Type*) [AddCommGroup V] [Module ℝ V] (n : ℕ) :=
  ExteriorAlgebra.exteriorPower ℝ n (Module.Dual ℝ V)

def toAlternating (n : ℕ) : Power V n →ₗ[ℝ] (V [⋀^Fin n]→ₗ[ℝ] ℝ) :=
  exteriorPower.alternatingMapLinearEquiv.symm.toLinearMap.comp
    (exteriorPower.pairingDual ℝ V n)

omit [FiniteDimensional ℝ V] in
@[simp] theorem toAlternating_apply (n : ℕ) (α : Power V n) (v : Fin n → V) :
    toAlternating n α v = exteriorPower.pairingDual ℝ V n α (exteriorPower.ιMulti ℝ n v) := by
  simp [toAlternating]

omit [FiniteDimensional ℝ V] in
@[simp] theorem toAlternating_decomposable (n : ℕ)
    (f : Fin n → Module.Dual ℝ V) (v : Fin n → V) :
    toAlternating n (exteriorPower.ιMulti ℝ n f) v =
      Matrix.det (fun i j => f j (v i)) := by
  simp only [toAlternating_apply, exteriorPower.pairingDual_ιMulti_ιMulti]
  rfl

theorem continuous_toAlternating (n : ℕ) (α : Power V n) :
    Continuous (toAlternating n α) := by
  classical
  have hα : α ∈ Submodule.span ℝ (Set.range (exteriorPower.ιMulti ℝ n)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hα using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, rfl⟩ := hx
    change Continuous (fun v => toAlternating n (exteriorPower.ιMulti ℝ n f) v)
    simp only [toAlternating_decomposable]
    exact (continuous_pi fun i => continuous_pi fun j =>
      (f j).continuous_of_finiteDimensional.comp (continuous_apply i)).matrix_det
  | zero => simpa using (continuous_const : Continuous (fun _ : Fin n → V => (0 : ℝ)))
  | add x y hx hy ihx ihy => simpa using ihx.add ihy
  | smul r x hx ih => simpa using ih.const_smul r

def toContinuous (n : ℕ) (α : Power V n) : V [⋀^Fin n]→L[ℝ] ℝ :=
  { toAlternating n α with cont := continuous_toAlternating n α }

@[simp] theorem toContinuous_apply (n : ℕ) (α : Power V n) (v : Fin n → V) :
    toContinuous n α v = exteriorPower.pairingDual ℝ V n α (exteriorPower.ιMulti ℝ n v) :=
  toAlternating_apply n α v

def toContinuousLinear (n : ℕ) : Power V n →ₗ[ℝ] (V [⋀^Fin n]→L[ℝ] ℝ) where
  toFun := toContinuous n
  map_add' α β := by ext v; simp
  map_smul' r α := by ext v; simp

@[simp] theorem toContinuous_zero (n : ℕ) : toContinuous (V := V) n 0 = 0 :=
  (toContinuousLinear n).map_zero

@[simp] theorem toContinuous_add (n : ℕ) (α β : Power V n) :
    toContinuous n (α + β) = toContinuous n α + toContinuous n β :=
  (toContinuousLinear n).map_add α β

@[simp] theorem toContinuous_smul (n : ℕ) (r : ℝ) (α : Power V n) :
    toContinuous n (r • α) = r • toContinuous n α :=
  (toContinuousLinear n).map_smul r α

theorem toContinuous_injective (n : ℕ) : Function.Injective (toContinuous (V := V) n) := by
  intro α β h
  apply (ExteriorDuality.pairingDual_bijective (Module.finBasis ℝ V) n).injective
  apply exteriorPower.linearMap_ext
  ext v
  exact congrArg (fun f : V [⋀^Fin n]→L[ℝ] ℝ => f v) h

theorem toContinuous_surjective (n : ℕ) : Function.Surjective (toContinuous (V := V) n) := by
  intro ω
  obtain ⟨α, hα⟩ := (ExteriorDuality.pairingDual_bijective (Module.finBasis ℝ V) n).surjective
    (exteriorPower.alternatingMapLinearEquiv ω.toAlternatingMap)
  refine ⟨α, ?_⟩
  ext v
  simp only [toContinuous_apply, hα, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- The canonical finite-dimensional identification, independent of any basis. -/
def equiv (n : ℕ) : Power V n ≃ₗ[ℝ] (V [⋀^Fin n]→L[ℝ] ℝ) :=
  LinearEquiv.ofBijective (toContinuousLinear n)
    ⟨toContinuous_injective n, toContinuous_surjective n⟩

theorem toContinuous_ofBilinear {ι : Type*} [Fintype ι]
    (b : Basis ι ℝ V) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (v w : V) :
    toContinuous 2 (BilinearExterior.ofBilinear b B) ![v,w] =
      (B v w - B w v) / 2 :=
  BilinearExterior.evaluate_ofBilinear b B v w

end
end QuaternionicSymmetry.ExteriorContinuousPairing
