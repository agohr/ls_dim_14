import QuaternionicSymmetry.FiniteBilinearBasisWitness
import QuaternionicSymmetry.ProjectorPeirceCurvatureBracket
import QuaternionicSymmetry.CompactSymplecticProjectorAmbientMetric

/-! The matrix commutator of any real-linear tangent immersion derivative is
a real-bilinear map. A noncommuting pair therefore forces a noncommuting
pair in every finite basis, without a special choice of frame. -/

namespace QuaternionicSymmetry.ProjectorCommutatorBilinearBasis

open Matrix
open ProjectorPeirceCurvatureBracket
open FiniteBilinearBasisWitness
open scoped Matrix.Norms.Operator
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ

def commutatorBilinear {E : Type*} [AddCommGroup E] [Module ℝ E]
    (n : ℕ) (T : E →ₗ[ℝ] Mat n) : E →ₗ[ℝ] E →ₗ[ℝ] Mat n := by
  refine {
    toFun := fun u => {
      toFun := fun v => ProjectorPeirceCurvatureBracket.commutator (T u) (T v)
      map_add' := ?_
      map_smul' := ?_
    }
    map_add' := ?_
    map_smul' := ?_
  }
  · intro v w
    simp [ProjectorPeirceCurvatureBracket.commutator, mul_add, add_mul,
      sub_add_sub_comm]
  · intro r v
    simp [ProjectorPeirceCurvatureBracket.commutator, mul_smul_comm,
      smul_mul_assoc, smul_sub]
  · intro u v
    ext w
    simp [ProjectorPeirceCurvatureBracket.commutator, add_mul, mul_add,
      sub_add_sub_comm]
  · intro r u
    ext v
    simp [ProjectorPeirceCurvatureBracket.commutator, smul_mul_assoc,
      mul_smul_comm, smul_sub]

theorem exists_basis_noncommuting {E ι : Type*}
    [AddCommGroup E] [Module ℝ E]
    (n : ℕ) (T : E →ₗ[ℝ] Mat n) (b : Module.Basis ι ℝ E)
    (h : ∃ u v : E,
      ProjectorPeirceCurvatureBracket.commutator (T u) (T v) ≠ 0) :
    ∃ i j : ι,
      ProjectorPeirceCurvatureBracket.commutator
        (T (b i)) (T (b j)) ≠ 0 :=
  exists_basis_pair_nonzero b (commutatorBilinear n T) h

end
end QuaternionicSymmetry.ProjectorCommutatorBilinearBasis
