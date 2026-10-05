import QuaternionicSymmetry.QuaternionicStructure
import QuaternionicSymmetry.QuaternionicFrame
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! A quaternionic eigenline from the real self-adjoint spectral theorem.

For a quaternionic skew-adjoint map `A`, the real map `I ∘ A` is symmetric.
A real eigenvector of this map generates an invariant quaternionic line.
-/

namespace QuaternionicSymmetry.QuaternionicStructure

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def symmetricComp (Q : QuaternionicStructure V) (A : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  Q.I.toLinearEquiv.toLinearMap.comp A

theorem symmetricComp_isSymmetric (Q : QuaternionicStructure V) (A : V →ₗ[ℝ] V)
    (hA : A ∈ Q.skewCentralizer) : (Q.symmetricComp A).IsSymmetric := by
  intro v w
  change inner ℝ (Q.I (A v)) w = inner ℝ v (Q.I (A w))
  rw [Q.I_skew, hA.1, neg_neg, hA.2.1]

/-- A nonzero quaternionic Hermitian space contains a unit quaternionic eigenline. -/
theorem exists_unit_eigenline [FiniteDimensional ℝ V] [Nontrivial V]
    (Q : QuaternionicStructure V) (A : V →ₗ[ℝ] V) (hA : A ∈ Q.skewCentralizer) :
    ∃ (lam : ℝ) (v : V), ‖v‖ = 1 ∧ A v = lam • Q.I v := by
  have hSym := Q.symmetricComp_isSymmetric A hA
  have hp : 0 < Module.finrank ℝ V := Module.finrank_pos
  let i : Fin (Module.finrank ℝ V) := ⟨0, hp⟩
  let b := hSym.eigenvectorBasis rfl
  let r := hSym.eigenvalues rfl i
  refine ⟨-r, b i, b.orthonormal.1 i, ?_⟩
  apply Q.I.injective
  have he := hSym.apply_eigenvectorBasis rfl i
  change Q.I (A (b i)) = Q.I ((-r) • Q.I (b i))
  rw [map_smul, Q.I_sq]
  change Q.symmetricComp A (b i) = _
  rw [he]
  simp [r, b]

theorem eigenline_action_I (Q : QuaternionicStructure V) (A : V →ₗ[ℝ] V)
    (hA : A ∈ Q.skewCentralizer) {lam : ℝ} {v : V} (hv : A v = lam • Q.I v) :
    A (Q.I v) = (-lam) • v := by
  rw [hA.2.1, hv, map_smul, Q.I_sq]
  simp

theorem eigenline_action_J (Q : QuaternionicStructure V) (A : V →ₗ[ℝ] V)
    (hA : A ∈ Q.skewCentralizer) {lam : ℝ} {v : V} (hv : A v = lam • Q.I v) :
    A (Q.J v) = (-lam) • Q.K v := by
  rw [hA.2.2, hv, map_smul, Q.J_I_anti]
  simp [K_apply]

theorem eigenline_action_K (Q : QuaternionicStructure V) (A : V →ₗ[ℝ] V)
    (hA : A ∈ Q.skewCentralizer) {lam : ℝ} {v : V} (hv : A v = lam • Q.I v) :
    A (Q.K v) = lam • Q.J v := by
  rw [Q.commute_K A hA.2.1 hA.2.2, hv, map_smul]
  change lam • Q.I (Q.J (Q.I v)) = lam • Q.J v
  rw [Q.J_I_anti, map_neg, Q.I_sq, neg_neg]

theorem eigenline_stable_frameSpan (Q : QuaternionicStructure V) (A : V →ₗ[ℝ] V)
    (hA : A ∈ Q.skewCentralizer) {lam : ℝ} {v : V} (hv : A v = lam • Q.I v)
    {x : V} (hx : x ∈ Q.frameSpan v) : A x ∈ Q.frameSpan v := by
  have hm (i : Fin 4) : Q.frame v i ∈ Q.frameSpan v := Submodule.subset_span ⟨i, rfl⟩
  have hmap : (Q.frameSpan v).map A ≤ Q.frameSpan v := by
    rw [frameSpan, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    fin_cases i
    · change A v ∈ Q.frameSpan v
      rw [hv]
      exact (Q.frameSpan v).smul_mem _ (hm 1)
    · change A (Q.I v) ∈ Q.frameSpan v
      rw [Q.eigenline_action_I A hA hv]
      exact (Q.frameSpan v).smul_mem _ (hm 0)
    · change A (Q.J v) ∈ Q.frameSpan v
      rw [Q.eigenline_action_J A hA hv]
      exact (Q.frameSpan v).smul_mem _ (hm 3)
    · change A (Q.K v) ∈ Q.frameSpan v
      rw [Q.eigenline_action_K A hA hv]
      exact (Q.frameSpan v).smul_mem _ (hm 2)
  exact hmap (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)

theorem eigenline_stable_orthogonal (Q : QuaternionicStructure V) (A : V →ₗ[ℝ] V)
    (hA : A ∈ Q.skewCentralizer) {lam : ℝ} {v : V} (hv : A v = lam • Q.I v)
    {x : V} (hx : x ∈ (Q.frameSpan v).orthogonal) :
    A x ∈ (Q.frameSpan v).orthogonal := by
  rw [Submodule.mem_orthogonal'] at hx ⊢
  intro y hy
  rw [hA.1]
  exact neg_eq_zero.mpr (hx (A y) (Q.eigenline_stable_frameSpan A hA hv hy))

theorem frameSpan_finrank (Q : QuaternionicStructure V) (v : V) (hv : ‖v‖ = 1) :
    Module.finrank ℝ (Q.frameSpan v) = 4 := by
  simpa [frameSpan] using finrank_span_eq_card (Q.frame_linearIndependent v hv)

theorem frameSpan_orthogonal_finrank [FiniteDimensional ℝ V]
    (Q : QuaternionicStructure V) (v : V) (hv : ‖v‖ = 1) :
    Module.finrank ℝ (Q.frameSpan v).orthogonal + 4 = Module.finrank ℝ V := by
  have h := (Q.frameSpan v).finrank_add_finrank_orthogonal
  rw [Q.frameSpan_finrank v hv] at h
  omega

theorem frameSpan_orthogonal_finrank_lt [FiniteDimensional ℝ V]
    (Q : QuaternionicStructure V) (v : V) (hv : ‖v‖ = 1) :
    Module.finrank ℝ (Q.frameSpan v).orthogonal < Module.finrank ℝ V := by
  have h := Q.frameSpan_orthogonal_finrank v hv
  omega

end
end QuaternionicSymmetry.QuaternionicStructure
