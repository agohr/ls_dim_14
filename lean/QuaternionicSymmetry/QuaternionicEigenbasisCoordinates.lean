import QuaternionicSymmetry.QuaternionicEigenbasis

/-! Concrete quaternionic block coordinates of the finite eigenbasis. -/

namespace QuaternionicSymmetry
namespace QuaternionicStructure

noncomputable section

variable {V β : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The standard skew matrix of a skew-centralizer eigenblock. -/
def alphaCoeff : Fin 4 → Fin 4 → ℝ :=
  ![![0, 1, 0, 0], ![-1, 0, 0, 0], ![0, 0, 0, -1], ![0, 0, 1, 0]]

/-- The standard skew matrix of `I` in a quaternionic frame. -/
def omegaICoeff : Fin 4 → Fin 4 → ℝ :=
  ![![0, 1, 0, 0], ![-1, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, -1, 0]]

/-- The standard skew matrix of `J` in a quaternionic frame. -/
def omegaJCoeff : Fin 4 → Fin 4 → ℝ :=
  ![![0, 0, 1, 0], ![0, 0, 0, -1], ![-1, 0, 0, 0], ![0, 1, 0, 0]]

/-- The standard skew matrix of `K` in a quaternionic frame. -/
def omegaKCoeff : Fin 4 → Fin 4 → ℝ :=
  ![![0, 0, 0, 1], ![0, 0, 1, 0], ![0, -1, 0, 0], ![-1, 0, 0, 0]]

theorem I_frame (Q : QuaternionicStructure V) (v : V) (k : Fin 4) :
    Q.I (Q.frame v k) = ![Q.frame v 1, -Q.frame v 0, Q.frame v 3, -Q.frame v 2] k := by
  fin_cases k <;> simp [frame, K_apply, Q.I_sq]

theorem J_frame (Q : QuaternionicStructure V) (v : V) (k : Fin 4) :
    Q.J (Q.frame v k) = ![Q.frame v 2, -Q.frame v 3, -Q.frame v 0, Q.frame v 1] k := by
  fin_cases k <;> simp [frame, K_apply, Q.J_I_anti, Q.J_sq]

theorem K_frame (Q : QuaternionicStructure V) (v : V) (k : Fin 4) :
    Q.K (Q.frame v k) = ![Q.frame v 3, Q.frame v 2, -Q.frame v 1, -Q.frame v 0] k := by
  fin_cases k <;> simp [frame, K_apply, Q.J_I_anti, Q.I_sq, Q.J_sq]

theorem A_frame (Q : QuaternionicStructure V) (A : V →ₗ[ℝ] V)
    (hA : A ∈ Q.skewCentralizer) {lam : ℝ} {v : V}
    (hv : A v = lam • Q.I v) (k : Fin 4) :
    A (Q.frame v k) =
      ![lam • Q.frame v 1, -lam • Q.frame v 0,
        -lam • Q.frame v 3, lam • Q.frame v 2] k := by
  fin_cases k
  · exact hv
  · simpa using Q.eigenline_action_I A hA hv
  · simpa using Q.eigenline_action_J A hA hv
  · simpa using Q.eigenline_action_K A hA hv

theorem I_frame_zero (Q : QuaternionicStructure V) (v : V) :
    Q.I (Q.frame v 0) = Q.frame v 1 := by simpa using I_frame Q v 0
theorem I_frame_one (Q : QuaternionicStructure V) (v : V) :
    Q.I (Q.frame v 1) = -Q.frame v 0 := by simpa using I_frame Q v 1
theorem I_frame_two (Q : QuaternionicStructure V) (v : V) :
    Q.I (Q.frame v 2) = Q.frame v 3 := by simpa using I_frame Q v 2
theorem I_frame_three (Q : QuaternionicStructure V) (v : V) :
    Q.I (Q.frame v 3) = -Q.frame v 2 := by simpa using I_frame Q v 3

theorem J_frame_zero (Q : QuaternionicStructure V) (v : V) :
    Q.J (Q.frame v 0) = Q.frame v 2 := by simpa using J_frame Q v 0
theorem J_frame_one (Q : QuaternionicStructure V) (v : V) :
    Q.J (Q.frame v 1) = -Q.frame v 3 := by simpa using J_frame Q v 1
theorem J_frame_two (Q : QuaternionicStructure V) (v : V) :
    Q.J (Q.frame v 2) = -Q.frame v 0 := by simpa using J_frame Q v 2
theorem J_frame_three (Q : QuaternionicStructure V) (v : V) :
    Q.J (Q.frame v 3) = Q.frame v 1 := by simpa using J_frame Q v 3

theorem K_frame_zero (Q : QuaternionicStructure V) (v : V) :
    Q.K (Q.frame v 0) = Q.frame v 3 := by simpa using K_frame Q v 0
theorem K_frame_one (Q : QuaternionicStructure V) (v : V) :
    Q.K (Q.frame v 1) = Q.frame v 2 := by simpa using K_frame Q v 1
theorem K_frame_two (Q : QuaternionicStructure V) (v : V) :
    Q.K (Q.frame v 2) = -Q.frame v 1 := by simpa using K_frame Q v 2
theorem K_frame_three (Q : QuaternionicStructure V) (v : V) :
    Q.K (Q.frame v 3) = -Q.frame v 0 := by simpa using K_frame Q v 3

theorem A_frame_zero (Q : QuaternionicStructure V) (A : V →ₗ[ℝ] V)
    (hA : A ∈ Q.skewCentralizer) {lam : ℝ} {v : V} (hv : A v = lam • Q.I v) :
    A (Q.frame v 0) = lam • Q.frame v 1 := by simpa using A_frame Q A hA hv 0
theorem A_frame_one (Q : QuaternionicStructure V) (A : V →ₗ[ℝ] V)
    (hA : A ∈ Q.skewCentralizer) {lam : ℝ} {v : V} (hv : A v = lam • Q.I v) :
    A (Q.frame v 1) = -lam • Q.frame v 0 := by simpa using A_frame Q A hA hv 1
theorem A_frame_two (Q : QuaternionicStructure V) (A : V →ₗ[ℝ] V)
    (hA : A ∈ Q.skewCentralizer) {lam : ℝ} {v : V} (hv : A v = lam • Q.I v) :
    A (Q.frame v 2) = -lam • Q.frame v 3 := by simpa using A_frame Q A hA hv 2
theorem A_frame_three (Q : QuaternionicStructure V) (A : V →ₗ[ℝ] V)
    (hA : A ∈ Q.skewCentralizer) {lam : ℝ} {v : V} (hv : A v = lam • Q.I v) :
    A (Q.frame v 3) = lam • Q.frame v 2 := by simpa using A_frame Q A hA hv 3

/-- The actual orthonormal basis associated to a spanning quaternionic eigenfamily. -/
noncomputable def eigenOrthonormalBasis [Fintype β] (Q : QuaternionicStructure V) (v : β → V)
    (horth : Orthonormal ℝ (fun p : β × Fin 4 => Q.frame (v p.1) p.2))
    (hspan : Submodule.span ℝ (Set.range (fun p : β × Fin 4 => Q.frame (v p.1) p.2)) = ⊤) :
    OrthonormalBasis (β × Fin 4) ℝ V :=
  OrthonormalBasis.mk horth hspan.ge

@[simp] theorem eigenOrthonormalBasis_apply [Fintype β] (Q : QuaternionicStructure V) (v : β → V)
    (horth : Orthonormal ℝ (fun p : β × Fin 4 => Q.frame (v p.1) p.2))
    (hspan : Submodule.span ℝ (Set.range (fun p : β × Fin 4 => Q.frame (v p.1) p.2)) = ⊤)
    (p : β × Fin 4) : eigenOrthonormalBasis Q v horth hspan p = Q.frame (v p.1) p.2 := by
  simp [eigenOrthonormalBasis]

/-- The eigenbasis theorem supplied as actual orthonormal-basis data. -/
theorem exists_eigenOrthonormalBasis [FiniteDimensional ℝ V]
    (Q : QuaternionicStructure V) (A : V →ₗ[ℝ] V) (hA : A ∈ Q.skewCentralizer) :
    ∃ (β : Type) (_ : Fintype β) (vals : β → ℝ) (v : β → V)
      (b : OrthonormalBasis (β × Fin 4) ℝ V),
      (∀ p, b p = Q.frame (v p.1) p.2) ∧
      (∀ j, A (v j) = vals j • Q.I (v j)) := by
  obtain ⟨β, hβ, vals, v, horth, hspan, heig⟩ := Q.exists_eigenbasis A hA
  letI : Finite β := hβ
  letI : Fintype β := Fintype.ofFinite β
  letI : DecidableEq β := Classical.decEq β
  refine ⟨β, inferInstance, vals, v, eigenOrthonormalBasis Q v horth hspan, ?_, heig⟩
  intro p
  exact eigenOrthonormalBasis_apply Q v horth hspan p

private theorem frame_inner [DecidableEq β] (Q : QuaternionicStructure V) (v : β → V)
    (horth : Orthonormal ℝ (fun p : β × Fin 4 => Q.frame (v p.1) p.2))
    (j l : β) (k m : Fin 4) :
    inner ℝ (Q.frame (v j) k) (Q.frame (v l) m) =
      if (j, k) = (l, m) then 1 else 0 :=
  orthonormal_iff_ite.mp horth (j, k) (l, m)

theorem I_coordinate [DecidableEq β] (Q : QuaternionicStructure V) (v : β → V)
    (horth : Orthonormal ℝ (fun p : β × Fin 4 => Q.frame (v p.1) p.2))
    (j l : β) (k m : Fin 4) :
    inner ℝ (Q.I (Q.frame (v j) k)) (Q.frame (v l) m) =
      if j = l then omegaICoeff k m else 0 := by
  have hinter (r s : β) (a b : Fin 4) := frame_inner Q v horth r s a b
  have hnorm (r : β) (a : Fin 4) : ‖Q.frame (v r) a‖ = 1 := horth.norm_eq_one (r, a)
  fin_cases k <;> fin_cases m <;> by_cases h : j = l <;>
    simp [I_frame, omegaICoeff, hinter, hnorm, h]

theorem J_coordinate [DecidableEq β] (Q : QuaternionicStructure V) (v : β → V)
    (horth : Orthonormal ℝ (fun p : β × Fin 4 => Q.frame (v p.1) p.2))
    (j l : β) (k m : Fin 4) :
    inner ℝ (Q.J (Q.frame (v j) k)) (Q.frame (v l) m) =
      if j = l then omegaJCoeff k m else 0 := by
  have hinter (r s : β) (a b : Fin 4) := frame_inner Q v horth r s a b
  have hnorm (r : β) (a : Fin 4) : ‖Q.frame (v r) a‖ = 1 := horth.norm_eq_one (r, a)
  fin_cases k <;> fin_cases m <;> by_cases h : j = l <;>
    simp [J_frame, omegaJCoeff, hinter, hnorm, h]

theorem K_coordinate [DecidableEq β] (Q : QuaternionicStructure V) (v : β → V)
    (horth : Orthonormal ℝ (fun p : β × Fin 4 => Q.frame (v p.1) p.2))
    (j l : β) (k m : Fin 4) :
    inner ℝ (Q.K (Q.frame (v j) k)) (Q.frame (v l) m) =
      if j = l then omegaKCoeff k m else 0 := by
  have hinter (r s : β) (a b : Fin 4) := frame_inner Q v horth r s a b
  have hnorm (r : β) (a : Fin 4) : ‖Q.frame (v r) a‖ = 1 := horth.norm_eq_one (r, a)
  rw [K_frame Q (v j) k]
  fin_cases k <;> fin_cases m <;> by_cases h : j = l <;>
    simp [omegaKCoeff, hinter, hnorm, h]

theorem A_coordinate [DecidableEq β] (Q : QuaternionicStructure V) (A : V →ₗ[ℝ] V)
    (hA : A ∈ Q.skewCentralizer) (vals : β → ℝ) (v : β → V)
    (horth : Orthonormal ℝ (fun p : β × Fin 4 => Q.frame (v p.1) p.2))
    (heig : ∀ j, A (v j) = vals j • Q.I (v j))
    (j l : β) (k m : Fin 4) :
    inner ℝ (A (Q.frame (v j) k)) (Q.frame (v l) m) =
      if j = l then vals j * alphaCoeff k m else 0 := by
  have hinter (r s : β) (a b : Fin 4) := frame_inner Q v horth r s a b
  have hnorm (r : β) (a : Fin 4) : ‖Q.frame (v r) a‖ = 1 := horth.norm_eq_one (r, a)
  rw [A_frame Q A hA (heig j) k]
  fin_cases k <;> fin_cases m <;> by_cases h : j = l <;>
    simp [real_inner_smul_left, alphaCoeff, hinter, hnorm, h]

theorem I_eigenOrthonormalBasis_coordinate [Fintype β] [DecidableEq β]
    (Q : QuaternionicStructure V) (v : β → V)
    (horth : Orthonormal ℝ (fun p : β × Fin 4 => Q.frame (v p.1) p.2))
    (hspan : Submodule.span ℝ (Set.range (fun p : β × Fin 4 => Q.frame (v p.1) p.2)) = ⊤)
    (j l : β) (k m : Fin 4) :
    inner ℝ (Q.I (eigenOrthonormalBasis Q v horth hspan (j, k)))
      (eigenOrthonormalBasis Q v horth hspan (l, m)) =
      if j = l then omegaICoeff k m else 0 := by
  simpa only [eigenOrthonormalBasis_apply] using I_coordinate Q v horth j l k m

theorem J_eigenOrthonormalBasis_coordinate [Fintype β] [DecidableEq β]
    (Q : QuaternionicStructure V) (v : β → V)
    (horth : Orthonormal ℝ (fun p : β × Fin 4 => Q.frame (v p.1) p.2))
    (hspan : Submodule.span ℝ (Set.range (fun p : β × Fin 4 => Q.frame (v p.1) p.2)) = ⊤)
    (j l : β) (k m : Fin 4) :
    inner ℝ (Q.J (eigenOrthonormalBasis Q v horth hspan (j, k)))
      (eigenOrthonormalBasis Q v horth hspan (l, m)) =
      if j = l then omegaJCoeff k m else 0 := by
  simpa only [eigenOrthonormalBasis_apply] using J_coordinate Q v horth j l k m

theorem K_eigenOrthonormalBasis_coordinate [Fintype β] [DecidableEq β]
    (Q : QuaternionicStructure V) (v : β → V)
    (horth : Orthonormal ℝ (fun p : β × Fin 4 => Q.frame (v p.1) p.2))
    (hspan : Submodule.span ℝ (Set.range (fun p : β × Fin 4 => Q.frame (v p.1) p.2)) = ⊤)
    (j l : β) (k m : Fin 4) :
    inner ℝ (Q.K (eigenOrthonormalBasis Q v horth hspan (j, k)))
      (eigenOrthonormalBasis Q v horth hspan (l, m)) =
      if j = l then omegaKCoeff k m else 0 := by
  simpa only [eigenOrthonormalBasis_apply] using K_coordinate Q v horth j l k m

theorem A_eigenOrthonormalBasis_coordinate [Fintype β] [DecidableEq β]
    (Q : QuaternionicStructure V) (A : V →ₗ[ℝ] V) (hA : A ∈ Q.skewCentralizer)
    (vals : β → ℝ) (v : β → V)
    (horth : Orthonormal ℝ (fun p : β × Fin 4 => Q.frame (v p.1) p.2))
    (hspan : Submodule.span ℝ (Set.range (fun p : β × Fin 4 => Q.frame (v p.1) p.2)) = ⊤)
    (heig : ∀ j, A (v j) = vals j • Q.I (v j))
    (j l : β) (k m : Fin 4) :
    inner ℝ (A (eigenOrthonormalBasis Q v horth hspan (j, k)))
      (eigenOrthonormalBasis Q v horth hspan (l, m)) =
      if j = l then vals j * alphaCoeff k m else 0 := by
  simpa only [eigenOrthonormalBasis_apply] using A_coordinate Q A hA vals v horth heig j l k m

end
end QuaternionicStructure
end QuaternionicSymmetry
