import Mathlib.LinearAlgebra.Matrix.SchurComplement
open scoped MatrixGroups
open scoped Matrix
open scoped ComplexConjugate

noncomputable abbrev ℍ₂ := selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)

noncomputable def toSelfAdjointMap (M : SL(2, ℂ)) : ℍ₂ →ₗ[ℝ] ℍ₂ where
  toFun | ⟨A, hA⟩ => ⟨↑M * A * Mᴴ, .conjugate hA M⟩
  map_add' | ⟨A, _⟩, ⟨B, _⟩ => Subtype.ext <|
    show ↑M * (A + B) * Mᴴ = ↑M * A * Mᴴ + ↑M * B * Mᴴ by noncomm_ring
  map_smul' | r, ⟨A, _⟩ => Subtype.ext <|
    show ↑M * (r • A) * Mᴴ = r • (↑M * A * Mᴴ) by simp

noncomputable def toSelfAdjointEquiv (M : SL(2, ℂ)) : ℍ₂ ≃ₗ[ℝ] ℍ₂ where
  toLinearMap := toSelfAdjointMap M
  invFun := toSelfAdjointMap M⁻¹
  left_inv | ⟨A, _⟩ => Subtype.ext <|
    calc  ↑M⁻¹ * (↑M * A * Mᴴ) * (↑M⁻¹)ᴴ
      _ = ↑M⁻¹ * ↑M * A * (Mᴴ * (↑M⁻¹)ᴴ) := by noncomm_ring
      _ = ↑M⁻¹ * ↑M * A * (↑M⁻¹ * ↑M)ᴴ := by rw [Matrix.conjTranspose_mul]
      _ = A := by simp [Matrix.adjugate_mul]
  right_inv | ⟨A, _⟩ => Subtype.ext <|
    calc  ↑M * (↑M⁻¹ * A * (↑M⁻¹)ᴴ) * Mᴴ
      _ = ↑M * ↑M⁻¹ * A * ((↑M⁻¹)ᴴ * Mᴴ) := by noncomm_ring
      _ = ↑M * ↑M⁻¹ * A * (↑M * ↑M⁻¹)ᴴ := by rw [Matrix.conjTranspose_mul]
      _ = A := by simp [Matrix.mul_adjugate]

theorem symm_of_selfAdjoint_conj (A : selfAdjoint (Matrix n n ℂ)) (i j : n)
    : conj (A.1 j i) = A.1 i j := congrFun (congrFun A.2 i) j
@[simp] theorem ℍ₂.z_conj (A : ℍ₂) : conj (A.1 0 1) = A.1 1 0 := symm_of_selfAdjoint_conj A 1 0
theorem diag_of_selAdjoint_re (A : selfAdjoint (Matrix n n ℂ)) (i : n)
    : (A.1 i i).re = A.1 i i := Complex.conj_eq_iff_re.mp (symm_of_selfAdjoint_conj A i i)
@[simp] theorem ℍ₂.a_re (A : ℍ₂) : (A.1 0 0).re = A.1 0 0 := diag_of_selAdjoint_re A 0
@[simp] theorem ℍ₂.b_re (A : ℍ₂) : (A.1 1 1).re = A.1 1 1 := diag_of_selAdjoint_re A 1

noncomputable def φ : ℍ₂ ≃ₗ[ℝ] Fin 2 ⊕ Fin 2 → ℝ where
  toFun | ⟨A, _⟩ => Sum.elim ![(A 0 0).re, (A 1 1).re] ![(A 0 1).re, (A 0 1).im]
  map_add' _ _ := funext fun | .inl 0 | .inl 1 | .inr 0 | .inr 1 => by simp
  map_smul' _ _ := funext fun | .inl 0 | .inl 1 | .inr 0 | .inr 1 => by simp
  invFun p := {
    val := let z : ℂ := ⟨p (.inr 0), p (.inr 1)⟩ ; !![p (.inl 0), z; conj z, p (.inl 1)]
    property := Matrix.ext fun | 0, 0 | 0, 1 | 1, 0 | 1, 1 => by simp
  }
  left_inv _ := Subtype.ext <| Matrix.ext fun | 0, 0 | 0, 1 | 1, 0 | 1, 1 => by simp
  right_inv _ := funext fun | .inl 0 | .inl 1 | .inr 0 | .inr 1 => by simp

structure UT where
  x : ℝ
  sq1 : x * x = 1
  w : ℂ

@[simp] theorem UT.sq1' (M : UT) : @Eq ℂ (M.x * M.x) 1 :=
  calc  (M.x * M.x : ℂ)
    _ = ↑(M.x * M.x) := by simp
    _ = 1 := congrArg Complex.ofReal M.sq1

@[simp] theorem UT.sq1_I (M : UT) : @Eq ℂ (M.x * Complex.I * M.x) Complex.I :=
  calc  M.x * Complex.I * M.x
    _ = M.x * M.x * Complex.I := by ring
    _ = Complex.I := by simp

abbrev UT.toSL2C (M : UT) : SL(2, ℂ) := ⟨!![M.x, M.w; 0, M.x], by simp⟩
instance : Coe UT SL(2, ℂ) where coe := UT.toSL2C

theorem UT.star (M : UT) : M.toSL2C.1ᴴ = !![↑M.x, 0; conj M.w, M.x] :=
  Matrix.ext fun | 0, 0 | 0, 1 | 1, 0 | 1, 1 => by simp

example (M : UT) : LinearMap.det (toSelfAdjointMap M) = 1 :=
  let f : (Fin 2 ⊕ Fin 2 → ℝ) →ₗ[ℝ] Fin 2 ⊕ Fin 2 → ℝ := φ ∘ₗ toSelfAdjointMap M ∘ₗ φ.symm
  let F : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ := LinearMap.toMatrix' f
  let E₀ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; conj 0, 0]
  let E₁ : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; conj 0, 1]
  let E₂ : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; conj 1, 0]
  let E₃ : Matrix (Fin 2) (Fin 2) ℂ := !![0, Complex.I; conj Complex.I, 0]
  let a := F.toBlocks₁₁ 0 1
  have hA : F.toBlocks₁₁ = !![1, a; 0, 1] :=
    Matrix.ext fun
      | 0, 1 => rfl
      | 0, 0 => congrArg Complex.re <| show (M * E₀ * M.toSL2C.1ᴴ) 0 0 = 1 by simp [M.star, E₀]
      | 1, 0 => congrArg Complex.re <| show (M * E₀ * M.toSL2C.1ᴴ) 1 1 = 0 by simp [M.star, E₀]
      | 1, 1 => congrArg Complex.re <| show (M * E₁ * M.toSL2C.1ᴴ) 1 1 = 1 by simp [M.star, E₁]
  let b j := F.toBlocks₁₂ 0 j
  have hB : F.toBlocks₁₂ = !![b 0, b 1; 0, 0] :=
    Matrix.ext fun
      | 0, 0 | 0, 1 => rfl
      | 1, 0 => congrArg Complex.re <| show (M * E₂ * M.toSL2C.1ᴴ) 1 1 = 0 by simp [M.star, E₂]
      | 1, 1 => congrArg Complex.re <| show (M * E₃ * M.toSL2C.1ᴴ) 1 1 = 0 by simp [M.star, E₃]
  let c i := F.toBlocks₂₁ i 1
  have hC : F.toBlocks₂₁ = !![0, c 0; 0, c 1] :=
    have k : (M * E₀ * M.toSL2C.1ᴴ) 0 1 = 0 := by simp [M.star, E₀]
    Matrix.ext fun
      | 0, 1 | 1, 1 => rfl
      | 0, 0 => congrArg Complex.re k | 1, 0 => congrArg Complex.im k
  have hD : F.toBlocks₂₂ = 1 :=
    have k₁ : (M * E₂ * M.toSL2C.1ᴴ) 0 1 = 1 := by simp [M.star, E₂]
    have k₂ : (M * E₃ * M.toSL2C.1ᴴ) 0 1 = Complex.I := by simp [M.star, E₃]
    Matrix.ext fun
      | 0, 0 => congrArg Complex.re k₁ | 1, 0 => congrArg Complex.im k₁
      | 0, 1 => congrArg Complex.re k₂ | 1, 1 => congrArg Complex.im k₂

  calc  LinearMap.det (toSelfAdjointMap M)
    _ = LinearMap.det f := (LinearMap.det_conj (toSelfAdjointMap M) φ).symm
    _ = F.det := (LinearMap.det_toMatrix' f).symm
    _ = (!![1, a; 0, 1] - !![b 0, b 1; 0, 0] * !![0, c 0; 0, c 1]).det
          := F.fromBlocks_toBlocks.symm.trans (Matrix.fromBlocks_inj.mpr ⟨hA, hB, hC, hD⟩)
              ▸ Matrix.det_fromBlocks_one₂₂ ..
    _ = !![1, a - b ⬝ᵥ c; 0, 1].det
          := congrArg Matrix.det <| Matrix.ext fun | 0, 0 | 1, 0 | 1, 1 | 0, 1 => by simp
    _ = 1 := by simp
