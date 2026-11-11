/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_linearIndependent_of_constantFieldExtension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.FunctionFields.Constants.LinearIndependentConstantExtensionAlgClosed
public import Mathlib.Algebra.Polynomial.Eval.Irreducible
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.SimpRw
public import Mathlib.Data.Fintype.EquivFin

/-!
# Linear Independent of constant Field Extension
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs.LinearIndependent_of_constantFieldExtension

open Polynomial

namespace AlgebraicCurve
namespace LinDisjSol

section Generic

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The monic polynomial with polynomial coefficients determined by the coefficient array. -/
noncomputable def genericPoly (d N : ℕ) (v : Fin d → Fin N → R) : R[X][X] :=
  X ^ d + ∑ j : Fin d, C (∑ n : Fin N, C (v j n) * X ^ (n : ℕ)) * X ^ (j : ℕ)

theorem genericPoly_map (d N : ℕ) (v : Fin d → Fin N → R) (φ : R →+* S) :
    (genericPoly d N v).map (mapRingHom φ) = genericPoly d N (fun j n => φ (v j n)) :=
  open LinearIndependentConstantsAlg.AlgebraicCurve.LinDisjSol renaming
    genericPoly_map → sharedProof in
  sharedProof d N v φ

theorem genericPoly_monic [Nontrivial R] (d N : ℕ) (v : Fin d → Fin N → R) :
    (genericPoly d N v).Monic :=
  open LinearIndependentConstantsAlg.AlgebraicCurve.LinDisjSol renaming
    genericPoly_monic → sharedProof in
  sharedProof d N v

theorem genericPoly_natDegree [Nontrivial R] (d N : ℕ) (v : Fin d → Fin N → R) :
    (genericPoly d N v).natDegree = d :=
  open LinearIndependentConstantsAlg.AlgebraicCurve.LinDisjSol renaming
    genericPoly_natDegree → sharedProof in
  sharedProof d N v

theorem genericPoly_coeff_eq (g : R[X][X]) (hg : g.Monic) (N : ℕ)
    (hN : ∀ j : ℕ, j < g.natDegree → (g.coeff j).natDegree < N) :
    genericPoly g.natDegree N (fun j n => (g.coeff j).coeff n) = g :=
  open LinearIndependentConstantsAlg.AlgebraicCurve.LinDisjSol renaming
    genericPoly_coeff_eq → sharedProof in
  sharedProof g hg N hN

end Generic

section Spec

variable {K K' : Type*} [Field K] [Field K'] [Algebra K K'] [IsAlgClosed K]

theorem exists_factorisation_of_factorisation_map (m : K[X][X])
    (g h : K'[X][X]) (hg : g.Monic) (hh : h.Monic)
    (hfac : m.map (mapRingHom (algebraMap K K')) = g * h) :
    ∃ g₀ h₀ : K[X][X], g₀.Monic ∧ h₀.Monic ∧ g₀.natDegree = g.natDegree ∧
      h₀.natDegree = h.natDegree ∧ m = g₀ * h₀ :=
  open LinearIndependentConstantsAlg.AlgebraicCurve.LinDisjSol renaming
    exists_factorisation_of_factorisation_map → sharedProof in
  sharedProof m g h hg hh hfac

theorem irreducible_map_of_isAlgClosed (m : K[X][X]) (hm : m.Monic) (hirr : Irreducible m) :
    Irreducible (m.map (mapRingHom (algebraMap K K'))) :=
  open LinearIndependentConstantsAlg.AlgebraicCurve.LinDisjSol renaming
    irreducible_map_of_isAlgClosed → sharedProof in
  sharedProof (K' := K') m hm hirr

end Spec

section FunctionField

open IntermediateField

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem algebraMap_comp_aeval_gen (x : F) :
    (algebraMap K⟮x⟯ F).comp (aeval (AdjoinSimple.gen K x) : K[X] →ₐ[K] K⟮x⟯).toRingHom =
      (aeval x : K[X] →ₐ[K] F).toRingHom :=
  RingHom.ext fun p => AdjoinSimple.coe_aeval_gen_apply (F := K) x p

theorem aeval_gen_injective {x : F} (hx : Transcendental K x) :
    Function.Injective (aeval (AdjoinSimple.gen K x) : K[X] →ₐ[K] K⟮x⟯) := by
  intro p q hpq
  apply transcendental_iff_injective.mp hx
  change aeval x p = aeval x q
  rw [← AdjoinSimple.coe_aeval_gen_apply (F := K) x p,
    ← AdjoinSimple.coe_aeval_gen_apply (F := K) x q, hpq]

theorem exists_common_denom {x : F} (hx : Transcendental K x) {T : Type*} [Finite T]
    (r : T → K⟮x⟯) : ∃ q : K[X], q ≠ 0 ∧ ∀ t, ∃ p : K[X],
      aeval (AdjoinSimple.gen K x) q * r t = aeval (AdjoinSimple.gen K x) p :=
  open LinearIndependentConstantsAlg.AlgebraicCurve.LinDisjSol renaming
    exists_common_denom → sharedProof in
  sharedProof hx r

theorem exists_primitive_integral [CharZero K] {x : F} (hx : Transcendental K x)
    [FiniteDimensional K⟮x⟯ F] :
    ∃ (y : F) (m : K[X][X]) (d : ℕ), m.Monic ∧ Irreducible m ∧ m.natDegree = d ∧
      m.eval₂ (aeval x : K[X] →ₐ[K] F).toRingHom y = 0 ∧
      ∀ f : F, ∃ r : Fin d → K⟮x⟯, f = ∑ j, algebraMap K⟮x⟯ F (r j) * y ^ (j : ℕ) :=
  open LinearIndependentConstantsAlg.AlgebraicCurve.LinDisjSol renaming
    exists_primitive_integral → sharedProof in
  by
    let : CharZero K⟮x⟯ :=
      charZero_of_injective_algebraMap (algebraMap K K⟮x⟯).injective
    let : Algebra.IsSeparable K⟮x⟯ F := Algebra.IsAlgebraic.isSeparable_of_perfectField
    exact sharedProof hx

end FunctionField

section Main

open IntermediateField

variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F'] [Algebra K F]
  [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F']
  [IsScalarTower K F F']

theorem algebraMap_mem_adjoin (x : F) (z : K⟮x⟯) :
    algebraMap F F' (z : F) ∈ K'⟮algebraMap F F' x⟯ := by
  let ιFa : F →ₐ[K] F' := IsScalarTower.toAlgHom K F F'
  have h1 : algebraMap F F' (z : F) ∈ (K⟮x⟯).map ιFa := ⟨z, z.2, rfl⟩
  rw [adjoin_map, Set.image_singleton] at h1
  have h2 : K⟮ιFa x⟯ ≤ (K'⟮algebraMap F F' x⟯).restrictScalars K :=
    adjoin_simple_le_iff.mpr (mem_adjoin_simple_self K' _)
  exact h2 h1

theorem exists_ringHom_adjoin (x : F) : ∃ ρ : K⟮x⟯ →+* K'⟮algebraMap F F' x⟯,
    ∀ z, algebraMap K'⟮algebraMap F F' x⟯ F' (ρ z) = algebraMap F F' (algebraMap K⟮x⟯ F z) :=
  ⟨((algebraMap F F').comp (algebraMap K⟮x⟯ F)).codRestrict (K'⟮algebraMap F F' x⟯)
      (fun z => algebraMap_mem_adjoin x z), fun _ => rfl⟩

theorem isIntegral_algebraMap (x : F) [FiniteDimensional K⟮x⟯ F] (f : F) :
    IsIntegral K'⟮algebraMap F F' x⟯ (algebraMap F F' f) := by
  obtain ⟨ρ, hρ⟩ := exists_ringHom_adjoin (K := K) (K' := K') (F' := F') x
  have hf : IsIntegral K⟮x⟯ f := Algebra.IsIntegral.isIntegral f
  refine ⟨(minpoly K⟮x⟯ f).map ρ, (minpoly.monic hf).map ρ, ?_⟩
  have hcomp : (algebraMap K'⟮algebraMap F F' x⟯ F').comp ρ =
      (algebraMap F F').comp (algebraMap K⟮x⟯ F) := RingHom.ext hρ
  rw [eval₂_map, hcomp, ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]

theorem transcendental_algebraMap {x : F} [FiniteDimensional K⟮x⟯ F]
    (hfg' : ∃ x' : F', Transcendental K' x' ∧ FiniteDimensional K'⟮x'⟯ F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤) :
    Transcendental K' (algebraMap F F' x) := by
  intro hx₁
  obtain ⟨x', hx', -⟩ := hfg'
  apply hx'
  have : FiniteDimensional K' K'⟮algebraMap F F' x⟯ := adjoin.finiteDimensional hx₁.isIntegral
  have hS : ∀ z ∈ Set.range (algebraMap F F'), IsIntegral K' z := by
    rintro _ ⟨f, rfl⟩
    exact isIntegral_trans (R := K') _ (isIntegral_algebraMap (K := K) (K' := K') x f)
  have := IntermediateField.isAlgebraic_adjoin hS
  have hmem : x' ∈ IntermediateField.adjoin K' (Set.range (algebraMap F F')) := by
    rw [hgen]; exact mem_top
  exact IntermediateField.isAlgebraic_iff.mp
    (Algebra.IsAlgebraic.isAlgebraic
      (⟨x', hmem⟩ : IntermediateField.adjoin K' (Set.range (algebraMap F F'))))

theorem linearIndependent_pow_algebraMap [IsAlgClosed K] {x : F}
    (hx₁ : Transcendental K' (algebraMap F F' x))
    {y : F} {m : K[X][X]} (hm : m.Monic) (hirr : Irreducible m)
    (hroot : m.eval₂ (aeval x : K[X] →ₐ[K] F).toRingHom y = 0) :
    LinearIndependent K'⟮algebraMap F F' x⟯
      (fun j : Fin m.natDegree => algebraMap F F' y ^ (j : ℕ)) :=
  open LinearIndependentConstantsAlg.AlgebraicCurve.LinDisjSol renaming
    linearIndependent_pow_algebraMap → sharedProof in
  sharedProof (K := K) hx₁ hm hirr hroot

theorem eq_zero_of_sum_C_mul_map {κ : Type*} [Fintype κ] {c : κ → K'}
    (hc : LinearIndependent K c) (p : κ → K[X])
    (h : ∑ k, C (c k) * (p k).map (algebraMap K K') = 0) : ∀ k, p k = 0 := by
  have hn : ∀ n : ℕ, ∀ k, (p k).coeff n = 0 := by
    intro n
    have h1 := congrArg (fun P : K'[X] => P.coeff n) h
    simp only [finsetSum_coeff, coeff_C_mul, coeff_map, coeff_zero] at h1
    have h2 : ∑ k, (p k).coeff n • c k = 0 := by
      rw [← h1]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Algebra.smul_def, mul_comm]
    exact Fintype.linearIndependent_iff.mp hc _ h2
  intro k
  ext n
  simp [hn n k]

omit [Algebra K F'] [IsScalarTower K K' F'] in
theorem eq_zero_of_sum_aeval {x₁ : F'} (hx₁ : Transcendental K' x₁) {κ : Type*} [Fintype κ]
    {c : κ → K'} (hc : LinearIndependent K c) (p : κ → K[X])
    (h : ∑ k, algebraMap K' K'⟮x₁⟯ (c k) *
      aeval (AdjoinSimple.gen K' x₁) ((p k).map (algebraMap K K')) = 0) : ∀ k, p k = 0 := by
  apply eq_zero_of_sum_C_mul_map hc
  apply aeval_gen_injective hx₁
  rw [map_sum, map_zero, ← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, aeval_C]

theorem eq_zero_of_sum_mul_algebraMap [IsAlgClosed K] [CharZero K] {x : F}
    (hx : Transcendental K x) [FiniteDimensional K⟮x⟯ F]
    (hx₁ : Transcendental K' (algebraMap F F' x))
    {κ : Type*} [Fintype κ] {c : κ → K'} (hc : LinearIndependent K c) (f : κ → F)
    (hrel : ∑ k, algebraMap F F' (f k) * algebraMap K' F' (c k) = 0) : ∀ k, f k = 0 :=
  open LinearIndependentConstantsAlg.AlgebraicCurve.LinDisjSol renaming
    eq_zero_of_sum_mul_algebraMap → sharedProof in
  by
    let : CharZero K⟮x⟯ :=
      charZero_of_injective_algebraMap (algebraMap K K⟮x⟯).injective
    let : Algebra.IsSeparable K⟮x⟯ F := Algebra.IsAlgebraic.isSeparable_of_perfectField
    exact sharedProof hx hx₁ hc f hrel

theorem linearIndependent_algebraMap_of_fintype [IsAlgClosed K] [CharZero K] {x : F}
    (hx : Transcendental K x) [FiniteDimensional K⟮x⟯ F]
    (hx₁ : Transcendental K' (algebraMap F F' x))
    {κ : Type*} [Finite κ] {b : κ → F} (hb : LinearIndependent K b) :
    LinearIndependent K' (fun i => algebraMap F F' (b i)) :=
  open LinearIndependentConstantsAlg.AlgebraicCurve.LinDisjSol renaming
    linearIndependent_algebraMap_of_fintype → sharedProof in
  by
    let : CharZero K⟮x⟯ :=
      charZero_of_injective_algebraMap (algebraMap K K⟮x⟯).injective
    let : Algebra.IsSeparable K⟮x⟯ F := Algebra.IsAlgebraic.isSeparable_of_perfectField
    exact sharedProof hx hx₁ hb

end Main

end AlgebraicCurve.LinDisjSol

open AlgebraicCurve.LinDisjSol in
theorem _root_.AlgebraicCurve.linearIndependent_of_constantFieldExtension (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set
      F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    {ι : Type*} {b : ι → F} (hb : LinearIndependent K b) :
    LinearIndependent K' (fun i => algebraMap F F' (b i)) := by
  obtain ⟨x, hx, hfin⟩ := hfg
  have := hfin
  have hx₁ : Transcendental K' (algebraMap F F' x) :=
    transcendental_algebraMap (K := K) (x := x) hfg' hgen
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  exact linearIndependent_algebraMap_of_fintype hx hx₁ (hb.comp ((↑) : s → ι) Subtype.val_injective)
end AlgebraicCurves.FunctionFields.Proofs.LinearIndependent_of_constantFieldExtension
end ProofImplementation
