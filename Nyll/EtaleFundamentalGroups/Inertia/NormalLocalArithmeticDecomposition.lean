/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.RationalCuspDecompositionConstants
public import Nyll.EtaleFundamentalGroups.Inertia.RationalCuspArithmeticNormalizer
public import Nyll.EtaleFundamentalGroups.Inertia.OriginalNormalizationResidueCoefficient
public import Nyll.EtaleFundamentalGroups.Inertia.InertiaConjugateImage
public import Nyll.SchemeTheory.RingTheory.Ramification.NormalizationResidueSequence

/-!
# Arithmetic decomposition at rational points of normal local schemes

The canonical constant-residue map is an isomorphism for an arbitrary local
coefficient ring with a rational residue map. For an integrally closed local
ring, the original normalization decomposition group surjects onto residue
automorphisms. Together these facts lift every constant-field automorphism
in the same normalization decomposition group.

The actual field-source fundamental-group image consequently has full
arithmetic projection. Neither regularity nor a discrete valuation ring
hypothesis is needed for this residue and decomposition argument.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.FiniteEtale SchemeTheory
open scoped Pointwise

namespace EtaleFundamentalGroups.Inertia

universe u

attribute [local instance] Ideal.Quotient.field normalizationCommAlgGaloisAction

/-- Every constant automorphism lifts in the original normalization decomposition
group over an integrally closed local ring with its specified rational residue map. -/
theorem exists_normalLocalDecomposition_lift_constants
    (k A F κ Ω : Type u)
    [Field k] [CommRing A] [IsLocalRing A] [IsIntegrallyClosed A]
    [Field F] [Field κ] [Field Ω]
    [Algebra k A] [Algebra k F] [Algebra k κ] [Algebra k Ω]
    [Algebra A F] [IsFractionRing A F]
    [Algebra F Ω] [Algebra A Ω] [Algebra κ Ω]
    [IsScalarTower A F Ω] [IsScalarTower k A Ω]
    [IsScalarTower k F Ω] [IsScalarTower k κ Ω]
    [IsGalois F Ω] [IsAlgClosed κ] [IsAlgClosure k κ]
    (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal]
    (r : A →ₐ[k] k) (hr : RingHom.ker r.toRingHom = IsLocalRing.maximalIdeal A)
    (σ : κ ≃ₐ[k] κ) :
    ∃ d : normalizationDecompositionGroup A F Ω Q,
      (d.val.restrictScalars k).restrictNormal κ = σ := by
  let B := normalizationCommAlgCat A Ω
  let E := B ⧸ Q
  let c : κ →+* B := arithmeticConstantNormalizationMap k A κ Ω
  let f : κ →+* E := arithmeticConstantResidueMap k A κ Ω Q
  let e : κ ≃+* E := RingEquiv.ofBijective f
    (arithmeticConstantResidueMap_bijective k A κ Ω Q r hr)
  let τ : E ≃+* E := e.symm.trans (σ.toRingEquiv.trans e)
  let : Algebra (A ⧸ nativeAlgebraResidueBaseIdeal B Q) E :=
    Ideal.Quotient.algebraQuotientOfLEComap (p := Q.under A) (P := Q) le_rfl
  let ρ : normalizationResidueAutomorphisms A Ω Q :=
    { τ with
      commutes' := by
        intro a
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        change τ (Ideal.Quotient.mk Q (algebraMap A B a)) =
          Ideal.Quotient.mk Q (algebraMap A B a)
        rw [arithmeticConstantResidueMap_coefficient k A κ Ω Q r hr a]
        change e (σ (e.symm (e (algebraMap k κ (r a))))) =
          e (algebraMap k κ (r a))
        rw [e.symm_apply_apply, σ.commutes] }
  obtain ⟨d, hd⟩ := normalizationResidueMorphism_surjective A F Ω Q ρ
  refine ⟨d, ?_⟩
  let δ := (d.val.restrictScalars k).restrictNormal κ
  have hc (x : κ) : c (δ x) = d.val • c x := by
    apply Subtype.ext
    have haction := congrArg (fun z : B →+* Ω => z (c x))
      (normalizationCommAlg_action_comp_inclusion A F Ω d.val)
    change d.val (algebraMap κ Ω x) =
      (show integralClosure A Ω from d.val • c x).val at haction
    exact ((d.val.restrictScalars k).restrictNormal_commutes κ x).trans haction
  have hres (b : B) : Ideal.Quotient.mk Q (d.val • b) =
      τ (Ideal.Quotient.mk Q b) := by
    have hmap := originalNormalizationResidueMorphism_coefficientMap A F Ω Q d
    rw [hd, normalizationGaloisRingHom_eq_original] at hmap
    have hb := congrArg (fun z : B →+* E => z b) hmap
    dsimp only [nativeAlgebraResidueCoefficientMap,
      nativeAlgebraResidueAutomorphismRingEquiv, nativeResidueAutomorphismRingEquiv,
      RingHom.comp_apply, ρ] at hb
    exact hb.symm
  apply AlgEquiv.ext
  intro x
  apply e.injective
  change Ideal.Quotient.mk Q (c (δ x)) = Ideal.Quotient.mk Q (c (σ x))
  rw [hc, hres]
  change e (σ (e.symm (e x))) = e (σ x)
  rw [e.symm_apply_apply]

/-- The same actual normalization-prime image contains inertia, normalizes it,
and surjects onto the marked constant Galois group for every normal local base. -/
theorem normalLocal_arithmetic_decomposition_image_data
    (k A F κ Ω : Type u)
    [Field k] [CommRing A] [IsLocalRing A] [IsIntegrallyClosed A]
    [Field F] [Field κ] [Field Ω]
    [Algebra k A] [Algebra k F] [Algebra k κ] [Algebra k Ω]
    [Algebra A F] [IsFractionRing A F]
    [Algebra F Ω] [Algebra A Ω] [Algebra κ Ω]
    [IsScalarTower A F Ω] [IsScalarTower k A Ω]
    [IsScalarTower k F Ω] [IsScalarTower k κ Ω]
    [IsGalois F Ω] [IsAlgClosed κ] [IsAlgClosure k κ]
    [IsSepClosure k κ] [IsSepClosure F Ω] [IsSepClosed Ω]
    (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal]
    (r : A →ₐ[k] k) (hr : RingHom.ker r.toRingHom = IsLocalRing.maximalIdeal A)
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) (j : Spec (.of F) ⟶ X)
    (hbase : (ξ F Ω ≫ j) ≫ f = ξ k Ω) :
    let q := fieldSourceAbsoluteGaloisHom F Ω j
    let I := (Q.inertia Gal(Ω/F)).map q.toMonoidHom
    let d := q.toMonoidHom.comp (normalizationDecompositionInclusion A F Ω Q)
    I ≤ d.range ∧ d.range ≤ Subgroup.normalizer I.carrier ∧
      ∀ τ : Gal(κ/k), ∃ γ : Aut (fiber (ξ F Ω ≫ j)),
        γ ∈ d.range ∧ arithmeticFundamentalGroupHom k κ f (ξ F Ω ≫ j) γ = τ := by
  intro q I d
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨γ, hγ, rfl⟩
    rw [← normalizationResidueMorphism_map_ker A F Ω Q] at hγ
    obtain ⟨δ, _hδ, hδγ⟩ := hγ
    exact ⟨δ, congrArg q hδγ⟩
  · rintro x ⟨δ, rfl⟩
    have hQ : δ.val • Q = Q := δ.property
    have hI : I.map (MulAut.conj (q δ.val)).toMonoidHom = I := by
      have hmap := inertia_smul_map (M := Gal(Ω/F)) Q
        (δ.val : Gal(Ω/F)) q.toMonoidHom
      rw [hQ] at hmap
      exact hmap.symm
    apply Subgroup.mem_set_normalizer_iff.mpr
    intro y
    constructor
    · intro hy
      rw [← hI]
      exact ⟨y, hy, rfl⟩
    · intro hy
      rw [← hI] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      exact (MulAut.conj (q δ.val)).injective hzy ▸ hz
  · obtain ⟨α, hα⟩ := exists_fieldSource_arithmetic_restriction_label k F κ Ω f j hbase
    intro τ
    obtain ⟨δ, hδ⟩ := exists_normalLocalDecomposition_lift_constants k A F κ Ω
      Q r hr (α⁻¹ * τ * α)
    refine ⟨q δ.val, ⟨δ, rfl⟩, ?_⟩
    rw [hα δ.val, hδ]
    simp only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]

end EtaleFundamentalGroups.Inertia
