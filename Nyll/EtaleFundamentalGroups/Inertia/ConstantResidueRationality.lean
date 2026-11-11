/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.RationalCuspDecompositionConstants
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
# Rational residue points from the original decomposition action

At any closed point of a finite-type algebra, the prescribed algebraic
constant closure maps bijectively to the absolute normalization residue field.
No rationality of the point is assumed for this comparison. If the original
decomposition group supplies all constant automorphisms, its coefficient
residue map therefore factors through the base field. The resulting rational
map has the original contracted prime as its kernel.
-/

@[expose] public section

noncomputable section

open SchemeTheory
open scoped Pointwise

namespace EtaleFundamentalGroups.Inertia

universe u

attribute [local instance] Ideal.Quotient.field normalizationCommAlgGaloisAction

variable (k A κ Ω : Type u)
  [Field k] [CommRing A] [Field κ] [Field Ω]
  [Algebra k A] [Algebra k κ] [Algebra k Ω]
  [Algebra A Ω] [Algebra κ Ω]
  [IsScalarTower k A Ω] [IsScalarTower k κ Ω]
  [Algebra.IsAlgebraic k κ]

/-- The literal constant residue map preserves the original base coefficients. -/
theorem arithmeticConstantResidueMap_base
    (Q : Ideal (normalizationCommAlgCat A Ω)) (x : k) :
    arithmeticConstantResidueMap k A κ Ω Q (algebraMap k κ x) =
      Ideal.Quotient.mk Q
        (algebraMap A (normalizationCommAlgCat A Ω) (algebraMap k A x)) := by
  apply congrArg (Ideal.Quotient.mk Q)
  apply Subtype.ext
  exact (IsScalarTower.algebraMap_apply k κ Ω x).symm.trans
    (IsScalarTower.algebraMap_apply k A Ω x)

/-- The original absolute constant residue comparison at an arbitrary closed
point of a finite-type algebra. The residue point need not be rational. -/
theorem arithmeticConstantResidueMap_bijective_of_finiteType
    [Algebra.FiniteType k A] [IsAlgClosed κ]
    (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal] :
    Function.Bijective (arithmeticConstantResidueMap k A κ Ω Q) := by
  let B := normalizationCommAlgCat A Ω
  let E := B ⧸ Q
  have : Algebra.IsIntegral A B :=
    ⟨fun b => integralClosure.isIntegral (show integralClosure A Ω from b)⟩
  let P : Ideal A := Q.comap (algebraMap A B)
  have : P.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
    (algebraMap A B) Algebra.IsIntegral.isIntegral Q
  let : Algebra k B := ((algebraMap A B).comp (algebraMap k A)).toAlgebra
  let : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra (A ⧸ P) E := Ideal.Quotient.algebraQuotientOfLEComap le_rfl
  have : Algebra.IsIntegral (A ⧸ P) E := Algebra.IsIntegral.quotient
  have : Module.Finite k (A ⧸ P) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ P)
  let : IsScalarTower k (A ⧸ P) E := IsScalarTower.of_algebraMap_eq' (by
    ext x
    rfl)
  have : Algebra.IsIntegral k E := Algebra.IsIntegral.trans (A ⧸ P)
  let f : κ →+* E := arithmeticConstantResidueMap k A κ Ω Q
  have hbase : f.comp (algebraMap k κ) = algebraMap k E := by
    ext x
    exact arithmeticConstantResidueMap_base k A κ Ω Q x
  have hf : f.IsIntegral := RingHom.IsIntegral.tower_top (algebraMap k κ) f (by
    rw [hbase]
    exact Algebra.IsIntegral.isIntegral)
  let : Algebra κ E := f.toAlgebra
  have : Algebra.IsIntegral κ E := ⟨hf⟩
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- Surjectivity of the actual decomposition action on constants gives a
rational residue map, with its exact original kernel and coefficient square. -/
theorem exists_rationalResidueMap_of_decomposition_constants
    [Algebra.FiniteType k A] [IsAlgClosed κ] [IsGalois k κ]
    (F : Type u) [Field F] [Algebra k F]
    [Algebra A F] [IsFractionRing A F]
    [Algebra F Ω] [IsScalarTower A F Ω] [IsScalarTower k F Ω] [IsGalois F Ω]
    (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal]
    (h : ∀ σ : Gal(κ/k), ∃ d : normalizationDecompositionGroup A F Ω Q,
      (d.val.restrictScalars k).restrictNormal κ = σ) :
    ∃ r : A →ₐ[k] k, RingHom.ker r.toRingHom = Q.under A ∧
      ∀ a : A, Ideal.Quotient.mk Q (algebraMap A (normalizationCommAlgCat A Ω) a) =
        arithmeticConstantResidueMap k A κ Ω Q (algebraMap k κ (r a)) := by
  let B := normalizationCommAlgCat A Ω
  let E := B ⧸ Q
  let f : κ →+* E := arithmeticConstantResidueMap k A κ Ω Q
  let e : κ ≃+* E := RingEquiv.ofBijective f
    (arithmeticConstantResidueMap_bijective_of_finiteType k A κ Ω Q)
  let rκ : A →ₐ[k] κ :=
    { toRingHom := e.symm.toRingHom.comp (algebraMap A E)
      commutes' := fun x => by
        apply e.injective
        change e (e.symm (algebraMap A E (algebraMap k A x))) = e (algebraMap k κ x)
        rw [e.apply_symm_apply]
        exact (arithmeticConstantResidueMap_base k A κ Ω Q x).symm }
  have he (a : A) : e (rκ a) = algebraMap A E a := e.apply_symm_apply _
  have hfixed (a : A) (σ : Gal(κ/k)) : σ (rκ a) = rκ a := by
    obtain ⟨d, hd⟩ := h σ
    let ρ := nativeAlgebraResidueAutomorphismRingEquiv B Q
      ((normalizationResidueMorphism A F Ω Q).hom' d)
    have hres (b : B) : Ideal.Quotient.mk Q (d.val • b) =
        ρ (Ideal.Quotient.mk Q b) := by
      have hmap := originalNormalizationResidueMorphism_coefficientMap A F Ω Q d
      rw [normalizationGaloisRingHom_eq_original] at hmap
      have hb := congrArg (fun z : B →+* E => z b) hmap
      dsimp only [nativeAlgebraResidueCoefficientMap,
        nativeAlgebraResidueAutomorphismRingEquiv, nativeResidueAutomorphismRingEquiv,
        RingHom.comp_apply, ρ] at hb
      exact hb.symm
    have hc (x : κ) : arithmeticConstantNormalizationMap k A κ Ω (σ x) =
        d.val • arithmeticConstantNormalizationMap k A κ Ω x := by
      apply Subtype.ext
      have ha := congrArg (fun z : B →+* Ω =>
        z (arithmeticConstantNormalizationMap k A κ Ω x))
        (normalizationCommAlg_action_comp_inclusion A F Ω d.val)
      change d.val (algebraMap κ Ω x) =
        (show integralClosure A Ω from
          d.val • arithmeticConstantNormalizationMap k A κ Ω x).val at ha
      rw [← hd]
      exact ((d.val.restrictScalars k).restrictNormal_commutes κ x).trans ha
    apply e.injective
    change Ideal.Quotient.mk Q (arithmeticConstantNormalizationMap k A κ Ω (σ (rκ a))) = _
    rw [hc, hres]
    change ρ (e (rκ a)) = e (rκ a)
    rw [he]
    have hcoeff : d.val • algebraMap A B a = algebraMap A B a :=
      congrArg (fun z : A →+* B => z a)
        (normalizationCommAlg_action_comp_coefficient A F Ω d.val)
    exact (hres (algebraMap A B a)).symm.trans
      (congrArg (Ideal.Quotient.mk Q) hcoeff)
  let t : A →ₐ[k] (⊥ : Subalgebra k κ) := rκ.codRestrict ⊥ fun a =>
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := k) (rκ a)).mpr (hfixed a)
  let r : A →ₐ[k] k := (Algebra.botEquiv k κ).toAlgHom.comp t
  have hr (a : A) : algebraMap k κ (r a) = rκ a := by
    exact congrArg (fun z : (⊥ : Subalgebra k κ) => (z : κ))
      ((Algebra.botEquiv k κ).symm_apply_apply (t a))
  have hsquare (a : A) : algebraMap A E a = f (algebraMap k κ (r a)) := by
    rw [hr]
    exact (he a).symm
  refine ⟨r, ?_, hsquare⟩
  ext a
  change r a = 0 ↔ algebraMap A B a ∈ Q
  constructor
  · intro ha
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change algebraMap A E a = 0
    rw [hsquare, ha, map_zero, map_zero]
  · intro ha
    apply (algebraMap k κ).injective
    rw [map_zero]
    apply e.injective
    change f (algebraMap k κ (r a)) = e 0
    rw [← hsquare, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha

end EtaleFundamentalGroups.Inertia
