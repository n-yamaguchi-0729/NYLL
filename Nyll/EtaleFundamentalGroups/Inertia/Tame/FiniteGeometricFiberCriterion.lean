/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.Tame.FiniteCoverCriterion
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGalois
public import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteResidueAction
public import Nyll.EtaleFundamentalGroups.Inertia.FiniteLevelFieldAlgebra
public import Nyll.EtaleFundamentalGroups.Inertia.FiniteNormalizationDedekind
public import Nyll.SchemeTheory.Normalization.NativeNormalizationPrime

/-!
# Classical tameness on the original finite Galois geometric fiber

The finite étale spectrum of a finite Galois subfield has its original
geometric fiber and its actual absolute Galois action. Its local wild
inertia acts trivially precisely when the same normalization has a
prime-to-residue-characteristic ramification index and separable residue
extension. No replacement finite action or comparison hypothesis is used.
-/

@[expose] public section

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open AlgebraicGeometry AlgebraicGeometry.FiniteEtale SchemeTheory

universe u v

attribute [local instance] Ideal.Quotient.field

/-- Local wild monodromy on the original geometric fiber of a finite Galois
field cover vanishes exactly under the classical ramification conditions.
The normalization, contracted prime, and coefficient actions are the same
ones used to define the absolute wild group and its finite restriction. -/
theorem finiteGaloisSubfieldCover_wild_fixed_iff
    (A : Type v) (K Ω : Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field Ω] [Algebra A K] [IsFractionRing A K]
    [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω]
    [IsSepClosure K Ω] [IsSepClosed Ω]
    (Q : Ideal (normalizationCommAlgCat A Ω).carrier) [Q.IsMaximal]
    (E : FiniteGaloisIntermediateField K Ω)
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p] :
    let B := finiteAbsoluteNormalizationAlgebra A K Ω E
    let q : Ideal B.carrier := finiteAbsoluteNormalizationPrime A K Ω Q E
    let : q.IsMaximal := actualFiniteNormalizationPrime_isMaximal A K Ω Q E
    let : q.LiesOver (IsLocalRing.maximalIdeal A) :=
      subalgebraNormalizationPrime_liesOver_maximalIdeal
        (finiteLevelNormalizationSubalgebra A K Ω E) Q
    (∀ σ : (actualNormalizationWildGroup A K Ω Q).carrier,
      ∀ x : (fib K Ω).obj (fieldSourceFiniteSubfieldCover K Ω E.toIntermediateField),
        σ.val.val • x = x) ↔
      p.Coprime (q.ramificationIdx A) ∧
        Algebra.IsSeparable (A ⧸ IsLocalRing.maximalIdeal A) (B.carrier ⧸ q) := by
  intro B q hmax hlying
  have hgeometry :
      (∀ σ : (actualNormalizationWildGroup A K Ω Q).carrier,
        ∀ x : (fib K Ω).obj (fieldSourceFiniteSubfieldCover K Ω E.toIntermediateField),
          σ.val.val • x = x) ↔
        ∀ σ : (actualNormalizationWildGroup A K Ω Q).carrier,
          ∀ φ : E →ₐ[K] Ω, σ.val.val.toAlgHom.comp φ = φ :=
    forall_congr' fun σ =>
      fieldSourceSubfieldFiber_fixed_iff K Ω E.toIntermediateField σ.val.val
  rw [hgeometry, actualNormalizationWild_fixes_embeddings_iff A K Ω Q E]
  let C := finiteLevelFieldAlgebra A K Ω E
  have : IsDedekindDomain B.carrier :=
    finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K Ω E
  have : Module.Finite A B.carrier :=
    nativeNormalization_finite A K C (Field.toIsField C.carrier)
  have : Module.IsTorsionFree A B.carrier :=
    nativeFieldNormalization_isTorsionFree A K C.carrier
  have : IsGaloisGroup (B.carrier ≃ₐ[A] B.carrier) A B.carrier :=
    nativeFieldNormalization_isGaloisGroup A K C.carrier
  exact finiteIdealWildSubgroup_eq_bot_iff_coprime_and_isSeparable
    A B.carrier q (finiteAbsoluteNormalizationPrime_ne_bot A K Ω Q E) p

end EtaleFundamentalGroups.Inertia
