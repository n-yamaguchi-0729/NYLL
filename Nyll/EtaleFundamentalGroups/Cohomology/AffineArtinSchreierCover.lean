/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.FormallyEtale
public import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ArtinSchreierPolynomial
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
public import Nyll.GaloisCohomology.ArtinSchreier.RootCharacter

/-!
# The actual affine Artin–Schreier cover of a coefficient

Every coefficient in a ring of characteristic `p` gives the original finite
étale cover defined by `T^p - T - a`. Its geometric fiber is identified with
the roots of that equation through the literal algebra homomorphisms from
the adjoined-root algebra. The cover need not be connected.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial
open ValuationTheory.DiscreteValuationField

namespace EtaleFundamentalGroups.Cohomology

universe u

variable (R : Type u) [CommRing R] [Nontrivial R]
  (p : ℕ) [Fact p.Prime] [CharP R p] (a : R)

/-- The actual root algebra of the given affine coefficient. -/
abbrev ArtinSchreierAlgebra := AdjoinRoot (artinSchreierPolynomial p a)

omit [Nontrivial R] [Fact p.Prime] [CharP R p] in
theorem artinSchreierAlgebra_root :
    AdjoinRoot.root (artinSchreierPolynomial p a) ^ p -
      AdjoinRoot.root (artinSchreierPolynomial p a) =
        algebraMap R (ArtinSchreierAlgebra R p a) a := by
  have h := AdjoinRoot.eval₂_root (artinSchreierPolynomial p a)
  change (X ^ p - X - C a : Polynomial R).eval₂
    (algebraMap R (ArtinSchreierAlgebra R p a))
      (AdjoinRoot.root (artinSchreierPolynomial p a)) = 0 at h
  rw [eval₂_sub, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] at h
  exact h

/-- The derivative is the unit `-1`, including when the cover is disconnected. -/
theorem artinSchreierAlgebra_etale :
    Algebra.Etale R (ArtinSchreierAlgebra R p a) := by
  have : Algebra.FormallyEtale R (ArtinSchreierAlgebra R p a) :=
    EtaleFundamentalGroups.Kummer.formallyEtale_adjoinRoot_of_monic_of_isUnit_aeval_derivative
      (artinSchreierPolynomial_monic p (Fact.out : p.Prime).one_lt a)
      (by rw [artinSchreierPolynomial_derivative, map_neg, map_one]
          exact isUnit_neg_one)
  exact ⟨inferInstance, inferInstance⟩

omit [CharP R p] in
theorem artinSchreierAlgebra_finite :
    Module.Finite R (ArtinSchreierAlgebra R p a) :=
  (artinSchreierPolynomial_monic p (Fact.out : p.Prime).one_lt a).finite_adjoinRoot

omit [CharP R p] in
/-- The monic root algebra is free of positive rank, hence faithfully flat.
This supplies finite étale root adjunctions in successive Witt coordinates. -/
theorem artinSchreierAlgebra_faithfullyFlat :
    Module.FaithfullyFlat R (ArtinSchreierAlgebra R p a) := by
  have hm := artinSchreierPolynomial_monic p (Fact.out : p.Prime).one_lt a
  have hd : (artinSchreierPolynomial p a).natDegree = p := by
    rw [artinSchreierPolynomial, natDegree_sub_C,
      natDegree_sub_eq_left_of_natDegree_lt, natDegree_X_pow]
    simpa only [natDegree_X, natDegree_X_pow] using (Fact.out : p.Prime).one_lt
  let : Nontrivial (ArtinSchreierAlgebra R p a) :=
    Ideal.Quotient.nontrivial_iff.mpr (by
      intro htop
      have hu := Ideal.span_singleton_eq_top.mp htop
      have hdeg := congrArg Polynomial.natDegree (hm.eq_one_of_isUnit hu)
      rw [hd, natDegree_one] at hdeg
      exact (Fact.out : p.Prime).ne_zero hdeg)
  let : Module.Free R (ArtinSchreierAlgebra R p a) := hm.free_adjoinRoot
  infer_instance

theorem artinSchreierAlgebra_charP : CharP (ArtinSchreierAlgebra R p a) p := by
  have : Module.FaithfullyFlat R (ArtinSchreierAlgebra R p a) :=
    artinSchreierAlgebra_faithfullyFlat R p a
  exact charP_of_injective_algebraMap
    (FaithfulSMul.algebraMap_injective R (ArtinSchreierAlgebra R p a)) p

/-- The polynomial construction gives an actual finite étale scheme morphism. -/
theorem artinSchreierAlgebra_isFiniteEtale :
    IsFiniteEtale (Spec.algebraMap R (ArtinSchreierAlgebra R p a)) := by
  have : Module.Finite R (ArtinSchreierAlgebra R p a) :=
    artinSchreierAlgebra_finite R p a
  have : Algebra.Etale R (ArtinSchreierAlgebra R p a) :=
    artinSchreierAlgebra_etale R p a
  have : IsFinite (Spec.algebraMap R (ArtinSchreierAlgebra R p a)) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have : Etale (Spec.algebraMap R (ArtinSchreierAlgebra R p a)) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  exact ⟨⟩

/-- The finite étale cover over the original affine base. -/
def artinSchreierCover : FiniteEtale (Spec (CommRingCat.of R)) := by
  have := artinSchreierAlgebra_isFiniteEtale R p a
  exact FiniteEtale.mk (Spec.algebraMap R (ArtinSchreierAlgebra R p a))

variable {Ω : Type u} [Field Ω] [Algebra R Ω]

omit [Nontrivial R] [Fact p.Prime] [CharP R p] in
/-- Field-valued points of the original root algebra are the actual roots. -/
def artinSchreierAlgebraHomEquivRoots :
    (ArtinSchreierAlgebra R p a →ₐ[R] Ω) ≃
      {β : Ω // β ^ p - β = algebraMap R Ω a} where
  toFun f := ⟨f (AdjoinRoot.root _), by
    rw [← map_pow, ← map_sub, artinSchreierAlgebra_root, f.commutes]⟩
  invFun β := AdjoinRoot.liftAlgHom _ (Algebra.ofId R Ω) β.1 (by
    change (X ^ p - X - C a : Polynomial R).eval₂ (algebraMap R Ω) β.1 = 0
    rw [eval₂_sub, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, β.2, sub_self])
  left_inv f := by
    apply AdjoinRoot.algHom_ext
    exact AdjoinRoot.liftAlgHom_root _ _ _ _
  right_inv β := Subtype.ext (AdjoinRoot.liftAlgHom_root _ _ _ _)

variable [IsSepClosed Ω]

/-- The actual geometric fiber consists of the roots, through the original
finite-étale fiber-to-morphism equivalence and the affine Spec equivalence. -/
def artinSchreierFiberEquivRoots :
    (FiniteEtale.fiber (Spec.algebraMap R Ω)).obj (artinSchreierCover R p a) ≃
      {β : Ω // β ^ p - β = algebraMap R Ω a} :=
  (FiniteEtale.fiberObjEquivHom (Spec.algebraMap R Ω) (artinSchreierCover R p a)).trans
    (({ toFun := fun f => ⟨f.left, f.w⟩
        invFun := fun f => Over.homMk f.1 f.2
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl } :
      (Over.mk (Spec.algebraMap R Ω) ⟶ (artinSchreierCover R p a).toComma) ≃
        {f : Spec (CommRingCat.of Ω) ⟶
            Spec (CommRingCat.of (ArtinSchreierAlgebra R p a)) //
          f ≫ Spec.algebraMap R (ArtinSchreierAlgebra R p a) = Spec.algebraMap R Ω}).trans
      (Spec.homEquivAlgHom.trans (artinSchreierAlgebraHomEquivRoots R p a)))

end EtaleFundamentalGroups.Cohomology
