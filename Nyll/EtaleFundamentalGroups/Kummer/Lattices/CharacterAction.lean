/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Nyll.EtaleFundamentalGroups.Kummer.Lattices.Cover

/-!
# Character action on a finite-index lattice cover

Characters of the finite quotient lattice act diagonally on the ambient
lattice algebra.  When the coefficient domain has enough roots of unity,
these characters separate the quotient degrees.  Consequently their common
fixed subalgebra is exactly the image of the subgroup lattice algebra.
-/

@[expose] public section

namespace EtaleFundamentalGroups.Kummer

universe u v

noncomputable section

/-- The coefficient weight obtained by pulling a quotient character back to the lattice. -/
def latticeCharacterWeight
    {k : Type u} {L : Type v} [CommRing k] [AddCommGroup L]
    (H : AddSubgroup L) (χ : Multiplicative (L ⧸ H) →* kˣ) :
    Multiplicative L →* k :=
  (Units.coeHom k).comp
    (χ.comp (QuotientAddGroup.mk' H).toMultiplicative)

/-- The lattice monomial multiplied by its quotient-character weight. -/
def latticeCharacterMonomial
    {k : Type u} {L : Type v} [CommRing k] [AddCommGroup L]
    (H : AddSubgroup L) (χ : Multiplicative (L ⧸ H) →* kˣ) :
    Multiplicative L →* AddMonoidAlgebra k L :=
  (AddMonoidAlgebra.singleHom :
      k × Multiplicative L →* AddMonoidAlgebra k L).comp
    ((latticeCharacterWeight H χ).prod
      (MonoidHom.id (Multiplicative L)))

/-- Extend the weighted lattice monomials to an algebra homomorphism. -/
def latticeCharacterAlgHom
    {k : Type u} {L : Type v} [CommRing k] [AddCommGroup L]
    (H : AddSubgroup L) (χ : Multiplicative (L ⧸ H) →* kˣ) :
    AddMonoidAlgebra k L →ₐ[k] AddMonoidAlgebra k L :=
  AddMonoidAlgebra.lift k (AddMonoidAlgebra k L) L
    (latticeCharacterMonomial H χ)

@[simp]
private theorem latticeCharacterAlgHom_single
    {k : Type u} {L : Type v} [CommRing k] [AddCommGroup L]
    (H : AddSubgroup L) (χ : Multiplicative (L ⧸ H) →* kˣ)
    (l : L) (a : k) :
    latticeCharacterAlgHom H χ (AddMonoidAlgebra.single l a) =
      AddMonoidAlgebra.single l
        (a * (χ (Multiplicative.ofAdd (QuotientAddGroup.mk' H l)) : k)) := by
  simp only [latticeCharacterAlgHom, latticeCharacterMonomial, latticeCharacterWeight,
    AddMonoidAlgebra.lift_single, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.prod_apply,
    AddMonoidHom.coe_toMultiplicative, QuotientAddGroup.coe_mk', toAdd_ofAdd, Units.coeHom_apply,
    MonoidHom.id_apply, AddMonoidAlgebra.singleHom_apply, Algebra.smul_def,
    AddMonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self, RingHom.coe_id, id_eq,
    AddMonoidAlgebra.single_mul_single, zero_add, QuotientAddGroup.mk'_apply]

/-- The inverse quotient character inverts the diagonal algebra homomorphism. -/
def latticeCharacterAlgEquiv
    {k : Type u} {L : Type v} [CommRing k] [AddCommGroup L]
    (H : AddSubgroup L) (χ : Multiplicative (L ⧸ H) →* kˣ) :
    AddMonoidAlgebra k L ≃ₐ[k] AddMonoidAlgebra k L :=
  AlgEquiv.ofAlgHom
    (latticeCharacterAlgHom H χ)
    (latticeCharacterAlgHom H χ⁻¹)
    (by
      apply AddMonoidAlgebra.algHom_ext
      · intro l
        simp only [AlgHom.coe_comp, Function.comp_apply, latticeCharacterAlgHom_single,
          QuotientAddGroup.mk'_apply, MonoidHom.inv_apply, one_mul, Units.inv_mul, AlgHom.coe_id,
          id_eq]
      · ext)
    (by
      apply AddMonoidAlgebra.algHom_ext
      · intro l
        simp only [AlgHom.coe_comp, Function.comp_apply, latticeCharacterAlgHom_single,
          QuotientAddGroup.mk'_apply, one_mul, MonoidHom.inv_apply, Units.mul_inv, AlgHom.coe_id,
          id_eq]
      · ext)

/-- The canonical diagonal action of quotient-lattice characters on the
ambient lattice algebra. -/
def latticeCharacterAction
    {k : Type u} {L : Type v} [CommRing k] [AddCommGroup L]
    (H : AddSubgroup L) :
    (Multiplicative (L ⧸ H) →* kˣ) →*
      (AddMonoidAlgebra k L ≃ₐ[k] AddMonoidAlgebra k L) where
  toFun := latticeCharacterAlgEquiv H
  map_one' := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply AddMonoidAlgebra.algHom_ext
    · intro l
      simp only [latticeCharacterAlgEquiv, AlgEquiv.coe_toAlgHom, AlgEquiv.ofAlgHom_apply,
        latticeCharacterAlgHom_single, QuotientAddGroup.mk'_apply, MonoidHom.one_apply,
        Units.val_one, mul_one, AlgEquiv.one_apply]
    · ext
  map_mul' χ ψ := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply AddMonoidAlgebra.algHom_ext
    · intro l
      simp only [latticeCharacterAlgEquiv, AlgEquiv.coe_toAlgHom, AlgEquiv.ofAlgHom_apply,
        latticeCharacterAlgHom_single, QuotientAddGroup.mk'_apply, MonoidHom.mul_apply,
        Units.val_mul, one_mul, AlgEquiv.mul_apply, mul_comm]
    · ext

@[simp]
theorem latticeCharacterAction_single
    {k : Type u} {L : Type v} [CommRing k] [AddCommGroup L]
    (H : AddSubgroup L) (χ : Multiplicative (L ⧸ H) →* kˣ)
    (l : L) (a : k) :
    latticeCharacterAction H χ (AddMonoidAlgebra.single l a) =
      AddMonoidAlgebra.single l
        (a * (χ (Multiplicative.ofAdd (QuotientAddGroup.mk' H l)) : k)) := by
  exact latticeCharacterAlgHom_single H χ l a

theorem latticeCharacterAction_coeff
    {k : Type u} {L : Type v} [CommRing k] [AddCommGroup L]
    (H : AddSubgroup L) (χ : Multiplicative (L ⧸ H) →* kˣ)
    (x : AddMonoidAlgebra k L) (l : L) :
    (latticeCharacterAction H χ x).coeff l =
      x.coeff l * (χ (Multiplicative.ofAdd (QuotientAddGroup.mk' H l)) : k) := by
  induction x using AddMonoidAlgebra.induction_on with
  | of m =>
      by_cases h : m = l
      · subst m
        simp only [AddMonoidAlgebra.of, MulHom.toFun_eq_coe, MonoidHom.coe_mk, OneHom.coe_mk,
          AddMonoidAlgebra.ofMagma_apply, toAdd_ofAdd, latticeCharacterAction_single,
          QuotientAddGroup.mk'_apply, one_mul, AddMonoidAlgebra.coeff_single,
          Finsupp.single_eq_same]
      · simp only [AddMonoidAlgebra.of, MulHom.toFun_eq_coe, MonoidHom.coe_mk, OneHom.coe_mk,
        AddMonoidAlgebra.ofMagma_apply, toAdd_ofAdd, latticeCharacterAction_single,
        QuotientAddGroup.mk'_apply, one_mul, AddMonoidAlgebra.coeff_single, ne_eq, h,
        not_false_eq_true, Finsupp.single_eq_of_ne', zero_mul]
  | add x y hx hy =>
      rw [map_add]
      change
        (latticeCharacterAction H χ x).coeff l +
            (latticeCharacterAction H χ y).coeff l =
          (x.coeff l + y.coeff l) *
            (χ (Multiplicative.ofAdd (QuotientAddGroup.mk' H l)) : k)
      rw [hx, hy]
      ring
  | smul a x hx =>
      rw [map_smul]
      change
        a * (latticeCharacterAction H χ x).coeff l =
          (a * x.coeff l) *
            (χ (Multiplicative.ofAdd (QuotientAddGroup.mk' H l)) : k)
      rw [hx]
      ring

/-- The elements fixed by every quotient character are exactly the
degree-zero part for the quotient grading. -/
theorem fixedBy_latticeCharacterAction_eq_gradeZero
    {k : Type u} {L : Type v} [CommRing k] [IsDomain k]
    [AddCommGroup L]
    (H : AddSubgroup L) [Finite (L ⧸ H)]
    [HasEnoughRootsOfUnity k
      (Monoid.exponent (Multiplicative (L ⧸ H)))] :
    {x : AddMonoidAlgebra k L |
        ∀ χ : Multiplicative (L ⧸ H) →* kˣ,
          latticeCharacterAction H χ x = x} =
      (SetLike.GradeZero.subalgebra
        (AddMonoidAlgebra.gradeBy k (QuotientAddGroup.mk' H)) :
        Set (AddMonoidAlgebra k L)) := by
  ext x
  constructor
  · intro hx
    change x ∈ AddMonoidAlgebra.gradeBy k (QuotientAddGroup.mk' H) 0
    intro l hl
    by_contra hq
    have hqMul :
        Multiplicative.ofAdd (QuotientAddGroup.mk' H l) ≠ 1 := by
      intro h
      apply hq
      exact congrArg Multiplicative.toAdd h
    obtain ⟨χ, hχ⟩ :=
      CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
        (Multiplicative (L ⧸ H)) k hqMul
    have hfix := congrArg
      (fun y : AddMonoidAlgebra k L => y.coeff l) (hx χ)
    rw [latticeCharacterAction_coeff] at hfix
    have hcoeff : x.coeff l ≠ 0 := Finsupp.mem_support_iff.mp hl
    have hχCoe :
        (χ (Multiplicative.ofAdd (QuotientAddGroup.mk' H l)) : k) = 1 :=
      (mul_eq_left₀ hcoeff).mp hfix
    apply hχ
    exact Units.ext hχCoe
  · intro hx χ
    ext l
    rw [latticeCharacterAction_coeff]
    by_cases hcoeff : x.coeff l = 0
    · simp only [hcoeff, zero_mul]
    · have hl : l ∈ x.coeff.support := Finsupp.mem_support_iff.mpr hcoeff
      have hdegree : QuotientAddGroup.mk' H l = 0 := hx l hl
      rw [hdegree]
      change x.coeff l * (χ 1 : k) = x.coeff l
      rw [map_one, Units.val_one, mul_one]

/-- The common fixed subalgebra of quotient characters is the image of the
subgroup lattice algebra. -/
theorem fixedBy_latticeCharacterAction_eq_range
    {k : Type u} {L : Type v} [CommRing k] [IsDomain k]
    [AddCommGroup L]
    (H : AddSubgroup L) [Finite (L ⧸ H)]
    [HasEnoughRootsOfUnity k
      (Monoid.exponent (Multiplicative (L ⧸ H)))] :
    {x : AddMonoidAlgebra k L |
        ∀ χ : Multiplicative (L ⧸ H) →* kˣ,
          latticeCharacterAction H χ x = x} =
      ((AddMonoidAlgebra.mapDomainAlgHom k k H.subtype).range :
        Set (AddMonoidAlgebra k L)) := by
  rw [fixedBy_latticeCharacterAction_eq_gradeZero,
    range_mapDomainAlgHom_eq_gradeZero_quotient]

end

end EtaleFundamentalGroups.Kummer
