/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.WeilRestriction.ScalarQuotientPresheaf
import Nyll.SchemeTheory.Affine.WeilRestriction.UnitRestriction

/-! # Actual unit fibres after taking the scalar quotient -/

noncomputable section

universe u

open Module
open scoped TensorProduct

namespace SchemeTheory.Affine.ScalarQuotientPresheaf

variable {R A B S : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing S]
  [Algebra R A] [Algebra R B] [Algebra R S] (f : A →ₐ[R] B)

/-- Restriction of the algebra factor acts on actual tensor units. -/
def algebraUnitRestriction : (S ⊗[R] A)ˣ →* (S ⊗[R] B)ˣ :=
  Units.map (Algebra.TensorProduct.map (AlgHom.id R S) f).toRingHom.toMonoidHom

/-- Restriction preserves the parameter scalar itself. -/
theorem algebraUnitRestriction_scalarHom (r : Sˣ) :
    algebraUnitRestriction f (scalarHom (R := R) (A := A) r) =
      scalarHom (R := R) (A := B) r := by
  apply Units.ext
  change Algebra.TensorProduct.map (AlgHom.id R S) f ((r : S) ⊗ₜ[R] (1 : A)) =
    (r : S) ⊗ₜ[R] (1 : B)
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

/-- Algebra restriction descends to the literal quotient by parameter scalars. -/
def algebraQuotientRestriction : ScalarQuotient (R := R) (A := A) (S := S) →*
    ScalarQuotient (R := R) (A := B) (S := S) :=
  QuotientGroup.map _ _ (algebraUnitRestriction f) (by
    rintro a ⟨r, rfl⟩
    exact ⟨r, (algebraUnitRestriction_scalarHom f r).symm⟩)

/-- A nonempty basis proves scalar injectivity after every scalar extension. -/
theorem scalarHom_injective_of_basis {κ : Type} [Nonempty κ] (bB : Basis κ R B) :
    Function.Injective (scalarHom (R := R) (A := B) (S := S)) := by
  intro r s h
  apply Units.ext
  let e := Algebra.TensorProduct.basis S bB
  let j : κ := Classical.choice inferInstance
  have hv : algebraMap S (S ⊗[R] B) (r : S) =
      algebraMap S (S ⊗[R] B) (s : S) := congrArg Units.val h
  have hm : (r : S) • e j = (s : S) • e j := by
    rw [Algebra.smul_def, Algebra.smul_def, hv]
  have hc := congrArg (fun z : S ⊗[R] B => e.repr z j) hm
  simpa only [map_smul, Finsupp.smul_apply, Basis.repr_self, Finsupp.single_eq_same,
    smul_eq_mul, mul_one] using hc

/-- The actual fibre product of scalar classes and target units. -/
abbrev RestrictionUnitFiber :=
  {p : ScalarQuotient (R := R) (A := A) (S := S) × (S ⊗[R] B)ˣ //
    algebraQuotientRestriction f p.1 = QuotientGroup.mk p.2}

/-- A source unit gives its scalar class and its actual restricted target unit. -/
def toRestrictionUnitFiber (a : (S ⊗[R] A)ˣ) : RestrictionUnitFiber (S := S) f :=
  ⟨(QuotientGroup.mk a, algebraUnitRestriction f a), rfl⟩

/-- Equality of source scalar classes and target units forces equality of actual
source units, because the target has a nonempty basis. -/
theorem toRestrictionUnitFiber_injective {κ : Type} [Nonempty κ] (bB : Basis κ R B) :
    Function.Injective (toRestrictionUnitFiber (S := S) f) := by
  intro a b h
  have hq : (QuotientGroup.mk a : ScalarQuotient (R := R) (A := A) (S := S)) =
      QuotientGroup.mk b := congrArg (fun p : RestrictionUnitFiber (S := S) f => p.val.1) h
  have hu : algebraUnitRestriction f a = algebraUnitRestriction f b :=
    congrArg (fun p : RestrictionUnitFiber (S := S) f => p.val.2) h
  obtain ⟨r, hr⟩ := QuotientGroup.eq_iff_div_mem.mp hq
  have hs : scalarHom (R := R) (A := B) r = 1 := by
    rw [← algebraUnitRestriction_scalarHom f r, hr, map_div, hu, div_self']
  have hr1 : r = 1 := scalarHom_injective_of_basis (S := S) bB
    (hs.trans (scalarHom (R := R) (A := B) (S := S)).map_one.symm)
  apply div_eq_one.mp
  exact hr.symm.trans ((congrArg (scalarHom (R := R) (A := A) (S := S)) hr1).trans
    (scalarHom (R := R) (A := A) (S := S)).map_one)

/-- A scalar-class lift can be uniquely normalized to any chosen target unit.
Existence uses only the actual equality in the target scalar quotient. -/
theorem toRestrictionUnitFiber_surjective :
    Function.Surjective (toRestrictionUnitFiber (S := S) f) := by
  rintro ⟨⟨x, b⟩, hx⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  change (QuotientGroup.mk (algebraUnitRestriction f a) :
    ScalarQuotient (R := R) (A := B) (S := S)) = QuotientGroup.mk b at hx
  obtain ⟨r, hr⟩ := QuotientGroup.eq_iff_div_mem.mp hx
  refine ⟨(scalarHom (R := R) (A := A) r)⁻¹ * a, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change (QuotientGroup.mk' (scalarSubgroup (R := R) (A := A) (S := S)))
      ((scalarHom r)⁻¹ * a) = QuotientGroup.mk a
    rw [map_mul, map_inv]
    have hs : (QuotientGroup.mk (scalarHom (R := R) (A := A) r) :
        ScalarQuotient (R := R) (A := A) (S := S)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨r, rfl⟩
    change (QuotientGroup.mk (scalarHom (R := R) (A := A) r) :
      ScalarQuotient (R := R) (A := A) (S := S))⁻¹ * QuotientGroup.mk a = QuotientGroup.mk a
    rw [hs, inv_one]
    exact one_mul (QuotientGroup.mk a : ScalarQuotient (R := R) (A := A) (S := S))
  · change algebraUnitRestriction f ((scalarHom r)⁻¹ * a) = b
    rw [map_mul, map_inv, algebraUnitRestriction_scalarHom, hr, inv_div, div_mul_cancel]

/-- The scalar-quotient restriction square is Cartesian on literal algebra points.
This is the concrete normalization underlying its geometric Cartesian comparison. -/
def restrictionUnitFiberEquiv {κ : Type} [Nonempty κ] (bB : Basis κ R B) :
    (S ⊗[R] A)ˣ ≃ RestrictionUnitFiber (S := S) f :=
  Equiv.ofBijective (toRestrictionUnitFiber f)
    ⟨toRestrictionUnitFiber_injective f bB, toRestrictionUnitFiber_surjective f⟩

end SchemeTheory.Affine.ScalarQuotientPresheaf
