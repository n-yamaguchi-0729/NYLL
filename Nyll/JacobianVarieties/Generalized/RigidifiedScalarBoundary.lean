/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Repository: https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.RigidifiedScalars
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# The scalar quotient for globally trivial underlying bundles

For an arbitrary scheme morphism, the quotient of units on the modulus by
restrictions of global units classifies exactly the chosen-rigidified classes
whose underlying line bundle is globally trivial. No assertion about the
relative Picard sheaf kernel or the constant field is built into this result.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

variable {X D : Scheme.{u}} (i : D ⟶ X)

/-- Transport the chosen trivialization along a genuine underlying trivialization. -/
def scalarAutOfTrivialization (M : RigidifiedLineBundle i)
    (e : M.L ≅ 𝟙_ X.Modules) : 𝟙_ D.Modules ≅ 𝟙_ D.Modules :=
  (Scheme.Modules.pullbackTensorUnitObjIso i).symm ≪≫
    ((Scheme.Modules.pullback i).mapIso e).symm ≪≫ M.trivialization

/-- The transported scalar automorphism yields a compatible isomorphism. -/
def isoUnitWithOfTrivialization (M : RigidifiedLineBundle i)
    (e : M.L ≅ 𝟙_ X.Modules) :
    Iso M (unitWith i (scalarAutOfTrivialization i M e)) where
  toIso := e
  compatible := by
    change (Scheme.Modules.pullback i).map e.hom ≫
      (Scheme.Modules.pullbackTensorUnitObjIso i).hom ≫
        (Scheme.Modules.pullbackTensorUnitObjIso i).inv ≫
          (Scheme.Modules.pullback i).map e.inv ≫ M.trivialization.hom = _
    rw [CategoryTheory.Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc,
      e.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- Global triviality of the underlying bundle is invariant under compatible isomorphism. -/
def IsGloballyTrivial : Classes i → Prop :=
  Quotient.lift (fun M => Nonempty (M.L ≅ 𝟙_ X.Modules)) (by
    intro M N h
    obtain ⟨e⟩ := h
    apply propext
    constructor
    · rintro ⟨f⟩
      exact ⟨e.toIso.symm ≪≫ f⟩
    · rintro ⟨f⟩
      exact ⟨e.toIso ≪≫ f⟩)

/-- The actual scalar boundary, retaining the chosen modulus automorphism. -/
def scalarClass (a : Γ(D, ⊤)ˣ) : Classes i :=
  classOf (unitWith i ((unitAutEquivUnits D).symm a))

/-- The relation on scalar classes is exactly the restriction of global units. -/
theorem scalarClass_eq_iff (a b : Γ(D, ⊤)ˣ) :
    scalarClass i a = scalarClass i b ↔
      ∃ c : Γ(X, ⊤)ˣ, Units.map i.appTop.hom.toMonoidHom c * b = a := by
  change Quotient.mk _ _ = Quotient.mk _ _ ↔ _
  exact Quotient.eq.trans (unitWith_scalars_iso_iff i a b)

/-- Scalar classes are precisely the classes with globally trivial underlying bundle. -/
theorem scalarClass_range : Set.range (scalarClass i) =
    {x | IsGloballyTrivial i x} := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨CategoryTheory.Iso.refl _⟩
  · intro hx
    induction x using Quotient.ind with
    | _ M =>
      obtain ⟨e⟩ := hx
      refine ⟨unitAutEquivUnits D (scalarAutOfTrivialization i M e), ?_⟩
      change classOf (unitWith i ((unitAutEquivUnits D).symm
        (unitAutEquivUnits D (scalarAutOfTrivialization i M e)))) = classOf M
      exact (congrArg (fun a : Aut (𝟙_ D.Modules) => classOf (unitWith i a))
        ((unitAutEquivUnits D).symm_apply_apply (scalarAutOfTrivialization i M e))).trans
          (Quotient.sound ⟨(isoUnitWithOfTrivialization i M e).symm⟩)

/-- Scalars that extend to global units of the ambient scheme. -/
def extendingScalars : Subgroup Γ(D, ⊤)ˣ :=
  (Units.map i.appTop.hom.toMonoidHom).range

/-- The scalar boundary descends through its exact scalar relation. -/
def scalarQuotientClass : Γ(D, ⊤)ˣ ⧸ extendingScalars i → Classes i :=
  Quotient.lift (scalarClass i) (by
    intro a b h
    have hab : (QuotientGroup.mk a : Γ(D, ⊤)ˣ ⧸ extendingScalars i) =
        QuotientGroup.mk b := Quotient.sound h
    obtain ⟨c, hc⟩ := QuotientGroup.eq_iff_div_mem.mp hab
    apply (scalarClass_eq_iff i a b).mpr
    refine ⟨c, ?_⟩
    rw [hc, div_mul_cancel])

theorem scalarQuotientClass_injective : Function.Injective (scalarQuotientClass i) := by
  intro x y
  refine QuotientGroup.induction_on x fun a => ?_
  refine QuotientGroup.induction_on y fun b => ?_
  intro h
  obtain ⟨c, hc⟩ := (scalarClass_eq_iff i a b).mp h
  apply QuotientGroup.eq_iff_div_mem.mpr
  exact ⟨c, (eq_div_iff_mul_eq').mpr hc⟩

/-- The quotient of actual units classifies exactly globally trivial underlying
bundles, with their chosen modulus trivializations and compatible isomorphisms. -/
def scalarQuotientEquivGloballyTrivial :
    Γ(D, ⊤)ˣ ⧸ extendingScalars i ≃ {x : Classes i // IsGloballyTrivial i x} := by
  let f : Γ(D, ⊤)ˣ ⧸ extendingScalars i → {x : Classes i // IsGloballyTrivial i x} :=
    fun q => ⟨scalarQuotientClass i q, by
      refine QuotientGroup.induction_on q fun a => ?_
      exact ⟨CategoryTheory.Iso.refl _⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    exact scalarQuotientClass_injective i (congrArg Subtype.val h)
  · intro x
    obtain ⟨a, ha⟩ := (Set.ext_iff.mp (scalarClass_range i) x.1).mpr x.2
    exact ⟨QuotientGroup.mk a, Subtype.ext ha⟩

end AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
