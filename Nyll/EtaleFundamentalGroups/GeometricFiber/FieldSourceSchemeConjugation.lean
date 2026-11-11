/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGalois
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGaloisPoint
public import Nyll.EtaleFundamentalGroups.GeometricFiber.ExtendedFiberGaloisAction
public import Nyll.EtaleFundamentalGroups.GeometricFiber.HenselianSpecializationConjugacy
public import Nyll.EtaleFundamentalGroups.GeometricFiber.SourceIso
public import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugation
public import Nyll.SchemeTheory.FunctionFields.GenericSourceIso
public import Nyll.SchemeTheory.FunctionFields.OpenImmersion

/-!
# Scheme pullback and semilinear conjugation at an actual field source

The original field-source Galois map and the source-isomorphism comparison
act on points by their specified spectrum maps. Their point formulas identify
the actual scheme-induced map with semilinear conjugation. The existing
generic-point lift supplies the source square for every scheme automorphism.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

/-- A scheme map compatible with a semilinear source lift sends the positively
conjugated field-source action to the source transport of the original action. -/
theorem fieldSourceAbsoluteGaloisHom_schemeConjugate
    {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω]
    [IsSepClosure F Ω] [IsSepClosed Ω]
    {X : Scheme.{u}} [IsIntegral X]
    (q : Spec (.of F) ⟶ X) (θ : X ⟶ X)
    (φ : F ≃+* F) (a : Ω ≃+* Ω)
    (ha : ∀ z : F, a (algebraMap F Ω z) = algebraMap F Ω (φ z))
    (hpoint : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (ξ F Ω ≫ q) =
      (ξ F Ω ≫ q) ≫ θ)
    (ρ : Gal(Ω/F)) :
    let e := Scheme.Spec.mapIso a.toCommRingCatIso.op
    let p := ξ F Ω ≫ q
    (eqToIso (congrArg fiber hpoint.symm)).conjAut
        (fundamentalGroupHom θ p
          (fieldSourceAbsoluteGaloisHom F Ω q
            (KummerTheory.semilinearGaloisConjugate φ a ha ρ))) =
      (fiberSourceIso p e).conjAut (fieldSourceAbsoluteGaloisHom F Ω q ρ) := by
  intro e p
  let ρ' := KummerTheory.semilinearGaloisConjugate φ a ha ρ
  let s : fiber p ≅ fiber (e.hom ≫ p) := fiberSourceIso p e
  let b : Aut (fiber (e.hom ≫ p)) :=
    (eqToIso (congrArg fiber hpoint.symm)).conjAut
      (fundamentalGroupHom θ p (fieldSourceAbsoluteGaloisHom F Ω q ρ'))
  have hj (τ : Gal(Ω/F)) (Z : FiniteEtale X) (z : (fiber p).obj Z) :
      (fiberObjEquivHom p Z
        ((fieldSourceAbsoluteGaloisHom F Ω q τ).asIso.hom.app Z z)).left =
        Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
          (fiberObjEquivHom p Z z).left :=
    fundamentalGroupHom_point_of_point_action q (ξ F Ω)
      (suppliedGaloisEquivFundamentalGroup F Ω τ) τ.toRingHom
      (suppliedGaloisEquivFundamentalGroup_point F Ω τ) Z z
  have hb (Z : FiniteEtale X) (z : (fiber (e.hom ≫ p)).obj Z) :
      (fiberObjEquivHom (e.hom ≫ p) Z (b.asIso.hom.app Z z)).left =
        Spec.map (CommRingCat.ofHom ρ'.toRingHom) ≫
          (fiberObjEquivHom (e.hom ≫ p) Z z).left :=
    point_action_of_eqToIso hpoint.symm
      (fundamentalGroupHom θ p (fieldSourceAbsoluteGaloisHom F Ω q ρ'))
      ρ'.toRingHom
      (fundamentalGroupHom_point_of_point_action θ p
        (fieldSourceAbsoluteGaloisHom F Ω q ρ') ρ'.toRingHom (hj ρ')) Z z
  have hr : ρ'.toRingHom.comp a.toRingHom = a.toRingHom.comp ρ.toRingHom := by
    apply RingHom.ext
    intro z
    change KummerTheory.semilinearGaloisConjugate φ a ha ρ (a z) = a (ρ z)
    rw [KummerTheory.semilinearGaloisConjugate_apply, a.symm_apply_apply]
  have hspec : Spec.map (CommRingCat.ofHom ρ'.toRingHom) ≫ e.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom ρ.toRingHom) := by
    change Spec.map (CommRingCat.ofHom ρ'.toRingHom) ≫
        Spec.map (CommRingCat.ofHom a.toRingHom) =
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫
        Spec.map (CommRingCat.ofHom ρ.toRingHom)
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun r : Ω →+* Ω => Spec.map (CommRingCat.ofHom r)) hr
  have hn : (fieldSourceAbsoluteGaloisHom F Ω q ρ).asIso.hom ≫ s.hom = s.hom ≫ b.asIso.hom := by
    ext Z z
    apply (fiberObjEquivHom (e.hom ≫ p) Z).injective
    apply Over.OverMorphism.ext
    change (fiberObjEquivHom (e.hom ≫ p) Z
        (s.hom.app Z ((fieldSourceAbsoluteGaloisHom F Ω q ρ).asIso.hom.app Z z))).left =
      (fiberObjEquivHom (e.hom ≫ p) Z (b.asIso.hom.app Z (s.hom.app Z z))).left
    rw [fiberSourceIso_point, hj, hb, fiberSourceIso_point]
    exact (Category.assoc e.hom (Spec.map (CommRingCat.ofHom ρ.toRingHom))
      (fiberObjEquivHom p Z z).left).symm.trans
        ((congrArg (fun t => t ≫ (fiberObjEquivHom p Z z).left) hspec.symm).trans
          (Category.assoc (Spec.map (CommRingCat.ofHom ρ'.toRingHom)) e.hom
            (fiberObjEquivHom p Z z).left))
  change b = s.conjAut (fieldSourceAbsoluteGaloisHom F Ω q ρ)
  apply Aut.ext
  apply Iso.ext
  rw [Iso.conjAut_hom, Iso.conj_apply_asHom]
  exact (s.inv_hom_id_assoc b.asIso.hom).symm.trans (congrArg (s.inv ≫ ·) hn.symm)

/-- The actual generic-point lift of a scheme automorphism satisfies the
field-source conjugation square for every original Galois element. -/
theorem exists_genericPoint_sourceIso_conjugate
    {X : Scheme.{u}} [IsIntegral X] (θ : X ≅ X)
    (Ω : Type u) [Field Ω] [Algebra X.functionField Ω]
    [IsSepClosure X.functionField Ω] :
    let _ : IsSepClosed Ω := IsSepClosure.sep_closed X.functionField
    let φ := θ.hom.functionFieldRingEquivOfIsOpenImmersion
    let q := X.fromSpecStalk (genericPoint X)
    let p := ξ X.functionField Ω ≫ q
    ∃ (a : Ω ≃+* Ω)
      (ha : ∀ z : X.functionField,
        a (algebraMap X.functionField Ω z) = algebraMap X.functionField Ω (φ z))
      (hpoint : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ p = p ≫ θ.hom),
      ∀ ρ : Gal(Ω/X.functionField),
        (eqToIso (congrArg fiber hpoint.symm)).conjAut
            (fundamentalGroupHom θ.hom p
              (fieldSourceAbsoluteGaloisHom X.functionField Ω q
                (KummerTheory.semilinearGaloisConjugate φ a ha ρ))) =
          (fiberSourceIso p (Scheme.Spec.mapIso a.toCommRingCatIso.op)).conjAut
            (fieldSourceAbsoluteGaloisHom X.functionField Ω q ρ) := by
  intro closureIsSepClosed φ q p
  obtain ⟨a, ha, hpoint⟩ :=
    AnabelianGeometry.WeightFiltration.exists_genericPoint_sourceIso θ Ω
  refine ⟨a, ha, hpoint, ?_⟩
  intro ρ
  exact fieldSourceAbsoluteGaloisHom_schemeConjugate q θ.hom φ a ha hpoint ρ

end AlgebraicGeometry.FiniteEtale
