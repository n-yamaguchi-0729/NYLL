/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.H1Character
public import Nyll.EtaleFundamentalGroups.Cohomology.H1CharacterPullback
public import Nyll.EtaleFundamentalGroups.Cohomology.SchemePullback
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGalois
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceSchemeConjugation
public import Nyll.EtaleFundamentalGroups.GeometricFiber.Functoriality
public import Nyll.EtaleFundamentalGroups.GeometricFiber.SourceIso
public import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugation
public import Nyll.SchemeTheory.FunctionFields.OpenImmersion
public import Mathlib.FieldTheory.IsSepClosed

/-!
# Actual H¹ pullback at a semilinear field source

The proved scheme-induced conjugation square and naturality of the original
finite-coefficient H¹ character identify pullback with inverse conjugation.
For a scheme automorphism, its actual generic-point lift supplies the source
square; no compatibility of cohomological actions is assumed.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Cohomology

/-- Actual scheme pullback, evaluated on the positively conjugated field
action, equals the original H¹ character on the original field action. -/
theorem h1Character_fieldSource_schemeConjugate
    {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω]
    [IsSepClosure F Ω] [IsSepClosed Ω]
    {X : Scheme.{u}} [IsIntegral X]
    (q : Spec (.of F) ⟶ X) (θ : X ⟶ X)
    (φ : F ≃+* F) (a : Ω ≃+* Ω)
    (ha : ∀ z : F, a (algebraMap F Ω z) = algebraMap F Ω (φ z))
    (hpoint : Spec.map (CommRingCat.ofHom a.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ q) =
      (Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ q) ≫ θ)
    (A : AddCommGrpCat.{u}) [Finite A]
    (x : Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) 1)
    (ρ : Gal(Ω/F)) :
    let p := Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ q
    let : TopologicalSpace (Multiplicative A) := ⊥
    h1Character A p (constantCohomologyPullback θ A 1 x)
        (FiniteEtale.fieldSourceAbsoluteGaloisHom F Ω q
          (KummerTheory.semilinearGaloisConjugate φ a ha ρ)) =
      h1Character A p x (FiniteEtale.fieldSourceAbsoluteGaloisHom F Ω q ρ) := by
  intro p tA
  let e : Spec (.of Ω) ≅ Spec (.of Ω) := Scheme.Spec.mapIso a.toCommRingCatIso.op
  let c : FiniteEtale.fiber (p ≫ θ) ≅ FiniteEtale.fiber (e.hom ≫ p) :=
    eqToIso (congrArg FiniteEtale.fiber hpoint.symm)
  let s : FiniteEtale.fiber p ≅ FiniteEtale.fiber (e.hom ≫ p) :=
    FiniteEtale.fiberSourceIso p e
  let J := FiniteEtale.fieldSourceAbsoluteGaloisHom F Ω q
  let ρ' := KummerTheory.semilinearGaloisConjugate φ a ha ρ
  have hconj : c.conjAut (FiniteEtale.fundamentalGroupHom θ p (J ρ')) =
      s.conjAut (J ρ) :=
    FiniteEtale.fieldSourceAbsoluteGaloisHom_schemeConjugate q θ φ a ha hpoint ρ
  have hp := DFunLike.congr_fun (h1Character_schemePullback θ A p x) (J ρ')
  change h1Character A (p ≫ θ) x (FiniteEtale.fundamentalGroupHom θ p (J ρ')) =
    h1Character A p (constantCohomologyPullback θ A 1 x) (J ρ') at hp
  have hc := DFunLike.congr_fun
    (h1Character_basePoint A (p ≫ θ) (e.hom ≫ p) c x)
    (FiniteEtale.fundamentalGroupHom θ p (J ρ'))
  change h1Character A (e.hom ≫ p) x
      (c.conjAut (FiniteEtale.fundamentalGroupHom θ p (J ρ'))) =
    h1Character A (p ≫ θ) x (FiniteEtale.fundamentalGroupHom θ p (J ρ')) at hc
  have hs := DFunLike.congr_fun (h1Character_basePoint A p (e.hom ≫ p) s x) (J ρ)
  change h1Character A (e.hom ≫ p) x (s.conjAut (J ρ)) =
    h1Character A p x (J ρ) at hs
  exact hp.symm.trans (hc.symm.trans
    ((congrArg (h1Character A (e.hom ≫ p) x) hconj).trans hs))

/-- Every scheme automorphism has an actual generic-point lift for which
the original finite-coefficient H¹ pullback satisfies the character square. -/
theorem exists_h1Character_genericSource_schemeConjugate
    {X : Scheme.{u}} [IsIntegral X] (θ : X ≅ X)
    (Ω : Type u) [Field Ω] [Algebra X.functionField Ω]
    [IsSepClosure X.functionField Ω]
    (A : AddCommGrpCat.{u}) [Finite A] :
    let _ : IsSepClosed Ω := IsSepClosure.sep_closed X.functionField
    let φ := θ.hom.functionFieldRingEquivOfIsOpenImmersion
    let q := X.fromSpecStalk (genericPoint X)
    let p := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫ q
    let : TopologicalSpace (Multiplicative A) := ⊥
    ∃ (a : Ω ≃+* Ω)
      (ha : ∀ z : X.functionField,
        a (algebraMap X.functionField Ω z) = algebraMap X.functionField Ω (φ z)),
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫ p = p ≫ θ.hom ∧
      ∀ (x : Sheaf.H.{u}
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) 1)
        (ρ : Gal(Ω/X.functionField)),
        h1Character A p (constantCohomologyPullback θ.hom A 1 x)
            (FiniteEtale.fieldSourceAbsoluteGaloisHom X.functionField Ω q
              (KummerTheory.semilinearGaloisConjugate φ a ha ρ)) =
          h1Character A p x (FiniteEtale.fieldSourceAbsoluteGaloisHom X.functionField Ω q ρ) := by
  intro closureIsSepClosed φ q p tA
  obtain ⟨a, ha, hpoint, _⟩ := FiniteEtale.exists_genericPoint_sourceIso_conjugate θ Ω
  refine ⟨a, ha, hpoint, ?_⟩
  intro x ρ
  exact h1Character_fieldSource_schemeConjugate q θ.hom φ a ha hpoint A x ρ

end EtaleFundamentalGroups.Cohomology
