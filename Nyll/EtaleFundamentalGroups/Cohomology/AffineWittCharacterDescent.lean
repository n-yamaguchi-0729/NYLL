/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.AffineArtinSchreierCharacters
public import Nyll.GaloisCohomology.ArtinSchreier.WittCharacters
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldMonodromyLift
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGalois
public import Nyll.EtaleFundamentalGroups.Cohomology.GenericPointCharacterDetection
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Descent of actual Witt roots along the generic fundamental-group map

A Witt section of a finite étale cover gives a field root at any geometric
generic fiber point. The kernel of the original generic Galois map fixes
that point, and hence every coefficient of the root. Its root character
therefore descends continuously to the original étale fundamental group.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open ArtinSchreierWittTheory

namespace EtaleFundamentalGroups.Cohomology

variable (X : Scheme.{u}) [IsIntegral X] [IsNormalIntegral X]
  (Ω : Type u) [Field Ω] [Algebra X.functionField Ω]
  [IsSepClosed Ω] [IsSepClosure X.functionField Ω]

private theorem generic_fieldSourceAbsoluteGaloisHom_surjective :
    Function.Surjective (FiniteEtale.fieldSourceAbsoluteGaloisHom
      X.functionField Ω (X.fromSpecStalk (genericPoint X))) :=
  FiniteEtale.genericFieldAction_surjective X Ω

omit [IsNormalIntegral X] in
/-- Evaluating a section after generic monodromy is evaluation followed by
the original field automorphism. -/
theorem finiteEtaleSectionValue_genericFieldAction (W : FiniteEtale X)
    (x : (FiniteEtale.fiber (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
      X.fromSpecStalk (genericPoint X))).obj W)
    (σ : Gal(Ω/X.functionField)) (b : Γ(W.left, ⊤)) :
    finiteEtaleSectionValue W _ (FiniteEtale.fieldSourceAbsoluteGaloisHom
      X.functionField Ω (X.fromSpecStalk (genericPoint X)) σ • x) b =
      σ (finiteEtaleSectionValue W _ x b) := by
  have hl :
      (FiniteEtale.fiberObjEquivHom _ W (FiniteEtale.fieldSourceAbsoluteGaloisHom
        X.functionField Ω (X.fromSpecStalk (genericPoint X)) σ • x)).left =
        Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
          (FiniteEtale.fiberObjEquivHom _ W x).left :=
    FiniteEtale.fundamentalGroupHom_field_fiberLift
      (X.fromSpecStalk (genericPoint X)) W σ x
  exact (congrArg (Scheme.ΓSpecIso (.of Ω)).hom
    ((congrArg (fun f : Spec (.of Ω) ⟶ W.left => f.appTop b) hl).trans
      (ConcreteCategory.congr_hom (Scheme.Hom.comp_appTop
        (Spec.map (CommRingCat.ofHom σ.toRingHom))
        (FiniteEtale.fiberObjEquivHom _ W x).left) b))).trans
    (ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ.toRingHom))
      ((FiniteEtale.fiberObjEquivHom _ W x).left.appTop b))

variable (p m : ℕ) [Fact p.Prime] [CharP Ω p]

/-- A root carried by an actual finite étale cover descends to a continuous
character of the original fundamental group, and its values are the literal
Witt-coordinate displacements on that cover. -/
theorem exists_generic_wittCharacter_of_section (W : FiniteEtale X)
    (x : (FiniteEtale.fiber (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
      X.fromSpecStalk (genericPoint X))).obj W)
    (β : TruncatedWittVector p m Γ(W.left, ⊤))
    (a : TruncatedWittVector p m X.functionField)
    (hβ : TruncatedWittVector.map (frobenius Ω p)
        (TruncatedWittVector.map (finiteEtaleSectionValue W _ x) β) -
          TruncatedWittVector.map (finiteEtaleSectionValue W _ x) β =
            TruncatedWittVector.map (algebraMap X.functionField Ω) a) :
    ∃ χ : Aut (FiniteEtale.fiber (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
        X.fromSpecStalk (genericPoint X))) →ₜ* Multiplicative (ZMod (p ^ m)),
      χ.comp (FiniteEtale.fieldSourceAbsoluteGaloisHom
      X.functionField Ω (X.fromSpecStalk (genericPoint X))) =
        rootCharacter p m Ω a (TruncatedWittVector.map (finiteEtaleSectionValue W _ x) β) hβ ∧
      ∀ γ, constantCast p m Ω (χ γ).toAdd =
        TruncatedWittVector.map (finiteEtaleSectionValue W _ (γ • x)) β -
          TruncatedWittVector.map (finiteEtaleSectionValue W _ x) β := by
  let φ := FiniteEtale.fieldSourceAbsoluteGaloisHom
      X.functionField Ω (X.fromSpecStalk (genericPoint X))
  let r := TruncatedWittVector.map (finiteEtaleSectionValue W _ x) β
  let c := rootCharacter p m Ω a r hβ
  have heval (σ : Gal(Ω/X.functionField)) :
      TruncatedWittVector.map (finiteEtaleSectionValue W _ (φ σ • x)) β =
        TruncatedWittVector.map σ.toRingHom r := by
    apply TruncatedWittVector.ext
    intro i
    simp only [r, TruncatedWittVector.map_coeff]
    exact finiteEtaleSectionValue_genericFieldAction X Ω W x σ (β.coeff i)
  have hker : φ.toMonoidHom.ker ≤ c.toMonoidHom.ker := by
    intro σ hσ
    apply (rootCharacter_eq_one_iff p m Ω a r hβ σ).mpr
    have hφ : φ σ = 1 := MonoidHom.mem_ker.mp hσ
    have hx : φ σ • x = x := by rw [hφ, one_smul]
    exact (heval σ).symm.trans
      (congrArg (fun y => TruncatedWittVector.map (finiteEtaleSectionValue W _ y) β) hx)
  have hsurj : Function.Surjective φ := generic_fieldSourceAbsoluteGaloisHom_surjective X Ω
  let d := φ.toMonoidHom.liftOfSurjective hsurj ⟨c.toMonoidHom, hker⟩
  have hd (σ : Gal(Ω/X.functionField)) : d (φ σ) = c σ :=
    φ.toMonoidHom.liftOfRightInverse_comp_apply
      (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj)
        ⟨c.toMonoidHom, hker⟩ σ
  have hdcont : Continuous d := by
    have hq : Topology.IsQuotientMap φ :=
      Topology.IsQuotientMap.of_surjective_continuous hsurj φ.continuous
    rw [hq.continuous_iff]
    have hcomp : d ∘ φ = c := funext hd
    rw [hcomp]
    exact c.continuous
  refine ⟨⟨d, hdcont⟩, ContinuousMonoidHom.ext hd, ?_⟩
  intro γ
  obtain ⟨σ, rfl⟩ := hsurj γ
  change constantCast p m Ω (d (φ σ)).toAdd = _
  rw [hd, rootCharacter_cast, heval]

end EtaleFundamentalGroups.Cohomology
