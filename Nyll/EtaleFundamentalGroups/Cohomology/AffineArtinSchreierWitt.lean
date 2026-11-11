/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GaloisCovers.AffineTorsorAction
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineArtinSchreierCharacters
public import Nyll.GaloisCohomology.GroupTheory.FiniteTorsorWitt
public import Nyll.EtaleFundamentalGroups.GaloisCategories.DiscreteCharacters
public import Mathlib.CategoryTheory.Endomorphism
public import Nyll.GaloisCohomology.ArtinSchreier.WittCharacters

/-!
# Actual affine étale characters as Artin–Schreier–Witt equations

The original fundamental-group character supplies its actual pointed
finite Galois cover. Its section-ring torsor and trace-one construction
give a Witt equation over the original affine base. Evaluation of the
Witt root on the same geometric fiber recovers the given character.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open ArtinSchreierWittTheory GaloisCohomology.FiniteTorsor

namespace EtaleFundamentalGroups.Cohomology

universe u

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (xi : Spec (.of Ω) ⟶ X) (p m : ℕ) [Fact p.Prime]

/-- Coefficientwise Witt evaluation respects the original geometric deck map. -/
theorem finiteEtaleWittSectionValue_deck (W : FiniteEtale X) (σ : Aut W)
    (w : (FiniteEtale.fiber xi).obj W) (β : TruncatedWittVector p m Γ(W.left, ⊤)) :
    TruncatedWittVector.map
        (finiteEtaleSectionValue W xi ((FiniteEtale.fiber xi).map σ.asIso.hom w)) β =
      TruncatedWittVector.map (finiteEtaleSectionValue W xi w)
        (TruncatedWittVector.map σ.asIso.hom.left.appTop.hom β) := by
  have hn :
      (FiniteEtale.fiberObjEquivHom xi W ((FiniteEtale.fiber xi).map σ.asIso.hom w)).left =
        (FiniteEtale.fiberObjEquivHom xi W w).left ≫ σ.asIso.hom.left :=
    (congrArg (fun f : Over.mk xi ⟶ W.toComma => f.left)
      (FiniteEtale.fiberObjEquivHom_naturality xi σ.asIso.hom w)).symm
  apply TruncatedWittVector.ext
  intro i
  simp only [TruncatedWittVector.map_coeff]
  exact congrArg (Scheme.ΓSpecIso (.of Ω)).hom
    ((congrArg (fun f : Spec (.of Ω) ⟶ W.left => f.appTop (β.coeff i)) hn).trans
      (ConcreteCategory.congr_hom (Scheme.Hom.comp_appTop
        (FiniteEtale.fiberObjEquivHom xi W w).left σ.asIso.hom.left) (β.coeff i)))

variable [ConnectedSpace X] [IsAffine X] [CharP Γ(X, ⊤) p] [CharP Ω p]

/-- Every continuous cyclic prime-power character of the original affine
étale fundamental group is the literal evaluation displacement of a Witt
root on its actual pointed finite Galois cover. -/
theorem exists_wittEquation_of_fundamentalGroup_character
    (χ : Aut (FiniteEtale.fiber xi) →ₜ* Multiplicative (ZMod (p ^ m))) :
    ∃ (W : FiniteEtale X) (hW : IsGalois W) (w : (FiniteEtale.fiber xi).obj W),
      let _ : IsGalois W := hW
      let _ : CharP Γ(W.left, ⊤) p := finiteEtaleSection_charP W p
      ∃ (a : TruncatedWittVector p m Γ(X, ⊤)) (β : TruncatedWittVector p m Γ(W.left, ⊤)),
        TruncatedWittVector.map (frobenius Γ(W.left, ⊤) p) β - β =
          TruncatedWittVector.map W.hom.appTop.hom a ∧
        ∀ γ : Aut (FiniteEtale.fiber xi),
          TruncatedWittVector.map (finiteEtaleSectionValue W xi (γ • w)) β -
            TruncatedWittVector.map (finiteEtaleSectionValue W xi w) β =
              constantCast p m Ω (χ γ).toAdd := by
  obtain ⟨W, hW, w, e, heinj, he⟩ :=
    exists_galoisObject_discreteCharacter_embedding (FiniteEtale.fiber xi) χ
  have : NeZero (p ^ m) := ⟨pow_ne_zero m (Fact.out : p.Prime).ne_zero⟩
  have : Finite (Aut W)ᵐᵒᵖ := Finite.of_injective e heinj
  let : IsGalois W := hW
  let : Algebra Γ(X, ⊤) Γ(W.left, ⊤) := finiteEtaleSectionAlgebra W
  have : Module.FaithfullyFlat Γ(X, ⊤) Γ(W.left, ⊤) :=
    finiteEtaleSection_faithfullyFlat W
  have : CharP Γ(W.left, ⊤) p := finiteEtaleSection_charP W p
  obtain ⟨a, β, hβ, ht⟩ := exists_witt_root_of_character Γ(X, ⊤) Γ(W.left, ⊤)
    (finiteEtaleSectionAction W) p m (finiteEtaleSection_tensorMap_bijective W) e
  refine ⟨W, hW, w, a, β, hβ, ?_⟩
  intro γ
  let q : Aut (FiniteEtale.fiber xi) →* (Aut W)ᵐᵒᵖ :=
    galoisObjectQuotientMonoidHom (FiniteEtale.fiber xi) (Aut (FiniteEtale.fiber xi)) W w
  have hq : (FiniteEtale.fiber xi).map (q γ).unop.asIso.hom w = γ • w :=
    galoisObjectQuotientMonoidHom_evaluation
      (FiniteEtale.fiber xi) (Aut (FiniteEtale.fiber xi)) W w γ
  have hχ : e (q γ) = χ γ := congrArg
    (fun f : Aut (FiniteEtale.fiber xi) →* Multiplicative (ZMod (p ^ m)) => f γ) he
  have hmap : TruncatedWittVector.map (finiteEtaleSectionAction W (q γ)).toRingHom β =
      TruncatedWittVector.map (q γ).unop.asIso.hom.left.appTop.hom β := by
    apply TruncatedWittVector.ext
    intro i
    simp only [TruncatedWittVector.map_coeff]
    exact finiteEtaleSectionAction_apply W (q γ) (β.coeff i)
  have htranslation := ht (q γ)
  rw [hmap, hχ] at htranslation
  calc
    TruncatedWittVector.map (finiteEtaleSectionValue W xi (γ • w)) β -
        TruncatedWittVector.map (finiteEtaleSectionValue W xi w) β =
      TruncatedWittVector.map (finiteEtaleSectionValue W xi w)
        (TruncatedWittVector.map (q γ).unop.asIso.hom.left.appTop.hom β - β) := by
      rw [map_sub, ← finiteEtaleWittSectionValue_deck xi p m W (q γ).unop w β, hq]
    _ = constantCast p m Ω (χ γ).toAdd := by
      rw [htranslation, constantCast_natural]

end EtaleFundamentalGroups.Cohomology
