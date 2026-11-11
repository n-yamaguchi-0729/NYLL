/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.AffineWittRootCover
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineWittCharacterDescent
public import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected
public import Nyll.GaloisCohomology.ArtinSchreier.WittCharacters

/-!
# Native characters of arbitrary affine Witt coefficients

The finite étale root algebra is placed over the original affine scheme.
Its actual geometric generic fiber supplies the root used in the continuous
descent theorem. Thus every affine coefficient gives a character of the
original étale fundamental group at every finite Witt length.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open ArtinSchreierWittTheory

namespace EtaleFundamentalGroups.Cohomology

variable (X : Scheme.{u}) [IsAffine X] (p m : ℕ) [Fact p.Prime]
  [Nontrivial Γ(X, ⊤)] [CharP Γ(X, ⊤) p]

/-- The recursively constructed Witt root algebra gives a nonempty actual
finite étale cover and a root in its original ring of global sections. -/
theorem exists_finiteEtale_wittSection (a : TruncatedWittVector p m Γ(X, ⊤)) :
    ∃ W : FiniteEtale X, Nonempty W.left ∧
      ∃ (_ : CharP Γ(W.left, ⊤) p) (β : TruncatedWittVector p m Γ(W.left, ⊤)),
        TruncatedWittVector.map (frobenius Γ(W.left, ⊤) p) β - β =
          TruncatedWittVector.map W.hom.appTop.hom a := by
  obtain ⟨S, ringS, algS, charS, finiteS, etaleS, flatS, β, hβ⟩ :=
    exists_finiteEtale_truncatedWittRoot_extension p m Γ(X, ⊤) a
  have : Nontrivial S := CharP.nontrivial_of_char_ne_one (Fact.out : p.Prime).ne_one
  have : IsFinite (Spec.algebraMap Γ(X, ⊤) S) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have : Etale (Spec.algebraMap Γ(X, ⊤) S) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  let g := Spec.algebraMap Γ(X, ⊤) S ≫ X.isoSpec.inv
  have : IsFinite g := inferInstance
  have : Etale g := inferInstance
  have : IsFiniteEtale g := ⟨⟩
  let W : FiniteEtale X := FiniteEtale.mk g
  have : Nonempty W.left := inferInstanceAs (Nonempty (Spec (.of S)))
  let e := (Scheme.ΓSpecIso (.of S)).commRingCatIsoToRingEquiv.symm
  have : CharP Γ(Spec (.of S), ⊤) p := charP_of_injective_ringHom e.injective p
  have : CharP Γ(W.left, ⊤) p := charP_of_injective_ringHom e.injective p
  have hinv : X.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).inv := by
    apply (cancel_mono (Scheme.ΓSpecIso Γ(X, ⊤)).hom).mp
    rw [Iso.inv_hom_id, ← Scheme.toSpecΓ_appTop]
    change X.isoSpec.inv.appTop ≫ X.isoSpec.hom.appTop = 𝟙 _
    rw [← Scheme.Hom.comp_appTop, X.isoSpec.hom_inv_id, Scheme.Hom.id_appTop]
  have hbase : W.hom.appTop.hom = e.toRingHom.comp (algebraMap Γ(X, ⊤) S) := by
    change (Spec.algebraMap Γ(X, ⊤) S ≫ X.isoSpec.inv).appTop.hom = _
    rw [Scheme.Hom.comp_appTop, hinv]
    exact congrArg CommRingCat.Hom.hom
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap Γ(X, ⊤) S))).symm
  have hroot : TruncatedWittVector.map (frobenius Γ(Spec (.of S), ⊤) p)
        (TruncatedWittVector.map e.toRingHom β) - TruncatedWittVector.map e.toRingHom β =
      TruncatedWittVector.map (e.toRingHom.comp (algebraMap Γ(X, ⊤) S)) a := by
    rw [TruncatedWittVector.map_frobenius, ← map_sub, hβ]
    exact TruncatedWittVector.map_map _ _ _
  refine ⟨W, inferInstance, inferInstance, TruncatedWittVector.map e.toRingHom β, ?_⟩
  exact hroot.trans (congrArg
    (fun f : Γ(X, ⊤) →+* Γ(Spec (.of S), ⊤) => TruncatedWittVector.map f a) hbase.symm)

section Generic

variable [IsIntegral X] [IsNormalIntegral X]
  (Ω : Type u) [Field Ω] [Algebra X.functionField Ω]
  [IsSepClosed Ω] [IsSepClosure X.functionField Ω]
  [CharP Ω p]

omit [IsAffine X] [Nontrivial Γ(X, ⊤)] [CharP Γ(X, ⊤) p] [IsNormalIntegral X]
  [IsSepClosure X.functionField Ω] in
theorem finiteEtaleSectionValue_base_generic (W : FiniteEtale X)
    (x : (FiniteEtale.fiber (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
      X.fromSpecStalk (genericPoint X))).obj W) (a : Γ(X, ⊤)) :
    finiteEtaleSectionValue W _ x (W.hom.appTop a) =
      algebraMap X.functionField Ω
        ((Scheme.ΓSpecIso X.functionField).hom
          ((X.fromSpecStalk (genericPoint X)).appTop a)) := by
  let l := FiniteEtale.fiberObjEquivHom
    (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
        X.fromSpecStalk (genericPoint X)) W x
  have hw : l.left ≫ W.hom =
      (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))) ≫
        X.fromSpecStalk (genericPoint X) := l.w
  exact (congrArg (Scheme.ΓSpecIso (.of Ω)).hom
    (((ConcreteCategory.congr_hom (Scheme.Hom.comp_appTop l.left W.hom) a).symm.trans
      (congrArg (fun f : Spec (.of Ω) ⟶ X => f.appTop a) hw)).trans
        (ConcreteCategory.congr_hom (Scheme.Hom.comp_appTop
          (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)))
          (X.fromSpecStalk (genericPoint X))) a))).trans
    (ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap X.functionField Ω)))
      ((X.fromSpecStalk (genericPoint X)).appTop a))

/-- Every coefficient on the original normal integral affine scheme has a
native continuous character whose generic restriction is its actual field
Artin–Schreier–Witt root character. -/
theorem exists_native_wittCharacter_of_coefficient
    (a : TruncatedWittVector p m Γ(X, ⊤)) :
    let aK := TruncatedWittVector.map
      ((Scheme.ΓSpecIso X.functionField).hom.hom.comp
        (X.fromSpecStalk (genericPoint X)).appTop.hom) a
    ∃ (r : TruncatedWittVector p m Ω)
      (hr : TruncatedWittVector.map (frobenius Ω p) r - r =
        TruncatedWittVector.map (algebraMap X.functionField Ω) aK)
      (χ : Aut (FiniteEtale.fiber (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
        X.fromSpecStalk (genericPoint X))) →ₜ* Multiplicative (ZMod (p ^ m))),
      χ.comp (FiniteEtale.fieldSourceAbsoluteGaloisHom X.functionField Ω
        (X.fromSpecStalk (genericPoint X))) = rootCharacter p m Ω aK r hr := by
  intro aK
  obtain ⟨W, hW, charW, β, hβ⟩ := exists_finiteEtale_wittSection X p m a
  have : Nonempty W.left := hW
  have : Nonempty ((FiniteEtale.fiber (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
      X.fromSpecStalk (genericPoint X))).obj W) :=
    (not_initial_iff_fiber_nonempty _ W).mp (FiniteEtale.notInitial_of_nonempty_left W)
  let x := Classical.choice this
  let e := finiteEtaleSectionValue W
    (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
        X.fromSpecStalk (genericPoint X)) x
  let r := TruncatedWittVector.map e β
  have hr : TruncatedWittVector.map (frobenius Ω p) r - r =
      TruncatedWittVector.map (algebraMap X.functionField Ω) aK := by
    change TruncatedWittVector.map (frobenius Ω p) (TruncatedWittVector.map e β) -
      TruncatedWittVector.map e β = _
    rw [TruncatedWittVector.map_frobenius, ← map_sub, hβ]
    apply TruncatedWittVector.ext
    intro i
    simp only [aK, TruncatedWittVector.map_coeff, RingHom.comp_apply]
    exact finiteEtaleSectionValue_base_generic X Ω W x (a.coeff i)
  obtain ⟨χ, hχ, _⟩ := exists_generic_wittCharacter_of_section X Ω p m W x β aK hr
  exact ⟨r, hr, χ, hχ⟩

end Generic

end EtaleFundamentalGroups.Cohomology
