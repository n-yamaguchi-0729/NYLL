/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.AffineWittCharacters
public import Nyll.SchemeTheory.Normalization.Normal
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Nyll.GaloisCohomology.ArtinSchreier.WittCharacterSurjectivity
public import Nyll.GaloisCohomology.ArtinSchreier.WittCharacters

/-!
# The exact affine Artin–Schreier–Witt coefficient kernel

The generic coefficient map is the original generic germ. A root furnished
by the actual finite étale cover is integral over the original affine ring.
If its native character is trivial, Galois descent puts that root in the
function field, and normality puts every coordinate back in the affine ring.
Thus the coefficient presentation has exactly the Frobenius-difference
kernel; no regularity or descent statement is an extra input.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open ArtinSchreierWittTheory

namespace EtaleFundamentalGroups.Cohomology

variable (X : Scheme) [IsAffine X] [IsIntegral X] [IsNormalIntegral X]
  (Ω : Type) [Field Ω] [Algebra X.functionField Ω]
  [IsSepClosed Ω] [IsSepClosure X.functionField Ω]
  (p m : ℕ) [Fact p.Prime] [Nontrivial Γ(X, ⊤)]
  [CharP Γ(X, ⊤) p] [CharP Ω p]

local notation "xi" => Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
  X.fromSpecStalk (genericPoint X)

omit [IsAffine X] [IsNormalIntegral X] [Nontrivial Γ(X, ⊤)] in
/-- Evaluating sections at the original generic source is the canonical
generic germ used by the original function-field algebra. -/
theorem affineWittGenericCoefficient_baseMap :
    let : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, by trivial⟩⟩
    (Scheme.ΓSpecIso X.functionField).hom.hom.comp
      (X.fromSpecStalk (genericPoint X)).appTop.hom = algebraMap Γ(X, ⊤) X.functionField := by
  intro nonemptyTop
  have hg : (X.fromSpecStalk (genericPoint X)).appTop ≫
      (Scheme.ΓSpecIso X.functionField).hom = X.germToFunctionField ⊤ := by
    rw [Scheme.fromSpecStalk_appTop]
    change (X.germToFunctionField ⊤ ≫ (Scheme.ΓSpecIso X.functionField).inv ≫
      (Spec X.functionField).presheaf.map (𝟙 _)) ≫
        (Scheme.ΓSpecIso X.functionField).hom = X.germToFunctionField ⊤
    rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  exact congrArg CommRingCat.Hom.hom hg

/-- A trivial native character has an actual Witt primitive in the original
normal affine section ring. The finite-cover root supplies integrality. -/
theorem exists_affineWittRoot_of_character_eq_one
    (a : TruncatedWittVector p m Γ(X, ⊤))
    (hχ : affineWittCharacter X Ω p m a = 1) :
    ∃ b : TruncatedWittVector p m Γ(X, ⊤),
      TruncatedWittVector.map (frobenius Γ(X, ⊤) p) b - b = a := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, by trivial⟩⟩
  have : IsFractionRing Γ(X, ⊤) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X ⊤ (isAffineOpen_top X)
  have : IsIntegrallyClosed Γ(X, ⊤) :=
    IsNormalIntegral.affine_isIntegrallyClosed ⊤ (isAffineOpen_top X)
  let : Algebra Γ(X, ⊤) Ω :=
    ((algebraMap X.functionField Ω).comp (algebraMap Γ(X, ⊤) X.functionField)).toAlgebra
  have : IsScalarTower Γ(X, ⊤) X.functionField Ω := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨W, hW, charW, β, hβ⟩ := exists_finiteEtale_wittSection X p m a
  have : Nonempty W.left := hW
  have : CharP Γ(W.left, ⊤) p := charW
  have : IsFiniteEtale W.hom := W.prop
  let : Algebra Γ(X, ⊤) Γ(W.left, ⊤) := W.hom.appTop.hom.toAlgebra
  have : IsAffine ((Functor.fromPUnit X).obj W.right) := inferInstanceAs (IsAffine X)
  have : Module.Finite Γ(X, ⊤) Γ(W.left, ⊤) :=
    RingHom.finite_algebraMap.mp W.hom.finite_appTop
  have : Nonempty ((FiniteEtale.fiber xi).obj W) :=
    (not_initial_iff_fiber_nonempty _ W).mp (FiniteEtale.notInitial_of_nonempty_left W)
  let w := Classical.choice this
  let e := finiteEtaleSectionValue W xi w
  let r := TruncatedWittVector.map e β
  have he (z : Γ(X, ⊤)) : e (algebraMap Γ(X, ⊤) Γ(W.left, ⊤) z) =
      algebraMap Γ(X, ⊤) Ω z :=
    (finiteEtaleSectionValue_base_generic X Ω W w z).trans
      (congrArg (algebraMap X.functionField Ω)
        (DFunLike.congr_fun (affineWittGenericCoefficient_baseMap X) z))
  let eA : Γ(W.left, ⊤) →ₐ[Γ(X, ⊤)] Ω := { e with commutes' := he }
  have hintegral (i : Fin m) : IsIntegral Γ(X, ⊤) (r.coeff i) := by
    change IsIntegral Γ(X, ⊤) ((TruncatedWittVector.map e β).coeff i)
    rw [TruncatedWittVector.map_coeff]
    exact IsIntegral.map eA (Algebra.IsIntegral.isIntegral (β.coeff i))
  have hr : TruncatedWittVector.map (frobenius Ω p) r - r =
      TruncatedWittVector.map (algebraMap X.functionField Ω)
        (affineWittGenericCoefficient X p m a) := by
    change TruncatedWittVector.map (frobenius Ω p) (TruncatedWittVector.map e β) -
      TruncatedWittVector.map e β = _
    rw [TruncatedWittVector.map_frobenius, ← map_sub, hβ]
    apply TruncatedWittVector.ext
    intro i
    simp only [affineWittGenericCoefficient, TruncatedWittVector.map_coeff, RingHom.comp_apply]
    exact finiteEtaleSectionValue_base_generic X Ω W w (a.coeff i)
  have hgeneric := affineWittCharacter_generic X Ω p m a r hr
  let genericGaloisMap : Gal(Ω/X.functionField) →ₜ* π₁ᵉᵗ(xi) :=
    FiniteEtale.fieldSourceAbsoluteGaloisHom
      X.functionField Ω (X.fromSpecStalk (genericPoint X))
  have hfixed (σ : Gal(Ω/X.functionField)) : TruncatedWittVector.map σ.toRingHom r = r := by
    apply (rootCharacter_eq_one_iff p m Ω (affineWittGenericCoefficient X p m a) r hr σ).mp
    exact (DFunLike.congr_fun hgeneric σ).symm.trans
      (DFunLike.congr_fun hχ (genericGaloisMap σ))
  obtain ⟨u, hu⟩ := ArtinSchreierWittTheory.exists_base_of_fixed p m r hfixed
  have huintegral (i : Fin m) : IsIntegral Γ(X, ⊤) (u.coeff i) := by
    have hi : algebraMap X.functionField Ω (u.coeff i) = r.coeff i := by
      simpa only [TruncatedWittVector.map_coeff] using
        congrArg (TruncatedWittVector.coeff i) hu
    exact isIntegral_algebraMap_iff.mp (hi.symm ▸ hintegral i)
  choose b hb using fun i : Fin m => IsIntegrallyClosed.algebraMap_eq_of_integral (huintegral i)
  let B := TruncatedWittVector.mk p b
  have hB : TruncatedWittVector.map (algebraMap Γ(X, ⊤) X.functionField) B = u := by
    apply TruncatedWittVector.ext
    intro i
    simp only [B, TruncatedWittVector.map_coeff, TruncatedWittVector.coeff_mk]
    exact hb i
  have hBΩ : TruncatedWittVector.map (algebraMap Γ(X, ⊤) Ω) B = r := by
    rw [IsScalarTower.algebraMap_eq Γ(X, ⊤) X.functionField Ω,
      ← TruncatedWittVector.map_map (algebraMap X.functionField Ω)
      (algebraMap Γ(X, ⊤) X.functionField), hB, hu]
  have hinj : Function.Injective (algebraMap Γ(X, ⊤) Ω) :=
    (algebraMap X.functionField Ω).injective.comp (IsFractionRing.injective Γ(X, ⊤) X.functionField)
  refine ⟨B, ?_⟩
  apply TruncatedWittVector.map_injective (algebraMap Γ(X, ⊤) Ω) hinj
  rw [map_sub, ← TruncatedWittVector.map_frobenius, hBΩ, hr]
  change TruncatedWittVector.map (algebraMap X.functionField Ω)
    (TruncatedWittVector.map
      ((Scheme.ΓSpecIso X.functionField).hom.hom.comp
        (X.fromSpecStalk (genericPoint X)).appTop.hom) a) = _
  rw [affineWittGenericCoefficient_baseMap, TruncatedWittVector.map_map]
  exact congrArg
    (fun f : Γ(X, ⊤) →+* Ω => TruncatedWittVector.map f a)
    (IsScalarTower.algebraMap_eq Γ(X, ⊤) X.functionField Ω).symm

/-- The kernel of the original native coefficient character is exactly the
image of Frobenius minus identity on the original affine Witt ring. -/
theorem affineWittCharacter_eq_one_iff
    (a : TruncatedWittVector p m Γ(X, ⊤)) :
    affineWittCharacter X Ω p m a = 1 ↔
      ∃ b : TruncatedWittVector p m Γ(X, ⊤),
        TruncatedWittVector.map (frobenius Γ(X, ⊤) p) b - b = a := by
  constructor
  · exact exists_affineWittRoot_of_character_eq_one X Ω p m a
  · rintro ⟨b, rfl⟩
    let f : Γ(X, ⊤) →+* Ω := (algebraMap X.functionField Ω).comp
      ((Scheme.ΓSpecIso X.functionField).hom.hom.comp
        (X.fromSpecStalk (genericPoint X)).appTop.hom)
    let r := TruncatedWittVector.map f b
    have hr : TruncatedWittVector.map (frobenius Ω p) r - r =
        TruncatedWittVector.map (algebraMap X.functionField Ω)
          (affineWittGenericCoefficient X p m
            (TruncatedWittVector.map (frobenius Γ(X, ⊤) p) b - b)) := by
      change TruncatedWittVector.map (frobenius Ω p) (TruncatedWittVector.map f b) -
        TruncatedWittVector.map f b = _
      rw [TruncatedWittVector.map_frobenius, ← map_sub]
      exact (TruncatedWittVector.map_map _ _ _).symm
    have hgeneric := affineWittCharacter_generic X Ω p m
      (TruncatedWittVector.map (frobenius Γ(X, ⊤) p) b - b) r hr
    apply ContinuousMonoidHom.ext
    intro γ
    obtain ⟨σ, rfl⟩ := FiniteEtale.genericFieldAction_surjective X Ω γ
    refine (DFunLike.congr_fun hgeneric σ).trans ?_
    apply (rootCharacter_eq_one_iff p m Ω _ r hr σ).mpr
    apply TruncatedWittVector.ext
    intro i
    simp only [r, TruncatedWittVector.map_coeff, f, RingHom.comp_apply]
    exact σ.commutes _

/-- The original affine Witt ring modulo the actual Frobenius-difference
image. The coefficient ring and the Witt length are retained in the type. -/
abbrev AffineWittClasses := TruncatedWittVector p m Γ(X, ⊤) ⧸
  ((TruncatedWittVector.map (frobenius Γ(X, ⊤) p)).toAddMonoidHom -
    AddMonoidHom.id (TruncatedWittVector p m Γ(X, ⊤))).range

/-- The additive coefficient map into all continuous native characters. -/
def affineWittCharacterAddHom : TruncatedWittVector p m Γ(X, ⊤) →+
    Additive (Aut (FiniteEtale.fiber xi) →ₜ* Multiplicative (ZMod (p ^ m))) where
  toFun a := Additive.ofMul (affineWittCharacter X Ω p m a)
  map_zero' := affineWittCharacter_zero X Ω p m
  map_add' a b := by
    change affineWittCharacter X Ω p m (a + b) =
      affineWittCharacter X Ω p m a * affineWittCharacter X Ω p m b
    calc
      affineWittCharacter X Ω p m (a + b) =
          (affineWittCharacter X Ω p m (a + b) / affineWittCharacter X Ω p m b) *
            affineWittCharacter X Ω p m b := (div_mul_cancel _ _).symm
      _ = affineWittCharacter X Ω p m a * affineWittCharacter X Ω p m b := by
        rw [← affineWittCharacter_sub, add_sub_cancel_right]

/-- The kernel equality in the original coefficient ring, before taking
any quotient or choosing a representative for a character class. -/
theorem affineWittCharacterAddHom_ker :
    ((TruncatedWittVector.map (frobenius Γ(X, ⊤) p)).toAddMonoidHom -
      AddMonoidHom.id (TruncatedWittVector p m Γ(X, ⊤))).range =
        (affineWittCharacterAddHom X Ω p m).ker := by
  apply AddSubgroup.ext
  intro a
  change (∃ b : TruncatedWittVector p m Γ(X, ⊤),
      TruncatedWittVector.map (frobenius Γ(X, ⊤) p) b - b = a) ↔
    affineWittCharacter X Ω p m a = 1
  exact (affineWittCharacter_eq_one_iff X Ω p m a).symm

/-- The affine Artin–Schreier–Witt classification of every original
continuous `p ^ m` character, with the exact coefficient quotient. -/
def affineWittClassCharacterEquiv : AffineWittClasses X p m ≃+
    Additive (Aut (FiniteEtale.fiber xi) →ₜ* Multiplicative (ZMod (p ^ m))) :=
  QuotientAddGroup.liftEquiv _
    (φ := affineWittCharacterAddHom X Ω p m)
    (fun χ => affineWittCharacter_surjective X Ω p m χ.toMul)
    (affineWittCharacterAddHom_ker X Ω p m)

/-- The classification sends an actual coefficient class to its original
native character, without changing the chosen geometric source. -/
theorem affineWittClassCharacterEquiv_mk (a : TruncatedWittVector p m Γ(X, ⊤)) :
    affineWittClassCharacterEquiv X Ω p m (a : AffineWittClasses X p m) =
      Additive.ofMul (affineWittCharacter X Ω p m a) := rfl

end EtaleFundamentalGroups.Cohomology
