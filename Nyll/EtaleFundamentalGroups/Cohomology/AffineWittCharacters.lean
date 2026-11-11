/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.AffineWittCoefficientCharacter
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineArtinSchreierWitt
public import Nyll.GaloisCohomology.ArtinSchreier.WittCharacterNaturality
public import Nyll.GaloisCohomology.ArtinSchreier.WittCharacters

/-!
# Witt coefficients and the original affine fundamental group

The coefficient character is the character of the original affine scheme,
not merely a character of its function field. Its generic restriction is
computed with any root of the original equation. The actual pointed Galois
cover attached to a character proves surjectivity, and root differences
prove compatibility with subtraction.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open ArtinSchreierWittTheory

namespace EtaleFundamentalGroups.Cohomology

variable (X : Scheme.{u}) [IsAffine X] [IsIntegral X] [IsNormalIntegral X]
  (Ω : Type u) [Field Ω] [Algebra X.functionField Ω]
  [IsSepClosed Ω] [IsSepClosure X.functionField Ω]
  (p m : ℕ) [Fact p.Prime] [Nontrivial Γ(X, ⊤)]
  [CharP Γ(X, ⊤) p] [CharP Ω p]

local notation "xi" => Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
  X.fromSpecStalk (genericPoint X)
local notation "phi" => FiniteEtale.fieldSourceAbsoluteGaloisHom
  X.functionField Ω (X.fromSpecStalk (genericPoint X))

/-- Restriction of a Witt coefficient to the original generic point. -/
def affineWittGenericCoefficient :
    TruncatedWittVector p m Γ(X, ⊤) →+* TruncatedWittVector p m X.functionField :=
  TruncatedWittVector.map
    ((Scheme.ΓSpecIso X.functionField).hom.hom.comp
      (X.fromSpecStalk (genericPoint X)).appTop.hom)

/-- The original affine fundamental-group character of a Witt coefficient. -/
def affineWittCharacter (a : TruncatedWittVector p m Γ(X, ⊤)) :
    Aut (FiniteEtale.fiber xi) →ₜ* Multiplicative (ZMod (p ^ m)) :=
  (exists_native_wittCharacter_of_coefficient X p m Ω a).choose_spec.choose_spec.choose

/-- A root of the original generic equation computes the chosen native character. -/
theorem affineWittCharacter_spec (a : TruncatedWittVector p m Γ(X, ⊤)) :
    ∃ (r : TruncatedWittVector p m Ω)
      (hr : TruncatedWittVector.map (frobenius Ω p) r - r =
        TruncatedWittVector.map (algebraMap X.functionField Ω)
          (affineWittGenericCoefficient X p m a)),
      (affineWittCharacter X Ω p m a).comp phi =
        rootCharacter p m Ω (affineWittGenericCoefficient X p m a) r hr := by
  let h := exists_native_wittCharacter_of_coefficient X p m Ω a
  exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose_spec⟩

/-- Generic restriction is independent of every root and finite-cover choice. -/
theorem affineWittCharacter_generic (a : TruncatedWittVector p m Γ(X, ⊤))
    (r : TruncatedWittVector p m Ω)
    (hr : TruncatedWittVector.map (frobenius Ω p) r - r =
      TruncatedWittVector.map (algebraMap X.functionField Ω)
        (affineWittGenericCoefficient X p m a)) :
    (affineWittCharacter X Ω p m a).comp phi =
      rootCharacter p m Ω (affineWittGenericCoefficient X p m a) r hr := by
  obtain ⟨r', hr', hχ⟩ := affineWittCharacter_spec X Ω p m a
  exact hχ.trans
    (rootCharacter_eq p m Ω (affineWittGenericCoefficient X p m a) r' r hr' hr)

/-- Subtracting actual affine coefficients divides their native characters. -/
theorem affineWittCharacter_sub (a b : TruncatedWittVector p m Γ(X, ⊤)) :
    affineWittCharacter X Ω p m (a - b) =
      affineWittCharacter X Ω p m a / affineWittCharacter X Ω p m b := by
  obtain ⟨r, hr, hχ⟩ := affineWittCharacter_spec X Ω p m a
  obtain ⟨s, hs, hψ⟩ := affineWittCharacter_spec X Ω p m b
  have hrs : TruncatedWittVector.map (frobenius Ω p) (r - s) - (r - s) =
      TruncatedWittVector.map (algebraMap X.functionField Ω)
        (affineWittGenericCoefficient X p m (a - b)) := by
    exact (wittRoot_sub p m _ _ r s hr hs).trans
      (congrArg (TruncatedWittVector.map (algebraMap X.functionField Ω))
        (map_sub (affineWittGenericCoefficient X p m) a b).symm)
  have hsub (c : TruncatedWittVector p m X.functionField)
      (hc : c = affineWittGenericCoefficient X p m a - affineWittGenericCoefficient X p m b)
      (hroot : TruncatedWittVector.map (frobenius Ω p) (r - s) - (r - s) =
        TruncatedWittVector.map (algebraMap X.functionField Ω) c) :
      rootCharacter p m Ω c (r - s) hroot =
        rootCharacter p m Ω (affineWittGenericCoefficient X p m a) r hr /
          rootCharacter p m Ω (affineWittGenericCoefficient X p m b) s hs := by
    subst c
    exact rootCharacter_sub p m _ _ r s hr hs
  have hχψ := (affineWittCharacter_generic X Ω p m (a - b) (r - s) hrs).trans
    (hsub _ (map_sub (affineWittGenericCoefficient X p m) a b) hrs)
  apply ContinuousMonoidHom.ext
  intro γ
  obtain ⟨σ, rfl⟩ := FiniteEtale.genericFieldAction_surjective X Ω γ
  exact (congrArg
    (fun f : Gal(Ω/X.functionField) →ₜ* Multiplicative (ZMod (p ^ m)) => f σ) hχψ).trans
      (congrArg₂ (fun x y : Multiplicative (ZMod (p ^ m)) => x / y)
        (congrArg
          (fun f : Gal(Ω/X.functionField) →ₜ* Multiplicative (ZMod (p ^ m)) => f σ) hχ).symm
        (congrArg
          (fun f : Gal(Ω/X.functionField) →ₜ* Multiplicative (ZMod (p ^ m)) => f σ) hψ).symm)

/-- The zero coefficient gives the trivial native character. -/
theorem affineWittCharacter_zero : affineWittCharacter X Ω p m 0 = 1 := by
  have h := affineWittCharacter_sub X Ω p m 0 0
  simpa only [sub_self, div_self'] using h

/-- Every native prime-power character comes from a coefficient in the
original affine section ring, using its own actual pointed Galois cover. -/
theorem affineWittCharacter_surjective :
    Function.Surjective (affineWittCharacter X Ω p m) := by
  intro χ
  obtain ⟨W, hW, w, a, β, hβ, hχ⟩ :=
    exists_wittEquation_of_fundamentalGroup_character xi p m χ
  have : IsGalois W := hW
  have : CharP Γ(W.left, ⊤) p := finiteEtaleSection_charP W p
  let e := finiteEtaleSectionValue W xi w
  let r := TruncatedWittVector.map e β
  have hr : TruncatedWittVector.map (frobenius Ω p) r - r =
      TruncatedWittVector.map (algebraMap X.functionField Ω)
        (affineWittGenericCoefficient X p m a) := by
    change TruncatedWittVector.map (frobenius Ω p) (TruncatedWittVector.map e β) -
      TruncatedWittVector.map e β = _
    rw [TruncatedWittVector.map_frobenius, ← map_sub, hβ]
    apply TruncatedWittVector.ext
    intro i
    simp only [affineWittGenericCoefficient, TruncatedWittVector.map_coeff,
      RingHom.comp_apply]
    exact finiteEtaleSectionValue_base_generic X Ω W w (a.coeff i)
  have hgeneric := affineWittCharacter_generic X Ω p m a r hr
  refine ⟨a, ContinuousMonoidHom.ext fun γ => ?_⟩
  obtain ⟨σ, rfl⟩ := FiniteEtale.genericFieldAction_surjective X Ω γ
  change (affineWittCharacter X Ω p m a (phi σ)).toAdd = (χ (phi σ)).toAdd
  apply constantCast_injective p m Ω
  rw [show affineWittCharacter X Ω p m a (phi σ) =
      rootCharacter p m Ω (affineWittGenericCoefficient X p m a) r hr σ from
    congrArg
      (fun f : Gal(Ω/X.functionField) →ₜ* Multiplicative (ZMod (p ^ m)) => f σ) hgeneric,
    rootCharacter_cast]
  have heval : TruncatedWittVector.map (finiteEtaleSectionValue W xi (phi σ • w)) β =
      TruncatedWittVector.map σ.toRingHom r := by
    apply TruncatedWittVector.ext
    intro i
    simp only [r, TruncatedWittVector.map_coeff]
    exact finiteEtaleSectionValue_genericFieldAction X Ω W w σ (β.coeff i)
  rw [← heval]
  exact hχ (phi σ)

end EtaleFundamentalGroups.Cohomology
