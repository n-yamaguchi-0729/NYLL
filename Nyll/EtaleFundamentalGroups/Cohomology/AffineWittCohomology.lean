/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.AffineWittCharacters
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineBaseChangeFrobenius
public import Nyll.EtaleFundamentalGroups.Cohomology.SemilinearSourcePullback
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1Comparison
public import Nyll.SchemeTheory.FunctionFields.GenericSourceIso
public import Nyll.GaloisCohomology.ArtinSchreier.WittCharacters
public import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugation

/-!
# Actual affine Witt classes and scheme pullback

The native coefficient character defines a class in the original derived
finite-coefficient H¹. The generic-point square of a scheme automorphism,
its internally constructed separable-closure lift, and the root formula
prove naturality for the original pullback on cohomology. Consequently a
surjective coefficient difference induces a surjective H¹ difference.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open ArtinSchreierWittTheory AnabelianGeometry.WeightFiltration

namespace EtaleFundamentalGroups.Cohomology

/-- The finite cyclic coefficient group for affine Witt classes. -/
abbrev affineWittCoefficient (p m : ℕ) : AddCommGrpCat.{0} :=
  AddCommGrpCat.of (ZMod (p ^ m))

/-- The first cohomology group with the affine Witt coefficients. -/
abbrev affineWittH1 (X : Scheme) (p m : ℕ) : Type :=
  Sheaf.H.{0}
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).obj
      (affineWittCoefficient p m)) 1

/-- The generic coefficient map commutes with the original scheme
automorphism and its actual function-field map. -/
theorem affineWittGenericCoefficient_pullback
    (X : Scheme.{u}) [IsIntegral X] (p m : ℕ) [Fact p.Prime] (θ : X ≅ X)
    (a : TruncatedWittVector p m Γ(X, ⊤)) :
    affineWittGenericCoefficient X p m (TruncatedWittVector.map θ.hom.appTop.hom a) =
      TruncatedWittVector.map θ.hom.functionFieldRingEquivOfIsOpenImmersion.toRingHom
        (affineWittGenericCoefficient X p m a) := by
  let q := X.fromSpecStalk (genericPoint X)
  let τ := θ.hom.functionFieldRingEquivOfIsOpenImmersion
  have hd : DenseRange θ.hom :=
    θ.hom.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace θ.hom
  have hs : Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ q = q ≫ θ.hom :=
    functionFieldMap_genericPoint θ.hom hd
  apply TruncatedWittVector.ext
  intro i
  simp only [affineWittGenericCoefficient, TruncatedWittVector.map_coeff,
    RingHom.comp_apply]
  exact (congrArg (Scheme.ΓSpecIso X.functionField).hom
    (((ConcreteCategory.congr_hom (Scheme.Hom.comp_appTop q θ.hom)
      (a.coeff i)).symm.trans
        (congrArg (fun f : Spec (.of X.functionField) ⟶ X => f.appTop (a.coeff i))
          hs.symm)).trans
      (ConcreteCategory.congr_hom
        (Scheme.Hom.comp_appTop (Spec.map (CommRingCat.ofHom τ.toRingHom)) q)
          (a.coeff i)))).trans
    (ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom τ.toRingHom)) (q.appTop (a.coeff i)))

variable (X : Scheme) [IsAffine X] [IsIntegral X] [IsNormalIntegral X]
  (Ω : Type) [Field Ω] [Algebra X.functionField Ω]
  [IsSepClosed Ω] [IsSepClosure X.functionField Ω]
  (p m : ℕ) [Fact p.Prime] [Nontrivial Γ(X, ⊤)]
  [CharP Γ(X, ⊤) p] [CharP Ω p]

local notation "xi" => Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
  X.fromSpecStalk (genericPoint X)
local notation "phi" => FiniteEtale.fieldSourceAbsoluteGaloisHom
  X.functionField Ω (X.fromSpecStalk (genericPoint X))
local notation "A" => affineWittCoefficient p m
local notation "H" => affineWittH1 X p m

variable [NeZero (p ^ m)]

/-- The actual derived H¹ class of an affine Witt coefficient. The finite
coefficient topology is the one used by the original H¹ comparison. -/
def affineWittCohomologyClass (a : TruncatedWittVector p m Γ(X, ⊤)) : H := by
  let χ := affineWittCharacter X Ω p m a
  have hχ : IsLocallyConstant χ := (IsLocallyConstant.iff_continuous χ).mpr χ.continuous
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  let ψ : Aut (FiniteEtale.fiber xi) →ₜ* Multiplicative A :=
    { χ.toMonoidHom with
      continuous_toFun := hχ.continuous }
  exact (finiteH1CharacterEquiv A xi).symm (Additive.ofMul ψ)

/-- The original H¹ class has the native coefficient character on every
element of the original affine fundamental group. -/
theorem h1Character_affineWittCohomologyClass
    (a : TruncatedWittVector p m Γ(X, ⊤)) :
    let : TopologicalSpace (Multiplicative A) := ⊥
    ∀ γ : Aut (FiniteEtale.fiber xi),
      h1Character A xi (affineWittCohomologyClass X Ω p m a) γ =
        affineWittCharacter X Ω p m a γ := by
  intro topology γ
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  unfold affineWittCohomologyClass
  exact congrArg (fun f : Additive (Aut (FiniteEtale.fiber xi) →ₜ* Multiplicative A) =>
    f.toMul γ) ((finiteH1CharacterEquiv A xi).apply_symm_apply _)

/-- Every actual finite prime-power H¹ class is represented by a coefficient
in the original affine section ring. -/
theorem affineWittCohomologyClass_surjective :
    Function.Surjective (affineWittCohomologyClass X Ω p m) := by
  intro c
  let χ₀ := h1Character A xi c
  have hχ₀ : IsLocallyConstant χ₀ := by
    let : TopologicalSpace (Multiplicative A) := ⊥
    have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
    exact (IsLocallyConstant.iff_continuous χ₀).mpr χ₀.continuous
  let χ : Aut (FiniteEtale.fiber xi) →ₜ* Multiplicative (ZMod (p ^ m)) :=
    { χ₀.toMonoidHom with
      continuous_toFun := hχ₀.continuous }
  obtain ⟨a, ha⟩ := affineWittCharacter_surjective X Ω p m χ
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  refine ⟨a, ?_⟩
  apply (finiteH1CharacterEquiv A xi).injective
  apply ContinuousMonoidHom.ext
  intro γ
  change h1Character A xi (affineWittCohomologyClass X Ω p m a) γ = h1Character A xi c γ
  exact (h1Character_affineWittCohomologyClass X Ω p m a γ).trans
    (DFunLike.congr_fun ha γ)

/-- Subtraction of original affine coefficients is subtraction in actual H¹. -/
theorem affineWittCohomologyClass_sub (a b : TruncatedWittVector p m Γ(X, ⊤)) :
    affineWittCohomologyClass X Ω p m (a - b) =
      affineWittCohomologyClass X Ω p m a - affineWittCohomologyClass X Ω p m b := by
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  apply (finiteH1CharacterEquiv A xi).injective
  rw [map_sub]
  apply ContinuousMonoidHom.ext
  intro γ
  change h1Character A xi (affineWittCohomologyClass X Ω p m (a - b)) γ =
    h1Character A xi (affineWittCohomologyClass X Ω p m a) γ /
      h1Character A xi (affineWittCohomologyClass X Ω p m b) γ
  rw [h1Character_affineWittCohomologyClass, h1Character_affineWittCohomologyClass,
    h1Character_affineWittCohomologyClass]
  exact DFunLike.congr_fun (affineWittCharacter_sub X Ω p m a b) γ

/-- Coefficient transport is the original scheme pullback on actual H¹.
The source automorphism and all comparison squares are constructed here. -/
theorem affineWittCohomologyClass_pullback (θ : X ≅ X)
    (a : TruncatedWittVector p m Γ(X, ⊤)) :
    affineWittCohomologyClass X Ω p m (TruncatedWittVector.map θ.hom.appTop.hom a) =
      constantCohomologyPullback θ.hom A 1 (affineWittCohomologyClass X Ω p m a) := by
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  obtain ⟨e, he, hpoint⟩ := exists_genericPoint_sourceIso θ Ω
  let τ := θ.hom.functionFieldRingEquivOfIsOpenImmersion
  obtain ⟨r, hr, hχ⟩ := affineWittCharacter_spec X Ω p m a
  have hcoeff := affineWittGenericCoefficient_pullback X p m θ a
  have hr' : TruncatedWittVector.map (frobenius Ω p) (TruncatedWittVector.map e.toRingHom r) -
      TruncatedWittVector.map e.toRingHom r =
        TruncatedWittVector.map (algebraMap X.functionField Ω)
          (affineWittGenericCoefficient X p m (TruncatedWittVector.map θ.hom.appTop.hom a)) := by
    rw [hcoeff]
    exact wittRoot_semilinear p m τ e he _ r hr
  have hχ' := affineWittCharacter_generic X Ω p m
    (TruncatedWittVector.map θ.hom.appTop.hom a) (TruncatedWittVector.map e.toRingHom r) hr'
  apply finiteH1_ext_genericFieldAction X Ω A
  intro ρ'
  obtain ⟨ρ, rfl⟩ := (KummerTheory.semilinearGaloisConjugateEquiv τ e he).surjective ρ'
  let σ := KummerTheory.semilinearGaloisConjugate τ e he ρ
  have hp := h1Character_semilinearSourcePullback (X.fromSpecStalk (genericPoint X))
    θ.hom τ e he hpoint A (affineWittCohomologyClass X Ω p m a) ρ
  change h1Character A xi
      (constantCohomologyPullback θ.hom A 1 (affineWittCohomologyClass X Ω p m a))
        (phi σ) = h1Character A xi (affineWittCohomologyClass X Ω p m a) (phi ρ) at hp
  change h1Character A xi
      (affineWittCohomologyClass X Ω p m (TruncatedWittVector.map θ.hom.appTop.hom a))
        (phi σ) =
    h1Character A xi
      (constantCohomologyPullback θ.hom A 1 (affineWittCohomologyClass X Ω p m a)) (phi σ)
  rw [hp, h1Character_affineWittCohomologyClass, h1Character_affineWittCohomologyClass]
  refine (DFunLike.congr_fun hχ' σ).trans ?_
  refine Eq.trans ?_ (DFunLike.congr_fun hχ ρ).symm
  simpa only [hcoeff] using rootCharacter_semilinear p m τ e he
    (affineWittGenericCoefficient X p m a) r hr ρ

include Ω in
/-- Surjectivity of an actual coefficient difference passes to the original
finite-coefficient H¹ difference by the natural coefficient presentation. -/
theorem affineWittCohomology_pullback_sub_id_surjective (θ : X ≅ X)
    (hθ : Function.Surjective (fun a : TruncatedWittVector p m Γ(X, ⊤) =>
      TruncatedWittVector.map θ.hom.appTop.hom a - a)) :
    Function.Surjective (fun c : H => constantCohomologyPullback θ.hom A 1 c - c) := by
  intro c
  obtain ⟨a, ha⟩ := affineWittCohomologyClass_surjective X Ω p m c
  obtain ⟨b, hb⟩ := hθ a
  refine ⟨affineWittCohomologyClass X Ω p m b, ?_⟩
  change constantCohomologyPullback θ.hom A 1 (affineWittCohomologyClass X Ω p m b) -
    affineWittCohomologyClass X Ω p m b = c
  change TruncatedWittVector.map θ.hom.appTop.hom b - b = a at hb
  rw [← affineWittCohomologyClass_pullback, ← affineWittCohomologyClass_sub, hb, ha]

end EtaleFundamentalGroups.Cohomology
