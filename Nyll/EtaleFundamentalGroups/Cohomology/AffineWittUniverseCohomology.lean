/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.AffineWittCohomology
public import Nyll.EtaleFundamentalGroups.Cohomology.PointedH1Pullback
public import Nyll.EtaleCohomology.Classical.Adic

/-!
# Affine Witt classes with coefficients in the scheme universe

The coefficient lift is the actual additive equivalence given by `ULift.down`.
Its character comparison retains the original small cyclic values and the
original ambient field action. In universe zero the class is the image of
the existing class under the actual map of constant coefficient sheaves.
-/

@[expose] public section

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open ArtinSchreierWittTheory AnabelianGeometry.WeightFiltration

namespace EtaleFundamentalGroups.Cohomology

/-- The actual cyclic coefficients at every Witt length, including zero. -/
abbrev affineWittLiftedCoefficient (p m : ℕ) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of (ULift.{u} (ZMod (p ^ m)))

/-- At positive length these are exactly the existing adic coefficients. -/
theorem affineWittLiftedCoefficient_succ (p m : ℕ) :
    affineWittLiftedCoefficient.{u} p (m + 1) =
      EtaleCohomology.Classical.ellPowerCoefficients.{u} p m := rfl

/-- Derived H¹ of the original scheme with the lifted cyclic coefficients. -/
abbrev affineWittLiftedH1 (X : Scheme.{u}) (p m : ℕ) : Type u :=
  Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (affineWittLiftedCoefficient p m)) 1

/-- Down and up on actual coefficient values give inverse character maps. -/
def affineWittLiftedCharacterEquiv
    (G : Type v) [Group G] [TopologicalSpace G] (p m : ℕ) [NeZero (p ^ m)] :
    let : TopologicalSpace (Multiplicative (affineWittLiftedCoefficient.{u} p m)) := ⊥
    let : DiscreteTopology (Multiplicative (affineWittLiftedCoefficient.{u} p m)) := ⟨rfl⟩
    Additive (G →ₜ* Multiplicative (affineWittLiftedCoefficient.{u} p m)) ≃+
      Additive (G →ₜ* Multiplicative (ZMod (p ^ m))) := by
  intro topology discreteTopology
  let e := (AddEquiv.ulift : ULift.{u} (ZMod (p ^ m)) ≃+ ZMod (p ^ m)).toMultiplicative
  let down : Multiplicative (affineWittLiftedCoefficient.{u} p m) →ₜ*
      Multiplicative (ZMod (p ^ m)) :=
    { e.toMonoidHom with continuous_toFun := continuous_of_discreteTopology }
  let up : Multiplicative (ZMod (p ^ m)) →ₜ*
      Multiplicative (affineWittLiftedCoefficient.{u} p m) :=
    { e.symm.toMonoidHom with continuous_toFun := continuous_of_discreteTopology }
  exact
    { toFun := fun χ => Additive.ofMul (down.comp χ.toMul)
      invFun := fun χ => Additive.ofMul (up.comp χ.toMul)
      left_inv := fun χ => ContinuousMonoidHom.ext fun g => e.symm_apply_apply (χ.toMul g)
      right_inv := fun χ => ContinuousMonoidHom.ext fun g => e.apply_symm_apply (χ.toMul g)
      map_add' := fun χ ψ => ContinuousMonoidHom.ext fun g => down.map_mul (χ.toMul g) (ψ.toMul g) }

section CharacterComparison

variable {X : Scheme.{u}} [ConnectedSpace X]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)
  (p m : ℕ) [NeZero (p ^ m)]

/-- Actual lifted H¹, evaluated as characters with the original cyclic values. -/
noncomputable def affineWittH1NativeCharacterEquiv :
    affineWittLiftedH1 X p m ≃+
      Additive (Aut (FiniteEtale.fiber ξ) →ₜ* Multiplicative (ZMod (p ^ m))) := by
  let : TopologicalSpace (Multiplicative (affineWittLiftedCoefficient.{u} p m)) := ⊥
  have : DiscreteTopology (Multiplicative (affineWittLiftedCoefficient.{u} p m)) := ⟨rfl⟩
  exact (finiteH1CharacterEquiv (affineWittLiftedCoefficient p m) ξ).trans
    (affineWittLiftedCharacterEquiv (Aut (FiniteEtale.fiber ξ)) p m)

/-- The comparison is literal coefficient descent on every character value. -/
theorem affineWittH1NativeCharacterEquiv_apply
    (c : affineWittLiftedH1 X p m) (g : Aut (FiniteEtale.fiber ξ)) :
    let : TopologicalSpace (Multiplicative (affineWittLiftedCoefficient.{u} p m)) := ⊥
    (affineWittH1NativeCharacterEquiv ξ p m c).toMul g =
      Multiplicative.ofAdd
        ((h1Character (affineWittLiftedCoefficient p m) ξ c g).toAdd.down) := rfl

/-- Coefficient descent preserves the actual pointed scheme pullback square. -/
theorem affineWittH1NativeCharacterEquiv_pointedPullback
    (f : X ⟶ X)
    (t : FiniteEtale.pullback f ⋙ FiniteEtale.fiber ξ ≅ FiniteEtale.fiber ξ)
    (c : affineWittLiftedH1 X p m) (g : Aut (FiniteEtale.fiber ξ)) :
    (affineWittH1NativeCharacterEquiv ξ p m c).toMul
        (autHomOfCompIso (FiniteEtale.pullback f) t g) =
      (affineWittH1NativeCharacterEquiv ξ p m
        (constantCohomologyPullback f (affineWittLiftedCoefficient p m) 1 c)).toMul g := by
  let A := affineWittLiftedCoefficient.{u} p m
  let : TopologicalSpace (Multiplicative A) := ⊥
  exact congrArg (fun χ : Aut (FiniteEtale.fiber ξ) →ₜ* Multiplicative A =>
    Multiplicative.ofAdd ((χ g).toAdd.down))
      (h1Character_pointedSchemePullback f A ξ ξ t c)

end CharacterComparison

section AffineClasses

variable (X : Scheme.{u}) [IsAffine X] [IsIntegral X] [IsNormalIntegral X]
  (Ω : Type u) [Field Ω] [Algebra X.functionField Ω]
  [IsSepClosed Ω] [IsSepClosure X.functionField Ω]
  (p m : ℕ) [Fact p.Prime] [NeZero (p ^ m)] [Nontrivial Γ(X, ⊤)]
  [CharP Γ(X, ⊤) p] [CharP Ω p]

local notation "xi" => Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
  X.fromSpecStalk (genericPoint X)
local notation "phi" => FiniteEtale.fieldSourceAbsoluteGaloisHom
  X.functionField Ω (X.fromSpecStalk (genericPoint X))

/-- The original Witt character defines the actual lifted coefficient class. -/
noncomputable def affineWittLiftedCohomologyClass
    (a : TruncatedWittVector p m Γ(X, ⊤)) : affineWittLiftedH1 X p m :=
  (affineWittH1NativeCharacterEquiv xi p m).symm
    (Additive.ofMul (affineWittCharacter X Ω p m a))

/-- Lifting a coefficient does not change any original cyclic character value. -/
theorem affineWittH1NativeCharacterEquiv_class
    (a : TruncatedWittVector p m Γ(X, ⊤)) (γ : Aut (FiniteEtale.fiber xi)) :
    (affineWittH1NativeCharacterEquiv xi p m
      (affineWittLiftedCohomologyClass X Ω p m a)).toMul γ =
        affineWittCharacter X Ω p m a γ :=
  congrArg (fun χ : Additive (Aut (FiniteEtale.fiber xi) →ₜ*
    Multiplicative (ZMod (p ^ m))) => χ.toMul γ)
      ((affineWittH1NativeCharacterEquiv xi p m).apply_symm_apply _)

/-- Every lifted H¹ class has a coefficient in the original affine ring. -/
theorem affineWittLiftedCohomologyClass_surjective :
    Function.Surjective (affineWittLiftedCohomologyClass X Ω p m) := by
  intro c
  obtain ⟨a, ha⟩ := affineWittCharacter_surjective X Ω p m
    (affineWittH1NativeCharacterEquiv xi p m c).toMul
  refine ⟨a, (affineWittH1NativeCharacterEquiv xi p m).injective ?_⟩
  apply ContinuousMonoidHom.ext
  intro γ
  exact (affineWittH1NativeCharacterEquiv_class X Ω p m a γ).trans
    (DFunLike.congr_fun ha γ)

/-- The class of a coefficient difference is the actual H¹ difference. -/
theorem affineWittLiftedCohomologyClass_sub
    (a b : TruncatedWittVector p m Γ(X, ⊤)) :
    affineWittLiftedCohomologyClass X Ω p m (a - b) =
      affineWittLiftedCohomologyClass X Ω p m a -
        affineWittLiftedCohomologyClass X Ω p m b := by
  apply (affineWittH1NativeCharacterEquiv xi p m).injective
  rw [map_sub]
  apply ContinuousMonoidHom.ext
  intro γ
  change (affineWittH1NativeCharacterEquiv xi p m
      (affineWittLiftedCohomologyClass X Ω p m (a - b))).toMul γ =
    (affineWittH1NativeCharacterEquiv xi p m
      (affineWittLiftedCohomologyClass X Ω p m a)).toMul γ /
    (affineWittH1NativeCharacterEquiv xi p m
      (affineWittLiftedCohomologyClass X Ω p m b)).toMul γ
  rw [affineWittH1NativeCharacterEquiv_class, affineWittH1NativeCharacterEquiv_class,
    affineWittH1NativeCharacterEquiv_class]
  exact DFunLike.congr_fun (affineWittCharacter_sub X Ω p m a b) γ

/-- The original coefficient transport is actual derived scheme pullback. -/
theorem affineWittLiftedCohomologyClass_pullback (θ : X ≅ X)
    (a : TruncatedWittVector p m Γ(X, ⊤)) :
    affineWittLiftedCohomologyClass X Ω p m (TruncatedWittVector.map θ.hom.appTop.hom a) =
      constantCohomologyPullback θ.hom (affineWittLiftedCoefficient p m) 1
        (affineWittLiftedCohomologyClass X Ω p m a) := by
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
  apply (affineWittH1NativeCharacterEquiv xi p m).injective
  apply ContinuousMonoidHom.ext
  intro γ
  obtain ⟨ρ', rfl⟩ := FiniteEtale.genericFieldAction_surjective X Ω γ
  obtain ⟨ρ, rfl⟩ := (KummerTheory.semilinearGaloisConjugateEquiv τ e he).surjective ρ'
  let σ := KummerTheory.semilinearGaloisConjugate τ e he ρ
  let A := affineWittLiftedCoefficient.{u} p m
  let : TopologicalSpace (Multiplicative A) := ⊥
  have hp := congrArg (fun z : Multiplicative A => Multiplicative.ofAdd z.toAdd.down)
    (h1Character_semilinearSourcePullback (X.fromSpecStalk (genericPoint X))
      θ.hom τ e he hpoint A (affineWittLiftedCohomologyClass X Ω p m a) ρ)
  change (affineWittH1NativeCharacterEquiv xi p m
      (constantCohomologyPullback θ.hom A 1 (affineWittLiftedCohomologyClass X Ω p m a))).toMul
        (phi σ) = (affineWittH1NativeCharacterEquiv xi p m
          (affineWittLiftedCohomologyClass X Ω p m a)).toMul (phi ρ) at hp
  change (affineWittH1NativeCharacterEquiv xi p m
      (affineWittLiftedCohomologyClass X Ω p m
        (TruncatedWittVector.map θ.hom.appTop.hom a))).toMul (phi σ) =
    (affineWittH1NativeCharacterEquiv xi p m
      (constantCohomologyPullback θ.hom A 1
        (affineWittLiftedCohomologyClass X Ω p m a))).toMul (phi σ)
  rw [hp, affineWittH1NativeCharacterEquiv_class, affineWittH1NativeCharacterEquiv_class]
  refine (DFunLike.congr_fun hχ' σ).trans ?_
  refine Eq.trans ?_ (DFunLike.congr_fun hχ ρ).symm
  simpa only [hcoeff] using rootCharacter_semilinear p m τ e he
    (affineWittGenericCoefficient X p m a) r hr ρ

include Ω in
/-- Coefficient difference surjectivity passes to actual lifted H¹. -/
theorem affineWittLiftedCohomology_pullback_sub_id_surjective (θ : X ≅ X)
    (hθ : Function.Surjective (fun a : TruncatedWittVector p m Γ(X, ⊤) =>
      TruncatedWittVector.map θ.hom.appTop.hom a - a)) :
    Function.Surjective (fun c : affineWittLiftedH1 X p m =>
      constantCohomologyPullback θ.hom (affineWittLiftedCoefficient p m) 1 c - c) := by
  intro c
  obtain ⟨a, ha⟩ := affineWittLiftedCohomologyClass_surjective X Ω p m c
  obtain ⟨b, hb⟩ := hθ a
  refine ⟨affineWittLiftedCohomologyClass X Ω p m b, ?_⟩
  change constantCohomologyPullback θ.hom (affineWittLiftedCoefficient p m) 1
    (affineWittLiftedCohomologyClass X Ω p m b) - affineWittLiftedCohomologyClass X Ω p m b = c
  change TruncatedWittVector.map θ.hom.appTop.hom b - b = a at hb
  rw [← affineWittLiftedCohomologyClass_pullback, ← affineWittLiftedCohomologyClass_sub, hb, ha]

end AffineClasses

section NativeComparison

variable (X : Scheme.{0}) [IsAffine X] [IsIntegral X] [IsNormalIntegral X]
  (Ω : Type) [Field Ω] [Algebra X.functionField Ω]
  [IsSepClosed Ω] [IsSepClosure X.functionField Ω]
  (p m : ℕ) [Fact p.Prime] [NeZero (p ^ m)] [Nontrivial Γ(X, ⊤)]
  [CharP Γ(X, ⊤) p] [CharP Ω p]

local notation "xi" => Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
  X.fromSpecStalk (genericPoint X)

/-- In universe zero the lift is the original derived coefficient map. -/
theorem affineWittLiftedCohomologyClass_eq_native_map
    (a : TruncatedWittVector p m Γ(X, ⊤)) :
    affineWittLiftedCohomologyClass X Ω p m a =
      Sheaf.H.map ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).map
        (AddCommGrpCat.ofHom
          (AddEquiv.ulift : ULift.{0} (ZMod (p ^ m)) ≃+ ZMod (p ^ m)).symm.toAddMonoidHom)) 1
            (affineWittCohomologyClass X Ω p m a) := by
  apply (affineWittH1NativeCharacterEquiv xi p m).injective
  apply ContinuousMonoidHom.ext
  intro γ
  let A := affineWittCoefficient p m
  let B := affineWittLiftedCoefficient.{0} p m
  let : TopologicalSpace (Multiplicative A) := ⊥
  let : TopologicalSpace (Multiplicative B) := ⊥
  let α : A ⟶ B := AddCommGrpCat.ofHom
    (AddEquiv.ulift : ULift.{0} (ZMod (p ^ m)) ≃+ ZMod (p ^ m)).symm.toAddMonoidHom
  have h := congrArg (fun χ : Aut (FiniteEtale.fiber xi) →ₜ* Multiplicative B =>
    Multiplicative.ofAdd ((χ γ).toAdd.down))
      (h1Character_naturality α xi (affineWittCohomologyClass X Ω p m a))
  exact (affineWittH1NativeCharacterEquiv_class X Ω p m a γ).trans
    ((h1Character_affineWittCohomologyClass X Ω p m a γ).symm.trans h)

end NativeComparison

end EtaleFundamentalGroups.Cohomology
