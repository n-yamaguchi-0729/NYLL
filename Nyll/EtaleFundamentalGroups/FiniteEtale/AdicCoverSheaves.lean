/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTower
import Nyll.SchemeTheory.Modules.Functoriality.DirectImageAlgebraMap
import Nyll.SchemeTheory.Affine.ClosedBaseChangeSections
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Ideal.Operations

/-!
# The genuine adic algebra sheaves of the lifted finite étale covers

The actual finite étale cover tower gives native direct-image algebras on
the fixed original scheme. Their underlying modules are quasicoherent
and of finite type. The actual cover morphisms induce algebra and module
transitions, and their cartesian reduction squares give surjectivity and
the precise ideal-power kernels on every affine open.

Each module is annihilated by the corresponding ideal power. All these
properties are proved from the constructed cover tower; no effective
algebra, algebraization, or comparison with an effective object is an
input. This supplies the geometric adic-system input to the existence
step in Stacks Project 0A48/0GS2.

https://stacks.math.columbia.edu/tag/0A48
https://stacks.math.columbia.edu/tag/0GS2
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))

/-- The actual finite morphism from the lifted cover to the fixed original scheme. -/
def coverToOriginal (n : ℕ) : (cover f I V n).left ⟶ X :=
  (cover f I V n).hom ≫ pullback.fst f (baseInclusion I n)

/-- The structural map of the lifted cover to its literal quotient base. -/
def coverToQuotient (n : ℕ) : (cover f I V n).left ⟶ base I n :=
  (cover f I V n).hom ≫ pullback.snd f (baseInclusion I n)

instance coverToOriginal_isFinite (n : ℕ) : IsFinite (coverToOriginal f I V n) := by
  have hcover : IsFinite (cover f I V n).hom := (cover f I V n).prop.1
  have hbase : IsClosedImmersion (baseInclusion I n) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (Ideal.Quotient.mk (levelIdeal I n)))
      Ideal.Quotient.mk_surjective
  change IsFinite ((cover f I V n).hom ≫ pullback.fst f (baseInclusion I n))
  infer_instance

/-- The original structural map factors through the prescribed quotient base. -/
theorem coverToOriginal_comp (n : ℕ) :
    coverToOriginal f I V n ≫ f = coverToQuotient f I V n ≫ baseInclusion I n := by
  let c : (cover f I V n).left ⟶ level f I n := (cover f I V n).hom
  change (c ≫ pullback.fst f (baseInclusion I n)) ≫ f =
    (c ≫ pullback.snd f (baseInclusion I n)) ≫ baseInclusion I n
  rw [Category.assoc, pullback.condition, Category.assoc]

/-- The actual cover transitions lie over the fixed original scheme. -/
theorem coverTransition_toOriginal (n : ℕ) :
    coverTransition f I V n ≫ coverToOriginal f I V (n + 1) = coverToOriginal f I V n := by
  let c : (cover f I V n).left ⟶ level f I n := (cover f I V n).hom
  let c' : (cover f I V (n + 1)).left ⟶ level f I (n + 1) :=
    (cover f I V (n + 1)).hom
  let r : (cover f I V n).left ⟶ (cover f I V (n + 1)).left := coverTransition f I V n
  let p : level f I n ⟶ X := pullback.fst f (baseInclusion I n)
  let p' : level f I (n + 1) ⟶ X := pullback.fst f (baseInclusion I (n + 1))
  have hc : r ≫ c' = c ≫ transition f I n := coverTransition_comm f I V n
  have hp : transition f I n ≫ p' = p := transition_fst f I n
  change r ≫ (c' ≫ p') = c ≫ p
  calc
    r ≫ (c' ≫ p') = (r ≫ c') ≫ p' := (Category.assoc _ _ _).symm
    _ = (c ≫ transition f I n) ≫ p' := congrArg (fun k => k ≫ p') hc
    _ = c ≫ p := (Category.assoc _ _ _).trans (congrArg (fun k => c ≫ k) hp)

/-- Pasting the actual cover and base-change squares gives the cartesian
square over the successive quotient spectra themselves. -/
theorem coverTransition_isPullback_quotient (n : ℕ) :
    IsPullback (coverTransition f I V n) (coverToQuotient f I V n)
      (coverToQuotient f I V (n + 1)) (baseTransition I n) :=
  (coverTransition_isPullback f I V n).paste_vert (transition_isPullback f I n)

instance coverTransition_isClosedImmersion (n : ℕ) :
    IsClosedImmersion (coverTransition f I V n) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (coverTransition_isPullback_quotient f I V n).flip (baseTransition_isClosedImmersion I n)

/-- The genuine ring sheaf on the fixed scheme at the `n+1`-st adic level. -/
def algebraSheaf (n : ℕ) : TopCat.Sheaf CommRingCat.{u} X :=
  Scheme.DirectImageAlgebra.sheaf (coverToOriginal f I V n)

/-- Its structural map is the actual finite morphism's map of structure sheaves. -/
def algebraStructure (n : ℕ) : X.sheaf ⟶ algebraSheaf f I V n :=
  Scheme.DirectImageAlgebra.structureMap (coverToOriginal f I V n)

/-- The native underlying module of the actual finite direct-image algebra. -/
def moduleSheaf (n : ℕ) : X.Modules :=
  Scheme.RelativeSpec.underlyingModule (algebraStructure f I V n)

instance moduleSheaf_isQuasicoherent (n : ℕ) : (moduleSheaf f I V n).IsQuasicoherent :=
  Scheme.DirectImageAlgebra.isQuasicoherent_underlyingModule (coverToOriginal f I V n)

instance moduleSheaf_isFiniteType (n : ℕ) : (moduleSheaf f I V n).IsFiniteType :=
  Scheme.DirectImageAlgebra.isFiniteType_underlyingModule (coverToOriginal f I V n)

/-- The actual cover map induces the transition of algebra sheaves. -/
def algebraTransition (n : ℕ) : algebraSheaf f I V (n + 1) ⟶ algebraSheaf f I V n :=
  Scheme.DirectImageAlgebra.map (coverToOriginal f I V n) (coverToOriginal f I V (n + 1))
    (coverTransition f I V n) (coverTransition_toOriginal f I V n)

/-- Every transition preserves the original structure-sheaf coefficients. -/
theorem algebraStructure_transition (n : ℕ) :
    algebraStructure f I V (n + 1) ≫ algebraTransition f I V n = algebraStructure f I V n :=
  Scheme.DirectImageAlgebra.structureMap_map _ _ _ _

/-- The native-module transition, with the same original section maps. -/
def moduleTransition (n : ℕ) : moduleSheaf f I V (n + 1) ⟶ moduleSheaf f I V n :=
  Scheme.DirectImageAlgebra.moduleMap _ _ _ (coverTransition_toOriginal f I V n)

/-- The ideal on an actual open is extended by the original structural coefficient map. -/
def sectionsIdeal (U : X.Opens) : Ideal Γ(X, U) :=
  I.map (f.constToPresheaf.app (op U)).hom

/-- The actual cover coefficients factor through the original quotient map. -/
theorem coverCoefficient_factor (n : ℕ) (U : X.Opens) :
    ((coverToOriginal f I V n).app U).hom.comp (f.constToPresheaf.app (op U)).hom =
      ((coverToQuotient f I V n).constToPresheaf.app
        (op (coverToOriginal f I V n ⁻¹ᵁ U))).hom.comp (Ideal.Quotient.mk (levelIdeal I n)) := by
  let W : (cover f I V n).left.Opens := coverToOriginal f I V n ⁻¹ᵁ U
  calc
    ((coverToOriginal f I V n).app U).hom.comp (f.constToPresheaf.app (op U)).hom =
        ((coverToOriginal f I V n ≫ f).constToPresheaf.app (op W)).hom :=
      Scheme.Hom.constToPresheaf_comp_app _ _ _
    _ = ((coverToQuotient f I V n ≫ baseInclusion I n).constToPresheaf.app (op W)).hom :=
      congrArg (fun p : (cover f I V n).left ⟶ Spec (.of A) =>
        (p.constToPresheaf.app (op W)).hom) (coverToOriginal_comp f I V n)
    _ = ((coverToQuotient f I V n).constToPresheaf.app (op W)).hom.comp
        (Ideal.Quotient.mk (levelIdeal I n)) :=
      Scheme.Hom.constToPresheaf_comp_Spec_map _ _ _

private theorem directImageMap_ker {Y Y' Z : Scheme.{u}}
    (g : Y ⟶ Z) (g' : Y' ⟶ Z) (r : Y ⟶ Y') (h : r ≫ g' = g) (U : Z.Opens) :
    RingHom.ker ((Scheme.DirectImageAlgebra.map g g' r h).hom.app (op U)).hom =
      RingHom.ker (r.app (g' ⁻¹ᵁ U)).hom := by
  subst g
  change RingHom.ker (r.appLE (g' ⁻¹ᵁ U) (r ⁻¹ᵁ (g' ⁻¹ᵁ U)) le_rfl).hom = _
  rw [Scheme.Hom.appLE_eq_app]

/-- Every algebra transition is surjective on the actual sections over
an affine open of the fixed original scheme. -/
theorem algebraTransition_app_surjective (n : ℕ) (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Surjective ((algebraTransition f I V n).hom.app (op U)) :=
  Scheme.DirectImageAlgebra.map_app_surjective _ _ _ _ U
    (hU.preimage (coverToOriginal f I V (n + 1)))

/-- The algebra transition kernel is the prescribed ideal power extended
to the actual section algebra of the later cover. -/
theorem algebraTransition_app_ker (n : ℕ) (U : X.Opens) (hU : IsAffineOpen U) :
    RingHom.ker ((algebraTransition f I V n).hom.app (op U)).hom =
      ((sectionsIdeal f I U) ^ (n + 1)).map ((coverToOriginal f I V (n + 1)).app U).hom := by
  let W : (cover f I V (n + 1)).left.Opens := coverToOriginal f I V (n + 1) ⁻¹ᵁ U
  have hW : IsAffineOpen W := hU.preimage (coverToOriginal f I V (n + 1))
  let B : CommRingCat.{u} := Γ((cover f I V (n + 1)).left, W)
  let τ : B →+* (algebraSheaf f I V n).obj.obj (op U) :=
    ((algebraTransition f I V n).hom.app (op U)).hom
  let k : B →+* Γ((cover f I V n).left, coverTransition f I V n ⁻¹ᵁ W) :=
    ((coverTransition f I V n).app W).hom
  let σ : (A ⧸ levelIdeal I (n + 1)) →+* B :=
    ((coverToQuotient f I V (n + 1)).constToPresheaf.app (op W)).hom
  let g : Γ(X, U) →+* B := ((coverToOriginal f I V (n + 1)).app U).hom
  let q : (A ⧸ levelIdeal I (n + 1)) →+* (A ⧸ levelIdeal I n) :=
    Ideal.Quotient.factor (levelIdeal_succ_le I n)
  have hq : Function.Surjective q := Ideal.Quotient.factor_surjective (levelIdeal_succ_le I n)
  have hker : RingHom.ker k = (RingHom.ker q).map σ :=
    Scheme.Hom.ker_app_of_closed_baseChange
    (coverToQuotient f I V (n + 1)) (coverToQuotient f I V n) (coverTransition f I V n)
    (CommRingCat.ofHom q) (coverTransition_isPullback_quotient f I V n) hq W hW
  have hcoeff : σ.comp (Ideal.Quotient.mk (levelIdeal I (n + 1))) =
      g.comp (f.constToPresheaf.app (op U)).hom :=
    (coverCoefficient_factor f I V (n + 1) U).symm
  have hqker : RingHom.ker q =
      (levelIdeal I n).map (Ideal.Quotient.mk (levelIdeal I (n + 1))) :=
    Ideal.Quotient.factor_ker (levelIdeal_succ_le I n)
  change RingHom.ker τ = ((sectionsIdeal f I U) ^ (n + 1)).map g
  calc
    RingHom.ker τ = RingHom.ker k :=
      directImageMap_ker _ _ _ _ U
    _ = (RingHom.ker q).map σ := hker
    _ = ((sectionsIdeal f I U) ^ (n + 1)).map g := by
      rw [hqker, Ideal.map_map, hcoeff, levelIdeal_eq_pow I n]
      rw [sectionsIdeal, ← Ideal.map_pow, Ideal.map_map]

/-- The actual affine module at every level is finite. -/
theorem moduleSheaf_finite_sections (n : ℕ) (U : X.Opens) (hU : IsAffineOpen U) :
    Module.Finite Γ(X, U) Γ(moduleSheaf f I V n, U) :=
  Scheme.DirectImageAlgebra.moduleFinite_sections (coverToOriginal f I V n) U hU

/-- The underlying native linear transition is surjective on affine sections. -/
theorem moduleTransition_app_surjective (n : ℕ) (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Surjective (((moduleTransition f I V n).val.app (op U)).hom) :=
  algebraTransition_app_surjective f I V n U hU

/-- The affine native linear transition has exactly the adic kernel,
with the original action by sections on the fixed scheme. -/
theorem moduleTransition_app_ker (n : ℕ) (U : X.Opens) (hU : IsAffineOpen U) :
    (((moduleTransition f I V n).val.app (op U)).hom).ker =
      (sectionsIdeal f I U) ^ (n + 1) •
        (⊤ : Submodule Γ(X, U) Γ(moduleSheaf f I V (n + 1), U)) := by
  let B : CommRingCat.{u} := Γ((cover f I V (n + 1)).left, coverToOriginal f I V (n + 1) ⁻¹ᵁ U)
  let q : Γ(X, U) →+* B := ((coverToOriginal f I V (n + 1)).app U).hom
  let τ : B →+* Γ((cover f I V n).left, coverToOriginal f I V n ⁻¹ᵁ U) :=
    ((algebraTransition f I V n).hom.app (op U)).hom
  let : Algebra Γ(X, U) B := q.toAlgebra
  change (RingHom.ker τ).restrictScalars Γ(X, U) =
    (sectionsIdeal f I U) ^ (n + 1) • (⊤ : Submodule Γ(X, U) B)
  rw [Ideal.smul_top_eq_map]
  have hker : RingHom.ker τ = ((sectionsIdeal f I U) ^ (n + 1)).map q :=
    algebraTransition_app_ker f I V n U hU
  exact congrArg (fun J : Ideal B => J.restrictScalars Γ(X, U))
    hker

/-- Each actual sheaf module is annihilated by its specified adic power,
on every open set, without an affine or completeness hypothesis. -/
theorem moduleSheaf_sections_annihilated (n : ℕ) (U : X.Opens) :
    (sectionsIdeal f I U) ^ (n + 1) •
      (⊤ : Submodule Γ(X, U) Γ(moduleSheaf f I V n, U)) = ⊥ := by
  have hker : (sectionsIdeal f I U) ^ (n + 1) ≤
      RingHom.ker ((coverToOriginal f I V n).app U).hom := by
    rw [sectionsIdeal, ← Ideal.map_pow]
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change (((coverToOriginal f I V n).app U).hom.comp
      (f.constToPresheaf.app (op U)).hom) a = 0
    rw [coverCoefficient_factor]
    change ((coverToQuotient f I V n).constToPresheaf.app
      (op (coverToOriginal f I V n ⁻¹ᵁ U))).hom (Ideal.Quotient.mk (levelIdeal I n) a) = 0
    have ha' : a ∈ levelIdeal I n := by
      rw [levelIdeal_eq_pow]
      exact ha
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha', map_zero]
  apply le_antisymm ?_ bot_le
  apply Submodule.smul_le.mpr
  intro a ha x _hx
  let y : Γ((cover f I V n).left, coverToOriginal f I V n ⁻¹ᵁ U) := x
  change ((coverToOriginal f I V n).app U).hom a * y = 0
  rw [show ((coverToOriginal f I V n).app U).hom a = 0 from hker ha]
  exact zero_mul y

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
