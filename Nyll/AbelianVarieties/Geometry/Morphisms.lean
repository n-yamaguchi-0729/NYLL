/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AbelianVarieties.Geometry.GroupLaw
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Translation
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.AbelianSchemeSchemeHomOverCompMulEqMul
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Morphisms of abelian schemes are translates of homomorphisms

Mumford, *Abelian Varieties*, §4, Corollary 1 (p. 43), over an arbitrary
commutative base ring. The existing theorem for zero-preserving morphisms
supplies the homomorphism property; the translation is the actual image of
the identity section. Both factors are unique as scheme morphisms.

The imported translation and pointed-morphism proofs retain their own
Anthropic FLT source notices. The proofs in this file are new compositions
of those existing APIs.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra
open AbelianVarieties.NOSProofs.TranslationAutomorphisms.Translations

namespace GoodReductionJacobian.AbelianSchemePropertyBundle

variable {R : Type u} [CommRing R] {A B : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of R)} {g : B ⟶ Spec (CommRingCat.of R)}

/-- A morphism between abelian schemes preserves the group operation on every
test scheme if and only if it preserves the identity section. -/
theorem preserves_mul_iff_preserves_one
    (hA : AbelianSchemePropertyBundle R f) (hB : AbelianSchemePropertyBundle R g)
    (L : RelativeGroupLaw R f) (M : RelativeGroupLaw R g) (φ : SchemeHomOver f g) :
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) φ =
        M.mul t (NeronModelInfra.schemeHomOverComp x φ)
          (NeronModelInfra.schemeHomOverComp y φ)) ↔
      NeronModelInfra.schemeHomOverComp (L.one (𝟙 (Spec (CommRingCat.of R)))) φ =
        M.one (𝟙 (Spec (CommRingCat.of R))) := by
  constructor
  · intro hmul
    let a : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) g :=
      NeronModelInfra.schemeHomOverComp (L.one (𝟙 _)) φ
    have ha : a = M.mul (𝟙 _) a a := by
      simpa only [L.one_mul] using hmul (𝟙 _) (L.one (𝟙 _)) (L.one (𝟙 _))
    have h := congrArg (fun b => M.mul (𝟙 _) (M.inv (𝟙 _) a) b) ha
    rw [M.inv_mul_cancel, ← M.mul_assoc, M.inv_mul_cancel, M.one_mul] at h
    exact h.symm
  · exact schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one hA hB L M φ

private theorem translate_eq_rt (M : RelativeGroupLaw R g)
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) g) :
    M.translate a = rt M a := rfl

/-- Every actual morphism over the base between abelian schemes has a unique
decomposition as a group homomorphism followed by translation by a base section.
The homomorphism condition is asserted on all scheme-valued points, so the
decomposition includes nonreduced test schemes and bases. -/
theorem existsUnique_hom_translate
    (hA : AbelianSchemePropertyBundle R f) (hB : AbelianSchemePropertyBundle R g)
    (L : RelativeGroupLaw R f) (M : RelativeGroupLaw R g)
    (φ : A ⟶ B) (hφ : φ ≫ g = f) :
    ∃! p : SchemeHomOver f g × SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) g,
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
        NeronModelInfra.schemeHomOverComp (L.mul t x y) p.1 =
          M.mul t (NeronModelInfra.schemeHomOverComp x p.1)
            (NeronModelInfra.schemeHomOverComp y p.1)) ∧
      p.1.1 ≫ M.translate p.2 = φ := by
  let φ' : SchemeHomOver f g := ⟨φ, hφ⟩
  let a : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) g :=
    NeronModelInfra.schemeHomOverComp (L.one (𝟙 _)) φ'
  let ψ : SchemeHomOver f g :=
    ⟨φ ≫ rt M (M.inv (𝟙 _) a), by rw [Category.assoc, rt_over, hφ]⟩
  have hψone : NeronModelInfra.schemeHomOverComp (L.one (𝟙 _)) ψ = M.one (𝟙 _) := by
    apply Subtype.ext
    change (L.one (𝟙 _)).1 ≫ (φ ≫ rt M (M.inv (𝟙 _) a)) = (M.one (𝟙 _)).1
    rw [← Category.assoc]
    change a.1 ≫ rt M (M.inv (𝟙 _) a) = (M.one (𝟙 _)).1
    rw [comp_rt]
    have hconst : const (M.inv (𝟙 _) a) (𝟙 (Spec (CommRingCat.of R))) = M.inv (𝟙 _) a :=
      Subtype.ext (Category.id_comp _)
    rw [hconst, M.mul_inv_cancel]
  have hψmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (x y : SchemeHomOver t f), NeronModelInfra.schemeHomOverComp (L.mul t x y) ψ =
        M.mul t (NeronModelInfra.schemeHomOverComp x ψ)
          (NeronModelInfra.schemeHomOverComp y ψ) :=
    (preserves_mul_iff_preserves_one hA hB L M ψ).mpr hψone
  have hψφ : ψ.1 ≫ M.translate a = φ := by
    rw [translate_eq_rt]
    change (φ ≫ rt M (M.inv (𝟙 _) a)) ≫ rt M a = φ
    rw [Category.assoc, rt_mul, M.inv_mul_cancel, rt_one, Category.comp_id]
  refine ⟨(ψ, a), ⟨hψmul, hψφ⟩, ?_⟩
  rintro ⟨θ, b⟩ ⟨hθmul, hθφ⟩
  have hθone := (preserves_mul_iff_preserves_one hA hB L M θ).mp hθmul
  have hθone' : (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ θ.1 =
      (M.one (𝟙 (Spec (CommRingCat.of R)))).1 := congrArg Subtype.val hθone
  have hb : b = a := by
    apply Subtype.ext
    have h := congrArg (fun z : A ⟶ B => (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ z) hθφ
    rw [← Category.assoc, hθone', translate_eq_rt, comp_rt, M.one_mul] at h
    change 𝟙 (Spec (CommRingCat.of R)) ≫ b.1 = a.1 at h
    simpa only [Category.id_comp] using h
  have hθ : θ = ψ := by
    apply Subtype.ext
    calc
      θ.1 = (θ.1 ≫ M.translate b) ≫ rt M (M.inv (𝟙 _) b) := by
        rw [translate_eq_rt, Category.assoc, rt_mul, M.mul_inv_cancel, rt_one,
          Category.comp_id]
      _ = φ ≫ rt M (M.inv (𝟙 _) b) := by rw [hθφ]
      _ = ψ.1 := by rw [hb]
  exact Prod.ext hθ hb

end GoodReductionJacobian.AbelianSchemePropertyBundle
