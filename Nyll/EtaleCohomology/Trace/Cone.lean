/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Trace.Perfect
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
# Trace additivity for a coherent mapping-cone endomorphism

A square of chain maps together with a specified homotopy induces the native
`mappingCone.mapOfHomotopy`. Its trace is the target trace minus the source
trace. The homotopy contributes only an off-diagonal term, and cyclicity
annihilates that term. These statements concern the actual coherent cone map;
they do not assert additivity for an arbitrary morphism of distinguished
triangles over a nonreduced coefficient ring.
-/

noncomputable section

universe u v w

open CategoryTheory CochainComplex CochainComplex.HomComplex

namespace EtaleCohomology

variable (R : Type u) [CommRing R]
variable {F G : CochainComplex (ModuleCat.{v} R) ℤ} (φ : F ⟶ G)
variable [∀ i : ℤ, Module.Finite R (F.X i)] [∀ i : ℤ, Module.Projective R (F.X i)]
  [∀ i : ℤ, Module.Finite R (G.X i)] [∀ i : ℤ, Module.Projective R (G.X i)]

/-- Each mapping-cone term is finite, using its actual binary-biproduct decomposition. -/
instance mappingCone_finite (i : ℤ) : Module.Finite R ((mappingCone φ).X i) :=
  Module.Finite.equiv
    ((HomologicalComplex.homotopyCofiber.XIsoBiprod φ i (i + 1) rfl) ≪≫
      ModuleCat.biprodIsoProd (F.X (i + 1)) (G.X i)).toLinearEquiv.symm

/-- Each mapping-cone term is projective, using its actual binary-biproduct decomposition. -/
instance mappingCone_projective (i : ℤ) : Module.Projective R ((mappingCone φ).X i) :=
  Module.Projective.of_equiv'
    ((HomologicalComplex.homotopyCofiber.XIsoBiprod φ i (i + 1) rfl) ≪≫
      ModuleCat.biprodIsoProd (F.X (i + 1)) (G.X i)).toLinearEquiv.symm

/-- The native cone is bounded below by the shifted source and the target bounds. -/
instance mappingCone_boundedBelow (a c : ℤ) [F.IsStrictlyGE a] [G.IsStrictlyGE c] :
    (mappingCone φ).IsStrictlyGE (min (a - 1) c) := by
  apply ((mappingCone φ).isStrictlyGE_iff _).mpr
  intro i hi
  apply (mappingCone.isZero_X_iff φ i).mpr
  exact ⟨F.isZero_of_isStrictlyGE a (i + 1) (by omega),
    G.isZero_of_isStrictlyGE c i (by omega)⟩

/-- The native cone is bounded above by the shifted source and the target bounds. -/
instance mappingCone_boundedAbove (b d : ℤ) [F.IsStrictlyLE b] [G.IsStrictlyLE d] :
    (mappingCone φ).IsStrictlyLE (max (b - 1) d) := by
  apply ((mappingCone φ).isStrictlyLE_iff _).mpr
  intro i hi
  apply (mappingCone.isZero_X_iff φ i).mpr
  exact ⟨F.isZero_of_isStrictlyLE b (i + 1) (by omega),
    G.isZero_of_isStrictlyLE d i (by omega)⟩

/-- The off-diagonal homotopy term contributes zero to the degreewise projective trace. -/
theorem mappingCone_projectiveTrace_mapOfHomotopy
    (f : F ⟶ F) (g : G ⟶ G) (H : Homotopy (φ ≫ g) (f ≫ φ)) (i : ℤ) :
    LinearMap.projectiveTrace R ((mappingCone φ).X i)
        ((mappingCone.mapOfHomotopy H).f i).hom =
      LinearMap.projectiveTrace R (F.X (i + 1)) (f.f (i + 1)).hom +
        LinearMap.projectiveTrace R (G.X i) (g.f i).hom := by
  let α : Cochain F (mappingCone φ) (-1) :=
    (Cochain.ofHom f).comp (mappingCone.inl φ) (zero_add _) +
      ((Cochain.equivHomotopy _ _) H).1.comp
        (Cochain.ofHom (mappingCone.inr φ)) (add_zero _)
  have hleft : α.v (i + 1) i (by omega) ≫ (mappingCone.fst φ).1.v i (i + 1) rfl =
      f.f (i + 1) := by
    dsimp only [α]
    simp only [Cochain.add_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
      Cochain.comp_zero_cochain_v, Preadditive.add_comp, Category.assoc,
      mappingCone.inl_v_fst_v, mappingCone.inr_f_fst_v, Category.comp_id,
      Limits.comp_zero, add_zero]
  have hright : (g ≫ mappingCone.inr φ).f i ≫ (mappingCone.snd φ).v i i (add_zero i) =
      g.f i := by
    rw [HomologicalComplex.comp_f, Category.assoc, mappingCone.inr_f_snd_v,
      Category.comp_id]
  change LinearMap.projectiveTrace R ((mappingCone φ).X i)
    ((mappingCone.desc φ α (g ≫ mappingCone.inr φ) _).f i).hom = _
  rw [mappingCone.desc_f φ α (g ≫ mappingCone.inr φ) _ i (i + 1) rfl,
    ModuleCat.hom_add, map_add, ModuleCat.hom_comp, ModuleCat.hom_comp,
    LinearMap.projectiveTrace_comp_comm ((mappingCone.fst φ).1.v i (i + 1) rfl).hom
      (α.v (i + 1) i (by omega)).hom,
    LinearMap.projectiveTrace_comp_comm ((mappingCone.snd φ).v i i (add_zero i)).hom
      ((g ≫ mappingCone.inr φ).f i).hom,
    ← ModuleCat.hom_comp, ← ModuleCat.hom_comp, hleft, hright]

variable (a b c d : ℤ) [F.IsStrictlyGE a] [F.IsStrictlyLE b]
  [G.IsStrictlyGE c] [G.IsStrictlyLE d]

/-- Additivity of the alternating trace for the native cone map of a homotopy-commutative square. -/
theorem boundedComplexTrace_mapOfHomotopy
    (f : F ⟶ F) (g : G ⟶ G) (H : Homotopy (φ ≫ g) (f ≫ φ)) :
    boundedComplexTrace R (mappingCone φ) (min (a - 1) c) (max (b - 1) d)
        (mappingCone.mapOfHomotopy H) =
      boundedComplexTrace R G c d g - boundedComplexTrace R F a b f := by
  let t : ℤ → R := fun i => i.negOnePow • LinearMap.projectiveTrace R (F.X i) (f.f i).hom
  have ht : Function.HasFiniteSupport t := signedTrace_hasFiniteSupport R F a b f.f
  have hshift (i : ℤ) :
      i.negOnePow • LinearMap.projectiveTrace R (F.X (i + 1)) (f.f (i + 1)).hom =
        -t (i + 1) := by
    dsimp only [t]
    rw [Int.negOnePow_succ, Units.neg_smul, neg_neg]
  have hs : Function.HasFiniteSupport (fun i : ℤ => -t (i + 1)) :=
    (ht.fun_comp_of_injective (Equiv.addRight (1 : ℤ)).injective).neg
  have hsum : (∑ᶠ i : ℤ, t (i + 1)) = ∑ᶠ i : ℤ, t i :=
    finsum_comp_equiv (Equiv.addRight (1 : ℤ)) (f := t)
  change (∑ᶠ i : ℤ, i.negOnePow • LinearMap.projectiveTrace R ((mappingCone φ).X i)
      ((mappingCone.mapOfHomotopy H).f i).hom) =
    (∑ᶠ i : ℤ, i.negOnePow • LinearMap.projectiveTrace R (G.X i) (g.f i).hom) -
      ∑ᶠ i : ℤ, t i
  simp_rw [mappingCone_projectiveTrace_mapOfHomotopy R φ f g H, smul_add, hshift]
  rw [finsum_add_distrib hs (signedTrace_hasFiniteSupport R G c d g.f),
    finsum_neg_distrib, hsum, sub_eq_add_neg, add_comm]

variable [HasDerivedCategory.{w} (ModuleCat.{v} R)]

/-- The same coherent additivity identity holds for the actual derived cone endomorphism. -/
theorem derivedBoundedComplexTrace_mapOfHomotopy
    (f : F ⟶ F) (g : G ⟶ G) (H : Homotopy (φ ≫ g) (f ≫ φ)) :
    derivedBoundedComplexTrace R (mappingCone φ) (min (a - 1) c) (max (b - 1) d)
        (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
          (mappingCone.mapOfHomotopy H))) =
      derivedBoundedComplexTrace R G c d
          (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map g)) -
        derivedBoundedComplexTrace R F a b
          (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map f)) := by
  rw [derivedBoundedComplexTrace_map, derivedBoundedComplexTrace_map,
    derivedBoundedComplexTrace_map, homotopyComplexTrace_map,
    homotopyComplexTrace_map, homotopyComplexTrace_map]
  exact boundedComplexTrace_mapOfHomotopy R φ a b c d f g H

/-- The cone itself gives an actual bounded finite projective model of its derived image. -/
def mappingConePerfectModel :
    PerfectComplexModel R (DerivedCategory.Q.obj (mappingCone φ)) where
  complex := mappingCone φ
  lower := min (a - 1) c
  upper := max (b - 1) d
  finite := mappingCone_finite R φ
  projective := mappingCone_projective R φ
  boundedBelow := inferInstance
  boundedAbove := inferInstance
  iso := Iso.refl _

end EtaleCohomology
