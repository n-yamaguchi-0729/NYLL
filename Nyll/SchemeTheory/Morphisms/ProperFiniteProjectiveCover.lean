/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Divisors.ReducedIrreducibleComponentGeometry
public import Nyll.SchemeTheory.FiniteEtale.Forget.FiniteCoproducts
public import Nyll.SchemeTheory.Morphisms.ChowDatumProj
public import Nyll.SchemeTheory.Morphisms.SigmaPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.Topology.NoetherianSpace

/-!
# Finite projective covers of proper Noetherian families

The reduced irreducible components of a proper scheme over a Noetherian ring
form a finite family. Applying the existing integral Chow construction to
each component gives an actual proper surjective coproduct whose components
are closed in projective spaces over the original ring.

The finite coproduct is proper because its fold map is finite. The latter is
obtained from the existing finite coproduct of identity finite étale covers,
using its preserved underlying coproduct. Thus no coproduct of schemes or
finite étale covers is reconstructed here. The conclusion retains the actual
pairwise pullbacks and the overlap of the single surjective morphism.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A finite coproduct of proper morphisms to a common scheme is proper. -/
theorem IsProper.sigmaDesc_of_finite {ι : Type v} [Finite ι] [Small.{u} ι]
    {X : Scheme.{u}} {Y : ι → Scheme.{u}} (q : ∀ i, Y i ⟶ X)
    [∀ i, IsProper (q i)] : IsProper (Sigma.desc q) := by
  have : IsFiniteEtale (𝟙 X) := .mk
  let E : ι → FiniteEtale X := fun _ => FiniteEtale.mk (𝟙 X)
  let F : FiniteEtale X ⥤ Scheme.{u} :=
    FiniteEtale.forget X ⋙ CategoryTheory.Over.forget X
  let Z : FiniteEtale X := ∐ E
  let p : F.obj Z ⟶ X := Z.hom
  let e : (∐ fun _ : ι => X) ⟶ F.obj Z := sigmaComparison F E
  have : IsIso e := inferInstanceAs (IsIso (sigmaComparison F E))
  have : IsFinite p := (inferInstance : IsFiniteEtale Z.hom).toIsFinite
  have hι (i : ι) : Sigma.ι (fun _ : ι => X) i ≫ e = F.map (Sigma.ι E i) :=
    ι_comp_sigmaComparison F E i
  have hw (i : ι) : F.map (Sigma.ι E i) ≫ p = 𝟙 X :=
    MorphismProperty.Over.w (Sigma.ι E i)
  have hfold : Sigma.desc (fun _ : ι => 𝟙 X) = e ≫ p := by
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_comp_desc]
    exact ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun a : X ⟶ F.obj Z => a ≫ p) (hι i)).trans (hw i))).symm
  have hfinite : IsFinite (Sigma.desc (fun _ : ι => 𝟙 X)) := by
    rw [hfold]
    infer_instance
  have hmap : IsProper (Limits.Sigma.map q) :=
    (IsZariskiLocalAtTarget.sigmaMap_iff q
      (show MorphismProperty Scheme.{u} from @IsProper)).mpr fun _ => inferInstance
  have hdesc : Sigma.desc q =
      Limits.Sigma.map q ≫ Sigma.desc (fun _ : ι => 𝟙 X) := by
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_comp_desc, ← Category.assoc, Sigma.ι_map,
      Category.assoc, Sigma.ι_comp_desc, Category.comp_id]
  rw [hdesc]
  infer_instance

/-- A proper family over a Noetherian affine base admits a finite, jointly
surjective family of integral projective sources. Its actual coproduct cover
is proper and surjective; all the displayed overlaps are the canonical
scheme-theoretic pullbacks over the original family. -/
theorem exists_finite_integral_projective_cover
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] :
    ∃ (m : ℕ) (Y : Fin m → Scheme.{u}) (d : Fin m → ℕ)
      (q : ∀ i, Y i ⟶ X)
      (j : ∀ i, Y i ⟶
        Proj (MvPolynomial.homogeneousSubmodule (Fin (d i + 1)) R)),
      (∀ i, IsIntegral (Y i) ∧ IsProper (q i) ∧ IsClosedImmersion (j i) ∧
        j i ≫ ProjSpace.π R (d i) = q i ≫ f) ∧
      IsProper (Sigma.desc q) ∧ Surjective (Sigma.desc q) ∧
      (∀ i k,
        IsPullback (pullback.fst (q i) (q k)) (pullback.snd (q i) (q k)) (q i) (q k) ∧
        IsProper (pullback.fst (q i) (q k)) ∧
        IsProper (pullback.snd (q i) (q k)) ∧
        IsProper (pullback.fst (q i) (q k) ≫ q i ≫ f)) ∧
      IsPullback (pullback.fst (Sigma.desc q) (Sigma.desc q))
        (pullback.snd (Sigma.desc q) (Sigma.desc q)) (Sigma.desc q) (Sigma.desc q) ∧
      IsProper (pullback.fst (Sigma.desc q) (Sigma.desc q)) ∧
      IsProper (pullback.snd (Sigma.desc q) (Sigma.desc q)) ∧
      IsProper (pullback.fst (Sigma.desc q) (Sigma.desc q) ≫ Sigma.desc q ≫ f) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := {}
  let κ := irreducibleComponents X
  have hfin : (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents
  have : Finite κ := hfin.to_subtype
  let : Fintype κ := Fintype.ofFinite κ
  let c (z : κ) := X.reducedIrreducibleComponentι z.1 z.2
  have hChow (z : κ) :
      ∃ D : ChowDatumProj (c z ≫ f), IsIntegral D.V' ∧ Surjective D.p :=
    ChowDatumProj.exists_integral (c z ≫ f)
  let D (z : κ) : ChowDatumProj (c z ≫ f) := (hChow z).choose
  have hIntegral (z : κ) : IsIntegral (D z).V' := (hChow z).choose_spec.1
  have hSurjective (z : κ) : Surjective (D z).p := (hChow z).choose_spec.2
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  let Y (i : Fin (Fintype.card κ)) := (D (e i)).V'
  let d (i : Fin (Fintype.card κ)) := (D (e i)).Nd
  let q (i : Fin (Fintype.card κ)) : Y i ⟶ X := (D (e i)).p ≫ c (e i)
  let j (i : Fin (Fintype.card κ)) := (D (e i)).ιN
  have hq (i : Fin (Fintype.card κ)) : IsProper (q i) := by
    dsimp only [q, c]
    infer_instance
  have hrange (i : Fin (Fintype.card κ)) : Set.range (q i) = (e i).1 := by
    calc
      Set.range (q i) = Set.range (c (e i)) :=
        range_eq_range_of_surjective (q i) (c (e i)) (D (e i)).p rfl
      _ = (e i).1 := X.range_reducedIrreducibleComponentι (e i).1 (e i).2
  have hunion : ⋃ i, Set.range (q i) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    let z : κ := ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
    apply Set.mem_iUnion.mpr
    refine ⟨e.symm z, ?_⟩
    rw [hrange, e.apply_symm_apply]
    exact mem_irreducibleComponent
  have hproper : IsProper (Sigma.desc q) := IsProper.sigmaDesc_of_finite q
  have hsurj : Surjective (Sigma.desc q) :=
    Surjective.sigmaDesc_of_union_range_eq_univ hunion
  refine ⟨Fintype.card κ, Y, d, q, j, ?_, hproper, hsurj, ?_,
    IsPullback.of_hasPullback _ _, inferInstance, inferInstance, inferInstance⟩
  · intro i
    refine ⟨hIntegral (e i), hq i, (D (e i)).hιN_closed, ?_⟩
    simpa only [q, j, Category.assoc] using (D (e i)).hoverN
  · intro i k
    exact ⟨IsPullback.of_hasPullback _ _, inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry
