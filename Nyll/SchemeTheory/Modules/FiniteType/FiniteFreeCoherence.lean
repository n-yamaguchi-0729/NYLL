/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Modules.FiniteType.FiniteFreeLocus
public import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeLocality
public import Nyll.SchemeTheory.Modules.Sections.FiniteFreeSections
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# Native coherence from compatible finite local bases

An actual compatible basis on an open constructs an isomorphism from
the native finite free sheaf on its slice site. Covering by such opens
therefore supplies native local-generator data that are simultaneously
finite and locally free. Quasicoherence and finite type follow for the
original module sheaf, without a separate sheaf model.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

private def sectionOver {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : Γ(M, U)) : (M.over U).sections :=
  PresheafOfModules.sectionsMk
    (fun W => M.val.map W.unop.hom.op e)
    (fun {V W} f => by
      change M.val.map f.unop.left.op (M.val.map V.unop.hom.op e) =
        M.val.map W.unop.hom.op e
      exact (M.val.map_comp_apply V.unop.hom.op f.unop.left.op e).symm.trans
        (M.val.congr_map_apply (Subsingleton.elim _ _) e))

/-- A compatible finite basis gives an actual finite free trivialization
on the native slice site. -/
theorem IsFiniteFreeOn.exists_free_iso_over
    {X : Scheme.{u}} {M : X.Modules} {U : X.Opens} (hU : IsFiniteFreeOn M U) :
    ∃ n : ℕ, Nonempty
      (SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u} (Fin n)) ≅ M.over U) := by
  classical
  obtain ⟨n, e, he⟩ := hU
  choose b hb using he
  let J := ULift.{u} (Fin n)
  let F := SheafOfModules.overFunctor X.ringCatSheaf U
  have : PreservesColimitsOfSize.{u, u} F :=
    Adjunction.leftAdjoint_preservesColimits
      (SheafOfModules.overPushforwardOverAdj (R := X.ringCatSheaf) U)
  let E : SheafOfModules.free (R := X.ringCatSheaf.over U) J ≅
      F.obj (SheafOfModules.free J) := SheafOfModules.mapFreeIso F J (Iso.refl _)
  let s : J → (M.over U).sections := fun i => sectionOver M U (e i.down)
  let ψ : SheafOfModules.free (R := X.ringCatSheaf.over U) J ⟶ M.over U :=
    (M.over U).freeHomEquiv.symm s
  let φ : F.obj (SheafOfModules.free J) ⟶ M.over U := E.inv ≫ ψ
  have hgenerator (W : Over U) (i : J) :
      φ.val.app (op W)
          ((SheafOfModules.freeSection (R := X.ringCatSheaf) i).val (op W.left)) =
        (s i).val (op W) := by
    have hc : F.map (SheafOfModules.ιFree i) ≫ φ =
        SheafOfModules.ιFree i ≫ ψ := by
      have hfree : F.map (SheafOfModules.ιFree i) ≫ E.inv =
          SheafOfModules.ιFree i :=
        (SheafOfModules.map_ιFree_mapFreeIso_inv F J (Iso.refl _) i).trans
          (Category.id_comp _)
      exact (Category.assoc (F.map (SheafOfModules.ιFree i)) E.inv ψ).symm.trans
        (congrArg (fun k => k ≫ ψ) hfree)
    have hv := congrArg
      (fun k : SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ M.over U =>
        k.val.app (op W) (1 : Γ(X, W.left))) hc
    have hs := congrArg (fun t : (M.over U).sections => t.val (op W))
      (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection s i)
    exact hv.trans hs
  have hφ (W : Over U) : Function.Bijective (φ.val.app (op W)) := by
    let B : Module.Basis J Γ(X, W.left) Γ(M, W.left) :=
      (b W.left W.hom.le).reindex Equiv.ulift.symm
    let A := finiteFreeSectionsEquiv (X := X) J W.left
    let φW : Γ((show X.Modules from SheafOfModules.free J), W.left) →ₗ[Γ(X, W.left)]
        Γ(M, W.left) := (φ.val.app (op W)).hom
    let l : (J →₀ Γ(X, W.left)) →ₗ[Γ(X, W.left)] Γ(M, W.left) :=
      φW.comp A.toLinearMap
    have hl : l = B.repr.symm.toLinearMap := by
      apply Finsupp.lhom_ext
      intro i a
      change φW (finiteFreeSectionsEquiv J W.left (Finsupp.single i a)) =
        B.repr.symm (Finsupp.single i a)
      rw [finiteFreeSectionsEquiv_single, φW.map_smul, Module.Basis.repr_symm_single]
      apply congrArg (fun z : Γ(M, W.left) => a • z)
      have hBi : B i = (s i).val (op W) :=
        ((b W.left W.hom.le).reindex_apply Equiv.ulift.symm i).trans
          (hb W.left W.hom.le i.down)
      exact (hgenerator W i).trans hBi.symm
    have hbij : Function.Bijective l := by
      rw [hl]
      exact B.repr.symm.bijective
    have hcomp : Function.Bijective (fun z => l (A.symm z)) :=
      hbij.comp A.symm.bijective
    simp only [l, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] at hcomp
    exact hcomp
  have hφpres : IsIso
      ((PresheafOfModules.toPresheaf _).map ((SheafOfModules.forget _).map φ)) := by
    have (W : (Over U)ᵒᵖ) : IsIso
        (((PresheafOfModules.toPresheaf _).map
          ((SheafOfModules.forget _).map φ)).app W) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr (hφ W.unop)
    exact NatIso.isIso_of_isIso_app _
  have hφval : IsIso ((SheafOfModules.forget _).map φ) :=
    isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf _)
  have : IsIso φ := isIso_of_reflects_iso φ (SheafOfModules.forget _)
  have : IsIso ψ := IsIso.of_isIso_comp_left E.inv ψ
  exact ⟨n, ⟨asIso ψ⟩⟩

private theorem exists_finite_locallyFreeData_of_finiteFreeLocus_eq_top
    {X : Scheme.{u}} (M : X.Modules) (hM : finiteFreeLocus M = ⊤) :
    ∃ q : SheafOfModules.LocalGeneratorsData.{u} M,
      q.IsFiniteType ∧ q.IsLocallyFreeData := by
  classical
  have hlocal (x : X) : ∃ U : X.Opens, x ∈ U ∧ IsFiniteFreeOn M U := by
    apply (mem_finiteFreeLocus_iff M x).mp
    rw [hM]
    trivial
  choose U hxU hU using hlocal
  choose n hIso using fun x => (hU x).exists_free_iso_over
  let E (x : X) := (hIso x).some
  let G (x : X) : (M.over (U x)).GeneratingSections :=
    (SheafOfModules.free.generatingSections
      (R := X.ringCatSheaf.over (U x)) (ULift.{u} (Fin (n x)))).ofEpi (E x).hom
  have hGiso (x : X) : IsIso (G x).π := by
    let σ := SheafOfModules.free.generatingSections
      (R := X.ringCatSheaf.over (U x)) (ULift.{u} (Fin (n x)))
    have hπ : (G x).π = σ.π ≫ (E x).hom :=
      SheafOfModules.GeneratingSections.ofEpi_π σ (E x).hom
    exact hπ.symm ▸ inferInstanceAs (IsIso (σ.π ≫ (E x).hom))
  let q : SheafOfModules.LocalGeneratorsData.{u} M :=
    { I := X
      X := U
      coversTop := by
        rw [Opens.coversTop_iff]
        apply top_unique
        intro x _
        exact Opens.mem_iSup.mpr ⟨x, hxU x⟩
      generators := G }
  refine ⟨q, ?_, ?_⟩
  · constructor
    intro x
    constructor
    exact inferInstanceAs (Finite (ULift.{u} (Fin (n x))))
  · exact { isIso := fun x => hGiso x }

/-- Compatible finite local bases supply the native local-freeness
predicate for the original module sheaf. -/
theorem isLocallyFree_of_finiteFreeLocus_eq_top
    {X : Scheme.{u}} (M : X.Modules) (hM : finiteFreeLocus M = ⊤) :
    M.IsLocallyFree := by
  obtain ⟨q, _, hq⟩ := exists_finite_locallyFreeData_of_finiteFreeLocus_eq_top M hM
  have : q.IsLocallyFreeData := hq
  exact q.isLocallyFree

/-- A module sheaf covered by compatible finite bases is quasicoherent. -/
theorem isQuasicoherent_of_finiteFreeLocus_eq_top
    {X : Scheme.{u}} (M : X.Modules) (hM : finiteFreeLocus M = ⊤) :
    M.IsQuasicoherent := by
  obtain ⟨q, _, hq⟩ := exists_finite_locallyFreeData_of_finiteFreeLocus_eq_top M hM
  have : q.IsLocallyFreeData := hq
  exact q.quasiCoherentData.isQuasicoherent

/-- The same actual finite local generators give native finite type. -/
theorem isFiniteType_of_finiteFreeLocus_eq_top
    {X : Scheme.{u}} (M : X.Modules) (hM : finiteFreeLocus M = ⊤) :
    M.IsFiniteType := by
  obtain ⟨q, hq, _⟩ := exists_finite_locallyFreeData_of_finiteFreeLocus_eq_top M hM
  exact q.isFiniteType hq

end AlgebraicGeometry.Scheme.Modules
