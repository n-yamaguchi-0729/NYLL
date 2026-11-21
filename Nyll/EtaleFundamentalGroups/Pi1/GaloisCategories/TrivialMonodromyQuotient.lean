/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Pi1.GaloisCategories.TrivialMonodromyFiber
public import Nyll.EtaleFundamentalGroups.Pi1.GaloisCategories.TrivialMonodromy
public import Nyll.EtaleFundamentalGroups.GaloisCategories.Functoriality
public import Nyll.EtaleFundamentalGroups.GaloisCategories.Surjectivity
public import Nyll.EtaleFundamentalGroups.GaloisCategories.PointStabilizerMorphism
public import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenNormalUniverse
public import Nyll.ProCGroups.ProC.OpenNormalSubgroups.FilteredFamilies
public import Nyll.ProCGroups.Topologies.ContinuousMulEquiv
public import Nyll.ProCGroups.Topologies.QuotientMaps

/-!
# The fundamental group of a trivial-monodromy Galois category

Restriction to the actual objects on which a closed normal subgroup `N` acts
trivially is surjective on fibre-functor automorphisms and has kernel exactly
`N`. To detect the kernel, every open normal subgroup containing `N` is
realized by a pointed Galois object in the original category. Thus the
restricted fibre functor has fundamental group canonically `Aut F / N`,
with the comparison retaining the original automorphism representatives.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory Limits
open scoped FintypeCatDiscrete

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u} [Category.{v} C] [GaloisCategory C]
  (F : C ⥤ FintypeCat.{w}) [FiberFunctor F] (N : Subgroup (Aut F))

omit [GaloisCategory C] [FiberFunctor F] in
/-- Every element of the prescribed subgroup acts trivially after restriction. -/
theorem le_ker_trivialMonodromyRestriction :
    N ≤ (trivialMonodromyRestrictionAt F N F).toMonoidHom.ker := by
  intro g hg
  change trivialMonodromyRestrictionAt F N F g = 1
  apply Aut.ext
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply FintypeCat.hom_ext
  intro x
  exact (trivialMonodromy_iff F N X.obj).mp X.property g hg x

variable [N.Normal] (hN : IsClosed (N : Set (Aut F)))

include hN in
/-- Finite Galois objects detect every element outside the closed normal subgroup. -/
theorem trivialMonodromyRestriction_ker :
    (trivialMonodromyRestrictionAt F N F).toMonoidHom.ker = N := by
  apply le_antisymm ?_ (le_ker_trivialMonodromyRestriction F N)
  intro g hg
  let K : ClosedSubgroup (Aut F) := ⟨N, hN⟩
  change g ∈ (K : Subgroup (Aut F))
  rw [ProCGroups.ProC.closedSubgroup_eq_sInf_openNormal K]
  simp only [Subgroup.mem_sInf, Set.mem_ofPred_eq]
  intro U hU
  let V : OpenNormalSubgroup (Aut F) :=
    { toSubgroup := U
      isOpen' := hU.1
      isNormal' := hU.2.2 }
  obtain ⟨A, hA, x, hx⟩ := exists_galois_object_point_stabilizer_eq_any_universe F V
  have : IsGalois A := hA
  have hAN : trivialMonodromy F N A := by
    apply (trivialMonodromy_iff F N A).mpr
    intro n hn y
    change n ∈ MulAction.stabilizer (Aut F) y
    rw [← stabilizer_eq_of_isGalois F A x y, hx]
    exact hU.2.1 hn
  let B : TrivialMonodromy F N := ⟨A, hAN⟩
  have hfix : (trivialMonodromyRestrictionAt F N F g).asIso.hom.app B x = x := by
    rw [show trivialMonodromyRestrictionAt F N F g = 1 from hg]
    rfl
  rw [trivialMonodromyRestrictionAt_apply] at hfix
  have hstab : g ∈ MulAction.stabilizer (Aut F) x := hfix
  rw [hx] at hstab
  exact hstab

/-- The restriction map descended through the prescribed closed normal subgroup. -/
def trivialMonodromyQuotientMap :
    Aut F ⧸ N →ₜ* Aut (trivialMonodromyFiber F N) :=
  ProCGroups.QuotientGroup.liftₜ N (trivialMonodromyRestrictionAt F N F)
    (le_ker_trivialMonodromyRestriction F N)

omit [GaloisCategory C] [FiberFunctor F] in
/-- The descended restriction map retains each original automorphism. -/
@[simp] theorem trivialMonodromyQuotientMap_apply_mk (g : Aut F) :
    trivialMonodromyQuotientMap F N (QuotientGroup.mk' N g) =
      trivialMonodromyRestrictionAt F N F g := rfl

include hN in
/-- The quotient restriction map is bijective by its exact original kernel. -/
theorem trivialMonodromyQuotientMap_bijective :
    Function.Bijective (trivialMonodromyQuotientMap F N) := by
  constructor
  · apply (MonoidHom.ker_eq_bot_iff
      (trivialMonodromyQuotientMap F N).toMonoidHom).mp
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro a ha
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N a
    apply (QuotientGroup.eq_one_iff (N := N) g).mpr
    rw [← trivialMonodromyRestriction_ker F N hN]
    exact ha
  · intro a
    obtain ⟨g, rfl⟩ := trivialMonodromyRestrictionAt_surjective F N F a
    exact ⟨QuotientGroup.mk' N g, rfl⟩

/-- The automorphism group of the restricted fibre functor is canonically the
quotient of the original group; the inverse gives the opposite comparison. -/
def trivialMonodromyQuotientEquiv :
    Aut F ⧸ N ≃ₜ* Aut (trivialMonodromyFiber F N) :=
  ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2
    (trivialMonodromyQuotientMap F N).toMonoidHom
    (trivialMonodromyQuotientMap F N).continuous_toFun
    (trivialMonodromyQuotientMap_bijective F N hN)

/-- The comparison identifies the quotient projection with actual restriction. -/
@[simp] theorem trivialMonodromyQuotientEquiv_apply_mk (g : Aut F) :
    trivialMonodromyQuotientEquiv F N hN (QuotientGroup.mk' N g) =
      trivialMonodromyRestrictionAt F N F g := rfl

/-- The inverse comparison sends a restricted automorphism to its original quotient class. -/
@[simp] theorem trivialMonodromyQuotientEquiv_symm_apply_restriction (g : Aut F) :
    (trivialMonodromyQuotientEquiv F N hN).symm
        (trivialMonodromyRestrictionAt F N F g) = QuotientGroup.mk' N g := by
  rw [← trivialMonodromyQuotientEquiv_apply_mk F N hN g]
  exact (trivialMonodromyQuotientEquiv F N hN).symm_apply_apply _

end CategoryTheory.PreGaloisCategory
